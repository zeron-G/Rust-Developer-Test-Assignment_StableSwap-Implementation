## 1. Research Background & Research Content

### 1.1. Background and Motivation

Decentralized exchanges (DEXs) rely on constant-function market makers (CFMMs) to quote prices without order books. The most prominent baseline, Uniswap V2, uses the constant-product formula $x\cdot y=k$, which guarantees continuous liquidity but yields curvature-driven slippage that is unnecessarily large when the two assets should trade near a fixed parity (e.g., stablecoins) (Adams, Zinsmeister, & Robinson, 2020; Uniswap Labs, n.d.). ([Uniswap][1], [Uniswap][2]) In practice, capital efficiency concerns around uniform liquidity distribution have motivated refined AMM designs, such as Uniswap V3’s concentrated-liquidity model, which explicitly acknowledges inefficiency of constant-product for assets expected to remain near a reference price (Adams et al., 2021). ([Uniswap][3])

Curve’s StableSwap algorithm addresses this stable-pair inefficiency by modifying the invariant so that, around the 1:1 region, the curve approximates a constant-sum segment (very low price impact) while asymptotically reverting toward constant-product away from parity (Egorov, 2019). ([stableswap-paper][4], [Curve][5]) This behavior is governed by an amplification coefficient $A$ that flattens the curve locally yet preserves global safety. For USDC/USDT on Solana—the target pair of this library—both tokens use 6-decimal fixed-point units, so an implementation suitable for on-chain use should adopt integer arithmetic with 6-decimal scaling (Solana Foundation, n.d.; Solscan, n.d.; SolanaFM, n.d.). ([Solana][6], [Solscan][7], [SolanaFM | Next-Gen Solana Explorer][8])

### 1.2. Problem Statement

Given reserves $(x_0,x_1)$ and amplification $A$, compute: (i) the StableSwap invariant $D$ for the current state, and (ii) the post-trade balance $y$ that preserves $D$ after adding a fee-adjusted input $\Delta x$ to one side, yielding an output $\Delta y$ on the other. The computation must be **deterministic**, **integer-only** (to match on-chain semantics), **numerically stable** (avoid overflow and catastrophic cancellation), and **conservative** in rounding to protect the invariant. These requirements are standard in Curve’s mathematical design and community derivations of the Newton steps for $D$ and $y$ (Egorov, 2019; RareSkills, n.d.). ([stableswap-paper][4], [RareSkills][9])

### 1.3. Research Content

**Scope.** We implement the two-asset StableSwap (USDC/USDT) using the whitepaper invariant and provide a constant-product baseline for controlled comparisons. The library is chain-agnostic but adopts Solana-style **6-decimal** fixed-point I/O with **u128** intermediates for headroom.

**(1) Formalization of the Invariant and Newton Solvers.**
We encode the two-asset StableSwap invariant

$$
A n^n \sum x_i + D \;=\; A n^n D \;+\; \frac{D^{n+1}}{n^n \prod x_i}\quad(n=2),
$$

derive $F(D)=0$ and its derivative $F'(D)$, and implement a **closed-form Newton step** that avoids subtractive cancellation. We also derive the scalar equation $f(y)=0$ at fixed $D$ and its closed-form Newton update for $y$. Both iterations terminate when consecutive iterates differ by at most one token-unit, yielding deterministic integer solutions suitable for smart-contract contexts (Egorov, 2019; RareSkills, n.d.). ([stableswap-paper][4], [RareSkills][9])

**(2) Integer Arithmetic & Rounding Policy.**
All quantities at the API boundary are 6-decimal `u64`; all internal operations promote to `u128` and use safe multiply-then-divide routines. Output amounts are rounded **down** and decreased by one minimal unit to conservatively preserve the invariant, mirroring on-chain implementations (Egorov, 2019). ([stableswap-paper][4])

**(3) Baseline and Evaluation.**
We implement a constant-product $x y = k$ baseline (without fees) and unit tests that (a) verify monotonicity of $D$ with liquidity, (b) confirm **lower slippage** than constant-product for balanced reserves and moderate $A$, and (c) validate fee-on-input accounting. This aligns with the literature’s critique of uniform-liquidity AMMs for near-peg assets (Adams et al., 2021; Uniswap Labs, n.d.; Egorov, 2019). ([Uniswap][3], [Uniswap][2], [stableswap-paper][4])

**(4) Token-Unit Choice (USDC/USDT on Solana).**
USDC’s Solana mint `EPjF…` is the canonical address referenced in Solana’s official docs; explorers report **6 decimals** for both USDC and USDT on Solana, motivating the library’s fixed-point scale (Solana Foundation, n.d.; Solscan, n.d.; SolanaFM, n.d.). ([Solana][6], [Solscan][7], [SolanaFM | Next-Gen Solana Explorer][8])

## Significance

The implementation provides a **transparent, reproducible** reference for StableSwap mathematics in Rust, suitable for teaching, research, and as a foundation for on-chain ports. By contrasting StableSwap with constant-product under identical test harnesses, the repository demonstrates why a carefully tuned $A$ markedly reduces price impact for stable pairs—an effect widely recognized in the AMM literature and practice (Egorov, 2019; Adams et al., 2021). ([stableswap-paper][4], [Uniswap][3])

# 2. Mathematical Model — Derivation, Proofs, and Numerical Solvers (General $n \to n=2$)

## 2.1. Setting, Axioms, and Minimal Normalization (General $n$)

Let $n\ge 2$ assets have **positive** balances $x_1,\dots,x_n>0$. Define

$$
S \;\equiv\; \sum_{i=1}^n x_i,\qquad 
P \;\equiv\; \prod_{i=1}^n x_i,
$$

and let $A>0$ be the amplification parameter. We seek an invariant $D=D(x_1,\dots,x_n;A)>0$ that satisfies:

* **(H) Homogeneity (degree 1):** $D(\tau x_1,\dots,\tau x_n;A)=\tau\,D(x_1,\dots,x_n;A)$ for all $\tau>0$.
* **(S) Constant-sum behavior near parity:** when $x_1\approx\dots\approx x_n$, marginal price impact is (locally) linear with slope $\approx 1$.
* **(C) Constant-product behavior far from parity:** when imbalanced, the curve reverts to product-type behavior to preserve finite liquidity.
* **(A) Single-parameter control:** a single $A$ tunes flatness near parity.

To encode (H) and keep algebra minimal, we write the **two canonical benchmarks** directly at **degree $n$** in $(x_i)$ and $D$:

**Sum benchmark (degree $n$)**

$$
\,D^{\,n-1}\,\sum_{i=1}^{n} x_i \;=\; D^{\,n}\,
\quad\Longleftrightarrow\quad
\sum_{i=1}^{n} x_i \;=\; D.
\tag{2.2.1a}
$$
**Product benchmark (degree $n$)**

$$
\prod_{i=1}^{n} x_i \;=\; \Big(\frac{D}{n}\Big)^{\!n}\,
\quad\Longleftrightarrow\quad
\Big(\prod x_i\Big)^{1/n} \;=\; \frac{D}{n}.
\tag{2.2.1b}
$$

At perfect balance $x_i=D/n$, both (2.2.1a) and (2.2.1b) hold. Writing them at the same total degree ensures homogeneity and simplifies blending.

---

## 2.2. Constructing the Invariant via a Single Weighted Constraint (General $n$)

**Blend the benchmarks.** Introduce a weight $\lambda>0$ and combine (2.2.1a–b) into one degree-$n$ identity:

$$

\lambda\,D^{\,n-1}\sum_{i=1}^{n} x_i \;+\; \prod_{i=1}^{n} x_i=\lambda\,D^{\,n} \;+\; \Big(\frac{D}{n}\Big)^{\!n}
\tag{2.2.2}
$$

This holds exactly at parity for any $\lambda>0$, is symmetric in $(x_i)$, and is degree-$n$ homogeneous.

**Dynamic weight.** To obtain a useful invariant with a **single tuning parameter $A>0$**, make $\lambda$ **state-dependent**:

$$
\lambda \;\equiv\; \frac{A\,\prod_{i=1}^{n} x_i}{\big(D/n\big)^{n}}=\frac{A\,n^{n}\,P}{D^{\,n}}
\tag{2.2.3}
$$

**Derivation of the invariant.** Substitute (2.2.3) into (2.2.2) and simplify carefully.

Left-hand side:

$$
\lambda\,D^{\,n-1}S + P=\Big(\frac{A n^{n} P}{D^{\,n}}\Big) D^{\,n-1} S + P=\frac{A n^{n} P}{D}\,S + P.
$$

Right-hand side:

$$
\lambda\,D^{\,n} + \Big(\frac{D}{n}\Big)^{\!n}=\Big(\frac{A n^{n} P}{D^{\,n}}\Big) D^{\,n} + \frac{D^{\,n}}{n^{n}}=A n^{n} P + \frac{D^{\,n}}{n^{n}}.
$$

Equate LHS and RHS and multiply by $D>0$:

$$
A n^{n} P\,S + P\,D=A n^{n} P\,D + \frac{D^{\,n+1}}{n^{n}}.
$$

Divide by $P>0$ and set $\mathrm{Ann}\equiv A n^{n}$ to obtain the **final invariant** (general $n$):

$$
\mathrm{Ann}\,S \;+\; D=\mathrm{Ann}\,D \;+\; \frac{D^{\,n+1}}{n^{n}\,P}
\tag{2.2.4}
$$

This is the Curve StableSwap invariant in the whitepaper form, now derived from the minimal benchmarks with a dynamic weight.

**Immediate checks.**

1. **Parity:** If $x_i=D/n$, then $S=D$ and $P=(D/n)^n$; plugging into (2.2.4) yields an identity.
2. **Homogeneity:** Replacing $x_i\mapsto \tau x_i$ and $D\mapsto \tau D$ leaves (2.2.4) invariant (each term scales by $\tau$).
3. **Single-parameter control:** $\mathrm{Ann}=A n^{n}$ is the only appearance of $A$. As $\mathrm{Ann}\to\infty$, (2.2.4) forces $D\to S$ (constant-sum limit). As $\mathrm{Ann}\to 0^+$, it forces $D^n=n^nP\Rightarrow D=nP^{1/n}$ (constant-product limit).

---

## 2.3. Core Properties of the Invariant (General $n$)

Let

$$
F(D)\;\equiv\;\mathrm{Ann}\,S + D - \mathrm{Ann}\,D - \frac{D^{\,n+1}}{n^{n}P}.
$$

### 2.3.1 Existence and uniqueness

$F$ is continuous on $(0,\infty)$, with $F(0^+)=\mathrm{Ann}\,S>0$ and $F(\infty)=-\infty$. Moreover,

$$
F'(D)=1-\mathrm{Ann}-\frac{(n+1)D^{\,n}}{n^{n}P}\;<\;0\quad(\forall D>0).
$$

Thus $F$ is strictly decreasing from $+\infty$ to $-\infty$, proving a **unique** positive root $D$.

### 2.3.2 Upper bound and equality condition

Evaluate at $D=S$ and use AM–GM, $S^{n}\ge n^{n}P$:

$$
F(S)=S-\frac{S^{\,n+1}}{n^{n}P}=S\!\left(1-\frac{S^{n}}{n^{n}P}\right)\le 0.
$$

Since $F(0^+)>0$ and $F$ is strictly decreasing, the unique root satisfies

$$
D\le S,\quad D=S\iff x_1=\cdots=x_n.
$$

### 2.3.3 Monotonicity in each reserve

Compute the partial (holding $D$ fixed):

$$
\frac{\partial F}{\partial x_j}=\mathrm{Ann}\;+\;\frac{D^{\,n+1}}{n^{n}P}\cdot\frac{1}{x_j}\;>\;0.
$$

Since $F'(D)<0$, the implicit function theorem yields

$$
\frac{\partial D}{\partial x_j}
=-\frac{(\partial F/\partial x_j)}{F'(D)}\;>\;0,
$$

i.e., **increasing any reserve strictly increases $D$**.

### 2.3.4 Homogeneity and symmetry

Equation (2.2.4) is invariant under $(x,D)\mapsto(\tau x,\tau D)$, so $D$ is degree-1 homogeneous. The equation is symmetric in the $x_i$’s.

### 2.3.5 Limiting regimes in $A$

Divide (2.2.4) by $\mathrm{Ann}$:

$$
S+\frac{D}{\mathrm{Ann}}=D+\frac{D^{\,n+1}}{\mathrm{Ann}\,n^{n}P}.
$$

As $\mathrm{Ann}\to\infty$, vanish the $1/\mathrm{Ann}$ terms to get $S=D$.
As $\mathrm{Ann}\to 0^+$, (2.2.4) gives $D^{n}=n^{n}P\Rightarrow D=n\,P^{1/n}$.

---

## 2.4. Newton’s Method for $D$ (General $n$)

Define

$$
D_P(D)\;\equiv\;\frac{D^{\,n+1}}{n^{n}P},\qquad
F'(D)=1-\mathrm{Ann}-\frac{(n+1)}{D}D_P(D).
$$

A single Newton step is

$$
D_{\text{new}}
= D - \frac{\mathrm{Ann}S + D - \mathrm{Ann}D - D_P}{1 - \mathrm{Ann} - (n+1)D_P/D}.
$$

Multiplying numerator and denominator by $D$ and simplifying yields the **closed-form, subtraction-free** update:

$$
D_{\text{new}}
=\frac{\big(\mathrm{Ann}\,S + n\,D_P\big)\,D}{(\mathrm{Ann}-1)\,D + (n+1)\,D_P}
\tag{2.4.1}
$$

This form is robust under integer arithmetic. In implementations, evaluate $D_P$ by **iterated safe mul/div** to avoid overflow.

**Convergence from a natural guess.** Let $r$ be the unique root. From §2.3.2, $r\le S$. With $D_0=S$, note

$$
F''(D)= -\frac{(n+1)n\,D^{\,n-1}}{n^{n}P}<0,
$$

so $F$ is strictly decreasing and strictly concave on $(0,\infty)$. By the standard Newton monotonicity lemma for decreasing concave functions, $(D_k)$ defined by (2.4.1) is decreasing and bounded below by $r$, hence converges to $r$ (typically in <10 iterations).

---

## 2.5. Solving the Post-Trade Balance $y$ at Fixed $D$ (General $n$)

Suppose after an input-side fee, net input $\Delta x_{\text{net}}$ is added to asset $i$, so $x_i' = x_i + \Delta x_{\text{net}}$. For output on asset $j\neq i$, **hold $D$ fixed** and solve for the new balance $y\equiv x'_j$. Let

$$
S' \;\equiv\; \sum_{k\ne j} x_k,\qquad
Q_j \;\equiv\; \prod_{k\ne j} x_k.
$$

Insert $(x_i',y)$ into (2.2.4):

$$
\mathrm{Ann}(S'+y) + D
\;=\;
\mathrm{Ann}D + \frac{D^{\,n+1}}{n^{n}\,(y\,Q_j)}.
$$

Multiply by $y$ and rearrange:

$$
\mathrm{Ann}\,y^2 + (\mathrm{Ann}S' + D - \mathrm{Ann}D)\,y - \frac{D^{\,n+1}}{n^{n}Q_j} = 0.
$$

Divide by $\mathrm{Ann}$ and define

$$
b \;\equiv\; S' + \frac{D}{\mathrm{Ann}},\qquad
c \;\equiv\; \frac{D^{\,n+1}}{n^{n}\,\mathrm{Ann}\,Q_j},
$$

to obtain the **canonical quadratic**:

$$
f(y)=y^2 + (b - D)\,y - c = 0
\tag{2.5.1}
$$

### 2.5.1 Existence, uniqueness, and positivity

$f$ is monic with $f''(y)=2>0$ (strictly convex), $f(0)=-c<0$, and $f(y)\to+\infty$ as $y\to\infty$; hence there is a **unique positive root** $y^\star>0$.

### 2.5.2 Newton’s update for $y$

With $f'(y)=2y+(b-D)$, Newton’s method gives the **single-division update**

$$
y \leftarrow \frac{y^2 + c}{\,2y + b - D\,}
\tag{2.5.2}
$$

Initialize $y:=D$ (positive, correct scale) and stop when $|\Delta y|\le 1$ (integer tolerance). The **ideal** output is $\Delta y_{\text{ideal}}=x_j-y^\star$; to protect the invariant under integer truncation, implementations return $\Delta y = x_j - y - 1$.

**Safety.** For $y>0$, $2y+b-D \ge y+b>0$, so division by zero cannot occur. Newton converges monotonically to $y^\star$ on $[y^\star,\infty)$ for convex monic quadratics; empirically a few iterations suffice.

---

## 2.6. Local Behavior and Regimes (General $n$)

* **Near parity (constant-sum).** Writing (2.2.4) in normalized variables gives
  $\mathrm{Ann}\cdot(\tfrac{1}{n}\sum y_i)+1=\mathrm{Ann}+1/(\prod y_i)$.
  Linearizing around $y_i=1$ forces $\sum(y_i-1)=O(\|y-1\|^2)$: **first-order sum preservation**, i.e., slope $\approx 1$ per unit moved—constant-sum-like. Larger $A$ suppresses higher-order curvature.
* **Imbalance (constant-product).** As imbalance grows, $D^{\,n+1}/(n^{n}P)$ dominates (2.2.4), pushing behavior toward constant-product. In the dynamic-$\lambda$ view, $\lambda\propto P/(D/n)^n$ increases with product deviations, emphasizing the product term.

---

## 2.7. Specialization to Two Assets ($n=2$)

With $n=2$ (the implementation case), let $\mathrm{Ann}=4A$, $S=x_1+x_2$, $P=x_1x_2$.

* **Invariant (from (2.2.4)).**

  $$
  \mathrm{Ann}\,(x_1+x_2) + D
  \;=\;
  \mathrm{Ann}\,D + \frac{D^{3}}{4\,x_1 x_2}.
  $$
* **Newton for $D$ (from (2.4.1)).** With $D_P=D^{3}/(4 x_1 x_2)$,

  $$
  D \;\leftarrow\; \frac{(\mathrm{Ann}(x_1+x_2) + 2D_P)\,D}{(\mathrm{Ann}-1)\,D + 3D_P}.
  $$
* **Solve $y$ at fixed $D$ (from (2.5.1)–(2.5.2)).**
  Here $S'=x_i'$, $Q_j=x_i'$, so

  $$
  b = x_i' + \frac{D}{\mathrm{Ann}},\qquad
  c = \frac{D^{3}}{4\,\mathrm{Ann}\,x_i'},\qquad
  y \leftarrow \frac{y^2 + c}{\,2y + b - D\,}.
  $$

These are exactly the formulas used in the code.

## 3. stable-swap-rs — Install via Git & Usage Guide

> **TL;DR**
>
> * Package name (Cargo dependency key): `stable-swap-rs`
> * **Crate name** (what you `use` in Rust): `stable_swap_rs`
> * Token amounts use **6 decimals** (e.g., `1 USDC = 1_000_000`)

---

### 3.1. Overview

A pure-math implementation of Curve’s **StableSwap** algorithm for a **two-asset** stablecoin pool (USDC/USDT).

* Invariant **D** and post-trade **y** via Newton’s method
* Integer-only arithmetic (`u128` internally)
* Input-side fee in **bps**
* Constant-product (x\*y=k) baseline for slippage comparison

This library is chain-agnostic and suitable for on-chain ports or off-chain simulation.

---

### 3.2. Requirements

* **Rust** 1.67+ (2021 edition)
* Platform with `u128` integer support (stable Rust toolchains do)

---

### 3.3. Install from Git (Recommended)

Add the dependency to your project’s `Cargo.toml` (replace with your real GitHub URL and an immutable tag or commit):

```toml
[dependencies]
# Git tag (recommended)
stable-swap-rs = { git = "https://github.com/zeron-G/Rust-Developer-Test-Assignment_StableSwap-Implementation", tag = "v0.1.0" }
# Or pin to a commit
# stable-swap-rs = { git = "https://github.com/zeron-G/Rust-Developer-Test-Assignment_StableSwap-Implementation", rev = "<commit-hash>" }
```

> **Note on names**
> The **package name** is `stable-swap-rs` (used in `Cargo.toml`).
> The **crate name** is `stable_swap_rs` (used in `use` statements).

---

### 3.4. Quickstart

Create a small binary to try the library:

```bash
cargo new demo-stable --bin
cd demo-stable
```

Edit `demo-stable/Cargo.toml` and add the Git dependency as shown above. Then paste the following into `src/main.rs`:

```rust
use stable_swap_rs::{StableSwapPool, constant_product_dy};

fn main() -> anyhow::Result<()> {
    // Amounts are 6-decimal integers: 1 USDC = 1_000_000
    // Build a balanced pool: 10,000 USDC & 10,000 USDT
    let mut pool = StableSwapPool::new(
        [10_000_000_000, 10_000_000_000], // 10,000 * 1e6
        100, // A = 100
    );
    pool.fee_bps = 30; // 0.30% input-side fee

    // Quote: swap 100 USDC -> USDT
    let dx: u64 = 100_000_000; // 100 * 1e6
    let dy = pool.get_dy(0, 1, dx).expect("quote failed");
    println!("StableSwap quote: 100 USDC -> {} USDT (6dp int)", dy);

    // Compare with constant product (no fee)
    let dy_xyk = constant_product_dy(pool.reserves, 0, 1, dx).unwrap();
    println!("x*y=k (no fee) output: {}", dy_xyk);

    // --- Executing the swap (caller updates reserves) ---
    let fee_bps = pool.fee_bps as u128;
    let dx_net = (dx as u128) * (10_000u128 - fee_bps) / 10_000u128;

    pool.reserves[0] = (pool.reserves[0] as u128 + dx_net) as u64; // add net input
    pool.reserves[1] = pool.reserves[1].checked_sub(dy)
        .expect("insufficient reserve for execution"); // subtract output

    // Optional: inspect invariant D after trade
    let d_now = pool.get_d();
    println!("D after trade: {}", d_now);

    // Curve-only slippage estimate (ignoring fees)
    let s_bps = pool.calculate_slippage_bps(100_000_000);
    println!("curve-only slippage for 100 USDC: {} bps", s_bps);

    Ok(())
}
```

Run it:

```bash
cargo run -q
```

---

### 3.5. API Snapshot

```rust
pub struct StableSwapPool {
    pub reserves: [u64; 2],
    pub amplification_coefficient: u64, // A
    pub fee_bps: u16,                   // input-side fee in bps
}
impl StableSwapPool {
    pub fn new(reserves: [u64; 2], amp: u64) -> Self;
    pub fn get_dy(&self, i: usize, j: usize, dx: u64) -> Result<u64, SwapError>;
    pub fn get_d(&self) -> u64;
    pub fn calculate_slippage_bps(&self, amount: u64) -> u16;
}

/// Constant-product baseline (no fee)
pub fn constant_product_dy(reserves: [u64;2], i: usize, j: usize, dx: u64) -> Option<u64>;
```

#### Units

* **All token amounts** are integers with **6 decimals** (USDC/USDT standard on Solana, but general-purpose here).
  Example: `1 USDC = 1_000_000`.

#### Errors

`get_dy` may return: `BadIndex`, `ZeroTrade`, `NoLiquidity`, `NoConvergence`, `Math`.
Callers should handle these explicitly.

---

### 3.6. Executing a Swap (State Update Contract)

`get_dy` is a **pure quote**. To "execute" a trade, the caller is responsible for mutating pool state consistently:

1. Compute net input: `dx_net = dx * (10000 - fee_bps) / 10000`
2. Update reserves:

   * `reserves[i] += dx_net`
   * `reserves[j] -= dy`
3. (Optional) Recompute `D` for observability/metrics

This separation allows you to quote multiple trades safely before committing.

---

### 3.7. Design Notes (What To Expect)

* **Integer-only math**: internal arithmetic uses `u128`; fractions are evaluated via a safe `mul_div` (checked multiply then divide).
* **Conservative rounding**: outputs are rounded down and reduced by 1 minimal unit to protect the invariant (standard on-chain practice).
* **Low slippage near balance**: with moderate `A` (e.g., 50–200) and balanced reserves, StableSwap outputs are strictly higher than constant-product for the same input.
* **Graceful degradation**: far from balance and for large trades, behavior transitions toward constant-product.

---

### 3.8. Versioning & Minimum Supported Rust Version (MSRV)

* **Versioning**: semantic versioning (`MAJOR.MINOR.PATCH`). Pin a **tag** or commit in your `Cargo.toml` for reproducibility.
* **MSRV**: tested with Rust 1.67+ (Edition 2021). We aim to avoid unstable features.

---

### 3.9. Testing

Clone the library and run:

```bash
cargo test -q
```

The tests cover: monotonicity of `D`, fee-on-input behavior, and lower slippage vs. x\*y=k in balanced pools.


Below is **Section 4 — function–by–function analysis** in English, written as a stand-alone reference that maps each piece of code to the mathematics from **Section 2** (general $n$ with specialization to $n=2$). I use the equation labels from Section 2:

* **(2.2.4)** — StableSwap invariant (general $n$)
  $\mathrm{Ann}\,S + D = \mathrm{Ann}\,D + \dfrac{D^{\,n+1}}{n^{n}P}$
* **(2.4.1)** — Newton update for $D$ (general $n$)
  $D \leftarrow \dfrac{\big(\mathrm{Ann}\,S + n\,D_P\big)\,D}{(\mathrm{Ann}-1)\,D + (n+1)\,D_P}$, with $D_P=\dfrac{D^{\,n+1}}{n^{n}P}$
* **(2.5.1)** — Quadratic for $y$ at fixed $D$ (general $n$)
  $y^2 + (b - D)\,y - c = 0$, where $b = S' + \dfrac{D}{\mathrm{Ann}}$, $c = \dfrac{D^{\,n+1}}{n^{n}\,\mathrm{Ann}\,\prod_{k\ne j}x_k}$
* **(2.5.2)** — Newton update for $y$ (closed form)
  $y \leftarrow \dfrac{y^2 + c}{\,2y + b - D\,}$

Throughout the code, $n=2$ (USDC/USDT), so $n^n=4$ and $\mathrm{Ann}=A\cdot 4$.

---

# 4. Code Analysis

## 4.1 Constants, error types, and units

```rust
const BPS_DENOM: u128 = 10_000;
const N_COINS: usize = 2;
const MAX_ITERS: usize = 256;
```

* `BPS_DENOM` fixes basis-points arithmetic (fees on input).
* `N_COINS = 2` specializes the general-$n$ model to the implementation case.
* `MAX_ITERS` is a hard cap for Newton iterations; convergence is typically < 10 iterations due to concavity/convexity proofs in §2.4 and §2.5.

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SwapError { BadIndex, ZeroTrade, NoLiquidity, NoConvergence, Math }
```

* Encodes well-typed failure modes tied to the math:

  * `BadIndex`: violates $i\neq j$ or out of range (precondition of the two-asset formulation).
  * `ZeroTrade`: trivial query $\Delta x=0$.
  * `NoLiquidity`: some $x_i=0$ ⇒ $P=0$ invalid in (2.2.4).
  * `NoConvergence`: fails to reach $|\Delta|\le 1$ within `MAX_ITERS` (extremely rare).
  * `Math`: overflow or divide-by-zero guard in integer arithmetic.

**Units:** All public amounts are 6-decimal fixed-point integers (`u64`). Internals use `u128` to preserve headroom for products like $D^{3}$ in $n=2$.

---

## 4.2 `StableSwapPool` — state and parameters

```rust
pub struct StableSwapPool {
    pub reserves: [u64; N_COINS],
    pub amplification_coefficient: u64, // A
    pub fee_bps: u16,                   // input-side fee
}
```

* `reserves` implement $(x_0,x_1)$ (Section 2: $x_i>0$).
* `amplification_coefficient` is $A$ (Section 2).
* `fee_bps` is applied **on input** (kept out of the core invariant, which is fee-free by design).

Constructor:

```rust
pub fn new(reserves: [u64; N_COINS], amp: u64) -> Self
```

* Initializes the state; leaves `fee_bps=0` so you can quote fee-free and then toggle fees explicitly.

---

## 4.3 `ann()` — $\mathrm{Ann}=A\,n^n$ (specialized to $n=2$)

```rust
fn ann(&self) -> u128 { (self.amplification_coefficient as u128) * 4u128 }
```

* Implements $\mathrm{Ann}=A\cdot n^{n}$ from (2.2.4). With $n=2$, $n^n=4$.

---

## 4.4 `get_d()` — compute the invariant $D$

```rust
pub fn get_d(&self) -> u64 {
    let amp = self.ann();                // Ann
    let x = [self.reserves[0] as u128, self.reserves[1] as u128];
    let d = compute_d(&x, amp);
    d as u64
}
```

* Thin wrapper that calls the Newton solver `compute_d` to return the unique root of (2.2.4).
* The mapping is direct: input $x=(x_0,x_1)$ and $\mathrm{Ann}$ → solve for $D$.

---

## 4.5 `compute_d()` — Newton’s method for $D$ (Eq. 2.4.1)

```rust
fn compute_d(x: &[u128; N_COINS], ann: u128) -> u128 {
    let s = x[0] + x[1];    // S = sum x_i
    if s == 0 { return 0; }
    let mut d = s;          // initial guess D0 = S  (cf. §2.4 convergence lemma)
```

* `d = s` is the recommended initial guess. In §2.3.2, $D\le S$ and $D=S$ iff balanced; with $F''<0$ (§2.4), Newton from $S$ is monotone decreasing and convergent.

**Safe construction of $D_P = \dfrac{D^{n+1}}{n^n \prod x_i}$ (here $n=2$)**

```rust
    for _ in 0..MAX_ITERS {
        let mut d_p = d; // start with D
        for k in 0..N_COINS {
            let denom = x[k].saturating_mul(N_COINS as u128);
            if denom == 0 { return 0; }
            d_p = match mul_div(d_p, d, denom) { Some(v) => v, None => return 0 };
        }
```

* Loop proves: after the first pass, $d_p = \dfrac{D^2}{x_0 n}$; after second,
  $d_p = \dfrac{D^3}{x_0 x_1 n^2} = \dfrac{D^{n+1}}{n^n \prod x_i}$.
  This is exactly the $D_P$ used in (2.4.1).
* `mul_div` performs **checked** multiply then divide to avoid overflow and division by zero.

**Closed-form Newton step (Eq. 2.4.1):**

```rust
        let prev = d;
        let num = (ann.saturating_mul(s) + d_p.saturating_mul(N_COINS as u128))
            .saturating_mul(d);
        let den = (ann.saturating_sub(1)).saturating_mul(d)
            + (N_COINS as u128 + 1) * d_p;
        d = num.checked_div(den).unwrap_or(0);
```

* Numerator implements $(\mathrm{Ann}\,S + n\,D_P)\,D$.
* Denominator implements $(\mathrm{Ann}-1)\,D + (n+1)\,D_P$.
* This is literally (2.4.1) with $n=2$.

**Stopping rule:**

```rust
        if d > prev { if d - prev <= 1 { break; }} else { if prev - d <= 1 { break; }}
```

* Integer-domain convergence: $|\Delta D|\le 1$ (as recommended in §2.4).

**Return `d`** — the unique invariant for current `x`.

---

## 4.6 `get_dy()` — quote output $\Delta y$ for input $\Delta x$

```rust
pub fn get_dy(&self, i: usize, j: usize, dx: u64) -> Result<u64, SwapError> {
    // (1) Guard preconditions: i != j, indices in range, nonzero trade, nonzero liquidity
```

* Mirrors model assumptions: $i\ne j$, $x_i>0$ (so $P>0$), and $\Delta x>0$.

```rust
    let mut xp = [self.reserves[0] as u128, self.reserves[1] as u128];
    let amp = self.ann();
    let d = compute_d(&xp, amp);   // D for the pre-trade state (solves 2.2.4)
```

* Compute the invariant $D$ for **current** reserves (never cached; §2.3).

**Fee on input (kept out of the invariant):**

```rust
    let dx_u = dx as u128;
    let fee = self.fee_bps as u128;
    let dx_less_fee = mul_div(dx_u, BPS_DENOM - fee, BPS_DENOM).ok_or(SwapError::Math)?;
    xp[i] = xp[i].checked_add(dx_less_fee).ok_or(SwapError::Math)?;
```

* Implements $\Delta x_{\text{net}} = \Delta x\cdot\frac{10\,000 - \text{feebps}}{10\,000}$.
* Only **net** input enters the mathematical state (consistent with “fee-on-input” convention).

**Solve for the post-trade balance $y$ at fixed $D$ (Eq. 2.5.1/2.5.2):**

```rust
    let y = get_y(i, j, &xp, d, amp)?;
```

* Calls the Newton solver for $y$ using the quadratic from (2.5.1) with the closed-form update (2.5.2).

**Conservative rounding of output (protect invariant):**

```rust
    let dy = (self.reserves[j] as u128)
        .checked_sub(y)
        .and_then(|v| v.checked_sub(1)) // round down like Curve
        .ok_or(SwapError::Math)?;
    Ok(dy as u64)
}
```

* Returns $\Delta y = x_j - y - 1$ per §2.5: “round down and minus one” avoids over-withdrawal under integer truncation.

> **Note**: `get_dy` **does not mutate** `self.reserves`. It is a pure quote. Execution, if desired, must be done by the caller (add $\Delta x_{\text{net}}$ to side $i$ and subtract returned $\Delta y$ from side $j$).

---

## 4.7 `get_y()` — Newton’s method for the post-trade balance (Eqs. 2.5.1–2.5.2)

```rust
fn get_y(i: usize, j: usize, xp: &[u128; N_COINS], d: u128, ann: u128) -> Result<u128, SwapError> {
    let mut c = d;
    let mut s: u128 = 0;
```

* We will assemble $b$ and $c$ to match the quadratic $y^2 + (b-D)y - c = 0$ (2.5.1).
* In the two-asset case, indices reduce the “exclude $j$” product/sum to just the other coin.

**Build $S'$ and $c$:**

```rust
    for k in 0..N_COINS {
        if k == j { continue; }
        let xk = xp[k];
        s = s.saturating_add(xk);                         // s := S' = sum_{k≠j} x_k
        let denom = xk.saturating_mul(N_COINS as u128);   // x_k * n
        c = mul_div(c, d, denom).ok_or(SwapError::Math)?; // c *= D / (x_k * n)
    }
    // c = D^{n+1}/(n^n * prod(x_except_j)) * 1/Ann
    c = mul_div(c, d, ann.saturating_mul(N_COINS as u128)).ok_or(SwapError::Math)?;
```

* Start with `c = d` and multiply by $D/(x_k\,n)$ once for each included $x_k$: after the loop,
  $c = \dfrac{D^{n}}{n^{n-1}\prod_{k\ne j}x_k}$.
* Then multiply by $D/(n\,\mathrm{Ann})$ to get
  $c = \dfrac{D^{n+1}}{n^{n}\,\mathrm{Ann}\,\prod_{k\ne j}x_k}$, which is exactly the $c$ in (2.5.1).

**Compute $b=S'+D/\mathrm{Ann}$:**

```rust
    let b = s + d / ann;
```

**Newton iteration with the closed-form step (2.5.2):**

```rust
    let mut y = d;  // initial guess y0 = D (positive, right scale)
    for _ in 0..MAX_ITERS {
        let num = y.saturating_mul(y).saturating_add(c);      // y^2 + c
        let den = y.saturating_mul(2).saturating_add(b).saturating_sub(d); // 2y + b - D
        if den == 0 { return Err(SwapError::Math); }
        let y_next = num / den;
        if y_next == y || (y_next > y && y_next - y <= 1) || (y > y_next && y - y_next <= 1) {
            y = y_next; break;
        }
        y = y_next;
    }
```

* Implements exactly $y \leftarrow \dfrac{y^2 + c}{2y + b - D}$ (2.5.2).
* Denominator $2y+b-D\ge y+b>0$ for $y>0$, so division by zero is structurally ruled out (see §2.5).

Return `Ok(y)`; the caller computes $\Delta y=x_j-y-1$.

---

## 4.8 `mul_div()` — safe integer fraction

```rust
fn mul_div(a: u128, b: u128, den: u128) -> Option<u128> {
    if den == 0 { return None; }
    a.checked_mul(b)?.checked_div(den)
}
```

* Encapsulates “multiply then divide” with overflow/zero-denominator checks.
* Critical to avoid transient overflow when constructing $D_P$ and $c$ (products like $D^{3}$ in $n=2$).

---

## 4.9 `constant_product_dy()` — baseline $x\,y=k$

```rust
pub fn constant_product_dy(reserves: [u64;2], i: usize, j: usize, dx: u64) -> Option<u64> {
    ...
    let k = x.checked_mul(y)?;     // k = x*y
    x = x.checked_add(dx as u128)?;// x' = x + dx
    let new_y = k.checked_div(x)?; // y' = k / x'
    let dy = y.checked_sub(new_y)?.saturating_sub(1);
    Some(dy as u64)
}
```

* Implements the classical constant-product trade without fees:

  * $k=xy$, $x\gets x+\Delta x$, $y'=\dfrac{k}{x+\Delta x}$, output $=\;y-y'-1$.
* Used in tests and documentation to **contrast slippage** versus StableSwap (§2.6).

---

## 4.10 `calculate_slippage_bps()` — curve-only slippage estimator

```rust
pub fn calculate_slippage_bps(&self, amount: u64) -> u16 {
    if self.reserves[0] == 0 || self.reserves[1] == 0 || amount == 0 { return 0; }
    let mut tmp = self.clone();
    tmp.fee_bps = 0;                       // isolate curve effect
    let dy = tmp.get_dy(0, 1, amount).unwrap_or(0);
    if dy == 0 { return 0; }
    let price_num = amount as u128;        // p = dx/dy
    let price_den = dy as u128;
    let diff_num = price_num.saturating_sub(price_den);
    let slippage_bps = mul_div(diff_num * 10_000u128, 1, price_den).unwrap_or(0);
    slippage_bps as u16
}
```

* Computes effective execution price $p=\Delta x/\Delta y$ with **fees disabled**.
* Returns $\text{slippagebps} \approx 10^{4}\,(p-1)$, the deviation from the ideal 1:1 peg (see §2.6 on near-parity constant-sum behavior).

---

## 4.11 Tests — mapping to Section 2 properties

```rust
#[test] fn d_monotonic_in_reserves() { ... }
```

* Increases both reserves $\Rightarrow$ `get_d()` increases. Matches §2.3.3 (∂D/∂xⱼ>0) and §2.3.2 (D≤S, monotone in $x$).

```rust
#[test] fn basic_swap_less_slippage_than_xyk() { ... }
```

* For balanced liquidity and moderate $A$, StableSwap returns a **larger** output than $x\,y=k$. Matches §2.6 (constant-sum-like near parity).

```rust
#[test] fn fee_is_applied_on_input() { ... }
```

* With fee>0, `get_dy` decreases vs fee=0 (fee on input). Purely accounting; invariant math is fee-free.

```rust
#[test] fn slippage_bps_reasonable() { ... }
```

* In deep, balanced pools with $A\approx 100$, curve-only slippage for moderate trades stays well below 1% (empirical property following from §2.6).

---

## 4.12 Subtle points & extensibility notes

* **No caching of $D$:** Always recompute from current $x$. The invariant depends on the instantaneous state; caching risks stale quotes (see §2.3).
* **Generality in $n$:** The loops in `compute_d` and `get_y` already mirror the general formulas (2.4.1) and (2.5.1); specialization occurs via `N_COINS`. To lift to $n>2$, parameterize `N_COINS`, compute $n^n$ at runtime for $\mathrm{Ann}=A\,n^n$, and keep the same iteration patterns.
* **Rounding policy:** Returning $x_j - y - 1$ ensures we never over-withdraw due to integer truncation (§2.5).
* **Safety of denominators:**

  * In `compute_d`, `den = (Ann−1)D + (n+1)D_P > 0` for $D>0$, $Ann>0$, $D_P>0$.
  * In `get_y`, `2y + b − D ≥ y + b > 0` for $y>0$.
* **Convergence guarantees:**

  * $D$: $F'(D)<0$, $F''(D)<0$ ⇒ Newton from $D_0=S$ is monotone $\downarrow$ to the unique root (§2.4).
  * $y$: Monic quadratic, strictly convex; Newton with update (2.5.2) converges rapidly (§2.5).


---

## References (APA)

Adams, H., Zinsmeister, N., & Robinson, D. (2020). *Uniswap v2 core* \[White paper]. Uniswap Labs. [https://app.uniswap.org/whitepaper.pdf](https://app.uniswap.org/whitepaper.pdf) ([Uniswap][1])

Adams, H., Zinsmeister, N., Salem, M., Keefer, R., & Robinson, D. (2021). *Uniswap v3 core* \[White paper]. Uniswap Labs. [https://app.uniswap.org/whitepaper-v3.pdf](https://app.uniswap.org/whitepaper-v3.pdf) ([Uniswap][3])

Egorov, M. (2019). *StableSwap: An efficient mechanism for stablecoin liquidity* \[White paper]. Curve Finance. [https://berkeley-defi.github.io/assets/material/StableSwap.pdf](https://berkeley-defi.github.io/assets/material/StableSwap.pdf) (see also Curve’s whitepaper index: [https://docs.curve.finance/references/whitepaper](https://docs.curve.finance/references/whitepaper)) ([Berkeley DeFi][4], [Curve][5])

RareSkills. (n.d.). *get\_D() and get\_y() in Curve StableSwap*. [https://rareskills.io/post/curve-get-d-get-y](https://rareskills.io/post/curve-get-d-get-y) ([RareSkills][9])

SolanaFM. (n.d.). *USDT (USDT) — Solana token details (decimals: 6)*. [https://solana.fm/address/Es9vMFrzaCERmJfrF4H2FYD4KCoNkY11McCe8BenwNYB](https://solana.fm/address/Es9vMFrzaCERmJfrF4H2FYD4KCoNkY11McCe8BenwNYB) ([SolanaFM | Next-Gen Solana Explorer][8])

Solana Foundation. (n.d.). *Create a token mint (SPL tokens)*. [https://solana.com/docs/tokens/basics/create-mint](https://solana.com/docs/tokens/basics/create-mint)  (references the USDC mint address on Solana) ([Solana][6])

Solscan. (n.d.). *USDC (USDC) — Solana token page (decimals: 6)*. [https://solscan.io/token/EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v](https://solscan.io/token/EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v) ([Solscan][7])

Uniswap Labs. (n.d.). *How Uniswap works* (Docs). [https://docs.uniswap.org/contracts/v2/concepts/protocol-overview/how-uniswap-works](https://docs.uniswap.org/contracts/v2/concepts/protocol-overview/how-uniswap-works) ([Uniswap][2])

---

**Notes for inclusion:**

* If you later change the target chain or tokens, update the **decimal** citations accordingly.
* If your instructor prefers a minimal reference list, you can keep only Egorov (2019), Uniswap V2/V3 whitepapers, and the Solana mint/decimals sources.

[1]: https://app.uniswap.org/whitepaper.pdf?utm_source=chatgpt.com "Uniswap v2 Core"
[2]: https://docs.uniswap.org/contracts/v2/concepts/protocol-overview/how-uniswap-works?utm_source=chatgpt.com "How Uniswap works"
[3]: https://app.uniswap.org/whitepaper-v3.pdf?utm_source=chatgpt.com "Uniswap v3 Core"
[4]: https://www.curve.finance/files/stableswap-paper.pdf "StableSwap - efficient mechanism for Stablecoin liquidity"
[5]: https://docs.curve.finance/references/whitepaper?utm_source=chatgpt.com "Whitepapers, Derivations and Useful Resources"
[6]: https://solana.com/docs/tokens/basics/create-mint?utm_source=chatgpt.com "Create a Token Mint"
[7]: https://solscan.io/token/EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v?utm_source=chatgpt.com "USDC (USDC)"
[8]: https://solana.fm/address/Es9vMFrzaCERmJfrF4H2FYD4KCoNkY11McCe8BenwNYB?utm_source=chatgpt.com "USDT (USDT) | Next-Gen Solana Explorer"
[9]: https://rareskills.io/post/curve-get-d-get-y "get_D() and get_y() in Curve StableSwap | By RareSkills – RareSkills"
