# StableSwap Rust (USDC/USDT, 6 decimals)

> **Abstract.** This crate provides a pure-math implementation of Curve's StableSwap algorithm for a two-asset stablecoin pool (USDC/USDT, 6 decimals). We formalize the invariant, derive the Newton iterations for the pool invariant $D$ and for the post-trade balance $y$, and discuss integer-precision arithmetic, rounding policy, numerical stability, and complexity. A constant-product baseline is also included for slippage comparison. The code is entirely deterministic and uses only integer arithmetic (`u128`), which makes it suitable for on-chain or reproducible off-chain contexts.

---

## 1. Notation and Problem Statement

Let $n=2$ be the number of coins in the pool with balances $x_0, x_1>0$, and define

$$
S = \sum_{i=0}^{n-1} x_i, \qquad P = \prod_{i=0}^{n-1} x_i .
$$

Let $A>0$ denote the amplification coefficient and $Ann = A\,n^n$ (for two coins, $Ann=4A$). All quantities are represented as integers with 6 fraction digits (e.g., `1 USDC = 1_000_000`). Internal arithmetic is performed in $\mathtt{u128}$.

**Objective.** Given an input trade of size $\Delta x$ on coin $i$, we seek the output $\Delta y$ on coin $j\ne i$ such that the trade preserves the StableSwap invariant (up to conservative rounding) and applies a basis-points fee on the input.

---

## 2. StableSwap Invariant (Two-Asset Case)

The invariant in the two-asset case is written as

$$
Ann\,S + D \;=\; Ann\,D + \frac{D^{n+1}}{n^n\,P}\qquad (n=2),
$$

where $D$ is the positive solution balancing the curve. Define

$$
F(D) \equiv Ann\,S + D - Ann\,D - \frac{D^{n+1}}{n^n\,P} = 0 .
$$

We compute $D$ by Newton’s method. Let

$$
D_P(D) \equiv \frac{D^{n+1}}{n^n\,P}, \qquad 
F'(D) = 1 - Ann - \frac{(n+1)D^n}{n^n\,P}
     = 1 - Ann - \frac{(n+1)D_P}{D}.
$$

Then

$$
D_{\text{new}} 
= D - \frac{F(D)}{F'(D)}
= D - \frac{AnnS + D - AnnD - D_P}{1 - Ann - (n+1)D_P/D}.
$$

Multiplying numerator/denominator by $D$ yields the closed-form update used in code:

$$
\boxed{\; D_{\text{new}} = \frac{\big(AnnS + nD_P\big)\,D}
{(Ann-1)D + (n+1)D_P} \;}
$$

with $n=2$. Iterate until $|D_{k+1}-D_k|\le 1$ (or a hard cap). In practice, convergence occurs in <10 steps.

**Safe evaluation of $D_P$.** Rather than forming $D^{n+1}$ directly, build it iteratively to avoid overflow:

$$
D_P \leftarrow D,\quad 
D_P \leftarrow (D_P\cdot D)/(x_0\cdot n),\quad
D_P \leftarrow (D_P\cdot D)/(x_1\cdot n).
$$

All products/divisions use checked integer arithmetic (`mul_div`).

---

## 3. Solving for the Post-Trade Balance $y$

After charging the input fee (see §4), set $x_i \leftarrow x_i + \Delta x_{\text{net}}$. Solve for the new output-side balance $y\equiv x'_j$ **holding $D$ fixed**. Let

$$
S' = \sum_{k\ne j} x_k,\qquad Ann = A\,n^n .
$$

With $D$ fixed, the invariant reduces to a scalar nonlinear equation in $y$. A standard rearrangement yields

$$
f(y) \equiv y^2 + (b - D)\,y - c = 0,
$$

where

$$
b = S' + \frac{D}{Ann}, \qquad
c = \frac{D^{n+1}}{n^n\,\prod_{k\ne j} x_k}\cdot \frac{1}{Ann} .
$$

Applying Newton’s method to $f(y)$ gives the practical update:

$$
\boxed{\; y \leftarrow \frac{y^2 + c}{2y + b - D} \;}
$$

Initialize $y\gets D$ and iterate until $|y_{k+1}-y_k|\le 1$. The output amount is

$$
\Delta y = x_j - y - 1,
$$

where the extra `-1` is a conservative guard against invariant drift due to integer truncation.

---

## 4. Fees, Price, and Slippage

Let `fee_bps` be the input-side fee in basis points (1% = 100 bps). We charge the fee on the input:

$$
\Delta x_{\text{net}} = \Delta x\cdot \frac{\text{BPS}_\text{denom} -\text{feebps}}{\text{BPS}\text{denom}}
$$

$$
\qquad \text{BPS}_\text{denom}=10{,}000.
$$

The execution price is $p=\Delta x/\Delta y$. To measure **curve-only** slippage, set fee to zero temporarily and compute

$$
\text{slippagebps} \approx 10^4\,(p-1),
$$

relative to the ideal 1:1 price.

---

## 5. Integer Arithmetic, Precision, and Rounding

* **Representation.** Token amounts are 6-decimal fixed-point integers (`u64` externally). Internal math promotes to `u128`.\n- **Exact integer math.** No floating point. Fractions via `mul_div(a,b,den)` (checked multiply, then checked divide).\n- **Conservative rounding.** After solving $y$, round down and subtract one minimal unit (`-1`).\n- **Convergence.** Both Newton solvers stop when successive iterates differ by ≤1 or after a hard cap (`MAX_ITERS=256`). Typical iterations <10.

---

## 6. Constant-Product Baseline

For $x\,y=k$ (no fee), a trade of size $\Delta x$ yields

$$
y' = \frac{k}{x+\Delta x},\qquad \Delta y = y - y' - 1.
$$

We expose this as `constant_product_dy` for direct slippage comparison; StableSwap dominates near balance for reasonable $A$.

---

## 7. Complexity and Stability

* **Time complexity.** $\mathcal{O}(1)$ work per Newton step; tiny constant factors.\n- **Stability.** `mul_div` encapsulates multiply-then-divide; denominators checked; edge cases (`BadIndex`, `ZeroTrade`, `NoLiquidity`, `NoConvergence`, `Math`) return explicit errors.\n- **Behavior.** Near balance and with sizeable $A$, the curve approximates constant-sum (very low slippage); far from balance it transitions toward constant-product, ensuring finite liquidity.

---

## 8. API

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
```

---

## 9. Tests and Expected Properties

* **Monotonic $D$.** Enlarging both reserves increases $D$.\n- **Lower slippage vs. $x y=k$.** In balanced states and moderate $A$, `get_dy` > baseline for the same $\Delta x$.\n- **Fee-on-input.** Non-zero `fee_bps` strictly reduces output versus zero-fee.\n- **Reasonable slippage.** Deep, balanced pools with $A\approx100$ show sub-100 bps slippage for moderate trades.

Run:

```bash
cargo test -q
```

---

## 10. Practical Guidance

* **Choosing $A$.** Larger $A$ flattens the curve near $x_0\!\approx\!x_1$ while retaining constant-product behavior when imbalanced.\n- **Do not cache $D$.** Always recompute from current reserves.\n- **Rounding policy.** The conservative “round down and `-1`” protects LPs; adjust tests if you move fees to the output side.

---

## 11. Reproducibility

The library is deterministic and integer-only, suitable for on-chain and off-chain verification.

---

## 12. Reference

* M. Egorov, *StableSwap: An efficient mechanism for Stablecoin liquidity*, 2019.
