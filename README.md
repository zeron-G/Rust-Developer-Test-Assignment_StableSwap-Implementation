# StableSwap Rust (USDC/USDT, 6 decimals)

**Abstract.** This crate provides a pure-math implementation of Curve's StableSwap algorithm for a two-asset stablecoin pool (USDC/USDT, 6 decimals). We formalize the invariant, derive Newton iterations for the pool invariant D and the post-trade balance y, and discuss integer-precision arithmetic, rounding policy, numerical stability, and complexity. A constant-product baseline is included for slippage comparison. The code is deterministic and uses only integer arithmetic (u128), suitable for on-chain or reproducible off-chain contexts.

---

## 1. Notation and Problem Statement
Let n = 2 be the number of coins with balances x0, x1 > 0. Define:
- S = x0 + x1
- P = x0 * x1
Let A > 0 be the amplification coefficient and define Ann = A · n^n (for two coins, Ann = 4A). Amounts are integers with 6 fractional digits (e.g., 1 USDC = 1_000_000). Internal arithmetic uses u128.

**Objective.** Given an input trade of size Δx on coin i, compute the output Δy on coin j ≠ i such that the trade preserves the StableSwap invariant (up to conservative rounding) while applying an input-side fee.

---

## 2. StableSwap Invariant (Two-Asset Case)
The two-asset invariant (paper notation) is:

Ann·S + D = Ann·D + D^{n+1} / (n^n · P)  (with n = 2).

Equivalently, define F(D) = Ann·S + D − Ann·D − D^{n+1}/(n^n·P) = 0 and solve for D by Newton’s method. Let:
- DP(D) = D^{n+1} / (n^n · P)
- F'(D) = 1 − Ann − (n+1)·DP/D

The Newton step simplifies to the closed form used in code:

D_next = ((Ann·S + n·DP) · D) / ((Ann − 1)·D + (n+1)·DP).

We iterate until |D_{k+1} − D_k| ≤ 1 or a hard cap. In practice, convergence occurs within <10 steps for well-posed states.

**Safe evaluation of DP.** To avoid overflow, we build DP iteratively instead of forming D^{n+1} directly:
- DP ← D
- DP ← (DP · D) / (x0 · n)
- DP ← (DP · D) / (x1 · n)

All multiply/divide operations use checked integer arithmetic (mul_div).

---

## 3. Solving for the Post-Trade Balance y
After fee (see §4), update the input balance: x_i ← x_i + Δx_net. Hold D fixed and solve for the new output-side balance y ≡ x'_j. Let:
- S' = sum of balances excluding j (here S' = x_i after update)
- Ann = A · n^n

Rearranging the invariant yields a scalar nonlinear equation:

f(y) = y^2 + (b − D)·y − c = 0,

with coefficients
- b = S' + D/Ann
- c = [ D^{n+1} / (n^n · (product of balances excluding j)) ] · (1/Ann)

Newton’s update used in practice:

y ← (y^2 + c) / (2y + b − D).

Initialize y ← D and iterate until |y_{k+1} − y_k| ≤ 1. The conservative output is then

Δy = x_j − y − 1,

where the extra “−1” guards the invariant against integer truncation (standard on-chain practice).

---

## 4. Fees, Execution Price, and Slippage
Let `fee_bps` be the input-side fee in basis points (1% = 100 bps). Charge fee on the input:

Δx_net = Δx · (BPS_DENOM − fee_bps) / BPS_DENOM, where BPS_DENOM = 10,000.

The execution price is p = Δx / Δy (after fee). To measure curve-only slippage, temporarily set fee to zero and compute

slippage_bps ≈ 10^4 · (p − 1),

relative to the ideal 1:1 price.

---

## 5. Integer Arithmetic, Precision, and Rounding
- Representation: 6-decimal fixed-point integers (u64 at API), promote to u128 internally.
- Exact integer math: no floats. Fractions via mul_div(a,b,den) = checked_mul followed by checked_div.
- Conservative rounding: after solving y, round down and subtract one minimal unit (−1).
- Convergence: both Newton solvers stop when successive iterates differ by ≤1 or after MAX_ITERS=256 (typical <10).

---

## 6. Constant-Product Baseline (for Comparison)
For x·y = k (ignoring fees), a trade of size Δx yields

y' = k / (x + Δx),   Δy = y − y' − 1.

We expose this as `constant_product_dy` to demonstrate that StableSwap exhibits lower slippage near balance for reasonable A.

---

## 7. Complexity and Stability
- Time complexity: O(1) per Newton step in the two-asset case; dominated by a handful of 128-bit mul/div operations.
- Stability: mul_div encapsulates multiply-then-divide; denominators checked; edge cases (BadIndex, ZeroTrade, NoLiquidity, NoConvergence, Math) return explicit errors.
- Behavior: near balance and with sizeable A, the curve approximates constant-sum (very low slippage); far from balance it transitions toward constant-product, ensuring finite liquidity.

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