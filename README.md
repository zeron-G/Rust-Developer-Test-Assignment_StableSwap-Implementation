# Rust-Developer-Test-Assignment_StableSwap-Implementation
Rust library implementing Curve's StableSwap algorithm for a USDC/USDT trading pair.

# StableSwap Rust (USDC/USDT, 6 decimals)

This crate is a **pure math** implementation of Curve's StableSwap algorithm for a 2-coin pool, tuned for **USDC/USDT** (6 decimals). It includes:

- Invariant D via Newton's method
- `get_y` and `get_dy` (fee on input in bps)
- Constant-product comparison helpers
- Unit tests proving lower slippage than x*y=k

## Why this works

We implement the whitepaper invariant (Egorov, 2019):

> \( A n^n \sum x_i + D = A D n^n + \dfrac{D^{n+1}}{n^n \prod x_i} \) with \(n=2\).

For `get_D`, we iterate the Newton update derived as

> \( D_{next} = \dfrac{(A n^n S + n D_p) D}{(A n^n - 1) D + (n+1) D_p} \), where \(D_p = D^{n+1} / (n^n \prod x_i)\).

For `get_y`, we fix D and solve for the new balance of token `j` via the classic update

> \( y \leftarrow \dfrac{y^2 + c}{2y + b - D} \), with \(c = D^{n+1}/(n^n \prod_{k\ne j} x_k)\cdot 1/Ann\), \(b = S' + D/Ann\), \(Ann = A n^n\).

All computations are done in **u128** to avoid overflow and keep exact integer math at 6-decimal precision.

## API

```rust
pub struct StableSwapPool {
    pub reserves: [u64; 2],
    pub amplification_coefficient: u64,
    pub fee_bps: u16,
}
impl StableSwapPool {
    pub fn new(reserves: [u64; 2], amp: u64) -> Self;
    pub fn get_dy(&self, i: usize, j: usize, dx: u64) -> Result<u64, SwapError>;
    pub fn get_d(&self) -> u64;
    pub fn calculate_slippage_bps(&self, amount: u64) -> u16;
}
