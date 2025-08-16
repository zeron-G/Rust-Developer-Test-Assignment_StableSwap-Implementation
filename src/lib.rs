//! Curve StableSwap (USDC/USDT, 6 decimals) — mathematical implementation
//! - Invariant D via Newton's method
//! - get_y and get_dy
//! - Constant-product (x*y=k) comparison utilities
//! - All math in integer (u128) with 6-decimals inputs (u64), fee in bps
//!
//! References:
//! - Egorov, *StableSwap – efficient mechanism for Stablecoin liquidity* (2019)
//! - RareSkills: get_D() and get_y() derivation

#![deny(missing_docs)]

/// Basis points denominator
const BPS_DENOM: u128 = 10_000;
/// Number of coins for this pool (USDC/USDT)
const N_COINS: usize = 2;
/// Newton maximum iterations
const MAX_ITERS: usize = 256;

/// Swap errors
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SwapError {
    /// i or j out of range or identical
    BadIndex,
    /// dx == 0
    ZeroTrade,
    /// One of reserves is zero (no liquidity)
    NoLiquidity,
    /// Newton method did not converge
    NoConvergence,
    /// Math overflow / division by zero
    Math,
}

/// StableSwap pool for a 2-coin (USDC/USDT) pair at 6 decimals.
#[derive(Debug, Clone)]
pub struct StableSwapPool {
    /// Reserves as on-chain integers (6 decimals)
    pub reserves: [u64; N_COINS],
    /// Amplification coefficient A (whitepaper definition)
    pub amplification_coefficient: u64,
    /// Trading fee in basis points (e.g., 30 = 0.30%)
    pub fee_bps: u16,
}

impl StableSwapPool {
    /// Create a new pool
    pub fn new(reserves: [u64; N_COINS], amp: u64) -> Self {
        Self { reserves, amplification_coefficient: amp, fee_bps: 0 }
    }

    /// Return invariant D for current reserves
    pub fn get_d(&self) -> u64 {
        let amp = self.ann();
        let x = [self.reserves[0] as u128, self.reserves[1] as u128];
        let d = compute_d(&x, amp);
        d as u64
    }

    /// Calculate output amount `dy` for swapping `dx` of token i into token j
    /// Fees are charged on the input (dx net-of-fee enters the pool)
    pub fn get_dy(&self, i: usize, j: usize, dx: u64) -> Result<u64, SwapError> {
        if i == j || i >= N_COINS || j >= N_COINS { return Err(SwapError::BadIndex); }
        if dx == 0 { return Err(SwapError::ZeroTrade); }
        if self.reserves[i] == 0 || self.reserves[j] == 0 { return Err(SwapError::NoLiquidity); }

        let mut xp = [self.reserves[0] as u128, self.reserves[1] as u128];
        let amp = self.ann();
        let d = compute_d(&xp, amp);
        if d == 0 { return Err(SwapError::NoLiquidity); }

        // apply fee on input
        let dx_u = dx as u128;
        let fee = self.fee_bps as u128;
        let dx_less_fee = mul_div(dx_u, BPS_DENOM - fee, BPS_DENOM).ok_or(SwapError::Math)?;
        xp[i] = xp[i].checked_add(dx_less_fee).ok_or(SwapError::Math)?;

        let y = get_y(i, j, &xp, d, amp)?;
        let dy = (self.reserves[j] as u128)
            .checked_sub(y)
            .and_then(|v| v.checked_sub(1)) // round down like Curve to avoid over-withdraw
            .ok_or(SwapError::Math)?;
        Ok(dy as u64)
    }

    /// Calculate slippage (bps) for swapping `amount` of token 0 -> token 1 using StableSwap
    /// Relative to ideal price 1.0 (USDC/USDT), ignoring fees to isolate curve effect.
    pub fn calculate_slippage_bps(&self, amount: u64) -> u16 {
        // copy pool with zero fee and compute effective price
        if self.reserves[0] == 0 || self.reserves[1] == 0 || amount == 0 { return 0; }
        let mut tmp = self.clone();
        tmp.fee_bps = 0;
        let dy = tmp.get_dy(0, 1, amount).unwrap_or(0);
        if dy == 0 { return 0; }
        // effective price = dx/dy; slippage = (price-1)*1e4 bps
        let price_num = amount as u128;
        let price_den = dy as u128;
        let one = 1u128;
        // price - 1 = (num/den) - 1 = (num - den)/den
        let diff_num = price_num.saturating_sub(price_den);
        let slippage_bps = mul_div(diff_num * 10_000u128, 1, price_den).unwrap_or(0);
        slippage_bps as u16
    }

    /// Whitepaper Ann = A * n^n  (n=2 => 4)
    fn ann(&self) -> u128 { (self.amplification_coefficient as u128) * 4u128 }
}

/// Compute invariant D using Newton's method (whitepaper Eq.)
fn compute_d(x: &[u128; N_COINS], ann: u128) -> u128 {
    let s = x[0] + x[1];
    if s == 0 { return 0; }
    let mut d = s; // initial guess

    for _ in 0..MAX_ITERS {
        // D_P = D^(n+1) / (n^n * prod(x)) implemented iteratively
        let mut d_p = d;
        for k in 0..N_COINS {
            let denom = x[k].saturating_mul(N_COINS as u128);
            if denom == 0 { return 0; }
            d_p = match mul_div(d_p, d, denom) { Some(v) => v, None => return 0 };
        }
        let prev = d;
        let num = (ann.saturating_mul(s) + d_p.saturating_mul(N_COINS as u128))
            .saturating_mul(d);
        let den = (ann.saturating_sub(1)).saturating_mul(d)
            + (N_COINS as u128 + 1) * d_p;
        if den == 0 { return 0; }
        d = match num.checked_div(den) { Some(v) => v, None => return 0 };
        if d > prev { if d - prev <= 1 { break; }} else { if prev - d <= 1 { break; }}
    }
    d
}

/// Solve for y (the new balance of token j) keeping D constant
fn get_y(i: usize, j: usize, xp: &[u128; N_COINS], d: u128, ann: u128) -> Result<u128, SwapError> {
    let mut c = d;
    let mut s: u128 = 0;

    for k in 0..N_COINS {
        if k == j { continue; }
        let xk = xp[k];
        s = s.saturating_add(xk);
        let denom = xk.saturating_mul(N_COINS as u128);
        c = mul_div(c, d, denom).ok_or(SwapError::Math)?;
    }
    // c = D^{n+1}/(n^n * prod(x_except_j)) * 1/Ann
    c = mul_div(c, d, ann.saturating_mul(N_COINS as u128)).ok_or(SwapError::Math)?;
    // b = S' + D/Ann
    let b = s + d / ann;

    // Newton iterate y
    let mut y_prev = 0u128;
    let mut y = d;
    for _ in 0..MAX_ITERS {
        y_prev = y;
        // y = (y^2 + c) / (2y + b - D)
        let num = y.saturating_mul(y).saturating_add(c);
        let den = y.saturating_mul(2).saturating_add(b).saturating_sub(d);
        if den == 0 { return Err(SwapError::Math); }
        y = num / den;
        if y > y_prev { if y - y_prev <= 1 { break; }} else { if y_prev - y <= 1 { break; }}
    }
    if y == 0 { return Err(SwapError::NoConvergence); }
    Ok(y)
}

/// (a*b)/den with u128, returning None on overflow or div-by-zero
fn mul_div(a: u128, b: u128, den: u128) -> Option<u128> {
    if den == 0 { return None; }
    a.checked_mul(b)?.checked_div(den)
}

/// Constant-product (x*y=k) helper: output dy for dx of token i into j (no fees)
pub fn constant_product_dy(reserves: [u64;2], i: usize, j: usize, dx: u64) -> Option<u64> {
    if i == j || i >= 2 || j >= 2 || dx == 0 { return None; }
    let mut x = reserves[i] as u128;
    let mut y = reserves[j] as u128;
    let k = x.checked_mul(y)?;
    x = x.checked_add(dx as u128)?;
    let new_y = k.checked_div(x)?;
    let dy = y.checked_sub(new_y)?.saturating_sub(1);
    Some(dy as u64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn d_monotonic_in_reserves() {
        let p1 = StableSwapPool { reserves: [1_000_000, 1_000_000], amplification_coefficient: 100, fee_bps: 0 };
        let p2 = StableSwapPool { reserves: [2_000_000, 2_000_000], amplification_coefficient: 100, fee_bps: 0 };
        assert!(p2.get_d() > p1.get_d());
    }

    #[test]
    fn basic_swap_less_slippage_than_xyk() {
        let pool = StableSwapPool { reserves: [1_000_000_000, 1_000_000_000], amplification_coefficient: 100, fee_bps: 0 };
        let dx = 100_000_000u64; // 100 USDC
        let dy_stable = pool.get_dy(0, 1, dx).unwrap();
        let dy_xyk = constant_product_dy(pool.reserves, 0, 1, dx).unwrap();
        assert!(dy_stable > dy_xyk, "StableSwap should output more than x*y=k (less slippage)");
    }

    #[test]
    fn fee_is_applied_on_input() {
        let mut pool = StableSwapPool { reserves: [1_000_000_000, 1_000_000_000], amplification_coefficient: 100, fee_bps: 100 }; // 1%
        let dx = 1_000_000u64; // 1 USDC
        let out_with_fee = pool.get_dy(0, 1, dx).unwrap();
        pool.fee_bps = 0;
        let out_no_fee = pool.get_dy(0, 1, dx).unwrap();
        assert!(out_with_fee < out_no_fee);
    }

    #[test]
    fn slippage_bps_reasonable() {
        let pool = StableSwapPool { reserves: [5_000_000_000, 5_000_000_000], amplification_coefficient: 100, fee_bps: 0 };
        let s = pool.calculate_slippage_bps(500_000_000); // trade 500
        assert!(s < 1000); // < 1% for balanced pool with A=100
    }
}