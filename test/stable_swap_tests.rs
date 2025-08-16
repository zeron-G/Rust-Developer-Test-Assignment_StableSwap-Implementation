use stable_swap_rs::{StableSwapPool, constant_product_dy};

#[test]
fn readme_example() {
    let mut pool = StableSwapPool { reserves: [10_000_000_000, 10_000_000_000], amplification_coefficient: 100, fee_bps: 30 };
    // swap 100 USDC -> USDT
    let dy = pool.get_dy(0, 1, 100_000_000).unwrap();
    assert!(dy > 99_000_000); // with A=100 & deep pool, very low slippage

    // Compare with x*y=k (no fee)
    pool.fee_bps = 0;
    let dx = 1_000_000_000u64; // 1000
    let dy_stable = pool.get_dy(0, 1, dx).unwrap();
    let dy_xyk = constant_product_dy(pool.reserves, 0, 1, dx).unwrap();
    assert!(dy_stable > dy_xyk);
}