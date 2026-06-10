//! Kani proof harnesses for Property D (implementation safety): overflow and
//! index-bounds safety of the arithmetic in the verifier internals — the
//! slice-indexing in the non-existence padding logic is the Dragonberry-class
//! surface.
//!
//! Run with `cargo kani` (the `kani` cfg is set only under Kani, so these are
//! invisible to normal builds). See `docs/rfc/001-formal-verification.md`.
//!
//! These harnesses are intentionally over the *arithmetic*, mirrored from the
//! verifier, rather than the full functions: the `anyhow`/`Result` error paths
//! pull in formatting machinery that explodes CBMC's formula. Panic-freedom of
//! the `Result`-returning entry points (`do_length`, `proto_len`) is left to a
//! later pass that stubs formatting.

/// `ensure_inner`'s prefix bound `max_prefix_length + (child_order.len()-1) *
/// child_size` is overflow-free in `i32` for well-formed bounds (cf. the
/// IAVL/Tendermint/SMT specs). A malformed spec with an enormous `child_size`
/// could overflow it — tracked as a finding; this pins the safe precondition.
#[kani::proof]
fn ensure_inner_prefix_bound_no_overflow() {
    let child_order_len: usize = kani::any();
    let child_size: i32 = kani::any();
    let max_prefix_length: i32 = kani::any();
    kani::assume((2..=16).contains(&child_order_len));
    kani::assume((1..=128).contains(&child_size));
    kani::assume((0..=4096).contains(&max_prefix_length));

    let max_left_child_bytes = (child_order_len as i32 - 1)
        .checked_mul(child_size)
        .expect("child_order/child_size product fits i32");
    let _bound = max_prefix_length
        .checked_add(max_left_child_bytes)
        .expect("inner prefix bound fits i32");
}

/// `get_padding` computes `prefix = idx * child_size` and
/// `suffix = child_size * (child_order.len() - 1 - idx)`. Both are overflow-free
/// in `i32` for well-formed bounds.
#[kani::proof]
fn get_padding_no_overflow() {
    let n: usize = kani::any();
    let idx: i32 = kani::any();
    let child_size: i32 = kani::any();
    kani::assume((2..=16).contains(&n));
    kani::assume((0..=(n as i32 - 1)).contains(&idx));
    kani::assume((1..=128).contains(&child_size));

    let _prefix = idx.checked_mul(child_size).expect("prefix offset fits i32");
    let _suffix = child_size
        .checked_mul(n as i32 - 1 - idx)
        .expect("suffix size fits i32");
}

/// The slice accesses in `left_branches_are_empty`,
/// `op.prefix[from .. from + child_size]` with `from = actual_prefix + i*child_size`
/// and `actual_prefix = prefix.len() - left_branches*child_size` (via
/// `checked_sub`), are always in bounds — so the padding scan never panics on an
/// out-of-range slice. This is the Dragonberry-relevant safety property.
#[kani::proof]
#[kani::unwind(17)]
fn left_branches_slice_in_bounds() {
    let prefix_len: usize = kani::any();
    let left_branches: usize = kani::any();
    let child_size: usize = kani::any();
    kani::assume((1..=64).contains(&child_size));
    kani::assume((1..=16).contains(&left_branches));

    if let Some(actual_prefix) = prefix_len.checked_sub(left_branches * child_size) {
        let mut i = 0usize;
        while i < left_branches {
            let from = actual_prefix + i * child_size;
            // models `op.prefix[from .. from + child_size]`
            assert!(from + child_size <= prefix_len, "left-branch slice in bounds");
            i += 1;
        }
    }
}
