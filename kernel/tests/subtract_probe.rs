use pathmap::PathMap;
use std::time::Instant;

/// Does stock `subtract` prune shared COW subtrees (pointer-equal nodes skipped)?
/// A 500k-fact map minus itself-plus-one-fact must be near-instant if it does,
/// and a full O(map) walk if it does not. The printed timing is the answer; the
/// count assertion just keeps the probe honest.
#[test]
fn subtract_of_cow_clone_probe() {
    let mut m: PathMap<()> = PathMap::new();
    for i in 0..500_000u32 {
        m.insert(format!("(edge n{i} n{})", i + 1).as_bytes(), ());
    }
    let mut c = m.clone();
    c.insert(b"(edge extra extra)", ());

    let t = Instant::now();
    let d = c.subtract(&m);
    let one = t.elapsed();

    let t = Instant::now();
    let d2 = m.subtract(&m);
    let zero = t.elapsed();

    println!("subtract(clone+1 \\ base) = {one:?}; subtract(self \\ self) = {zero:?}");
    assert_eq!(d.val_count(), 1);
    assert_eq!(d2.val_count(), 0);
}
