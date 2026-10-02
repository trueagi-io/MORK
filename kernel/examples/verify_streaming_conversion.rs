//! Compare every serialized path with an on-disk ACT, without constructing a Space.
//! cargo run --release -p mork --example verify_streaming_conversion -- FILE.paths FILE.act
use pathmap::arena_compact::ArenaCompactTree;
use pathmap::paths_serialization::for_each_deserialized_path;
use std::fs::File;
use std::io::{self, BufReader};

fn main() -> io::Result<()> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() != 2 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "expected FILE.paths FILE.act",
        ));
    }
    let tree = ArenaCompactTree::open_mmap(&args[1])?;
    let mut actual = tree.iter();
    let mut probes = 0;
    let stats =
        for_each_deserialized_path(BufReader::new(File::open(&args[0])?), |index, expected| {
            let Some((path, value)) = actual.next() else {
                return Err(io::Error::other(format!("ACT ended at path {index}")));
            };
            if path != expected || value != 0 {
                return Err(io::Error::other(format!("ACT mismatch at path {index}")));
            }
            if index % 1_000_000 == 0 {
                if tree.get_val_at(expected) != Some(0) {
                    return Err(io::Error::other(format!(
                        "point lookup mismatch at path {index}"
                    )));
                }
                probes += 1;
            }
            Ok(())
        })?;
    if actual.next().is_some() {
        return Err(io::Error::other("ACT contains extra paths"));
    }
    println!(
        "verified all {} paths and {probes} on-disk point lookups",
        stats.path_count
    );
    Ok(())
}
