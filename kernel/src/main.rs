use std::time::Instant;
use mork::space::{Space, SymbolMapping};

fn main() {
    let mut s = Space::new();
    let mut sm = SymbolMapping::new();
    let t0 = Instant::now();
    let nodesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/nodes.json").unwrap();
    let loaded = s.load_json(nodesf, &mut sm).unwrap();
    println!("loaded {} nodes in {} seconds", loaded, t0.elapsed().as_secs());
    let t1 = Instant::now();
    let edgesf = std::fs::File::open("/run/media/adam/43323a1c-ad7e-4d9a-b3c0-cf84e69ec61a/awesome-biomedical-kg/ckg_v3-002/results/edges.json").unwrap();
    let loaded = s.load_json(edgesf, &mut sm).unwrap();
    println!("loaded {} edges in {} seconds", loaded, t1.elapsed().as_secs());
    #[cfg(feature = "pathmap_counters")]{
      s.done(sm);
    }

}

