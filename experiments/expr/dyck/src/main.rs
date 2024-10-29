extern crate alloc;
use dyck::test_parser::DyckParser;
use std::hint::black_box;

fn main() {
  let s = std::fs::read_to_string("/home/adam/Projects/MORK/frontend/resources/edges67458171.metta").unwrap();
  let start = std::time::Instant::now();
  let mut count = 0u64;
  for each in DyckParser::new(&s) {
    match each {
      Ok(triple) => {
        black_box(triple);
        count += 1;
      }
      Err(e) => std::println!("{e:?}"),
    }
  }
  let end = start.elapsed().as_millis();
  std::println!("count : {count}\ntime : {end}") // 36 seconds
}
