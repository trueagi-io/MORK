use std::str::from_utf8;

use pathmap::trie_map::BytesTrieMap;


pub struct SymbolMapping {
count: u64,
  symbols: BytesTrieMap<Vec<u8>>,
  strings: BytesTrieMap<String>,
}

impl SymbolMapping {
    pub fn new() -> Self {
        Self {
            count: 3,
            symbols: BytesTrieMap::new(),
            strings: BytesTrieMap::new(),
        }
    }

    // // temporary workaround for the inability of making BytesTrieMaps static
    // pub fn as_static_mut(&mut self) -> &'static mut SymbolMapping {
    //     unsafe { core::mem::transmute::<&mut SymbolMapping, &'static mut SymbolMapping>(self) }
    // }

    // pub fn as_static(&self) -> &'static SymbolMapping {
    //     unsafe { core::mem::transmute::<&SymbolMapping, &'static SymbolMapping>(&self) }
    // }
}

fn gen_key<'a>(i: u64, buffer: *mut u8) -> &'a [u8] {
  let ir = u64::from_be(i);
  unsafe { core::ptr::write_unaligned(buffer as *mut u64, ir) };
  let bs = (8 - ir.trailing_zeros()/8) as usize;
  let l = bs.max(1);
  unsafe { std::slice::from_raw_parts(buffer.byte_offset((8 - l) as isize), l) }
}


// // TODO put the trait back!
// impl /* Parser for */ SymbolMapping {
//     pub fn tokenizer(&mut self, s: String) -> Vec<u8> {
//         if s.len() == 0 { return vec![] }
//         // return s.as_bytes().to_vec();
//         let mut z = self.symbols.write_zipper_at_path(s.as_bytes());
//         if let Some(r) = z.get_value() {
//             r.clone()
//         } else {
//             self.count += 1;
//             let mut buf: [u8; 8] = [0; 8];
//             let slice = gen_key(self.count, buf.as_mut_ptr());
//             let internal = slice.to_vec();
//             z.set_value(internal.clone());
//             drop(z);
//             self.strings.insert(slice, s);
//             internal
//         }
//     }
// }

impl mork_frontend::bytestring_parser::Parser for SymbolMapping {
    fn tokenizer<'r>(&mut self, s: &[u8]) -> &'r [u8] {
        if s.len() == 0 { return &[][..] }
        let mut z = self.symbols.write_zipper_at_path(s);
        let out = if let Some(r) = z.get_value() {
            r
        } else {
            self.count += 1;
            let mut buf: [u8; 8] = [0; 8];
            let slice = gen_key(self.count, buf.as_mut_ptr());
            let internal = slice.to_vec();
            z.set_value(internal.clone());
            drop(z);

            let utf8 = core::str::from_utf8(s);
            if let Ok(s_checked) = utf8 {

              self.strings.insert(slice, s_checked.to_string());
              self.token_lookup(s).unwrap().as_bytes()
            } else {
              core::todo!("Assumptions need to be changed!")
            }
        };
        // Safety : SymbolMapping will never mutate the values it stores
        unsafe {&*(out as *const _)}
    }
}


impl SymbolMapping {
    pub fn token_lookup(&self, token: &[u8]) -> Option<&String> {
        self.strings.get(token)
    }
}

