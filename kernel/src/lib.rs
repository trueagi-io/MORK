pub mod space;


#[cfg(test)]
mod tests {
    use std::mem;
    use crate::space::*;

    #[test]
    fn parse() {
        let input = "(foo bar)\n";
        let mut sm = SymbolMapping::new();
        let mut s = Space::new();
        s.load(input.as_bytes(), &mut sm);
        let mut res = Vec::<u8>::new();
        s.dump(&mut res, unsafe { std::mem::transmute::<&SymbolMapping, &'static SymbolMapping>(&sm) });
        assert_eq!(input, String::from_utf8(res).unwrap());
    }
}
