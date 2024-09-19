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
        assert_eq!(s.load(input.as_bytes(), &mut sm).unwrap(), 1);
        let mut res = Vec::<u8>::new();
        s.dump(&mut res, unsafe { std::mem::transmute::<&SymbolMapping, &'static SymbolMapping>(&sm) });
        assert_eq!(input, String::from_utf8(res).unwrap());
    }

    #[test]
    fn parse_csv() {
        let csv_input = "0,123,foo\n1,321,bar\n";
        let reconstruction = "(0 123 foo)\n(1 321 bar)\n";
        let mut sm = SymbolMapping::new();
        let mut s = Space::new();
        assert_eq!(s.load_csv(csv_input.as_bytes(), &mut sm).unwrap(), 2);
        let mut res = Vec::<u8>::new();
        s.dump(&mut res, unsafe { std::mem::transmute::<&SymbolMapping, &'static SymbolMapping>(&sm) });
        assert_eq!(reconstruction, String::from_utf8(res).unwrap());
    }
}
