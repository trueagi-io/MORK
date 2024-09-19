pub mod space;
mod json_parser;

#[cfg(test)]
mod tests {
    use std::mem;
    use crate::json_parser::Parser;
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

    #[test]
    fn parse_json() {
        let json_input = r#"{
  "first_name": "John",
  "last_name": "Smith",
  "is_alive": true,
  "age": 27,
  "address": {
    "street_address": "21 2nd Street",
    "city": "New York",
    "state": "NY",
    "postal_code": "10021-3100"
  },
  "phone_numbers": [
    {
      "type": "home",
      "number": "212 555-1234"
    },
    {
      "type": "office",
      "number": "646 555-4567"
    }
  ],
  "children": [
    "Catherine",
    "Thomas",
    "Trevor"
  ],
  "spouse": null
}"#;

        let mut p = Parser::new(json_input);
        println!("{:?}", p.parse());
        // let reconstruction = "(0 123 foo)\n(1 321 bar)\n";
        // let mut sm = SymbolMapping::new();
        // let mut s = Space::new();
        // assert_eq!(s.load_json(json_input.as_bytes(), &mut sm).unwrap(), 2);
        // let mut res = Vec::<u8>::new();
        // s.dump(&mut res, unsafe { std::mem::transmute::<&SymbolMapping, &'static SymbolMapping>(&sm) });
        // assert_eq!(reconstruction, String::from_utf8(res).unwrap());
    }
}
