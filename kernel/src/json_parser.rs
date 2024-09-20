use std::{str, slice};
use std::char::decode_utf16;
use std::convert::TryFrom;
use std::{ char, error, fmt };
use std::io::Write;

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    UnexpectedCharacter {
        ch: char,
        line: usize,
        column: usize,
    },
    UnexpectedEndOfJson,
    ExceededDepthLimit,
    FailedUtf8Parsing,
    WrongType(String),
}

impl Error {
    pub fn wrong_type(expected: &str) -> Self {
        Error::WrongType(expected.into())
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;

        match *self {
            UnexpectedCharacter {
                ref ch,
                ref line,
                ref column,
            } => write!(f, "Unexpected character: {} at ({}:{})", ch, line, column),

            UnexpectedEndOfJson   => write!(f, "Unexpected end of JSON"),
            ExceededDepthLimit    => write!(f, "Exceeded depth limit"),
            FailedUtf8Parsing     => write!(f, "Failed to parse UTF-8 bytes"),
            WrongType(ref s)      => write!(f, "Wrong type, expected: {}", s),
        }
    }
}

impl error::Error for Error {
    fn description(&self) -> &str {
        use Error::*;

        match *self {
            UnexpectedCharacter { .. } => "Unexpected character",
            UnexpectedEndOfJson        => "Unexpected end of JSON",
            ExceededDepthLimit         => "Exceeded depth limit",
            FailedUtf8Parsing          => "Failed to read bytes as UTF-8 from JSON",
            WrongType(_)               => "Wrong type",
        }
    }
}

pub (crate) trait Transcriber {
    fn descend_index(&mut self, i: usize, first: bool) -> ();
    fn ascend_index(&mut self, i: usize, last: bool) -> ();
    fn write_empty_array(&mut self) -> ();

    fn descend_key(&mut self, k: &str, first: bool) -> ();
    fn ascend_key(&mut self, k: &str, last: bool) -> ();
    fn write_empty_object(&mut self) -> ();

    fn write_string(&mut self, s: &str) -> ();
    fn write_positive(&mut self, s: u64) -> ();
    fn write_negative(&mut self, s: u64) -> ();
    fn write_true(&mut self) -> ();
    fn write_false(&mut self) -> ();
    fn write_null(&mut self) -> ();

    fn begin(&mut self) -> ();
    fn end(&mut self) -> ();
}


pub(crate) struct DebugTranscriber;
impl Transcriber for DebugTranscriber {
    fn begin(&mut self) -> () { println!("begin") }
    fn descend_index(&mut self, i: usize, first: bool) -> () { if first { println!("descend array") }; println!("descend index {}", i) }
    fn ascend_index(&mut self, i: usize, last: bool) -> () { println!("ascend index {}", i); if last { println!("ascend array") }; }
    fn write_empty_array(&mut self) -> () { println!("write empty array") }
    fn descend_key(&mut self, k: &str, first: bool) -> () { if first { println!("descend object") }; println!("descend key {}", k) }
    fn ascend_key(&mut self, k: &str, last: bool) -> () { println!("ascend key {}", k); if last { println!("ascend object") }; }
    fn write_empty_object(&mut self) -> () { println!("write empty object") }
    fn write_string(&mut self, s: &str) -> () { println!("write string \"{}\"", s) }
    fn write_positive(&mut self, s: u64) -> () { println!("write {}", s) }
    fn write_negative(&mut self, s: u64) -> () { println!("write -{}", s) }
    fn write_true(&mut self) -> () { println!("write true") }
    fn write_false(&mut self) -> () { println!("write false") }
    fn write_null(&mut self) -> () { println!("write null") }
    fn end(&mut self) -> () { println!("end") }
}

pub(crate) struct WriteTranscriber<W : Write>{ pub w: W }
impl <W : Write> Transcriber for WriteTranscriber<W> {
    fn begin(&mut self) -> () { }
    fn descend_index(&mut self, i: usize, first: bool) -> () { if first { self.w.write("[".as_bytes()).unwrap(); }; }
    fn ascend_index(&mut self, i: usize, last: bool) -> () { if last { self.w.write("]".as_bytes()).unwrap(); } else { self.w.write(", ".as_bytes()).unwrap(); }; }
    fn write_empty_array(&mut self) -> () { self.w.write("[]".as_bytes()).unwrap(); }
    fn descend_key(&mut self, k: &str, first: bool) -> () { if first { self.w.write("{".as_bytes()).unwrap(); }; self.w.write("\"".as_bytes()).unwrap(); self.w.write(k.as_bytes()).unwrap(); self.w.write("\": ".as_bytes()).unwrap(); }
    fn ascend_key(&mut self, k: &str, last: bool) -> () { if last { self.w.write("}".as_bytes()).unwrap(); } else { self.w.write(", ".as_bytes()).unwrap(); }; }
    fn write_empty_object(&mut self) -> () { self.w.write("{}".as_bytes()).unwrap(); }
    fn write_string(&mut self, s: &str) -> () { self.w.write("\"".as_bytes()).unwrap(); self.w.write(s.as_bytes()).unwrap(); self.w.write("\"".as_bytes()).unwrap(); }
    fn write_positive(&mut self, s: u64) -> () { self.w.write(s.to_string().as_bytes()).unwrap(); }
    fn write_negative(&mut self, s: u64) -> () { self.w.write("-".as_bytes()).unwrap(); self.w.write(s.to_string().as_bytes()).unwrap(); }
    fn write_true(&mut self) -> () { self.w.write("true".as_bytes()).unwrap(); }
    fn write_false(&mut self) -> () { self.w.write("false".as_bytes()).unwrap(); }
    fn write_null(&mut self) -> () { self.w.write("null".as_bytes()).unwrap(); }
    fn end(&mut self) -> () { }
}

#[derive(Debug, Clone)]
pub enum JsonValue {
    Null,
    String(String),
    Number(i64),
    Boolean(bool),
    Object(std::collections::HashMap<String, JsonValue>),
    Array(Vec<JsonValue>),
}

// This is not actual max precision, but a threshold at which number parsing
// kicks into checked math.
const MAX_PRECISION: u64 = 576460752303423500;


// How many nested Objects/Arrays are allowed to be parsed
const DEPTH_LIMIT: usize = 512;


// The `Parser` struct keeps track of indexing over our buffer. All niceness
// has been abandoned in favor of raw pointer magic. Does that make you feel
// dirty? _Good._
pub (crate) struct Parser<'a> {
    // Helper buffer for parsing strings that can't be just memcopied from
    // the original source (escaped characters)
    buffer: Vec<u8>,

    // String slice to parse
    source: &'a str,

    // Byte pointer to the slice above
    byte_ptr: *const u8,

    // Current index
    index: usize,

    // Length of the source
    length: usize,
}

// Read a byte from the source.
// Will return an error if there are no more bytes.
macro_rules! expect_byte {
    ($parser:ident) => ({
        if $parser.is_eof() {
            return Err(Error::UnexpectedEndOfJson);
        }

        let ch = $parser.read_byte();
        $parser.bump();
        ch
    })
}


// Expect a sequence of specific bytes in specific order, error otherwise.
// This is useful for reading the 3 JSON identifiers:
//
// - "t" has to be followed by "rue"
// - "f" has to be followed by "alse"
// - "n" has to be followed by "ull"
//
// Anything else is an error.
macro_rules! expect_sequence {
    ($parser:ident, $( $ch:pat ),*) => {
        $(
            match expect_byte!($parser) {
                $ch => {},
                _   => return $parser.unexpected_character(),
            }
        )*
    }
}


// A drop in macro for when we expect to read a byte, but we don't care
// about any whitespace characters that might occur before it.
macro_rules! expect_byte_ignore_whitespace {
    ($parser:ident) => ({
        let mut ch = expect_byte!($parser);

        // Don't go straight for the loop, assume we are in the clear first.
        match ch {
            // whitespace
            9 ..= 13 | 32 => {
                loop {
                    match expect_byte!($parser) {
                        9 ..= 13 | 32 => {},
                        next          => {
                            ch = next;
                            break;
                        }
                    }
                }
            },
            _ => {}
        }

        ch
    })
}

// Expect to find EOF or just whitespaces leading to EOF after a JSON value
macro_rules! expect_eof {
    ($parser:ident) => ({
        while !$parser.is_eof() {
            match $parser.read_byte() {
                9 ..= 13 | 32 => $parser.bump(),
                _             => {
                    $parser.bump();
                    return $parser.unexpected_character();
                }
            }
        }
    })
}

// Expect a particular byte to be next. Also available with a variant
// creates a `match` expression just to ease some pain.
macro_rules! expect {
    ($parser:ident, $byte:expr) => ({
        let ch = expect_byte_ignore_whitespace!($parser);

        if ch != $byte {
            return $parser.unexpected_character()
        }
    });

    {$parser:ident $(, $byte:pat => $then:expr )*} => ({
        let ch = expect_byte_ignore_whitespace!($parser);

        match ch {
            $(
                $byte => $then,
            )*
            _ => return $parser.unexpected_character()
        }

    })
}


// Look up table that marks which characters are allowed in their raw
// form in a string.
const QU: bool = false;  // double quote       0x22
const BS: bool = false;  // backslash          0x5C
const CT: bool = false;  // control character  0x00 ..= 0x1F
const __: bool = true;

static ALLOWED: [bool; 256] = [
    // 0   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
    CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, // 0
    CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, // 1
    __, __, QU, __, __, __, __, __, __, __, __, __, __, __, __, __, // 2
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 3
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 4
    __, __, __, __, __, __, __, __, __, __, __, __, BS, __, __, __, // 5
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 6
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 7
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 8
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // 9
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // A
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // B
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // C
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // D
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // E
    __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, __, // F
];


// Expect a string. This is called after encountering, and consuming, a
// double quote character. This macro has a happy path variant where it
// does almost nothing as long as all characters are allowed (as described
// in the look up table above). If it encounters a closing quote without
// any escapes, it will use a slice straight from the source, avoiding
// unnecessary buffering.
macro_rules! expect_string {
    ($parser:ident) => ({
        let result: &str;
        let start = $parser.index;

        loop {
            let ch = expect_byte!($parser);
            if ALLOWED[ch as usize] {
                continue;
            }
            if ch == b'"' {
                unsafe {
                    let ptr = $parser.byte_ptr.offset(start as isize);
                    let len = $parser.index - 1 - start;
                    result = str::from_utf8_unchecked(slice::from_raw_parts(ptr, len));
                }
                break;
            }
            if ch == b'\\' {
                result = $parser.read_complex_string(start)?;
                break;
            }

            return $parser.unexpected_character();
        }

        result
    })
}


// Expect a number. Of some kind.
macro_rules! expect_number {
    ($parser:ident, $first:ident) => ({
        let mut num = ($first - b'0') as u64;

        // let result: Number;

        // Cap on how many iterations we do while reading to u64
        // in order to avoid an overflow.
        loop {
            if num >= MAX_PRECISION {
                panic!("max precision exceeded");
                // result = $parser.read_big_number(num)?;
                break;
            }

            if $parser.is_eof() {
                // result = num.into();
                break;
            }

            let ch = $parser.read_byte();

            match ch {
                b'0' ..= b'9' => {
                    $parser.bump();
                    num = num * 10 + (ch - b'0') as u64;
                },
                _             => {
                    let mut e = 0;
                    num = allow_number_extensions!($parser, num, e, ch);
                    // result = allow_number_extensions!($parser, num, e, ch);
                    break;
                }
            }
        }

        // result
        num
    })
}


// Invoked after parsing an integer, this will account for fractions and/or
// `e` notation.
macro_rules! allow_number_extensions {
    ($parser:ident, $num:ident, $e:ident, $ch:ident) => ({
        match $ch {
            b'.'        => {
                panic!("fractions unimplemented");
                // $parser.bump();
                // expect_fraction!($parser, $num, $e)
            },
            b'e' | b'E' => {
                panic!("exponents unimplemented");
                // $parser.bump();
                // $parser.expect_exponent($num, $e)?
            },
            _  => $num.into()
        }
    });

    // Alternative variant that defaults everything to 0. This is actually
    // quite handy as the only number that can begin with zero, has to have
    // a zero mantissa. Leading zeroes are illegal in JSON!
    ($parser:ident) => ({
        if $parser.is_eof() {
            0.into()
        } else {
            let mut num = 0;
            let mut e = 0;
            let ch = $parser.read_byte();
            allow_number_extensions!($parser, num, e, ch)
        }
    })
}


// If a dot `b"."` byte has been read, start reading the decimal fraction
// of the number.
// macro_rules! expect_fraction {
//     ($parser:ident, $num:ident, $e:ident) => ({
//         let result: Number;
//
//         let ch = expect_byte!($parser);
//
//         match ch {
//             b'0' ..= b'9' => {
//                 if $num < MAX_PRECISION {
//                     $num = $num * 10 + (ch - b'0') as u64;
//                     $e -= 1;
//                 } else {
//                     match $num.checked_mul(10).and_then(|num| {
//                         num.checked_add((ch - b'0') as u64)
//                     }) {
//                         Some(result) => {
//                             $num = result;
//                             $e -= 1;
//                         },
//                         None => {}
//                     }
//                 }
//             },
//             _ => return $parser.unexpected_character()
//         }
//
//         loop {
//             if $parser.is_eof() {
//                 result = unsafe { Number::from_parts_unchecked(true, $num, $e) };
//                 break;
//             }
//             let ch = $parser.read_byte();
//
//             match ch {
//                 b'0' ..= b'9' => {
//                     $parser.bump();
//                     if $num < MAX_PRECISION {
//                         $num = $num * 10 + (ch - b'0') as u64;
//                         $e -= 1;
//                     } else {
//                         match $num.checked_mul(10).and_then(|num| {
//                             num.checked_add((ch - b'0') as u64)
//                         }) {
//                             Some(result) => {
//                                 $num = result;
//                                 $e -= 1;
//                             },
//                             None => {}
//                         }
//                     }
//                 },
//                 b'e' | b'E' => {
//                     $parser.bump();
//                     result = $parser.expect_exponent($num, $e)?;
//                     break;
//                 }
//                 _ => {
//                     result = unsafe { Number::from_parts_unchecked(true, $num, $e) };
//                     break;
//                 }
//             }
//         }
//
//         result
//     })
// }

impl<'a> Parser<'a> {
    pub fn new(source: &'a str) -> Self {
        Parser {
            buffer: Vec::with_capacity(30),
            source: source,
            byte_ptr: source.as_ptr(),
            index: 0,
            length: source.len(),
        }
    }

    // Check if we are at the end of the source.
    #[inline(always)]
    fn is_eof(&mut self) -> bool {
        self.index == self.length
    }

    // Read a byte from the source. Note that this does not increment
    // the index. In few cases (all of them related to number parsing)
    // we want to peek at the byte before doing anything. This will,
    // very very rarely, lead to a situation where the same byte is read
    // twice, but since this operation is using a raw pointer, the cost
    // is virtually irrelevant.
    #[inline(always)]
    fn read_byte(&mut self) -> u8 {
        debug_assert!(self.index < self.length, "Reading out of bounds");

        unsafe { *self.byte_ptr.offset(self.index as isize) }
    }

    // Manually increment the index. Calling `read_byte` and then `bump`
    // is equivalent to consuming a byte on an iterator.
    #[inline(always)]
    fn bump(&mut self) {
        self.index = self.index.wrapping_add(1);
    }

    // So we got an unexpected character, now what? Well, figure out where
    // it is, and throw an error!
    fn unexpected_character<T: Sized>(&mut self) -> Result<T> {
        let at = self.index - 1;

        let ch = self.source[at..]
            .chars()
            .next()
            .expect("Must have a character");

        let (lineno, col) = self.source[..at]
            .lines()
            .enumerate()
            .last()
            .unwrap_or((0, ""));

        let colno = col.chars().count();

        Err(Error::UnexpectedCharacter {
            ch: ch,
            line: lineno + 1,
            column: colno + 1,
        })
    }

    // Boring
    fn read_hexdec_digit(&mut self) -> Result<u16> {
        let ch = expect_byte!(self);
        Ok(match ch {
            b'0' ..= b'9' => (ch - b'0'),
            b'a' ..= b'f' => (ch + 10 - b'a'),
            b'A' ..= b'F' => (ch + 10 - b'A'),
            _             => return self.unexpected_character(),
        } as u16)
    }

    // Boring
    fn read_hexdec_codepoint(&mut self) -> Result<u16> {
        Ok(
            self.read_hexdec_digit()? << 12 |
                self.read_hexdec_digit()? << 8  |
                self.read_hexdec_digit()? << 4  |
                self.read_hexdec_digit()?
        )
    }

    // Oh look, some action. This method reads an escaped unicode
    // sequence such as `\uDEAD` from the string. Except `DEAD` is
    // not a valid codepoint, so it also needs to handle errors...
    fn read_codepoint(&mut self) -> Result<()> {
        let mut buf = [0; 4];
        let codepoint = self.read_hexdec_codepoint()?;

        let unicode = match char::try_from(codepoint as u32) {
            Ok(code) => code,
            // Handle surrogate pairs
            Err(_) => {
                expect_sequence!(self, b'\\', b'u');

                match decode_utf16(
                    [codepoint, self.read_hexdec_codepoint()?].iter().copied()
                ).next() {
                    Some(Ok(code)) => code,
                    _ => return Err(Error::FailedUtf8Parsing),
                }
            }
        };

        self.buffer.extend_from_slice(unicode.encode_utf8(&mut buf).as_bytes());

        Ok(())
    }

    // What's so complex about strings you may ask? Not that much really.
    // This method is called if the `expect_string!` macro encounters an
    // escape. The added complexity is that it will have to use an internal
    // buffer to read all the escaped characters into, before finally
    // producing a usable slice. What it means it that parsing "foo\bar"
    // is whole lot slower than parsing "foobar", as the former suffers from
    // having to be read from source to a buffer and then from a buffer to
    // our target string. Nothing to be done about this, really.
    fn read_complex_string<'b>(&mut self, start: usize) -> Result<&'b str> {
        // Since string slices are returned by this function that are created via pointers into `self.buffer`
        // we shouldn't be clearing or modifying the buffer in consecutive calls to this function. Instead
        // we continuously append bytes to `self.buffer` and keep track of the starting offset of the buffer on each
        // call to this function. Later when creating string slices that point to the contents of this buffer
        // we use this starting offset to make sure that newly created slices point only to the bytes that were
        // appended in the most recent call to this function.
        //
        // Failing to do this can result in the StackBlock `key` values being modified in place later.
        let len = self.buffer.len();
        //self.buffer.clear();
        let mut ch = b'\\';

        // TODO: Use fastwrite here as well
        self.buffer.extend_from_slice(&self.source.as_bytes()[start .. self.index - 1]);

        loop {
            if ALLOWED[ch as usize] {
                self.buffer.push(ch);
                ch = expect_byte!(self);
                continue;
            }
            match ch {
                b'"'  => break,
                b'\\' => {
                    let escaped = expect_byte!(self);
                    let escaped = match escaped {
                        b'u'  => {
                            self.read_codepoint()?;
                            ch = expect_byte!(self);
                            continue;
                        },
                        b'"'  |
                        b'\\' |
                        b'/'  => escaped,
                        b'b'  => 0x8,
                        b'f'  => 0xC,
                        b't'  => b'\t',
                        b'r'  => b'\r',
                        b'n'  => b'\n',
                        _     => return self.unexpected_character()
                    };
                    self.buffer.push(escaped);
                },
                _ => return self.unexpected_character()
            }
            ch = expect_byte!(self);
        }

        // Since the original source is already valid UTF-8, and `\`
        // cannot occur in front of a codepoint > 127, this is safe.
        Ok(unsafe {
            str::from_utf8_unchecked(
                // Because the buffer is stored on the parser, returning it
                // as a slice here freaks out the borrow checker. The compiler
                // can't know that the buffer isn't used till the result
                // of this function is long used and irrelevant. To avoid
                // issues here, we construct a new slice from raw parts, which
                // then has lifetime bound to the outer function scope instead
                // of the parser itself.
                slice::from_raw_parts(self.buffer[len .. ].as_ptr(), self.buffer.len() - len)
            )
        })
    }

    // Big numbers! If the `expect_number!` reaches a point where the decimal
    // mantissa could have overflown the size of u64, it will switch to this
    // control path instead. This method will pick up where the macro started,
    // but instead of continuing to read into the mantissa, it will increment
    // the exponent. Note that no digits are actually read here, as we already
    // exceeded the precision range of f64 anyway.
    // fn read_big_number(&mut self, mut num: u64) -> Result<Number> {
        // let mut e = 0i16;
        // loop {
        //     if self.is_eof() {
        //         return Ok(unsafe { Number::from_parts_unchecked(true, num, e) });
        //     }
        //     let ch = self.read_byte();
        //     match ch {
        //         b'0' ..= b'9' => {
        //             self.bump();
        //             match num.checked_mul(10).and_then(|num| {
        //                 num.checked_add((ch - b'0') as u64)
        //             }) {
        //                 Some(result) => num = result,
        //                 None         => e = e.checked_add(1).ok_or_else(|| Error::ExceededDepthLimit)?,
        //             }
        //         },
        //         b'.' => {
        //             self.bump();
        //             return Ok(expect_fraction!(self, num, e));
        //         },
        //         b'e' | b'E' => {
        //             self.bump();
        //             return self.expect_exponent(num, e);
        //         }
        //         _  => break
        //     }
        // }
        //
        // Ok(unsafe { Number::from_parts_unchecked(true, num, e) })
        // }

    // Called in the rare case that a number with `e` notation has been
    // encountered. This is pretty straight forward, I guess.
    // fn expect_exponent(&mut self, num: u64, big_e: i16) -> Result<Number> {
    //     let mut ch = expect_byte!(self);
    //     let sign = match ch {
    //         b'-' => {
    //             ch = expect_byte!(self);
    //             -1
    //         },
    //         b'+' => {
    //             ch = expect_byte!(self);
    //             1
    //         },
    //         _    => 1
    //     };
    //
    //     let mut e = match ch {
    //         b'0' ..= b'9' => (ch - b'0') as i16,
    //         _ => return self.unexpected_character(),
    //     };
    //
    //     loop {
    //         if self.is_eof() {
    //             break;
    //         }
    //         let ch = self.read_byte();
    //         match ch {
    //             b'0' ..= b'9' => {
    //                 self.bump();
    //                 e = e.saturating_mul(10).saturating_add((ch - b'0') as i16);
    //             },
    //             _  => break
    //         }
    //     }
    //
    //     Ok(unsafe { Number::from_parts_unchecked(true, num, big_e.saturating_add(e * sign)) })
    // }

    // Parse away!
    pub (crate) fn parse<T : Transcriber>(&mut self, t: &mut T) -> Result<JsonValue> {
        let mut stack = Vec::with_capacity(3);
        let mut ch = expect_byte_ignore_whitespace!(self);
        t.begin();

        'parsing: loop {
            let mut value = match ch {
                b'[' => {
                    ch = expect_byte_ignore_whitespace!(self);

                    if ch != b']' {
                        if stack.len() == DEPTH_LIMIT {
                            return Err(Error::ExceededDepthLimit);
                        }
                        t.descend_index(0, true);
                        stack.push(StackBlock(JsonValue::Array(Vec::with_capacity(2)), "".to_string()));
                        continue 'parsing;
                    }

                    t.write_empty_array();

                    JsonValue::Array(Vec::new())
                },
                b'{' => {
                    ch = expect_byte_ignore_whitespace!(self);

                    if ch != b'}' {
                        if stack.len() == DEPTH_LIMIT {
                            return Err(Error::ExceededDepthLimit);
                        }

                        let mut object = std::collections::HashMap::with_capacity(3);

                        if ch != b'"' {
                            return self.unexpected_character()
                        }

                        let k = expect_string!(self).to_string();
                        object.insert(k.clone(), JsonValue::Null);
                        t.descend_key(k.as_str(), true);

                        expect!(self, b':');

                        stack.push(StackBlock(JsonValue::Object(object), k));

                        ch = expect_byte_ignore_whitespace!(self);

                        continue 'parsing;
                    }

                    t.write_empty_object();

                    JsonValue::Object(std::collections::HashMap::new())
                },
                b'"' => {
                    let s = expect_string!(self).to_string();
                    t.write_string(s.as_str());
                    // insert_symbol!(z, sm, s.to_string());
                    JsonValue::String(s)
                },
                b'0' => panic!("number extension not allowed") /*JsonValue::Number(allow_number_extensions!(self))*/,
                b'1' ..= b'9' => {
                    let n = expect_number!(self, ch);
                    t.write_positive(n);
                    JsonValue::Number(n as i64)
                },
                b'-' => {
                    let ch = expect_byte!(self);
                    let n = match ch {
                        b'0' => panic!("number extension not allowed") /*allow_number_extensions!(self)*/,
                        b'1' ..= b'9' => expect_number!(self, ch),
                        _    => return self.unexpected_character()
                    };
                    t.write_negative(n);
                    JsonValue::Number(-(n as i64))
                }
                b't' => {
                    expect_sequence!(self, b'r', b'u', b'e');
                    t.write_true();
                    JsonValue::Boolean(true)
                },
                b'f' => {
                    expect_sequence!(self, b'a', b'l', b's', b'e');
                    t.write_false();
                    JsonValue::Boolean(false)
                },
                b'n' => {
                    expect_sequence!(self, b'u', b'l', b'l');
                    t.write_null();
                    JsonValue::Null
                },
                _    => return self.unexpected_character()
            };

            'popping: loop {
                match stack.last_mut() {
                    None => {
                        expect_eof!(self);
                        t.end();
                        return Ok(value);
                    },

                    Some(&mut StackBlock(JsonValue::Array(ref mut array), _)) => {
                        let i = array.len();
                        array.push(value);

                        ch = expect_byte_ignore_whitespace!(self);

                        match ch {
                            b',' => {
                                ch = expect_byte_ignore_whitespace!(self);
                                t.ascend_index(i, false);
                                t.descend_index(i + 1, false);
                                continue 'parsing;
                            },
                            b']' => { t.ascend_index(i, true); },
                            _    => return self.unexpected_character()
                        }
                    },

                    Some(&mut StackBlock(JsonValue::Object(ref mut object), ref mut index )) => {
                        object.insert(index.clone(), value);

                        ch = expect_byte_ignore_whitespace!(self);

                        match ch {
                            b',' => {
                                t.ascend_key(index.as_str(), false);
                                expect!(self, b'"');
                                let k = expect_string!(self).to_string();
                                t.descend_key(k.as_str(), false);
                                object.insert(k.clone(), JsonValue::Null);
                                *index = k;
                                expect!(self, b':');

                                ch = expect_byte_ignore_whitespace!(self);

                                continue 'parsing;
                            },
                            b'}' => { t.ascend_key(index.as_str(), true); },
                            _    => return self.unexpected_character()
                        }
                    },

                    _ => unreachable!(),
                }

                value = match stack.pop() {
                    Some(StackBlock(value, _)) => value,
                    None                       => break 'popping
                }
            }
        }
    }
}

struct StackBlock(JsonValue, String);