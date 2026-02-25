use log::trace;
use std::io::Write;
use std::ops::Div;
use base64::Engine;
use hex;
use eval::{EvalScope, FuncType};
use mork_expr::SourceItem;
use eval_ffi::{ExprSink, ExprSource, EvalError, Tag};

macro_rules! op {
    (num nary $name:ident($initial:expr, $t:ident: $tt:ty, $x:ident: $tx:ty) => $e:expr) => {
        pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
            let expr = unsafe { &mut *expr };
            let sink = unsafe { &mut *sink };
            let items = expr.consume_head_check(stringify!($name).as_bytes())?;
            let mut $t: $tt = $initial;
            for _ in 0..items {
                let $x = expr.consume::<$tx>()?;
                $t = $e;
            }
            sink.write(SourceItem::Symbol(($t).to_be_bytes()[..].into()))?;
            Ok(())
        }
    };
    (num quaternary $name:ident($x:ident: $tx:ty, $y:ident: $ty:ty, $z:ident: $tz:ty, $w:ident: $tw:ty) => $e:expr) => {
        pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
            let expr = unsafe { &mut *expr };
            let sink = unsafe { &mut *sink };
            let items = expr.consume_head_check(stringify!($name).as_bytes())?;
            if items != 3 { return Err(EvalError::from(concat!(stringify!($name), " takes three arguments"))) }
            let $x = expr.consume::<$tx>()?;
            let $y = expr.consume::<$ty>()?;
            let $z = expr.consume::<$tz>()?;
            let $w = expr.consume::<$tw>()?;
            sink.write(SourceItem::Symbol(($e).to_be_bytes()[..].into()))?;
            Ok(())
        }
    };
    (num ternary $name:ident($x:ident: $tx:ty, $y:ident: $ty:ty, $z:ident: $tz:ty) => $e:expr) => {
        pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
            let expr = unsafe { &mut *expr };
            let sink = unsafe { &mut *sink };
            let items = expr.consume_head_check(stringify!($name).as_bytes())?;
            if items != 3 { return Err(EvalError::from(concat!(stringify!($name), " takes three arguments"))) }
            let $x = expr.consume::<$tx>()?;
            let $y = expr.consume::<$ty>()?;
            let $z = expr.consume::<$tz>()?;
            sink.write(SourceItem::Symbol(($e).to_be_bytes()[..].into()))?;
            Ok(())
        }
    };
    (num binary $name:ident($x:ident: $tx:ty, $y:ident: $ty:ty) => $e:expr) => {
        pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
            let expr = unsafe { &mut *expr };
            let sink = unsafe { &mut *sink };
            let items = expr.consume_head_check(stringify!($name).as_bytes())?;
            if items != 2 { return Err(EvalError::from(concat!(stringify!($name), " takes two arguments"))) }
            let $x = expr.consume::<$tx>()?;
            let $y = expr.consume::<$ty>()?;
            sink.write(SourceItem::Symbol(($e).to_be_bytes()[..].into()))?;
            Ok(())
        }
    };
    (num unary $name:ident($x:ident: $tx:ty) => $e:expr) => {
        pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
            let expr = unsafe { &mut *expr };
            let sink = unsafe { &mut *sink };
            let items = expr.consume_head_check(stringify!($name).as_bytes())?;
            if items != 1 { return Err(EvalError::from(concat!(stringify!($name), " takes one argument"))) }
            let $x = expr.consume::<$tx>()?;
            sink.write(SourceItem::Symbol(($e).to_be_bytes()[..].into()))?;
            Ok(())
        }
    };
    (num nulary $name:ident() => $e:expr) => {
        pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
            let expr = unsafe { &mut *expr };
            let sink = unsafe { &mut *sink };
            let items = expr.consume_head_check(stringify!($name).as_bytes())?;
            if items != 0 { return Err(EvalError::from(concat!(stringify!($name), " takes no arguments"))) }
            sink.write(SourceItem::Symbol(($e).to_be_bytes()[..].into()))?;
            Ok(())
        }
    };
    (num from_string $name:ident<$t:ty>) => {
        pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
            let expr = unsafe { &mut *expr };
            let sink = unsafe { &mut *sink };
            let items = expr.consume_head_check(stringify!($name).as_bytes())?;
            if items != 1 { return Err(EvalError::from("only takes one argument")) }
            let SourceItem::Symbol(symbol) = expr.read() else { return Err(EvalError::from("only parses symbols")) };
            let result: $t = str::from_utf8(symbol).map_err(|_| EvalError::from(concat!(stringify!($name), " parsing string not utf8")))?.parse().map_err(|_| EvalError::from(concat!("string not a valid type in ", stringify!($name))))?;
            sink.write(SourceItem::Symbol(result.to_be_bytes()[..].into()))?;
            Ok(())
        }
    };
    (num to_string $name:ident<$t:ty>) => {
        pub extern "C" fn $name(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
            let expr = unsafe { &mut *expr };
            let sink = unsafe { &mut *sink };
            let items = expr.consume_head_check(stringify!($name).as_bytes())?;
            if items != 1 { return Err(EvalError::from("only takes one argument")) }
            let x = expr.consume::<$t>()?;
            let mut buf = [0u8; 64];
            let mut cur = std::io::Cursor::new(&mut buf[..]);
            debug_assert!(format!("{:?}", x).len() <= 64, "too long {}", x);
            write!(&mut cur, "{:?}", x).unwrap();
            let pos = cur.position() as usize;
            sink.write(SourceItem::Symbol(&buf[..pos]))?;
            Ok(())
        }
    };
    (ternary_table($s:expr)($x:ident, $y:ident, $z:ident)) => { match $s {
        0 => 0,
        1 => (!(($x | $y) | $z)),
        2 => ($z & (!($x | $y))),
        3 => (!($x | $y)),
        4 => ($y & (!($x | $z))),
        5 => (!($x | $z)),
        6 => ((!$x) & ($y ^ $z)),
        7 => (!($x | ($y & $z))),
        8 => (($y & $z) & (!$x)),
        9 => (!($x | ($y ^ $z))),
        10 => ($z & (!$x)),
        11 => ((!$x) & ($z | (!$y))),
        12 => ($y & (!$x)),
        13 => ((!$x) & ($y | (!$z))),
        14 => ((!$x) & ($y | $z)),
        15 => (!$x),
        16 => ($x & (!($y | $z))),
        17 => (!($y | $z)),
        18 => ((!$y) & ($x ^ $z)),
        19 => (!($y | ($x & $z))),
        20 => ((!$z) & ($x ^ $y)),
        21 => (!($z | ($x & $y))),
        22 => ((((($x & $y) & $z) ^ $x) ^ $y) ^ $z),
        23 => (!(($x | $y) & ($z | ($x & $y)))),
        24 => (($x ^ $y) & ($x ^ $z)),
        25 => (!(($x & $y) | ($y ^ $z))),
        26 => (($z | ($x & $y)) ^ $x),
        27 => (!(($z & ($x ^ $y)) ^ $y)),
        28 => (($y | ($x & $z)) ^ $x),
        29 => (!(($y & ($x ^ $z)) ^ $z)),
        30 => (($y | $z) ^ $x),
        31 => (!($x & ($y | $z))),
        32 => (($x & $z) & (!$y)),
        33 => (!($y | ($x ^ $z))),
        34 => ($z & (!$y)),
        35 => ((!$y) & ($z | (!$x))),
        36 => (($x ^ $y) & ($y ^ $z)),
        37 => (!(($x & $y) | ($x ^ $z))),
        38 => (($z | ($x & $y)) ^ $y),
        39 => (!(($z & ($x ^ $y)) ^ $x)),
        40 => ($z & ($x ^ $y)),
        41 => (!(($x & $y) | (($x ^ $y) ^ $z))),
        42 => ($z & (!($x & $y))),
        43 => (!((($x ^ $y) & ($y ^ $z)) ^ $x)),
        44 => (($y | $z) & ($x ^ $y)),
        45 => (($y | (!$z)) ^ $x),
        46 => (($y | ($x ^ $z)) ^ $x),
        47 => (!($x & ($y | (!$z)))),
        48 => ($x & (!$y)),
        49 => ((!$y) & ($x | (!$z))),
        50 => ((!$y) & ($x | $z)),
        51 => (!$y),
        52 => (($x | ($y & $z)) ^ $y),
        53 => (!(($x & ($y ^ $z)) ^ $z)),
        54 => (($x | $z) ^ $y),
        55 => (!($y & ($x | $z))),
        56 => (($x | $z) & ($x ^ $y)),
        57 => (($x | (!$z)) ^ $y),
        58 => (($x | ($y ^ $z)) ^ $y),
        59 => (!($y & ($x | (!$z)))),
        60 => ($x ^ $y),
        61 => ((!($x | $z)) | ($x ^ $y)),
        62 => (($z & (!$x)) | ($x ^ $y)),
        63 => (!($x & $y)),
        64 => (($x & $y) & (!$z)),
        65 => (!($z | ($x ^ $y))),
        66 => (($x ^ $z) & ($y ^ $z)),
        67 => (!(($x & $z) | ($x ^ $y))),
        68 => ($y & (!$z)),
        69 => ((!$z) & ($y | (!$x))),
        70 => (($y | ($x & $z)) ^ $z),
        71 => (!(($y & ($x ^ $z)) ^ $x)),
        72 => ($y & ($x ^ $z)),
        73 => (!(($x & $z) | (($x ^ $y) ^ $z))),
        74 => (($y | $z) & ($x ^ $z)),
        75 => (($z | (!$y)) ^ $x),
        76 => ($y & (!($x & $z))),
        77 => (!((($x ^ $z) & ($y ^ $z)) ^ $x)),
        78 => (($z | ($x ^ $y)) ^ $x),
        79 => (!($x & ($z | (!$y)))),
        80 => ($x & (!$z)),
        81 => ((!$z) & ($x | (!$y))),
        82 => (($x | ($y & $z)) ^ $z),
        83 => (!(($x & ($y ^ $z)) ^ $y)),
        84 => ((!$z) & ($x | $y)),
        85 => (!$z),
        86 => (($x | $y) ^ $z),
        87 => (!($z & ($x | $y))),
        88 => (($x | $y) & ($x ^ $z)),
        89 => (($x | (!$y)) ^ $z),
        90 => ($x ^ $z),
        91 => ((!($x | $y)) | ($x ^ $z)),
        92 => (($x | ($y ^ $z)) ^ $z),
        93 => (!($z & ($x | (!$y)))),
        94 => (($y & (!$x)) | ($x ^ $z)),
        95 => (!($x & $z)),
        96 => ($x & ($y ^ $z)),
        97 => (!(($y & $z) | (($x ^ $y) ^ $z))),
        98 => (($x | $z) & ($y ^ $z)),
        99 => (($z | (!$x)) ^ $y),
        100 => (($x | $y) & ($y ^ $z)),
        101 => (($y | (!$x)) ^ $z),
        102 => ($y ^ $z),
        103 => ((!($x | $y)) | ($y ^ $z)),
        104 => ((((($x | $y) | $z) ^ $x) ^ $y) ^ $z),
        105 => (!(($x ^ $y) ^ $z)),
        106 => (($x & $y) ^ $z),
        107 => (!(($x | $y) & (($x ^ $y) ^ $z))),
        108 => (($x & $z) ^ $y),
        109 => (!(($x | $z) & (($x ^ $y) ^ $z))),
        110 => (($y & (!$x)) | ($y ^ $z)),
        111 => ((!$x) | ($y ^ $z)),
        112 => ($x & (!($y & $z))),
        113 => (!((($x ^ $y) | ($x ^ $z)) ^ $x)),
        114 => (($z | ($x ^ $y)) ^ $y),
        115 => (!($y & ($z | (!$x)))),
        116 => (($y | ($x ^ $z)) ^ $z),
        117 => (!($z & ($y | (!$x)))),
        118 => (($x & (!$y)) | ($y ^ $z)),
        119 => (!($y & $z)),
        120 => (($y & $z) ^ $x),
        121 => (!(($y | $z) & (($x ^ $y) ^ $z))),
        122 => (($x & (!$y)) | ($x ^ $z)),
        123 => ((!$y) | ($x ^ $z)),
        124 => (($x & (!$z)) | ($x ^ $y)),
        125 => ((!$z) | ($x ^ $y)),
        126 => (($x ^ $y) | ($x ^ $z)),
        127 => (!(($x & $y) & $z)),
        128 => (($x & $y) & $z),
        129 => (!(($x ^ $y) | ($x ^ $z))),
        130 => ($z & (!($x ^ $y))),
        131 => ((!($x ^ $y)) & ($z | (!$x))),
        132 => ($y & (!($x ^ $z))),
        133 => ((!($x ^ $z)) & ($y | (!$x))),
        134 => (($y | $z) & (($x ^ $y) ^ $z)),
        135 => (!(($y & $z) ^ $x)),
        136 => ($y & $z),
        137 => (((($y | $z) | (!$x)) ^ $y) ^ $z),
        138 => ($z & ($y | (!$x))),
        139 => (!(($y | ($x ^ $z)) ^ $z)),
        140 => ($y & ($z | (!$x))),
        141 => (!(($z | ($x ^ $y)) ^ $y)),
        142 => ((($x ^ $y) | ($x ^ $z)) ^ $x),
        143 => (($y & $z) | (!$x)),
        144 => ($x & (!($y ^ $z))),
        145 => ((!($y ^ $z)) & ($x | (!$y))),
        146 => (($x | $z) & (($x ^ $y) ^ $z)),
        147 => (!(($x & $z) ^ $y)),
        148 => (($x | $y) & (($x ^ $y) ^ $z)),
        149 => (!(($x & $y) ^ $z)),
        150 => (($x ^ $y) ^ $z),
        151 => ((!($x | $y)) | (($x ^ $y) ^ $z)),
        152 => (((($x | $y) | $z) ^ $y) ^ $z),
        153 => (!($y ^ $z)),
        154 => (($x & (!$y)) ^ $z),
        155 => (!(($x | $y) & ($y ^ $z))),
        156 => (($x & (!$z)) ^ $y),
        157 => (!(($x | $z) & ($y ^ $z))),
        158 => (($y & $z) | (($x ^ $y) ^ $z)),
        159 => (!($x & ($y ^ $z))),
        160 => ($x & $z),
        161 => (((($x | $z) | (!$y)) ^ $x) ^ $z),
        162 => ($z & ($x | (!$y))),
        163 => (!(($x | ($y ^ $z)) ^ $z)),
        164 => (((($x | $y) | $z) ^ $x) ^ $z),
        165 => (!($x ^ $z)),
        166 => (($y & (!$x)) ^ $z),
        167 => (!(($x | $y) & ($x ^ $z))),
        168 => ($z & ($x | $y)),
        169 => (!(($x | $y) ^ $z)),
        170 => $z,
        171 => ($z | (!($x | $y))),
        172 => (($x & ($y ^ $z)) ^ $y),
        173 => (!(($x | ($y & $z)) ^ $z)),
        174 => ($z | ($y & (!$x))),
        175 => ($z | (!$x)),
        176 => ($x & ($z | (!$y))),
        177 => (!(($z | ($x ^ $y)) ^ $x)),
        178 => ((($x ^ $z) & ($y ^ $z)) ^ $x),
        179 => (($x & $z) | (!$y)),
        180 => (($y & (!$z)) ^ $x),
        181 => (!(($y | $z) & ($x ^ $z))),
        182 => (($x & $z) | (($x ^ $y) ^ $z)),
        183 => (!($y & ($x ^ $z))),
        184 => (($y & ($x ^ $z)) ^ $x),
        185 => (!(($y | ($x & $z)) ^ $z)),
        186 => ($z | ($x & (!$y))),
        187 => ($z | (!$y)),
        188 => (($x & $z) | ($x ^ $y)),
        189 => (!(($x ^ $z) & ($y ^ $z))),
        190 => ($z | ($x ^ $y)),
        191 => (!(($x & $y) & (!$z))),
        192 => ($x & $y),
        193 => (((($x | $y) | (!$z)) ^ $x) ^ $y),
        194 => (((($x | $y) | $z) ^ $x) ^ $y),
        195 => (!($x ^ $y)),
        196 => ($y & ($x | (!$z))),
        197 => (!(($x | ($y ^ $z)) ^ $y)),
        198 => (($z & (!$x)) ^ $y),
        199 => (!(($x | $z) & ($x ^ $y))),
        200 => ($y & ($x | $z)),
        201 => (!(($x | $z) ^ $y)),
        202 => (($x & ($y ^ $z)) ^ $z),
        203 => (!(($x | ($y & $z)) ^ $y)),
        204 => $y,
        205 => ($y | (!($x | $z))),
        206 => ($y | ($z & (!$x))),
        207 => ($y | (!$x)),
        208 => ($x & ($y | (!$z))),
        209 => (!(($y | ($x ^ $z)) ^ $x)),
        210 => (($z & (!$y)) ^ $x),
        211 => (!(($y | $z) & ($x ^ $y))),
        212 => ((($x ^ $y) & ($y ^ $z)) ^ $x),
        213 => (($x & $y) | (!$z)),
        214 => (($x & $y) | (($x ^ $y) ^ $z)),
        215 => (!($z & ($x ^ $y))),
        216 => (($z & ($x ^ $y)) ^ $x),
        217 => (!(($z | ($x & $y)) ^ $y)),
        218 => (($x & $y) | ($x ^ $z)),
        219 => (!(($x ^ $y) & ($y ^ $z))),
        220 => ($y | ($x & (!$z))),
        221 => ($y | (!$z)),
        222 => ($y | ($x ^ $z)),
        223 => (!(($x & $z) & (!$y))),
        224 => ($x & ($y | $z)),
        225 => (!(($y | $z) ^ $x)),
        226 => (($y & ($x ^ $z)) ^ $z),
        227 => (!(($y | ($x & $z)) ^ $x)),
        228 => (($z & ($x ^ $y)) ^ $y),
        229 => (!(($z | ($x & $y)) ^ $x)),
        230 => (($x & $y) | ($y ^ $z)),
        231 => (!(($x ^ $y) & ($x ^ $z))),
        232 => (($x | $y) & ($z | ($x & $y))),
        233 => (($x & $y) | (((!$z) ^ $x) ^ $y)),
        234 => ($z | ($x & $y)),
        235 => ($z | (!($x ^ $y))),
        236 => ($y | ($x & $z)),
        237 => ($y | (!($x ^ $z))),
        238 => ($y | $z),
        239 => (($y | $z) | (!$x)),
        240 => $x,
        241 => ($x | (!($y | $z))),
        242 => ($x | ($z & (!$y))),
        243 => ($x | (!$y)),
        244 => ($x | ($y & (!$z))),
        245 => ($x | (!$z)),
        246 => ($x | ($y ^ $z)),
        247 => (!(($y & $z) & (!$x))),
        248 => ($x | ($y & $z)),
        249 => ($x | (!($y ^ $z))),
        250 => ($x | $z),
        251 => (($x | $z) | (!$y)),
        252 => ($x | $y),
        253 => (($x | $y) | (!$z)),
        254 => (($x | $y) | $z),
        255 => !0,
    }};
}

op!(num nulary u8_zeros() => 0u8);
op!(num nulary u8_ones() => !0u8);
op!(num unary u8_not(x: u8) => !x);
op!(num unary u8_swap_bytes(x: u8) => x.swap_bytes());
op!(num unary u8_leading_zeros(x: u8) => x.leading_zeros());
op!(num unary u8_leading_ones(x: u8) => x.leading_ones());
op!(num unary u8_count_zeros(x: u8) => x.count_zeros());
op!(num unary u8_count_ones(x: u8) => x.count_ones());
op!(num unary u8_reverse_bits(x: u8) => x.reverse_bits());
op!(num binary u8_nand(x: u8, y: u8) => !(x & y));
op!(num binary u8_andn(x: u8, y: u8) => x & !y);
op!(num binary u8_nor(x: u8, y: u8) => !(x | y));
op!(num binary u8_xor(x: u8, y: u8) => x ^ y);
op!(num binary u8_xnor(x: u8, y: u8) => !(x ^ y));
op!(num binary u8_shl(x: u8, y: u32) =>
    {println!("shl {x:?} {y:?}");
    x.checked_shl(y).ok_or(EvalError::from("shl overflow"))?});
op!(num binary u8_shr(x: u8, y: u32) => x.checked_shr(y).ok_or(EvalError::from("shr overflow"))?);
op!(num quaternary u8_ternarylogic(x: u8, y: u8, z: u8, s: u8) => op!(ternary_table(s)(x, y, z)));
op!(num nary u8_and(!0u8, t: u8, x: u8) => t & x);
op!(num nary u8_or(0u8, t: u8, x: u8) => t | x);
op!(num nary u8_parity(0u8, t: u8, x: u8) => t ^ x);

op!(num nulary u16_zeros() => 0u16);
op!(num nulary u16_ones() => !0u16);
op!(num unary u16_not(x: u16) => !x);
op!(num unary u16_swap_bytes(x: u16) => x.swap_bytes());
op!(num unary u16_leading_zeros(x: u16) => x.leading_zeros());
op!(num unary u16_leading_ones(x: u16) => x.leading_ones());
op!(num unary u16_count_zeros(x: u16) => x.count_zeros());
op!(num unary u16_count_ones(x: u16) => x.count_ones());
op!(num unary u16_reverse_bits(x: u16) => x.reverse_bits());
op!(num binary u16_nand(x: u16, y: u16) => !(x & y));
op!(num binary u16_andn(x: u16, y: u16) => x & !y);
op!(num binary u16_nor(x: u16, y: u16) => !(x | y));
op!(num binary u16_xor(x: u16, y: u16) => x ^ y);
op!(num binary u16_xnor(x: u16, y: u16) => !(x ^ y));
op!(num binary u16_shl(x: u16, y: u32) => x.checked_shl(y).ok_or(EvalError::from("shl overflow"))?);
op!(num binary u16_shr(x: u16, y: u32) => x.checked_shr(y).ok_or(EvalError::from("shr overflow"))?);
op!(num quaternary u16_ternarylogic(x: u16, y: u16, z: u16, s: u8) => op!(ternary_table(s)(x, y, z)));
op!(num nary u16_and(!0u16, t: u16, x: u16) => t & x);
op!(num nary u16_or(0u16, t: u16, x: u16) => t | x);
op!(num nary u16_parity(0u16, t: u16, x: u16) => t ^ x);

op!(num nulary u32_zeros() => 0u32);
op!(num nulary u32_ones() => !0u32);
op!(num unary u32_not(x: u32) => !x);
op!(num unary u32_swap_bytes(x: u32) => x.swap_bytes());
op!(num unary u32_leading_zeros(x: u32) => x.leading_zeros());
op!(num unary u32_leading_ones(x: u32) => x.leading_ones());
op!(num unary u32_count_zeros(x: u32) => x.count_zeros());
op!(num unary u32_count_ones(x: u32) => x.count_ones());
op!(num unary u32_reverse_bits(x: u32) => x.reverse_bits());
op!(num binary u32_nand(x: u32, y: u32) => !(x & y));
op!(num binary u32_andn(x: u32, y: u32) => x & !y);
op!(num binary u32_nor(x: u32, y: u32) => !(x | y));
op!(num binary u32_xor(x: u32, y: u32) => x ^ y);
op!(num binary u32_xnor(x: u32, y: u32) => !(x ^ y));
op!(num binary u32_eq(x: u32, y: u32) => if x == y { 1u8 } else { 0u8 });
op!(num binary u32_shl(x: u32, y: u32) => x.checked_shl(y).ok_or(EvalError::from("shl overflow"))?);
op!(num binary u32_shr(x: u32, y: u32) => x.checked_shr(y).ok_or(EvalError::from("shr overflow"))?);
op!(num quaternary u32_ternarylogic(x: u32, y: u32, z: u32, s: u8) => op!(ternary_table(s)(x, y, z)));
op!(num nary u32_and(!0u32, t: u32, x: u32) => t & x);
op!(num nary u32_or(0u32, t: u32, x: u32) => t | x);
op!(num nary u32_parity(0u32, t: u32, x: u32) => t ^ x);

op!(num nulary u64_zeros() => 0u64);
op!(num nulary u64_ones() => !0u64);
op!(num unary u64_not(x: u64) => !x);
op!(num unary u64_swap_bytes(x: u64) => x.swap_bytes());
op!(num unary u64_leading_zeros(x: u64) => x.leading_zeros());
op!(num unary u64_leading_ones(x: u64) => x.leading_ones());
op!(num unary u64_count_zeros(x: u64) => x.count_zeros());
op!(num unary u64_count_ones(x: u64) => x.count_ones());
op!(num unary u64_reverse_bits(x: u64) => x.reverse_bits());
op!(num binary u64_nand(x: u64, y: u64) => !(x & y));
op!(num binary u64_andn(x: u64, y: u64) => x & !y);
op!(num binary u64_nor(x: u64, y: u64) => !(x | y));
op!(num binary u64_xor(x: u64, y: u64) => x ^ y);
op!(num binary u64_xnor(x: u64, y: u64) => !(x ^ y));
op!(num binary u64_shl(x: u64, y: u32) => x.checked_shl(y).ok_or(EvalError::from("shl overflow"))?);
op!(num binary u64_shr(x: u64, y: u32) => x.checked_shr(y).ok_or(EvalError::from("shr overflow"))?);
op!(num quaternary u64_ternarylogic(x: u64, y: u64, z: u64, s: u8) => op!(ternary_table(s)(x, y, z)));
op!(num nary u64_and(!0u64, t: u64, x: u64) => t & x);
op!(num nary u64_or(0u64, t: u64, x: u64) => t | x);
op!(num nary u64_parity(0u64, t: u64, x: u64) => t ^ x);

op!(num nulary u128_zeros() => 0u128);
op!(num nulary u128_ones() => !0u128);
op!(num unary u128_not(x: u128) => !x);
op!(num unary u128_swap_bytes(x: u128) => x.swap_bytes());
op!(num unary u128_leading_zeros(x: u128) => x.leading_zeros());
op!(num unary u128_leading_ones(x: u128) => x.leading_ones());
op!(num unary u128_count_zeros(x: u128) => x.count_zeros());
op!(num unary u128_count_ones(x: u128) => x.count_ones());
op!(num unary u128_reverse_bits(x: u128) => x.reverse_bits());
op!(num binary u128_nand(x: u128, y: u128) => !(x & y));
op!(num binary u128_andn(x: u128, y: u128) => x & !y);
op!(num binary u128_nor(x: u128, y: u128) => !(x | y));
op!(num binary u128_xor(x: u128, y: u128) => x ^ y);
op!(num binary u128_xnor(x: u128, y: u128) => !(x ^ y));
op!(num binary u128_shl(x: u128, y: u32) => x.checked_shl(y).ok_or(EvalError::from("shl overflow"))?);
op!(num binary u128_shr(x: u128, y: u32) => x.checked_shr(y).ok_or(EvalError::from("shr overflow"))?);
op!(num quaternary u128_ternarylogic(x: u128, y: u128, z: u128, s: u8) => op!(ternary_table(s)(x, y, z)));
op!(num nary u128_and(!0u128, t: u128, x: u128) => t & x);
op!(num nary u128_or(0u128, t: u128, x: u128) => t | x);
op!(num nary u128_parity(0u128, t: u128, x: u128) => t ^ x);

op!(num unary i8_as_i16(x: i8) => x as i16);
op!(num unary i8_as_i32(x: i8) => x as i32);
op!(num unary i8_as_i64(x: i8) => x as i64);
op!(num unary i8_as_i128(x: i8) => x as i128);
op!(num unary i8_as_f32(x: i8) => x as f32);
op!(num unary i8_as_f64(x: i8) => x as f64);
op!(num nulary i8_one() => 1i8);
op!(num unary neg_i8(x: i8) => -x);
op!(num unary abs_i8(x: i8) => x.abs());
op!(num unary signum_i8(x: i8) => x.signum());
op!(num binary sub_i8(x: i8, y: i8) => x - y);
op!(num binary div_i8(x: i8, y: i8) => x.checked_div(y).ok_or(EvalError::from("div 0"))?);
op!(num binary mod_i8(x: i8, y: i8) => x % y);
op!(num binary pow_i8(x: i8, exp: i8) => x.pow(exp as u32));
op!(num ternary clamp_i8(x: i8, y: i8, z: i8) => x.clamp(y, z));
op!(num nary sum_i8(0i8, t: i8, x: i8) => t + x);
op!(num nary product_i8(1i8, t: i8, x: i8) => t * x);
op!(num nary max_i8(i8::MIN, t: i8, x: i8) => t.max(x));
op!(num nary min_i8(i8::MAX, t: i8, x: i8) => t.min(x));
op!(num from_string i8_from_string<i8>);
op!(num to_string i8_to_string<i8>);

op!(num unary i16_as_i8(x: i16) => x as i8);
op!(num unary i16_as_i32(x: i16) => x as i32);
op!(num unary i16_as_i64(x: i16) => x as i64);
op!(num unary i16_as_i128(x: i16) => x as i128);
op!(num unary i16_as_f32(x: i16) => x as f32);
op!(num unary i16_as_f64(x: i16) => x as f64);
op!(num nulary i16_one() => 1i16);
op!(num unary neg_i16(x: i16) => -x);
op!(num unary abs_i16(x: i16) => x.abs());
op!(num unary signum_i16(x: i16) => x.signum());
op!(num binary sub_i16(x: i16, y: i16) => x - y);
op!(num binary div_i16(x: i16, y: i16) => x.checked_div(y).ok_or(EvalError::from("div 0"))?);
op!(num binary mod_i16(x: i16, y: i16) => x % y);
op!(num binary pow_i16(x: i16, exp: i16) => x.pow(exp as u32));
op!(num ternary clamp_i16(x: i16, y: i16, z: i16) => x.clamp(y, z));
op!(num nary sum_i16(0i16, t: i16, x: i16) => t + x);
op!(num nary product_i16(1i16, t: i16, x: i16) => t * x);
op!(num nary max_i16(i16::MIN, t: i16, x: i16) => t.max(x));
op!(num nary min_i16(i16::MAX, t: i16, x: i16) => t.min(x));
op!(num from_string i16_from_string<i16>);
op!(num to_string i16_to_string<i16>);

op!(num unary i32_as_i8(x: i32) => x as i8);
op!(num unary i32_as_i16(x: i32) => x as i16);
op!(num unary i32_as_i64(x: i32) => x as i64);
op!(num unary i32_as_i128(x: i32) => x as i128);
op!(num unary i32_as_f32(x: i32) => x as f32);
op!(num unary i32_as_f64(x: i32) => x as f64);
op!(num nulary i32_one() => 1i32);
op!(num unary neg_i32(x: i32) => -x);
op!(num unary abs_i32(x: i32) => x.abs());
op!(num unary signum_i32(x: i32) => x.signum());
op!(num binary sub_i32(x: i32, y: i32) => x - y);
op!(num binary div_i32(x: i32, y: i32) => x.checked_div(y).ok_or(EvalError::from("div 0"))?);
op!(num binary mod_i32(x: i32, y: i32) => x % y);
op!(num binary pow_i32(x: i32, exp: i32) => x.pow(exp as u32));
op!(num ternary clamp_i32(x: i32, y: i32, z: i32) => x.clamp(y, z));
op!(num nary sum_i32(0i32, t: i32, x: i32) => t + x);
op!(num nary product_i32(1i32, t: i32, x: i32) => t * x);
op!(num nary max_i32(i32::MIN, t: i32, x: i32) => t.max(x));
op!(num nary min_i32(i32::MAX, t: i32, x: i32) => t.min(x));
op!(num from_string i32_from_string<i32>);
op!(num to_string i32_to_string<i32>);

op!(num unary i64_as_i8(x: i64) => x as i8);
op!(num unary i64_as_i16(x: i64) => x as i16);
op!(num unary i64_as_i32(x: i64) => x as i32);
op!(num unary i64_as_i128(x: i64) => x as i128);
op!(num unary i64_as_f32(x: i64) => x as f32);
op!(num unary i64_as_f64(x: i64) => x as f64);
op!(num nulary i64_one() => 1i64);
op!(num unary neg_i64(x: i64) => -x);
op!(num unary abs_i64(x: i64) => x.abs());
op!(num unary signum_i64(x: i64) => x.signum());
op!(num binary sub_i64(x: i64, y: i64) => x - y);
op!(num binary div_i64(x: i64, y: i64) => x.checked_div(y).ok_or(EvalError::from("div 0"))?);
op!(num binary mod_i64(x: i64, y: i64) => x % y);
op!(num binary pow_i64(x: i64, exp: i64) => x.pow(exp as u32));
op!(num ternary clamp_i64(x: i64, y: i64, z: i64) => x.clamp(y, z));
op!(num nary sum_i64(0i64, t: i64, x: i64) => t + x);
op!(num nary product_i64(1i64, t: i64, x: i64) => t * x);
op!(num nary max_i64(i64::MIN, t: i64, x: i64) => t.max(x));
op!(num nary min_i64(i64::MAX, t: i64, x: i64) => t.min(x));
op!(num from_string i64_from_string<i64>);
op!(num to_string i64_to_string<i64>);

op!(num unary i128_as_i8(x: i128) => x as i8);
op!(num unary i128_as_i16(x: i128) => x as i16);
op!(num unary i128_as_i32(x: i128) => x as i32);
op!(num unary i128_as_i64(x: i128) => x as i64);
op!(num unary i128_as_f32(x: i128) => x as f32);
op!(num unary i128_as_f64(x: i128) => x as f64);
op!(num nulary i128_one() => 1i128);
op!(num unary neg_i128(x: i128) => -x);
op!(num unary abs_i128(x: i128) => x.abs());
op!(num unary signum_i128(x: i128) => x.signum());
op!(num binary sub_i128(x: i128, y: i128) => x - y);
op!(num binary div_i128(x: i128, y: i128) => x.checked_div(y).ok_or(EvalError::from("div 0"))?);
op!(num binary mod_i128(x: i128, y: i128) => x % y);
op!(num binary pow_i128(x: i128, exp: i128) => x.pow(exp as u32));
op!(num ternary clamp_i128(x: i128, y: i128, z: i128) => x.clamp(y, z));
op!(num nary sum_i128(0i128, t: i128, x: i128) => t + x);
op!(num nary product_i128(1i128, t: i128, x: i128) => t * x);
op!(num nary max_i128(i128::MIN, t: i128, x: i128) => t.max(x));
op!(num nary min_i128(i128::MAX, t: i128, x: i128) => t.min(x));
op!(num from_string i128_from_string<i128>);
op!(num to_string i128_to_string<i128>);

op!(num unary f64_as_i8(x: f64) => x as i8);
op!(num unary f64_as_i16(x: f64) => x as i16);
op!(num unary f64_as_i32(x: f64) => x as i32);
op!(num unary f64_as_i64(x: f64) => x as i64);
op!(num unary f64_as_i128(x: f64) => x as i128);
op!(num unary f64_as_f32(x: f64) => x as f32);
op!(num nulary inf_f64() => f64::INFINITY);
op!(num nulary neginf_f64() => f64::NEG_INFINITY);
op!(num nulary e_f64() => std::f64::consts::E);
op!(num nulary pi_f64() => std::f64::consts::PI);
op!(num nulary tau_f64() => std::f64::consts::TAU);
// op!(num nulary phi_f64() => std::f64::consts::PHI); // pre https://github.com/rust-lang/rust/pull/151164
op!(num nulary phi_f64() => std::f64::consts::GOLDEN_RATIO);
op!(num unary to_radians_f64(x: f64) => x.to_radians());
op!(num unary to_degrees_f64(x: f64) => x.to_degrees());
op!(num unary sin_f64(x: f64) => x.sin());
op!(num unary cos_f64(x: f64) => x.cos());
op!(num unary tan_f64(x: f64) => x.tan());
op!(num unary asin_f64(x: f64) => x.asin());
op!(num unary acos_f64(x: f64) => x.acos());
op!(num unary atan_f64(x: f64) => x.atan());
op!(num unary sinh_f64(x: f64) => x.sinh());
op!(num unary cosh_f64(x: f64) => x.cosh());
op!(num unary tanh_f64(x: f64) => x.tanh());
op!(num unary asinh_f64(x: f64) => x.asinh());
op!(num unary acosh_f64(x: f64) => x.acosh());
op!(num unary atanh_f64(x: f64) => x.atanh());
op!(num unary neg_f64(x: f64) => -x);
op!(num unary abs_f64(x: f64) => x.abs());
op!(num unary floor_f64(x: f64) => x.floor());
op!(num unary ceil_f64(x: f64) => x.ceil());
op!(num unary round_f64(x: f64) => x.round());
op!(num unary sqrt_f64(x: f64) => x.sqrt());
op!(num unary cbrt_f64(x: f64) => x.cbrt());
op!(num unary exp_f64(x: f64) => x.exp());
op!(num unary exp2_f64(x: f64) => x.exp2());
op!(num unary ln_f64(x: f64) => x.ln());
op!(num unary log2_f64(x: f64) => x.log2());
op!(num unary log10_f64(x: f64) => x.log10());
op!(num unary trunc_f64(x: f64) => x.trunc());
op!(num unary recip_f64(x: f64) => x.recip());
op!(num unary fract_f64(x: f64) => x.fract());
op!(num unary signum_f64(x: f64) => x.signum());
op!(num binary copysign_f64(x: f64, s: f64) => x.copysign(s));
op!(num binary powf_f64(x: f64, exp: f64) => x.powf(exp));
op!(num binary powi_f64(x: f64, exp: i32) => x.powi(exp));
op!(num binary sub_f64(x: f64, y: f64) => x - y);
op!(num binary div_f64(x: f64, y: f64) => x.div(y));
op!(num binary atan2_f64(x: f64, y: f64) => x.atan2(y));
op!(num binary hypot_f64(x: f64, y: f64) => x.hypot(y));
op!(num ternary clamp_f64(x: f64, y: f64, z: f64) => x.clamp(y, z));
op!(num nary sum_f64(0f64, t: f64, x: f64) => t + x);
op!(num nary product_f64(1f64, t: f64, x: f64) => t * x);
op!(num nary max_f64(f64::NEG_INFINITY, t: f64, x: f64) => t.max(x));
op!(num nary min_f64(f64::INFINITY, t: f64, x: f64) => t.min(x));
op!(num from_string f64_from_string<f64>);
op!(num to_string f64_to_string<f64>);

op!(num unary f32_as_i8(x: f32) => x as i8);
op!(num unary f32_as_i16(x: f32) => x as i16);
op!(num unary f32_as_i32(x: f32) => x as i32);
op!(num unary f32_as_i128(x: f32) => x as i128);
op!(num unary f32_as_i64(x: f32) => x as i64);
op!(num unary f32_as_f64(x: f32) => x as f64);
op!(num nulary inf_f32() => f32::INFINITY);
op!(num nulary neginf_f32() => f32::NEG_INFINITY);
op!(num nulary e_f32() => std::f32::consts::E);
op!(num nulary pi_f32() => std::f32::consts::PI);
op!(num nulary tau_f32() => std::f32::consts::TAU);
op!(num nulary phi_f32() => std::f32::consts::GOLDEN_RATIO);
op!(num unary to_radians_f32(x: f32) => x.to_radians());
op!(num unary to_degrees_f32(x: f32) => x.to_degrees());
op!(num unary sin_f32(x: f32) => x.sin());
op!(num unary cos_f32(x: f32) => x.cos());
op!(num unary tan_f32(x: f32) => x.tan());
op!(num unary asin_f32(x: f32) => x.asin());
op!(num unary acos_f32(x: f32) => x.acos());
op!(num unary atan_f32(x: f32) => x.atan());
op!(num unary sinh_f32(x: f32) => x.sinh());
op!(num unary cosh_f32(x: f32) => x.cosh());
op!(num unary tanh_f32(x: f32) => x.tanh());
op!(num unary asinh_f32(x: f32) => x.asinh());
op!(num unary acosh_f32(x: f32) => x.acosh());
op!(num unary atanh_f32(x: f32) => x.atanh());
op!(num unary neg_f32(x: f32) => -x);
op!(num unary abs_f32(x: f32) => x.abs());
op!(num unary floor_f32(x: f32) => x.floor());
op!(num unary ceil_f32(x: f32) => x.ceil());
op!(num unary round_f32(x: f32) => x.round());
op!(num unary sqrt_f32(x: f32) => x.sqrt());
op!(num unary cbrt_f32(x: f32) => x.cbrt());
op!(num unary exp_f32(x: f32) => x.exp());
op!(num unary exp2_f32(x: f32) => x.exp2());
op!(num unary ln_f32(x: f32) => x.ln());
op!(num unary log2_f32(x: f32) => x.log2());
op!(num unary log10_f32(x: f32) => x.log10());
op!(num unary trunc_f32(x: f32) => x.trunc());
op!(num unary recip_f32(x: f32) => x.recip());
op!(num unary fract_f32(x: f32) => x.fract());
op!(num unary signum_f32(x: f32) => x.signum());
op!(num binary copysign_f32(x: f32, s: f32) => x.copysign(s));
op!(num binary powf_f32(x: f32, exp: f32) => x.powf(exp));
op!(num binary powi_f32(x: f32, exp: i32) => x.powi(exp));
op!(num binary sub_f32(x: f32, y: f32) => x - y);
op!(num binary div_f32(x: f32, y: f32) => x.div(y));
op!(num binary atan2_f32(x: f32, y: f32) => x.atan2(y));
op!(num binary hypot_f32(x: f32, y: f32) => x.hypot(y));
op!(num ternary clamp_f32(x: f32, y: f32, z: f32) => x.clamp(y, z));
op!(num nary sum_f32(0f32, t: f32, x: f32) => t + x);
op!(num nary product_f32(1f32, t: f32, x: f32) => t * x);
op!(num nary max_f32(f32::NEG_INFINITY, t: f32, x: f32) => t.max(x));
op!(num nary min_f32(f32::INFINITY, t: f32, x: f32) => t.min(x));
op!(num from_string f32_from_string<f32>);
op!(num to_string f32_to_string<f32>);

pub extern "C" fn encode_hex(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"encode_hex")?;
    if items != 1 { return Err(EvalError::from("only takes one argument")) }
    let SourceItem::Symbol(symbol) = expr.read() else { return Err(EvalError::from("only parses symbols")) };
    let mut buf = [0u8; 64];
    hex::encode_to_slice(symbol, &mut buf[..2*symbol.len()])
        .map_err(|e| { println!("{:?}", e); EvalError::from(concat!("string not a valid type in ", "encode_hex"))})?;
    sink.write(SourceItem::Symbol(&buf[..2*symbol.len()]))?;
    Ok(())
}

pub extern "C" fn decode_hex(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"decode_hex")?;
    if items != 1 { return Err(EvalError::from("only takes one argument")) }
    let SourceItem::Symbol(symbol) = expr.read() else { return Err(EvalError::from("only parses symbols")) };
    let mut buf = [0u8; 64];
    hex::decode_to_slice(symbol, &mut buf[..symbol.len().div_ceil(2)])
        .map_err(|_| EvalError::from(concat!("string not a valid type in ", "decode_hex")))?;
    sink.write(SourceItem::Symbol(&buf[..symbol.len().div_ceil(2)]))?;
    Ok(())
}

pub extern "C" fn decode_base64url(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"decode_base64url")?;
    if items != 1 { return Err(EvalError::from("only takes one argument")) }
    let SourceItem::Symbol(symbol) = expr.read() else { return Err(EvalError::from("only parses symbols")) };
    let mut buf = [0u8; 64];
    let written = base64::engine::general_purpose::URL_SAFE_NO_PAD.decode_slice_unchecked(symbol, &mut buf[..])
        .map_err(|_| EvalError::from(concat!("string not a valid type in ", "decode_base64url")))?;
    sink.write(SourceItem::Symbol(&buf[..written]))?;
    Ok(())
}

pub extern "C" fn encode_base64url(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"encode_base64url")?;
    if items != 1 { return Err(EvalError::from("only takes one argument")) }
    let SourceItem::Symbol(symbol) = expr.read() else { return Err(EvalError::from("only parses symbols")) };
    let mut buf = [0u8; 64];
    let written = base64::engine::general_purpose::URL_SAFE_NO_PAD.encode_slice(symbol, &mut buf[..])
        .map_err(|_| EvalError::from(concat!("string not a valid type in ", "encode_base64url")))?;
    sink.write(SourceItem::Symbol(&buf[..written]))?;
    Ok(())
}

pub extern "C" fn hash_expr(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"hash_expr")?;
    if items != 1 { return Err(EvalError::from("only takes one argument")) }
    let e: mork_expr::Expr = expr.consume()?;
    let h = e.hash();
    let buf = h.to_le_bytes();
    sink.write(SourceItem::Symbol(&buf))?;
    Ok(())
}

pub extern "C" fn reverse_symbol(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"reverse_symbol")?;
    if items != 1 { return Err(EvalError::from("only takes one argument")) }
    let SourceItem::Symbol(symbol) = expr.read() else { return Err(EvalError::from("only reverses symbols")) };
    let mut buf = [0u8; 64];
    buf[..symbol.len()].clone_from_slice(symbol);
    buf[..symbol.len()].reverse();
    sink.write(SourceItem::Symbol(&buf[..symbol.len()]))?;
    Ok(())
}

pub extern "C" fn collapse_symbol(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"collapse_symbol")?;
    if items != 1 { return Err(EvalError::from("only takes one argument (an expression of symbols)")) }
    let si = expr.read();
    if let SourceItem::Symbol(s) = si { println!("si {:?}", s); }
    let SourceItem::Tag(Tag::Arity(a)) = si else { return Err(EvalError::from("argument should be an expression")) };
    let mut buf = [0u8; 64];
    let mut i = 0;
    for _ in 0..a {
        let SourceItem::Symbol(symbol) = expr.read() else { return Err(EvalError::from("can only concat symbols in collapse")) };
        if i + symbol.len() >= 64 { return Err(EvalError::from("new symbol can not be larger than 63 bytes")) }
        buf[i..i+symbol.len()].clone_from_slice(symbol);
        i += symbol.len();
    }
    sink.write(SourceItem::Symbol(&buf[..i]))?;
    Ok(())
}

pub extern "C" fn explode_symbol(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"explode_symbol")?;
    if items != 1 { return Err(EvalError::from("only takes one argument (a symbol)")) }
    let SourceItem::Symbol(symbol) = expr.read() else { return Err(EvalError::from("arguments needs to be a symbol")) };
    sink.write(SourceItem::Tag(Tag::Arity(symbol.len() as _)))?;
    for i in 0..symbol.len() {
        sink.write(SourceItem::Symbol(&symbol[i..i+1]))?;
    }
    Ok(())
}

// pub extern "C" fn nth_expr(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
//     let expr = unsafe { &mut *expr };
//     let sink = unsafe { &mut *sink };
//     let items = expr.consume_head_check(b"nth_expr")?;
//     if items != 1 { return Err(EvalError::from("only takes one argument (an expression)")) }
//     let SourceItem::Tag(Tag::Arity(k)) = expr.read() else { return Err(EvalError::from("arguments needs to be an expression")) };
//     for i in 0..symbol.len() {
//         sink.write(SourceItem::Symbol(&symbol[i..i+1]))?;
//     }
//     Ok(())
// }

// (ifnz <symbol> then <nonzero expr>)
// (ifnz <symbol> then <nonzero expr> else <zero expr>)
// The condition <symbol> may be of any length (<symbol> is always len >= 1), 
//   but all bytes in the <symbol> must be b'\0' in order for the condition to be considered `false`
pub extern "C" fn ifnz(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"ifnz")?;
    if items != 3 && items != 5 { return Err(EvalError::from("shaped either (ifnz <symbol> then <nonzero expr>) or (ifnz <symbol> then <nonzero expr> else <zero expr>)")) }
    let SourceItem::Symbol(symbol) = expr.read() else { return Err(EvalError::from("condition needs to be a symbol")) };
    let is_nz = !symbol.iter().all(|x| *x == 0);
    let SourceItem::Symbol(b"then") = expr.read() else { return Err(EvalError::from("expected then symbol")) };
    let t: mork_expr::Expr = expr.consume()?;
    if is_nz {
        sink.extend_from_slice(unsafe { t.span().as_ref().unwrap() })?;
        Ok(())
    } else {
        if items == 5 {
            let SourceItem::Symbol(b"else") = expr.read() else { return Err(EvalError::from("expected else symbol")) };
            let f: mork_expr::Expr = expr.consume()?;
            sink.extend_from_slice(unsafe { f.span().as_ref().unwrap() })?;
            Ok(())
        } else {
            Err(EvalError::from("ifnz no else branch"))
        }
    }
}

pub extern "C" fn tuple(expr: *mut ExprSource, sink: *mut ExprSink) -> Result<(), EvalError> {
    let expr = unsafe { &mut *expr };
    let sink = unsafe { &mut *sink };
    let items = expr.consume_head_check(b"tuple")?;
    sink.write(SourceItem::Tag(Tag::Arity(items as _)))?;
    for i in 0..items {
        let f: mork_expr::Expr = expr.consume()?;
        sink.extend_from_slice(unsafe { f.span().as_ref().unwrap() })?;
    }
    Ok(())
}

pub fn register(scope: &mut EvalScope) {
    scope.add_func("ifnz", ifnz, FuncType::Pure);
    scope.add_func("tuple", tuple, FuncType::Pure);

    scope.add_func("reverse_symbol", reverse_symbol, FuncType::Pure);
    scope.add_func("collapse_symbol", collapse_symbol, FuncType::Pure);
    scope.add_func("explode_symbol", explode_symbol, FuncType::Pure);

    scope.add_func("hash_expr", hash_expr, FuncType::Pure);

    scope.add_func("encode_hex", encode_hex, FuncType::Pure);
    scope.add_func("decode_hex", decode_hex, FuncType::Pure);
    scope.add_func("encode_base64url", encode_base64url, FuncType::Pure);
    scope.add_func("decode_base64url", decode_base64url, FuncType::Pure);

    // GENERATED from the above
    // op!\(num \w+ (\w+)\W.+
    // scope.add_func("$1", $1, FuncType::Pure);

    scope.add_func("u8_zeros", u8_zeros, FuncType::Pure);
    scope.add_func("u8_ones", u8_ones, FuncType::Pure);
    scope.add_func("u8_not", u8_not, FuncType::Pure);
    scope.add_func("u8_swap_bytes", u8_swap_bytes, FuncType::Pure);
    scope.add_func("u8_leading_zeros", u8_leading_zeros, FuncType::Pure);
    scope.add_func("u8_leading_ones", u8_leading_ones, FuncType::Pure);
    scope.add_func("u8_count_zeros", u8_count_zeros, FuncType::Pure);
    scope.add_func("u8_count_ones", u8_count_ones, FuncType::Pure);
    scope.add_func("u8_reverse_bits", u8_reverse_bits, FuncType::Pure);
    scope.add_func("u8_nand", u8_nand, FuncType::Pure);
    scope.add_func("u8_andn", u8_andn, FuncType::Pure);
    scope.add_func("u8_nor", u8_nor, FuncType::Pure);
    scope.add_func("u8_xor", u8_xor, FuncType::Pure);
    scope.add_func("u8_xnor", u8_xnor, FuncType::Pure);
    scope.add_func("u8_shl", u8_shl, FuncType::Pure);
    scope.add_func("u8_shr", u8_shr, FuncType::Pure);
    scope.add_func("u8_ternarylogic", u8_ternarylogic, FuncType::Pure);
    scope.add_func("u8_and", u8_and, FuncType::Pure);
    scope.add_func("u8_or", u8_or, FuncType::Pure);
    scope.add_func("u8_parity", u8_parity, FuncType::Pure);

    scope.add_func("u16_zeros", u16_zeros, FuncType::Pure);
    scope.add_func("u16_ones", u16_ones, FuncType::Pure);
    scope.add_func("u16_not", u16_not, FuncType::Pure);
    scope.add_func("u16_swap_bytes", u16_swap_bytes, FuncType::Pure);
    scope.add_func("u16_leading_zeros", u16_leading_zeros, FuncType::Pure);
    scope.add_func("u16_leading_ones", u16_leading_ones, FuncType::Pure);
    scope.add_func("u16_count_zeros", u16_count_zeros, FuncType::Pure);
    scope.add_func("u16_count_ones", u16_count_ones, FuncType::Pure);
    scope.add_func("u16_reverse_bits", u16_reverse_bits, FuncType::Pure);
    scope.add_func("u16_nand", u16_nand, FuncType::Pure);
    scope.add_func("u16_andn", u16_andn, FuncType::Pure);
    scope.add_func("u16_nor", u16_nor, FuncType::Pure);
    scope.add_func("u16_xor", u16_xor, FuncType::Pure);
    scope.add_func("u16_xnor", u16_xnor, FuncType::Pure);
    scope.add_func("u16_shl", u16_shl, FuncType::Pure);
    scope.add_func("u16_shr", u16_shr, FuncType::Pure);
    scope.add_func("u16_ternarylogic", u16_ternarylogic, FuncType::Pure);
    scope.add_func("u16_and", u16_and, FuncType::Pure);
    scope.add_func("u16_or", u16_or, FuncType::Pure);
    scope.add_func("u16_parity", u16_parity, FuncType::Pure);

    scope.add_func("u32_zeros", u32_zeros, FuncType::Pure);
    scope.add_func("u32_ones", u32_ones, FuncType::Pure);
    scope.add_func("u32_not", u32_not, FuncType::Pure);
    scope.add_func("u32_swap_bytes", u32_swap_bytes, FuncType::Pure);
    scope.add_func("u32_leading_zeros", u32_leading_zeros, FuncType::Pure);
    scope.add_func("u32_leading_ones", u32_leading_ones, FuncType::Pure);
    scope.add_func("u32_count_zeros", u32_count_zeros, FuncType::Pure);
    scope.add_func("u32_count_ones", u32_count_ones, FuncType::Pure);
    scope.add_func("u32_reverse_bits", u32_reverse_bits, FuncType::Pure);
    scope.add_func("u32_nand", u32_nand, FuncType::Pure);
    scope.add_func("u32_andn", u32_andn, FuncType::Pure);
    scope.add_func("u32_nor", u32_nor, FuncType::Pure);
    scope.add_func("u32_xor", u32_xor, FuncType::Pure);
    scope.add_func("u32_xnor", u32_xnor, FuncType::Pure);
    scope.add_func("u32_eq", u32_eq, FuncType::Pure);
    scope.add_func("u32_shl", u32_shl, FuncType::Pure);
    scope.add_func("u32_shr", u32_shr, FuncType::Pure);
    scope.add_func("u32_ternarylogic", u32_ternarylogic, FuncType::Pure);
    scope.add_func("u32_and", u32_and, FuncType::Pure);
    scope.add_func("u32_or", u32_or, FuncType::Pure);
    scope.add_func("u32_parity", u32_parity, FuncType::Pure);

    scope.add_func("u64_zeros", u64_zeros, FuncType::Pure);
    scope.add_func("u64_ones", u64_ones, FuncType::Pure);
    scope.add_func("u64_not", u64_not, FuncType::Pure);
    scope.add_func("u64_swap_bytes", u64_swap_bytes, FuncType::Pure);
    scope.add_func("u64_leading_zeros", u64_leading_zeros, FuncType::Pure);
    scope.add_func("u64_leading_ones", u64_leading_ones, FuncType::Pure);
    scope.add_func("u64_count_zeros", u64_count_zeros, FuncType::Pure);
    scope.add_func("u64_count_ones", u64_count_ones, FuncType::Pure);
    scope.add_func("u64_reverse_bits", u64_reverse_bits, FuncType::Pure);
    scope.add_func("u64_nand", u64_nand, FuncType::Pure);
    scope.add_func("u64_andn", u64_andn, FuncType::Pure);
    scope.add_func("u64_nor", u64_nor, FuncType::Pure);
    scope.add_func("u64_xor", u64_xor, FuncType::Pure);
    scope.add_func("u64_xnor", u64_xnor, FuncType::Pure);
    scope.add_func("u64_shl", u64_shl, FuncType::Pure);
    scope.add_func("u64_shr", u64_shr, FuncType::Pure);
    scope.add_func("u64_ternarylogic", u64_ternarylogic, FuncType::Pure);
    scope.add_func("u64_and", u64_and, FuncType::Pure);
    scope.add_func("u64_or", u64_or, FuncType::Pure);
    scope.add_func("u64_parity", u64_parity, FuncType::Pure);

    scope.add_func("u128_zeros", u128_zeros, FuncType::Pure);
    scope.add_func("u128_ones", u128_ones, FuncType::Pure);
    scope.add_func("u128_not", u128_not, FuncType::Pure);
    scope.add_func("u128_swap_bytes", u128_swap_bytes, FuncType::Pure);
    scope.add_func("u128_leading_zeros", u128_leading_zeros, FuncType::Pure);
    scope.add_func("u128_leading_ones", u128_leading_ones, FuncType::Pure);
    scope.add_func("u128_count_zeros", u128_count_zeros, FuncType::Pure);
    scope.add_func("u128_count_ones", u128_count_ones, FuncType::Pure);
    scope.add_func("u128_reverse_bits", u128_reverse_bits, FuncType::Pure);
    scope.add_func("u128_nand", u128_nand, FuncType::Pure);
    scope.add_func("u128_andn", u128_andn, FuncType::Pure);
    scope.add_func("u128_nor", u128_nor, FuncType::Pure);
    scope.add_func("u128_xor", u128_xor, FuncType::Pure);
    scope.add_func("u128_xnor", u128_xnor, FuncType::Pure);
    scope.add_func("u128_shl", u128_shl, FuncType::Pure);
    scope.add_func("u128_shr", u128_shr, FuncType::Pure);
    scope.add_func("u128_ternarylogic", u128_ternarylogic, FuncType::Pure);
    scope.add_func("u128_and", u128_and, FuncType::Pure);
    scope.add_func("u128_or", u128_or, FuncType::Pure);
    scope.add_func("u128_parity", u128_parity, FuncType::Pure);

    scope.add_func("i8_as_i16", i8_as_i16, FuncType::Pure);
    scope.add_func("i8_as_i32", i8_as_i32, FuncType::Pure);
    scope.add_func("i8_as_i64", i8_as_i64, FuncType::Pure);
    scope.add_func("i8_as_i128", i8_as_i128, FuncType::Pure);
    scope.add_func("i8_as_f32", i8_as_f32, FuncType::Pure);
    scope.add_func("i8_as_f64", i8_as_f64, FuncType::Pure);
    scope.add_func("i8_one", i8_one, FuncType::Pure);
    scope.add_func("neg_i8", neg_i8, FuncType::Pure);
    scope.add_func("abs_i8", abs_i8, FuncType::Pure);
    scope.add_func("signum_i8", signum_i8, FuncType::Pure);
    scope.add_func("sub_i8", sub_i8, FuncType::Pure);
    scope.add_func("div_i8", div_i8, FuncType::Pure);
    scope.add_func("mod_i8", mod_i8, FuncType::Pure);
    scope.add_func("pow_i8", pow_i8, FuncType::Pure);
    scope.add_func("clamp_i8", clamp_i8, FuncType::Pure);
    scope.add_func("sum_i8", sum_i8, FuncType::Pure);
    scope.add_func("product_i8", product_i8, FuncType::Pure);
    scope.add_func("max_i8", max_i8, FuncType::Pure);
    scope.add_func("min_i8", min_i8, FuncType::Pure);
    scope.add_func("i8_from_string", i8_from_string, FuncType::Pure);
    scope.add_func("i8_to_string", i8_to_string, FuncType::Pure);

    scope.add_func("i16_as_i8", i16_as_i8, FuncType::Pure);
    scope.add_func("i16_as_i32", i16_as_i32, FuncType::Pure);
    scope.add_func("i16_as_i64", i16_as_i64, FuncType::Pure);
    scope.add_func("i16_as_i128", i16_as_i128, FuncType::Pure);
    scope.add_func("i16_as_f32", i16_as_f32, FuncType::Pure);
    scope.add_func("i16_as_f64", i16_as_f64, FuncType::Pure);
    scope.add_func("i16_one", i16_one, FuncType::Pure);
    scope.add_func("neg_i16", neg_i16, FuncType::Pure);
    scope.add_func("abs_i16", abs_i16, FuncType::Pure);
    scope.add_func("signum_i16", signum_i16, FuncType::Pure);
    scope.add_func("sub_i16", sub_i16, FuncType::Pure);
    scope.add_func("div_i16", div_i16, FuncType::Pure);
    scope.add_func("mod_i16", mod_i16, FuncType::Pure);
    scope.add_func("pow_i16", pow_i16, FuncType::Pure);
    scope.add_func("clamp_i16", clamp_i16, FuncType::Pure);
    scope.add_func("sum_i16", sum_i16, FuncType::Pure);
    scope.add_func("product_i16", product_i16, FuncType::Pure);
    scope.add_func("max_i16", max_i16, FuncType::Pure);
    scope.add_func("min_i16", min_i16, FuncType::Pure);
    scope.add_func("i16_from_string", i16_from_string, FuncType::Pure);
    scope.add_func("i16_to_string", i16_to_string, FuncType::Pure);

    scope.add_func("i32_as_i8", i32_as_i8, FuncType::Pure);
    scope.add_func("i32_as_i16", i32_as_i16, FuncType::Pure);
    scope.add_func("i32_as_i64", i32_as_i64, FuncType::Pure);
    scope.add_func("i32_as_i128", i32_as_i128, FuncType::Pure);
    scope.add_func("i32_as_f32", i32_as_f32, FuncType::Pure);
    scope.add_func("i32_as_f64", i32_as_f64, FuncType::Pure);
    scope.add_func("i32_one", i32_one, FuncType::Pure);
    scope.add_func("neg_i32", neg_i32, FuncType::Pure);
    scope.add_func("abs_i32", abs_i32, FuncType::Pure);
    scope.add_func("signum_i32", signum_i32, FuncType::Pure);
    scope.add_func("sub_i32", sub_i32, FuncType::Pure);
    scope.add_func("div_i32", div_i32, FuncType::Pure);
    scope.add_func("mod_i32", mod_i32, FuncType::Pure);
    scope.add_func("pow_i32", pow_i32, FuncType::Pure);
    scope.add_func("clamp_i32", clamp_i32, FuncType::Pure);
    scope.add_func("sum_i32", sum_i32, FuncType::Pure);
    scope.add_func("product_i32", product_i32, FuncType::Pure);
    scope.add_func("max_i32", max_i32, FuncType::Pure);
    scope.add_func("min_i32", min_i32, FuncType::Pure);
    scope.add_func("i32_from_string", i32_from_string, FuncType::Pure);
    scope.add_func("i32_to_string", i32_to_string, FuncType::Pure);

    scope.add_func("i64_as_i8", i64_as_i8, FuncType::Pure);
    scope.add_func("i64_as_i16", i64_as_i16, FuncType::Pure);
    scope.add_func("i64_as_i32", i64_as_i32, FuncType::Pure);
    scope.add_func("i64_as_i128", i64_as_i128, FuncType::Pure);
    scope.add_func("i64_as_f32", i64_as_f32, FuncType::Pure);
    scope.add_func("i64_as_f64", i64_as_f64, FuncType::Pure);
    scope.add_func("i64_one", i64_one, FuncType::Pure);
    scope.add_func("neg_i64", neg_i64, FuncType::Pure);
    scope.add_func("abs_i64", abs_i64, FuncType::Pure);
    scope.add_func("signum_i64", signum_i64, FuncType::Pure);
    scope.add_func("sub_i64", sub_i64, FuncType::Pure);
    scope.add_func("div_i64", div_i64, FuncType::Pure);
    scope.add_func("mod_i64", mod_i64, FuncType::Pure);
    scope.add_func("pow_i64", pow_i64, FuncType::Pure);
    scope.add_func("clamp_i64", clamp_i64, FuncType::Pure);
    scope.add_func("sum_i64", sum_i64, FuncType::Pure);
    scope.add_func("product_i64", product_i64, FuncType::Pure);
    scope.add_func("max_i64", max_i64, FuncType::Pure);
    scope.add_func("min_i64", min_i64, FuncType::Pure);
    scope.add_func("i64_from_string", i64_from_string, FuncType::Pure);
    scope.add_func("i64_to_string", i64_to_string, FuncType::Pure);

    scope.add_func("i128_as_i8", i128_as_i8, FuncType::Pure);
    scope.add_func("i128_as_i16", i128_as_i16, FuncType::Pure);
    scope.add_func("i128_as_i32", i128_as_i32, FuncType::Pure);
    scope.add_func("i128_as_i64", i128_as_i64, FuncType::Pure);
    scope.add_func("i128_as_f32", i128_as_f32, FuncType::Pure);
    scope.add_func("i128_as_f64", i128_as_f64, FuncType::Pure);
    scope.add_func("i128_one", i128_one, FuncType::Pure);
    scope.add_func("neg_i128", neg_i128, FuncType::Pure);
    scope.add_func("abs_i128", abs_i128, FuncType::Pure);
    scope.add_func("signum_i128", signum_i128, FuncType::Pure);
    scope.add_func("sub_i128", sub_i128, FuncType::Pure);
    scope.add_func("div_i128", div_i128, FuncType::Pure);
    scope.add_func("mod_i128", mod_i128, FuncType::Pure);
    scope.add_func("pow_i128", pow_i128, FuncType::Pure);
    scope.add_func("clamp_i128", clamp_i128, FuncType::Pure);
    scope.add_func("sum_i128", sum_i128, FuncType::Pure);
    scope.add_func("product_i128", product_i128, FuncType::Pure);
    scope.add_func("max_i128", max_i128, FuncType::Pure);
    scope.add_func("min_i128", min_i128, FuncType::Pure);
    scope.add_func("i128_from_string", i128_from_string, FuncType::Pure);
    scope.add_func("i128_to_string", i128_to_string, FuncType::Pure);

    scope.add_func("f64_as_i8", f64_as_i8, FuncType::Pure);
    scope.add_func("f64_as_i16", f64_as_i16, FuncType::Pure);
    scope.add_func("f64_as_i32", f64_as_i32, FuncType::Pure);
    scope.add_func("f64_as_i64", f64_as_i64, FuncType::Pure);
    scope.add_func("f64_as_i128", f64_as_i128, FuncType::Pure);
    scope.add_func("f64_as_f32", f64_as_f32, FuncType::Pure);
    scope.add_func("inf_f64", inf_f64, FuncType::Pure);
    scope.add_func("neginf_f64", neginf_f64, FuncType::Pure);
    scope.add_func("e_f64", e_f64, FuncType::Pure);
    scope.add_func("pi_f64", pi_f64, FuncType::Pure);
    scope.add_func("tau_f64", tau_f64, FuncType::Pure);
    scope.add_func("phi_f64", phi_f64, FuncType::Pure);
    scope.add_func("to_radians_f64", to_radians_f64, FuncType::Pure);
    scope.add_func("to_degrees_f64", to_degrees_f64, FuncType::Pure);
    scope.add_func("sin_f64", sin_f64, FuncType::Pure);
    scope.add_func("cos_f64", cos_f64, FuncType::Pure);
    scope.add_func("tan_f64", tan_f64, FuncType::Pure);
    scope.add_func("asin_f64", asin_f64, FuncType::Pure);
    scope.add_func("acos_f64", acos_f64, FuncType::Pure);
    scope.add_func("atan_f64", atan_f64, FuncType::Pure);
    scope.add_func("sinh_f64", sinh_f64, FuncType::Pure);
    scope.add_func("cosh_f64", cosh_f64, FuncType::Pure);
    scope.add_func("tanh_f64", tanh_f64, FuncType::Pure);
    scope.add_func("asinh_f64", asinh_f64, FuncType::Pure);
    scope.add_func("acosh_f64", acosh_f64, FuncType::Pure);
    scope.add_func("atanh_f64", atanh_f64, FuncType::Pure);
    scope.add_func("neg_f64", neg_f64, FuncType::Pure);
    scope.add_func("abs_f64", abs_f64, FuncType::Pure);
    scope.add_func("floor_f64", floor_f64, FuncType::Pure);
    scope.add_func("ceil_f64", ceil_f64, FuncType::Pure);
    scope.add_func("round_f64", round_f64, FuncType::Pure);
    scope.add_func("sqrt_f64", sqrt_f64, FuncType::Pure);
    scope.add_func("cbrt_f64", cbrt_f64, FuncType::Pure);
    scope.add_func("exp_f64", exp_f64, FuncType::Pure);
    scope.add_func("exp2_f64", exp2_f64, FuncType::Pure);
    scope.add_func("ln_f64", ln_f64, FuncType::Pure);
    scope.add_func("log2_f64", log2_f64, FuncType::Pure);
    scope.add_func("log10_f64", log10_f64, FuncType::Pure);
    scope.add_func("trunc_f64", trunc_f64, FuncType::Pure);
    scope.add_func("recip_f64", recip_f64, FuncType::Pure);
    scope.add_func("fract_f64", fract_f64, FuncType::Pure);
    scope.add_func("signum_f64", signum_f64, FuncType::Pure);
    scope.add_func("copysign_f64", copysign_f64, FuncType::Pure);
    scope.add_func("powf_f64", powf_f64, FuncType::Pure);
    scope.add_func("powi_f64", powi_f64, FuncType::Pure);
    scope.add_func("sub_f64", sub_f64, FuncType::Pure);
    scope.add_func("div_f64", div_f64, FuncType::Pure);
    scope.add_func("atan2_f64", atan2_f64, FuncType::Pure);
    scope.add_func("hypot_f64", hypot_f64, FuncType::Pure);
    scope.add_func("clamp_f64", clamp_f64, FuncType::Pure);
    scope.add_func("sum_f64", sum_f64, FuncType::Pure);
    scope.add_func("product_f64", product_f64, FuncType::Pure);
    scope.add_func("max_f64", max_f64, FuncType::Pure);
    scope.add_func("min_f64", min_f64, FuncType::Pure);
    scope.add_func("f64_from_string", f64_from_string, FuncType::Pure);
    scope.add_func("f64_to_string", f64_to_string, FuncType::Pure);

    scope.add_func("f32_as_i8", f32_as_i8, FuncType::Pure);
    scope.add_func("f32_as_i16", f32_as_i16, FuncType::Pure);
    scope.add_func("f32_as_i32", f32_as_i32, FuncType::Pure);
    scope.add_func("f32_as_i128", f32_as_i128, FuncType::Pure);
    scope.add_func("f32_as_i64", f32_as_i64, FuncType::Pure);
    scope.add_func("f32_as_f64", f32_as_f64, FuncType::Pure);
    scope.add_func("inf_f32", inf_f32, FuncType::Pure);
    scope.add_func("neginf_f32", neginf_f32, FuncType::Pure);
    scope.add_func("e_f32", e_f32, FuncType::Pure);
    scope.add_func("pi_f32", pi_f32, FuncType::Pure);
    scope.add_func("tau_f32", tau_f32, FuncType::Pure);
    scope.add_func("phi_f32", phi_f32, FuncType::Pure);
    scope.add_func("to_radians_f32", to_radians_f32, FuncType::Pure);
    scope.add_func("to_degrees_f32", to_degrees_f32, FuncType::Pure);
    scope.add_func("sin_f32", sin_f32, FuncType::Pure);
    scope.add_func("cos_f32", cos_f32, FuncType::Pure);
    scope.add_func("tan_f32", tan_f32, FuncType::Pure);
    scope.add_func("asin_f32", asin_f32, FuncType::Pure);
    scope.add_func("acos_f32", acos_f32, FuncType::Pure);
    scope.add_func("atan_f32", atan_f32, FuncType::Pure);
    scope.add_func("sinh_f32", sinh_f32, FuncType::Pure);
    scope.add_func("cosh_f32", cosh_f32, FuncType::Pure);
    scope.add_func("tanh_f32", tanh_f32, FuncType::Pure);
    scope.add_func("asinh_f32", asinh_f32, FuncType::Pure);
    scope.add_func("acosh_f32", acosh_f32, FuncType::Pure);
    scope.add_func("atanh_f32", atanh_f32, FuncType::Pure);
    scope.add_func("neg_f32", neg_f32, FuncType::Pure);
    scope.add_func("abs_f32", abs_f32, FuncType::Pure);
    scope.add_func("floor_f32", floor_f32, FuncType::Pure);
    scope.add_func("ceil_f32", ceil_f32, FuncType::Pure);
    scope.add_func("round_f32", round_f32, FuncType::Pure);
    scope.add_func("sqrt_f32", sqrt_f32, FuncType::Pure);
    scope.add_func("cbrt_f32", cbrt_f32, FuncType::Pure);
    scope.add_func("exp_f32", exp_f32, FuncType::Pure);
    scope.add_func("exp2_f32", exp2_f32, FuncType::Pure);
    scope.add_func("ln_f32", ln_f32, FuncType::Pure);
    scope.add_func("log2_f32", log2_f32, FuncType::Pure);
    scope.add_func("log10_f32", log10_f32, FuncType::Pure);
    scope.add_func("trunc_f32", trunc_f32, FuncType::Pure);
    scope.add_func("recip_f32", recip_f32, FuncType::Pure);
    scope.add_func("fract_f32", fract_f32, FuncType::Pure);
    scope.add_func("signum_f32", signum_f32, FuncType::Pure);
    scope.add_func("copysign_f32", copysign_f32, FuncType::Pure);
    scope.add_func("powf_f32", powf_f32, FuncType::Pure);
    scope.add_func("powi_f32", powi_f32, FuncType::Pure);
    scope.add_func("sub_f32", sub_f32, FuncType::Pure);
    scope.add_func("div_f32", div_f32, FuncType::Pure);
    scope.add_func("atan2_f32", atan2_f32, FuncType::Pure);
    scope.add_func("hypot_f32", hypot_f32, FuncType::Pure);
    scope.add_func("clamp_f32", clamp_f32, FuncType::Pure);
    scope.add_func("sum_f32", sum_f32, FuncType::Pure);
    scope.add_func("product_f32", product_f32, FuncType::Pure);
    scope.add_func("max_f32", max_f32, FuncType::Pure);
    scope.add_func("min_f32", min_f32, FuncType::Pure);
    scope.add_func("f32_from_string", f32_from_string, FuncType::Pure);
    scope.add_func("f32_to_string", f32_to_string, FuncType::Pure);
}
