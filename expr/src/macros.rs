use ::core::convert::TryFrom;
use std::ptr::slice_from_raw_parts;
use crate::{Expr, Tag, byte_item, item_byte};

/// A macro to destructure a mork-bytestring expression into its components.
///
/// The pattern can include:
/// - Symbols, represented as string/byte literals, e.g. `"eq?"` or `b"eq?"`.
/// - Variables, represented as identifiers, e.g. `out_1`, `out_2`.
///   These will be bound to `mork_bytestring::Expr` instances.
/// - Nested expressions, represented as parenthesized patterns, e.g. `("+" out_1 out_2)`.
///
/// Macro arguments:
/// `destruct!(expression, (pattern...), good_expr, err_ident => bad_expr)`
///
/// Example usage:
/// ```
/// // let mut expr = mork_expr::parse!("(eq? (+ 2 2) 4)");
/// let mut expr = mork_expr::parse!("[3] eq? [3] + 2 2 4");
/// let expr = mork_expr::Expr { ptr: expr.as_mut_ptr() };
/// mork_expr::destruct!(
///     expr, ("eq?" ("+" out_1 out_2) out_3),
///     eprintln!("{out_1:?}, {out_2:?}, {out_3:?}"),
///     err => { panic!("failed: {err:?}") }
/// );
/// ```
#[macro_export]
macro_rules! destruct {
    // top-level variables
    ($expr:expr, { $var:ident : $ty:ty }, $good:expr, $err:ident => $bad:expr) => {
        $crate::destruct!(@at($expr, 0), { $var: $ty } , $good, $err => $bad);
    };
    (@at($expr:expr, $offset:expr), { $var:ident : $ty:ty }, $good:expr, $err:ident => $bad:expr) => {
        use $crate::macros::{DeserializableExpr};
        let expr = Expr { ptr: unsafe { $expr.ptr.add($offset) } };
        if !<$ty as DeserializableExpr>::check(expr) {
            let $err: String = format!("expression did not match expected type");
            $bad
        } else {
            let $var: $ty = <$ty as DeserializableExpr>::deserialize_unchecked(expr);
            $good
        }
    };
    ($expr:expr, ( $($pattern:tt)* ), $good:expr, $err:ident => $bad:expr) => {
        $crate::destruct!(@at($expr, 0), ( $($pattern)* ), $good, $err => $bad);
    };
    (@at($expr:expr, $offset:expr), ( $($pattern:tt)* ), $good:expr, $err:ident => $bad:expr) => {
        {
            use ::core::convert::TryFrom;
            use $crate::{Tag, Expr, byte_item, parse};
            use $crate::macros::{DeserializableExpr};
            let rv = 'ret: loop {
                unsafe {
                    let mut offset = $offset;
                    $crate::destruct!(@chomp, 'ret, $expr, offset, ( $($pattern)* ) );
                    let _ = offset;
                    break 'ret Ok($crate::destruct!(@vars, $($pattern)*))
                }
            };
            match rv {
                Ok($crate::destruct!(@vars, $($pattern)*)) => $good,
                Err($err) => $bad,
            }
        }
    };
    // Helper to ignore a token, used for counting length,
    // can be removed when meta-variable expressions are stable.
    // https://github.com/rust-lang/rust/issues/83527
    (@ignore, $x:tt) => {  };
    // Compute the length of a token tree sequence
    (@length, $( $tts:tt )*) => { {
        let mut len = 0;
        // meta-variable expressions are unstable, so we use a workaround
        // $( ${ignore($tts)} len += 1; )*
        $( $crate::destruct!(@ignore, $tts); len += 1; )*
        len
    } };
    // Collect variables from the pattern into a tuple.
    // This works both for destructuring and for binding.
    // Example: `("eq?" ("+" out_1 out_2) out_3)`
    // produces `((out_1, (out_2, ())), (out_3, ()))`
    // These aren't visible to the user, since they are destructed in the `$good` arm.
    (@vars, ( $( $head:tt )* ) $( $rest:tt )*) => {
        (
            $crate::destruct!(@vars, $( $head )*),
            $crate::destruct!(@vars, $( $rest )*),
        )
    };
    (@vars, $pattern:literal $( $rest:tt )*) => {
        $crate::destruct!(@vars, $( $rest )*)
    };
    (@vars, { $var:ident : $ty:ty } $( $rest:tt )*) => {
        ($var, $crate::destruct!(@vars, $( $rest )*))
    };
    (@vars, $var:ident $( $rest:tt )*) => {
        ($var, $crate::destruct!(@vars, $( $rest )*))
    };
    (@vars, ) => {
        ()
    };
    // The main destructuring logic.
    // It matches the pattern against the expression token by token, updating the offset as it goes.
    // 1) If it sees a parenthesized pattern, it expects an arity tag and recurses into the sub-pattern.
    (@chomp, $label:lifetime, $expr:expr, $offset:ident, ( $( $head:tt )* ) $( $rest:tt )*) => {
        let arity = $crate::destruct!(@length, $( $head )*);
        let tag = Tag::Arity(arity);
        let tmp = byte_item(*$expr.ptr.add($offset));
        if tmp != tag {
            break $label Err(format!("{:?} did not match expected tag {:?}", tmp, tag))
        }
        $offset += 1;
        $crate::destruct!(@chomp, $label, $expr, $offset, $( $head )*);
        $crate::destruct!(@chomp, $label, $expr, $offset, $( $rest )*);
    };
    // 2) If it sees a string/byte literal, it expects a symbol tag and the corresponding bytes.
    (@chomp, $label:lifetime, $expr:expr, $offset:ident, $pattern:literal $( $rest:tt )* ) => {
        let pattern: &[u8] = $pattern.as_ref();
        let pattern_len: u8 = if pattern.len() > 63 {
            break $label Err(format!("pattern length {} exceeds 63", pattern.len()));
        } else {
            pattern.len().try_into().unwrap()
        };
        let tag = Tag::SymbolSize(pattern_len);
        let tmp = byte_item(*$expr.ptr.add($offset));
        if tmp != tag {
            break $label Err(format!("{:?} did not match expected tag {:?}", tmp, tag));
        }
        $offset += 1;
        let s = ::core::ptr::slice_from_raw_parts($expr.ptr.add($offset), pattern.len()).as_ref().unwrap();
        if s != pattern {
            break $label Err(format!("{:?} did not match expected symbol bytes '{:?}'", s, pattern));
        }
        $offset += pattern.len();
        $crate::destruct!(@chomp, $label, $expr, $offset, $( $rest )*);
    };
    // 3) If it sees an identifier, it expects a variable (NOT NewVar or VarRef) and binds it.
    (@chomp, $label:lifetime, $expr:expr, $offset:ident, $var:ident $( $rest:tt )* ) => {
        let rv = byte_item(*$expr.ptr.add($offset));
        if matches!(rv, Tag::NewVar | Tag::VarRef(_)) {
            break $label Err(format!("{rv:?} did not match expected variable $$"));
        }
        let $var = Expr { ptr: $expr.ptr.add($offset) };
        let expr_size = $var.span().len();
        $offset += expr_size;
        $crate::destruct!(@chomp, $label, $expr, $offset, $( $rest )*);
    };
    (@chomp, $label:lifetime, $expr:expr, $offset:ident, { $var:ident : $ty:ty } $( $rest:tt )* ) => {
        // let rv = byte_item(*$expr.ptr.add($offset));
        // if matches!(rv, Tag::NewVar | Tag::VarRef(_)) {
        //     break $label Err(format!("{rv:?} did not match expected variable $$"));
        // }
        let expr = Expr { ptr: $expr.ptr.add($offset) };
        let $var = <$ty as DeserializableExpr>::deserialize_unchecked(expr);
        $offset += <$ty as DeserializableExpr>::advanced(expr);
        $crate::destruct!(@chomp, $label, $expr, $offset, $( $rest )*);
    };
    // 4) If it sees nothing, the destructuring is complete.
    (@chomp, $label:lifetime, $expr:expr, $offset:ident, ) => {

    };
}

impl TryFrom<Expr> for i32 {
    type Error = String;
    #[inline(always)]
    fn try_from(value: Expr) -> Result<Self, Self::Error> {
        let tag = unsafe { byte_item(*value.ptr) };
        if tag != Tag::SymbolSize(4) {
            return Err(format!("expected symbol of size 4, got: {tag:?}"));
        }
        Ok(unsafe { std::ptr::read_unaligned(value.ptr.add(1) as *const i32) }.swap_bytes())
    }
}

impl SerializableExpr for i32 {
    fn size(&self) -> usize { core::mem::size_of::<Self>() + 1 }
    fn serialize<W: std::io::Write>(&self, buf: &mut W) -> Result<(), std::io::Error> {
        let size = core::mem::size_of::<Self>();
        buf.write_all(&[item_byte(Tag::SymbolSize(size as u8))])?;
        buf.write_all(&self.swap_bytes().to_le_bytes())
    }
}

impl DeserializableExpr for i32 {
    #[inline(always)]
    fn advanced(e: Expr) -> usize {
        1 + core::mem::size_of::<Self>()
    }
    #[inline(always)]
    fn check(e: Expr) -> bool {
        unsafe { *e.ptr == item_byte(Tag::SymbolSize(4)) }
    }
    #[inline(always)]
    fn deserialize_unchecked(e: Expr) -> Self {
        unsafe { std::ptr::read_unaligned(e.ptr.add(1) as *const i32) }.swap_bytes()
    }
}

impl DeserializableExpr for &str {
    #[inline(always)]
    fn advanced(e: Expr) -> usize {
        unsafe {
            let Tag::SymbolSize(arity) = byte_item(*e.ptr) else { panic!("wrong symbol for str") };
            1usize + (arity as usize)
        }
    }
    #[inline(always)]
    fn check(e: Expr) -> bool {
        unsafe {
            let Tag::SymbolSize(arity) = byte_item(*e.ptr) else { unreachable!() };
            str::from_utf8(slice_from_raw_parts(e.ptr.add(1), arity as _).as_ref().unwrap()).is_ok()
        }
    }
    #[inline(always)]
    fn deserialize_unchecked(e: Expr) -> Self {
        unsafe {
            let Tag::SymbolSize(arity) = byte_item(*e.ptr) else { unreachable!() };
            str::from_utf8_unchecked(slice_from_raw_parts(e.ptr.add(1), arity as _).as_ref().unwrap())
        }
    }
}

pub trait DeserializableExpr {
    fn advanced(e: Expr) -> usize;
    fn check(e: Expr) -> bool;
    fn deserialize_unchecked(e: Expr) -> Self;
}

/// A trait for types that can be serialized into a mork-bytestring expression.
/// This is used by the `construct!` macro to handle different kinds of inputs.
pub trait SerializableExpr {
    fn size(&self) -> usize;
    fn serialize<W: std::io::Write>(&self, buf: &mut W) -> Result<(), std::io::Error>;
}

impl SerializableExpr for crate::Expr {
    fn size(&self) -> usize {
        self.span().len()
    }
    fn serialize<W: std::io::Write>(&self, buf: &mut W) -> Result<(), std::io::Error> {
        let slice = unsafe { std::slice::from_raw_parts(self.ptr, self.size()) };
        buf.write_all(slice)?;
        Ok(())
    }
}

impl SerializableExpr for &[u8] {
    fn size(&self) -> usize {
        self.len() + 1
    }
    fn serialize<W: std::io::Write>(&self, buf: &mut W) -> Result<(), std::io::Error> {
        use crate::{Tag, item_byte};
        let bytes = self;
        buf.write_all(&[item_byte(Tag::SymbolSize(bytes.len() as u8))])?;
        buf.write_all(bytes)?;
        Ok(())
    }
}
impl<const N: usize> SerializableExpr for &[u8; N] {
    fn size(&self) -> usize {
        self.len() + 1
    }
    fn serialize<W: std::io::Write>(&self, buf: &mut W) -> Result<(), std::io::Error> {
        use crate::{Tag, item_byte};
        let bytes = &self[..];
        buf.write_all(&[item_byte(Tag::SymbolSize(bytes.len() as u8))])?;
        buf.write_all(bytes)?;
        Ok(())
    }
}

impl SerializableExpr for &str {
    fn size(&self) -> usize {
        self.as_bytes().len() + 1
    }
    fn serialize<W: std::io::Write>(&self, buf: &mut W) -> Result<(), std::io::Error> {
        use crate::{Tag, item_byte};
        let bytes = self.as_bytes();
        buf.write_all(&[item_byte(Tag::SymbolSize(bytes.len() as u8))])?;
        buf.write_all(bytes)?;
        Ok(())
    }
}

/// A macro to construct a mork-bytestring expression from a pattern.
/// The pattern can include:
/// - Symbols, represented as string/byte literals, e.g. `"eq?"` or `b"eq?"`.
/// - Variables, containing existing `mork_bytestring::Expr`, `&str` or `&[u8]`.
/// - Nested expressions, represented as parenthesized patterns, e.g. `("+" "2" "2")`.
///
/// Returns `Result<Vec<u8>, String>`, where the error string indicates any issues encountered.
///
/// Example usage:
/// ```
/// let buf = mork_expr::construct!( "eq?" ( "+" "2" "2" ) "4" )
///     .expect("construct failed");
/// let expr = mork_expr::Expr { ptr: buf.as_ptr() as *mut u8 };
/// ```
#[macro_export]
macro_rules! construct {
    ($($expr:tt)*) => {
        'out: {
            use $crate::{
                Tag, item_byte,
                macros::{SerializableExpr},
            };
            use ::std::io::Write;
            // precompute the serialized size of the expression
            let size: usize = $crate::construct_impl!(@byte_len, ( $($expr)* ) );
            let mut buf = vec![0u8; size];
            let buf_len = buf.len();
            let mut cursor = std::io::Cursor::new(buf.as_mut_slice());
            $crate::construct_impl!(@write, 'out, cursor, ( $($expr)* ) );
            debug_assert_eq!(cursor.position(), buf_len as u64);
            Ok(buf)
        }
    };
}

#[macro_export]
macro_rules! construct_impl {
    // Compute the byte length of a token tree sequence
    // 1) parenthesized patterns
    (@byte_len, ( $($head:tt)* ) $( $rest:tt )* ) => {
        1 + $crate::construct_impl!(@byte_len, $($head)*) + $crate::construct_impl!(@byte_len, $($rest)*)
    };
    // 2) string/byte literals
    (@byte_len, $literal:literal $( $rest:tt )* ) => {
        SerializableExpr::size(&$literal) + $crate::construct_impl!(@byte_len, $($rest)*)
    };
    // 3) variables
    (@byte_len, $var:ident $( $rest:tt )* ) => {
        SerializableExpr::size(&$var) + $crate::construct_impl!(@byte_len, $($rest)*)
    };
    (@byte_len, ) => { 0 };
    (@ignore, $x:tt) => {  };
    // Compute the length of a token tree sequence
    (@length, $( $tts:tt )*) => { {
        let mut len = 0;
        // meta-variable expressions are unstable, so we use a workaround
        // $( ${ignore($tts)} len += 1; )*
        $( $crate::construct_impl!(@ignore, $tts); len += 1; )*
        len
    } };
    (@write, $label:lifetime, $cursor:ident, ( $($child:tt)* ) $($rest:tt)* ) => {
        let arity = $crate::construct_impl!(@length, $($child)*);
        let arity: u8 = if arity > 63 {
            break $label Err(format!("arity {} exceeds 63", arity));
        } else {
            arity.try_into().unwrap()
        };
        if let Err(e) = $cursor.write_all(&[item_byte(Tag::Arity(arity))]) {
            break $label Err(e.to_string());
        }
        $crate::construct_impl!(@write, $label, $cursor, $($child)*);
        $crate::construct_impl!(@write, $label, $cursor, $($rest)*);
    };
    (@write, $label:lifetime, $cursor:ident, $literal:literal $($rest:tt)* ) => {
        let value = $literal;
        let size = SerializableExpr::size(&$literal);
        let pattern_len: u8 = if size > 63 {
            break $label Err(format!("pattern length {} exceeds 63", size));
        } else {
            size.try_into().unwrap()
        };
        if let Err(e) = SerializableExpr::serialize(&value, &mut $cursor) {
            break $label Err(e.to_string());
        }
        $crate::construct_impl!(@write, $label, $cursor, $($rest)*);
    };
    (@write, $label:lifetime, $cursor:ident, $var:ident $($rest:tt)* ) => {
        let var_size = SerializableExpr::size(&$var);
        if let Err(e) = SerializableExpr::serialize(&$var, &mut $cursor) {
            break $label Err(e.to_string());
        }
        $crate::construct_impl!(@write, $label, $cursor, $($rest)*);
    };
    (@write, $label:lifetime, $cursor:ident, ) => { };
}

#[cfg(test)]
mod tests {
    use crate::{Tag, Expr, parse, construct, destruct};

    #[test]
    fn test_parse_simple() {
        let mut expr = parse!("[3] a 42 69");
        let expr = Expr { ptr: expr.as_mut_ptr() };
        destruct!(
            expr, ("a" out_1 out_2),
            {
                eprintln!("variables out_1={out_1:?} out_2={out_2:?}");
                assert_eq!(format!("{out_1:?}"), "42");
                assert_eq!(format!("{out_2:?}"), "69");
            },
            err => { panic!("failed {err:?}") }
        );
    }

    #[test]
    fn test_parse_typed() {
        let a = 42_i32;
        let buf = construct!( "a" a 69_i32 )
            .expect("construct failed");
        eprintln!("constructed: {buf:?}");
        let expr = Expr { ptr: buf.as_ptr() as *mut u8 };
        destruct!(
            expr, ("a" {out_1:i32} {out_2:i32}),
            {
                eprintln!("variables out_1={out_1:?} out_2={out_2:?}");
                assert_eq!(out_1, 42);
                assert_eq!(out_2, 69);
            },
            err => { panic!("failed {err:?}") }
        );
    }
    #[test]
    fn test_parse_typed_top() {
        use crate::macros::SerializableExpr;
        let mut buf = Vec::new();
        SerializableExpr::serialize(&42_i32, &mut buf)
            .expect("construct failed");

        eprintln!("constructed: {buf:?}");
        let expr = Expr { ptr: buf.as_ptr() as *mut u8 };
        destruct!(
            expr, {out_1:i32},
            assert_eq!(out_1, 42),
            err => panic!("failed {err:?}")
        );
    }
    #[test]
    fn test_parse_typed_top_offset() {
        let buf = construct!( 42_i32 )
            .expect("construct failed");

        eprintln!("constructed: {buf:?}");
        let expr = Expr { ptr: buf.as_ptr() as *mut u8 };
        destruct!(
            @at(expr, 1), {out_1:i32},
            assert_eq!(out_1, 42),
            err => panic!("failed {err:?}")
        );
    }

    #[test]
    fn test_parse_2p2e4() {
        let mut expr = parse!("[3] eq? [3] + 2 2 4");
        let expr = Expr { ptr: expr.as_mut_ptr() };
        destruct!(
            expr, ("eq?" ("+" out_1 out_2) out_3),
            {
                eprintln!("variables out_1={out_1:?} out_2={out_2:?} out_3={out_3:?}");
                assert_eq!(format!("{out_1:?}"), "2");
                assert_eq!(format!("{out_2:?}"), "2");
                assert_eq!(format!("{out_3:?}"), "4");
            },
            err => { panic!("failed {err:?}") }
        );
    }

    #[test]
    fn test_parse_2p2e4_expr() {
        let mut expr = parse!("[3] eq? [3] + 2 2 4");
        let expr = Expr { ptr: expr.as_mut_ptr() };
        destruct!(
            expr, ("eq?" out_1 out_2),
            {
                eprintln!("variables out_1={out_1:?} out_2={out_2:?}");
                assert_eq!(format!("{out_1:?}"), "(+ 2 2)");
                assert_eq!(format!("{out_2:?}"), "4");
            },
            err => { panic!("failed {err:?}") }
        );
    }

    #[test]
    fn test_construct() {
        let buf = construct!( "eq?" ( "+" "2" "2" ) "4" )
            .expect("construct failed");
        eprintln!("constructed: {buf:?}");
        let expr = Expr { ptr: buf.as_ptr() as *mut u8 };
        eprintln!("expr: {expr:?}");
    }

    #[test]
    fn test_construct_nested() {
        let a = construct!( "+" "2" "2" ).expect("construct failed");
        let a = Expr { ptr: a.as_ptr() as *mut u8 };
        let b = "4";
        let buf = construct!( "eq?" a b )
            .expect("construct failed");
        eprintln!("constructed: {buf:?}");
        let expr = Expr { ptr: buf.as_ptr() as *mut u8 };
        eprintln!("expr: {expr:?}");
    }

    #[test]
    fn test_round_trip() {
        let mut buf = construct!( "eq?" ( "+" "2" "2" ) "4" )
            .expect("construct failed");
        eprintln!("constructed: {buf:?}");
        let expr = Expr { ptr: buf.as_mut_ptr() };
        destruct!(
            expr, ("eq?" ("+" out_1 out_2) out_3),
            {
                eprintln!("variables out_1={out_1:?} out_2={out_2:?} out_3={out_3:?}");
                assert_eq!(format!("{out_1:?}"), "2");
                assert_eq!(format!("{out_2:?}"), "2");
                assert_eq!(format!("{out_3:?}"), "4");
            },
            err => { panic!("failed {err:?}") }
        );
        destruct!(
            expr, ("eq?" out_1 out_2),
            {
                eprintln!("variables out_1={out_1:?} out_2={out_2:?}");
                assert_eq!(format!("{out_1:?}"), "(+ 2 2)");
                assert_eq!(format!("{out_2:?}"), "4");
            },
            err => { panic!("failed {err:?}") }
        );
    }
}
