use core::ops::Range;
use std::str::CharIndices;
use std::iter::Peekable;
use regex::Regex;
use std::rc::Rc;


use std::any::Any;
use std::fmt::{Display, Debug};
use std::convert::TryFrom;

use crate::immutable_string::ImmutableString;

// Symbol atom

/// A symbol atom structure.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SymbolAtom {
    name: ImmutableString,
}

impl SymbolAtom {
    /// Constructs new symbol from `name`. Not intended to be used directly,
    /// use [sym!] or [Atom::sym] instead.
    #[doc(hidden)]
    pub const fn new(name: ImmutableString) -> Self {
        Self{ name }
    }

    /// Returns the name of the symbol.
    pub fn name(&self) -> &str {
        self.name.as_str()
    }
}

impl Display for SymbolAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

// Expression atom

/// An expression atom structure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpressionAtom {
    children: Vec<Atom>,
}

impl ExpressionAtom {
    /// Constructs new expression from vector of sub-atoms. Not intended to be
    /// used directly, use [Atom::expr] instead.
    #[doc(hidden)]
    pub(crate) fn new(children: Vec<Atom>) -> Self {
        Self{ children }
    }

    /// Returns true if expression doesn't contain sub-expressions.
    pub fn is_plain(&self) -> bool {
        self.children.iter().all(|atom| ! matches!(atom, Atom::Expression(_)))
    }

    /// Returns a reference to a vector of sub-atoms.
    pub fn children(&self) -> &Vec<Atom> {
        &self.children
    }

    /// Returns a mutable reference to a vector of sub-atoms.
    pub fn children_mut(&mut self) -> &mut Vec<Atom> {
        &mut self.children
    }

    /// Converts into a vector of sub-atoms.
    pub fn into_children(self) -> Vec<Atom> {
        self.children
    }
}

impl Display for ExpressionAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")
            .and_then(|_| self.children.iter().take(1).fold(Ok(()),
                                                            |res, atom| res.and_then(|_| write!(f, "{}", atom))))
            .and_then(|_| self.children.iter().skip(1).fold(Ok(()),
                                                            |res, atom| res.and_then(|_| write!(f, " {}", atom))))
            .and_then(|_| write!(f, ")"))
    }
}

// Variable atom

use std::sync::atomic::{AtomicUsize, Ordering};

/// Global variable id counter to provide unique variable id values.
static NEXT_VARIABLE_ID: AtomicUsize = AtomicUsize::new(1);

/// Returns next unique variable id and increments the global counter.
fn next_variable_id() -> usize {
    NEXT_VARIABLE_ID.fetch_add(1, Ordering::Relaxed)
}

/// A variable atom structure
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariableAtom {
    name: String,
    id: usize,
}

impl VariableAtom {
    /// Constructs new variable using `name` provided. Usually [Atom::var]
    /// should be preffered. But sometimes [VariableAtom] instance is required.
    /// For example for using as a key in variable bindings (see [matcher::Bindings]).
    pub fn new<T: Into<String>>(name: T) -> Self {
        Self{ name: name.into(), id: 0 }
    }

    /// Constructs new variable using `name` and 'id' provided. This method is
    /// used to convert C API [matcher::Bindings] to Rust.
    pub fn new_id<T: Into<String>>(name: T, id: usize) -> Self {
        Self{ name: name.into(), id: id }
    }

    // TODO: for now name() is used to expose keys of Bindings via C API as
    // strings (which are variable names). Looks like better approach is using
    // Atom as a key in Bindings structure but it requires implementing
    // Hash trait for Atom.
    /// Returns name of the variable.
    pub fn name(&self) -> String {
        if self.id == 0 {
            format!("{}", self.name)
        } else {
            format!("{}#{}", self.name, self.id)
        }
    }

    /// Returns an unique instance of the variable with the same name.
    ///
    /// # Examples
    ///
    /// ```
    /// use hyperon::VariableAtom;
    ///
    /// let x1 = VariableAtom::new("x");
    /// let x2 = x1.clone().make_unique();
    ///
    /// assert_eq!(x1.name(), "x");
    /// assert_ne!(x1.name(), x2.name());
    /// assert_ne!(x1, x2);
    /// ```
    pub fn make_unique(mut self) -> Self {
        self.id = next_variable_id();
        self
    }
}

impl Display for VariableAtom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.name())
    }
}

/// Returns `atom` with all variables replaced by unique instances.
// pub fn make_variables_unique(mut atom: Atom) -> Atom {
//     let mut mapper = crate::common::CachingMapper::new(VariableAtom::make_unique);
//     atom.iter_mut().filter_type::<&mut VariableAtom>().for_each(|var| *var = mapper.replace(var.clone()));
//     atom
// }

// Grounded atom

// The main idea is to keep grounded atom behaviour implementation inside
// type rather then in type instance. To allow default behaviour overriding
// two wrappers for grounded values are introduced:
// - AutoGroundedAtom<T> for intrinsic Rust types;
// - CustomGroundedAtom<T> for customized grounded types.
//
// Both of them implement GroundedAtom trait which serves for type erasure
// and has all necessary methods to implement traits required by Atom:
// PartialEq, Clone, Debug, Display. AutoGroundedAtom<T> implements
// default behaviour (match via equality, no execution) and doesn't
// expect any specific traits implemented. And CustomGroundedAtom<T> expects
// Grounded trait to be implemented and delegates calls to it.

// Both grounded atom wrappers expect grounded type implements PartialEq,
// Clone, Debug and Any traits and use them to implement eq_gnd(),
// clone_gnd() and as_any_...() methods. This allows reusing standard
// behaviour as much as possible. CustomGroundedAtom<T> also expects Display
// implemented. AutoGroundedAtom<T> implements Display via Debug because not
// all standard Rust types implement Display (HashMap for example).
// as_any_...() methods are used to transparently convert grounded atom to
// original Rust type.

// Grounded trait contains three methods to customize behaviour of the grounded
// values:
// - type_() to return MeTTa type of the atom;
// - execute() to represent functions as atoms;
// - match_() to implement custom matching behaviour.

// match_by_equality() method allows reusing default match_() implementation in
// 3rd party code when it is not required to be customized.

/// Grounded function execution error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExecError {
    /// Unexpected runtime error thrown by code. When [crate::metta::interpreter]
    /// algorithm receives this kind of error it interrupts the executon
    /// and returns error expression atom.
    Runtime(String),
    /// Returned intentionally to let [crate::metta::interpreter] algorithm
    /// know that this expression should be returned "as is" without reducing.
    NoReduce,
}

impl From<String> for ExecError {
    fn from(msg: String) -> Self {
        Self::Runtime(msg)
    }
}

impl From<&str> for ExecError {
    fn from(msg: &str) -> Self {
        Self::Runtime(msg.into())
    }
}

/// A trait to erase an actual type of the grounded atom. Not intended to be
/// implemented by users. Use [Atom::value] or implement [Grounded] and use
/// [Atom::gnd] instead.
pub trait GroundedAtom : Any + Debug + Display {
    fn eq_gnd(&self, other: &dyn GroundedAtom) -> bool;
    fn clone_gnd(&self) -> Box<dyn GroundedAtom>;
    fn as_any_ref(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;

    // TODO: type_() should return Vec<Atom> because of type non-determinism
    // TODO: type_() could return Vec<&Atom> as anyway each atom should be replaced
    // by its alpha equivalent with unique variables

    fn as_grounded(&self) -> &dyn Grounded;
}

impl dyn GroundedAtom {
    pub fn downcast_ref<T: Any>(&self) -> Option<&T> {
        self.as_any_ref().downcast_ref()
    }

    pub fn downcast_mut<T: Any>(&mut self) -> Option<&mut T> {
        self.as_any_mut().downcast_mut()
    }
}

/// Trait allows implementing grounded atom with custom behaviour.
/// [rust_type_atom], [match_by_equality] and [execute_not_executable]
/// functions can be used to implement default behavior if requried.
/// If no custom behavior is needed then simpler way is using [Atom::value]
/// function for automatic grounding.
///
/// # Examples
///
/// ```
/// use hyperon::*;
/// use hyperon::matcher::{Bindings, MatchResultIter, match_atoms};
/// use std::fmt::{Display, Formatter};
/// use std::iter::once;
///
/// #[derive(Debug, PartialEq, Clone)]
/// struct MyGrounded {}
///
/// impl Grounded for MyGrounded {
///     fn type_(&self) -> Atom {
///         rust_type_atom::<MyGrounded>()
///     }
///
///     fn execute(&self, args: &[Atom]) -> Result<Vec<Atom>, ExecError> {
///         execute_not_executable(self)
///     }
///
///     fn match_(&self, other: &Atom) -> MatchResultIter {
///         match_by_equality(self, other)
///     }
/// }
///
/// impl Display for MyGrounded {
///     fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
///         write!(f, "MyGrounded")
///     }
/// }
///
/// let atom = Atom::gnd(MyGrounded{});
/// let other = Atom::gnd(MyGrounded{});
/// let gnd = if let Atom::Grounded(ref gnd) = atom { gnd } else { panic!("Non grounded atom"); };
///
/// println!("{}", gnd.type_());
///
/// assert_eq!(atom.to_string(), "MyGrounded");
/// assert_ne!(atom, Atom::sym("MyGrounded"));
/// assert_eq!(gnd.execute(&mut vec![]), Err(ExecError::NoReduce));
/// assert_eq!(match_atoms(&atom, &other).collect::<Vec<Bindings>>(), vec![Bindings::new()]);
/// assert_eq!(atom, other);
/// ```
///
pub trait Grounded : Display {

}

/// Returns the name of the Rust type wrapped into [Atom::Symbol]. This is a
/// default implementation of `type_()` for the grounded types wrapped
/// automatically.
pub fn rust_type_atom<T>() -> Atom {
    Atom::sym(std::any::type_name::<T>())
}

/// Alias for the list of traits required for the standard Rust types to be
/// automatically wrapped into [GroundedAtom]. It is implemented automatically
/// when type implements `'static + PartialEq + Clone + Debug`. No need
/// to implement its manually.
pub trait AutoGroundedType: 'static + PartialEq + Clone + Debug {}
impl<T> AutoGroundedType for T where T: 'static + PartialEq + Clone + Debug {}

/// Wrapper of the automatically implemented grounded atoms.
#[derive(PartialEq, Clone, Debug)]
struct AutoGroundedAtom<T: AutoGroundedType>(T);

impl<T: AutoGroundedType> Grounded for AutoGroundedAtom<T> {

}

impl Grounded for f64 {}

impl<T: AutoGroundedType> GroundedAtom for AutoGroundedAtom<T> {
    fn eq_gnd(&self, other: &dyn GroundedAtom) -> bool {
        match other.downcast_ref::<T>() {
            Some(other) => self.0 == *other,
            _ => false,
        }
    }

    fn clone_gnd(&self) -> Box<dyn GroundedAtom> {
        Box::new(self.clone())
    }

    fn as_any_ref(&self) -> &dyn Any {
        &self.0
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        &mut self.0
    }

    fn as_grounded(&self) -> &dyn Grounded {
        self
    }
}

impl<T: AutoGroundedType> Display for AutoGroundedAtom<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

/// Alias for the list of traits required for a custom Rust grounded type
/// to be successfully wrapped into [GroundedAtom]. It is implemented automatically
/// when type implements `AutoGroundedType + Display + Grounded`. No need to
/// implement it manually. Implement [Grounded] and `Display` instead.
pub trait CustomGroundedType: AutoGroundedType + Display + Grounded {}
impl<T> CustomGroundedType for T where T: AutoGroundedType + Display + Grounded {}

/// Wrapper of the custom grounded atom implementations.
#[derive(PartialEq, Clone, Debug)]
struct CustomGroundedAtom<T: CustomGroundedType>(T);

impl<T: CustomGroundedType> GroundedAtom for CustomGroundedAtom<T> {
    fn eq_gnd(&self, other: &dyn GroundedAtom) -> bool {
        match other.downcast_ref::<T>() {
            Some(other) => self.0 == *other,
            _ => false,
        }
    }

    fn clone_gnd(&self) -> Box<dyn GroundedAtom> {
        Box::new(CustomGroundedAtom(self.0.clone()))
    }

    fn as_any_ref(&self) -> &dyn Any {
        &self.0
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        &mut self.0
    }

    fn as_grounded(&self) -> &dyn Grounded {
        &self.0
    }
}

impl<T: CustomGroundedType> Display for CustomGroundedAtom<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

// Convertors below are implemented for macroses only. They are not effective
// because require calling Clone. In manually written code one can always
// choose more effective moving constructor.
//
// See the explanation of the trick on the link below:
// https://lukaskalbertodt.github.io/2019/12/05/generalized-autoref-based-specialization.html

/// Allows selecting between custom and automatic wrapping of the grounded
/// value. Only for using in [expr!] macro. Not intended to be used by library users.
#[doc(hidden)]
pub struct Wrap<T>(pub T);

/// Converts Rust value into grounded atom using default behaviour.
/// Only for using in [expr!] macro.  Not intended to be used by library users.
#[doc(hidden)]
pub trait AutoGroundedTypeToAtom { fn to_atom(&self) -> Atom; }
impl<T: AutoGroundedType> AutoGroundedTypeToAtom for Wrap<T> {
    fn to_atom(&self) -> Atom {
        Atom::Grounded(Box::new(AutoGroundedAtom(self.0.clone())))
    }
}

/// Converts Rust value into grounded atom using custom behaviour.
/// Only for using in [expr!] macro.  Not intended to be used by library users.
#[doc(hidden)]
pub trait CustomGroundedTypeToAtom { fn to_atom(&self) -> Atom; }
impl<T: CustomGroundedType> CustomGroundedTypeToAtom for &Wrap<T> {
    fn to_atom(&self) -> Atom {
        Atom::Grounded(Box::new(CustomGroundedAtom(self.0.clone())))
    }
}

impl PartialEq for Box<dyn GroundedAtom> {
    fn eq(&self, other: &Self) -> bool {
        self.eq_gnd(&**other)
    }
}

impl Eq for Box<dyn GroundedAtom> {}

impl Clone for Box<dyn GroundedAtom> {
    fn clone(&self) -> Self {
        self.clone_gnd()
    }
}

// Atom enum

/// Atoms are main components of the atomspace. There are four meta-types of
/// atoms: symbol, expression, variable and grounded.
#[derive(Clone)]
pub enum Atom {
    /// Symbol represents some idea or concept. Two symbols having
    /// the same name are considered equal and representing the same concept.
    /// Name of the symbol can be arbitrary string. Use [Atom::sym] to construct
    /// new symbol.
    Symbol(SymbolAtom),

    /// An expression which may encapsulate other atoms including other
    /// expressions. Use [Atom::expr] to construct new expression.
    Expression(ExpressionAtom),

    /// Variable is used to create patterns. Such pattern can be matched with
    /// other atom to assign some specific binding to the variable. Use
    /// [Atom::var] to construct new variable.
    Variable(VariableAtom),

    /// Grounded atom represents sub-symbolic data in the atomspace. It may
    /// contain any binary object, for example operation, collection or value.
    /// Grounded value type creator can define custom type, execution and
    /// matching logic for the value (see [Grounded]). Use [Atom::value] and
    /// [Atom::gnd] to construct new grounded atom.
    Grounded(Box<dyn GroundedAtom>),
}

impl Atom {
    /// Constructs new symbol atom with given `name`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hyperon::Atom;
    ///
    /// let a = Atom::sym("A");
    /// let aa = Atom::sym("A");
    /// let b = Atom::sym("B");
    ///
    /// assert_eq!(a.to_string(), "A");
    /// assert_eq!(a, aa);
    /// assert_ne!(a, b);
    /// ```
    // TODO: can be rewritten using Into<ImmutableString> to convert &str
    // literasl into ImmutableString::Literal.
    pub fn sym<T: Into<String>>(name: T) -> Self {
        Self::Symbol(SymbolAtom::new(ImmutableString::Allocated(name.into())))
    }

    /// Constructs expression out of array of children.
    ///
    /// # Examples
    ///
    /// ```
    /// use hyperon::Atom;
    ///
    /// let expr = Atom::expr([Atom::sym("a"), Atom::sym("b")]);
    /// let same_expr = Atom::expr([Atom::sym("a"), Atom::sym("b")]);
    /// let other_expr = Atom::expr([Atom::sym("+"), Atom::var("x"),
    ///     Atom::expr([Atom::sym("*"), Atom::value(5), Atom::value(8)])]);
    ///
    /// assert_eq!(expr.to_string(), "(a b)");
    /// assert_eq!(other_expr.to_string(), "(+ $x (* 5 8))");
    /// assert_eq!(expr, same_expr);
    /// assert_ne!(expr, other_expr);
    /// ```
    pub fn expr<T: Into<Vec<Atom>>>(children: T) -> Self {
        Self::Expression(ExpressionAtom::new(children.into()))
    }

    /// Constructs variable out of name.
    ///
    /// # Examples
    ///
    /// ```
    /// use hyperon::Atom;
    ///
    /// let a = Atom::var("a");
    /// let aa = Atom::var("a");
    /// let b = Atom::var("b");
    ///
    /// assert_eq!(a.to_string(), "$a");
    /// assert_eq!(a, aa);
    /// assert_ne!(a, b);
    /// ```
    pub fn var<T: Into<String>>(name: T) -> Self {
        Self::Variable(VariableAtom::new(name))
    }

    /// Constructs grounded atom with customized behaviour.
    /// See [Grounded] for examples.
    pub fn gnd<T: CustomGroundedType>(gnd: T) -> Atom {
        Self::Grounded(Box::new(CustomGroundedAtom(gnd)))
    }

    /// Constructs grounded atom from Rust value automatically.
    ///
    /// # Examples
    ///
    /// ```
    /// use hyperon::Atom;
    ///
    /// let i = Atom::value(1);
    /// let j = Atom::value(1);
    /// let x = Atom::value("b");
    ///
    /// assert_eq!(i.to_string(), "1");
    /// assert_eq!(x.to_string(), "\"b\"");
    /// assert_eq!(i, j);
    /// assert_ne!(i, x);
    /// ```
    pub fn value<T: AutoGroundedType>(value: T) -> Atom {
        Self::Grounded(Box::new(AutoGroundedAtom(value)))
    }

    /// Returns reference to the wrapped Rust value of type `T` if atom is
    /// grounded. `T` should be the exactly the type of the value inside atom.
    ///
    /// # Examples
    ///
    /// ```
    /// use hyperon::Atom;
    ///
    /// let x = Atom::value(1u32);
    ///
    /// assert_eq!(x.to_string(), "1");
    /// assert_eq!(x.as_gnd::<u32>(), Some(&1u32));
    /// assert_eq!(x.as_gnd::<String>(), None);
    /// ```
    pub fn as_gnd<T: 'static>(&self) -> Option<&T> {
        match self {
            Atom::Grounded(gnd) => gnd.downcast_ref::<T>(),
            _ => None,
        }
    }

    /// Returns mutable reference to the wrapped Rust value of type `T`
    /// if atom is grounded. `T` should be the exactly the type of the value
    /// inside atom.
    ///
    /// # Examples
    ///
    /// ```
    /// use hyperon::Atom;
    ///
    /// let mut x = Atom::value(123u32);
    /// assert_eq!(x.to_string(), "123");
    ///
    /// *(x.as_gnd_mut::<u32>().unwrap()) = 321u32;
    /// assert_eq!(x.to_string(), "321");
    /// ```
    pub fn as_gnd_mut<T: 'static>(&mut self) -> Option<&mut T> {
        match self {
            Atom::Grounded(gnd) => gnd.downcast_mut::<T>(),
            _ => None,
        }
    }
}

impl PartialEq for Atom {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Atom::Symbol(sym), Atom::Symbol(other)) => PartialEq::eq(sym, other),
            (Atom::Expression(expr), Atom::Expression(other)) => PartialEq::eq(expr, other),
            (Atom::Variable(var), Atom::Variable(other)) => PartialEq::eq(var, other),
            // TODO: PartialEq cannot be derived for the Box<dyn GroundedAtom>
            // because of strange compiler error which requires Copy trait
            // to be implemented. It prevents using constant atoms as patterns
            // for matching (see COMMA_SYMBOL in grounding.rs for instance).
            (Atom::Grounded(gnd), Atom::Grounded(other)) => PartialEq::eq(gnd, other),
            _ => false,
        }
    }
}

impl TryFrom<Atom> for VariableAtom {
    type Error = &'static str;
    fn try_from(atom: Atom) -> Result<Self, &'static str> {
        match atom {
            Atom::Variable(var) => Ok(var),
            _ => Err("Atom is not a VariableAtom")
        }
    }
}

impl<'a> TryFrom<&'a Atom> for &'a VariableAtom {
    type Error = &'static str;
    fn try_from(atom: &Atom) -> Result<&VariableAtom, &'static str> {
        match atom {
            Atom::Variable(var) => Ok(var),
            _ => Err("Atom is not a VariableAtom")
        }
    }
}

impl<'a> TryFrom<&'a mut Atom> for &'a mut VariableAtom {
    type Error = &'static str;
    fn try_from(atom: &mut Atom) -> Result<&mut VariableAtom, &'static str> {
        match atom {
            Atom::Variable(ref mut var) => Ok(var),
            _ => Err("Atom is not a VariableAtom")
        }
    }
}

impl TryFrom<Atom> for ExpressionAtom {
    type Error = &'static str;
    fn try_from(atom: Atom) -> Result<Self, &'static str> {
        match atom {
            Atom::Expression(expr) => Ok(expr),
            _ => Err("Atom is not an ExpressionAtom")
        }
    }
}

impl<'a> TryFrom<&'a Atom> for &'a ExpressionAtom {
    type Error = &'static str;
    fn try_from(atom: &Atom) -> Result<&ExpressionAtom, &'static str> {
        match atom {
            Atom::Expression(expr) => Ok(&expr),
            _ => Err("Atom is not an ExpressionAtom")
        }
    }
}

impl<const N: usize> TryFrom<Atom> for [Atom; N] {
    type Error = &'static str;
    fn try_from(atom: Atom) -> Result<[Atom; N], &'static str> {
        match atom {
            Atom::Expression(expr) => {
                <[Atom; N]>::try_from(expr.into_children())
                    .map_err(|_| concat!("ExpressionAtom length is not equal to expected"))
            },
            _ => Err("Atom is not an ExpressionAtom")
        }
    }
}

impl<'a> TryFrom<&'a Atom> for &'a [Atom] {
    type Error = &'static str;
    fn try_from(atom: &Atom) -> Result<&[Atom], &'static str> {
        match atom {
            Atom::Expression(expr) => Ok(expr.children().as_slice()),
            _ => Err("Atom is not an ExpressionAtom")
        }
    }
}

impl<'a> TryFrom<&'a mut Atom> for &'a mut [Atom] {
    type Error = &'static str;
    fn try_from(atom: &mut Atom) -> Result<&mut [Atom], &'static str> {
        match atom {
            Atom::Expression(expr) => Ok(expr.children_mut().as_mut_slice()),
            _ => Err("Atom is not an ExpressionAtom")
        }
    }
}

impl TryFrom<Atom> for SymbolAtom {
    type Error = &'static str;
    fn try_from(atom: Atom) -> Result<Self, &'static str> {
        match atom {
            Atom::Symbol(sym) => Ok(sym),
            _ => Err("Atom is not a SymbolAtom")
        }
    }
}

impl<'a> TryFrom<&'a Atom> for &'a SymbolAtom {
    type Error = &'static str;
    fn try_from(atom: &Atom) -> Result<&SymbolAtom, &'static str> {
        match atom {
            Atom::Symbol(sym) => Ok(&sym),
            _ => Err("Atom is not a SymbolAtom")
        }
    }
}

impl<'a> TryFrom<&'a Atom> for &'a dyn GroundedAtom {
    type Error = &'static str;
    fn try_from(atom: &'a Atom) -> Result<Self, &'static str> {
        match atom {
            Atom::Grounded(gnd) => Ok(gnd.as_ref()),
            _ => Err("Atom is not a GroundedAtom")
        }
    }
}

impl Eq for Atom {}

impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Atom::Symbol(sym) => Display::fmt(sym, f),
            Atom::Expression(expr) => Display::fmt(expr, f),
            Atom::Variable(var) => Display::fmt(var, f),
            Atom::Grounded(gnd) => Display::fmt(gnd, f),
        }
    }
}

impl Debug for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

#[derive(Clone, Debug)]
pub struct Tokenizer {
    tokens: Vec<TokenDescr>,
}

#[derive(Clone)]
struct TokenDescr {
    regex: Regex,
    constr: Rc<AtomConstr>,
}

impl std::fmt::Debug for TokenDescr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "TokenDescr{{ regex: {:?}, constr: {:?} }}", self.regex, Rc::as_ptr(&self.constr))
    }
}

type AtomConstr = dyn Fn(&str) -> Result<Atom, String>;

impl Tokenizer {

    pub fn new() -> Self {
        Self{ tokens: Vec::new() }
    }

    pub fn register_token<C: 'static + Fn(&str) -> Atom>(&mut self, regex: Regex, constr: C) {
        self.register_token_with_func_ptr(regex, Rc::new(move |the_str| Ok(constr(the_str))))
    }

    pub fn register_fallible_token<C: 'static + Fn(&str) -> Result<Atom, String>>(&mut self, regex: Regex, constr: C) {
        self.register_token_with_func_ptr(regex, Rc::new(constr))
    }

    pub fn register_token_with_regex_str<C: 'static + Fn(&str) -> Atom>(&mut self, regex: &str, constr: C) {
        let regex = Regex::new(regex).unwrap();
        self.register_token(regex, constr)
    }

    /// Moves all tokenizer entries from `from` into `self`, leaving `from` empty
    ///
    /// NOTE: Tokens are tried in reverse order, so `move_front` actually adds entries that will be tried
    /// **last** in the priority order
    pub fn move_front(&mut self, from: &mut Tokenizer) {
        from.move_back(self);
        self.move_back(from);
    }

    /// Moves all tokenizer entries from `from` into `self`, leaving `from` empty
    ///
    /// NOTE: Tokens are tried in reverse order, so `move_back` actually adds entries that will be tried
    /// **first** in the priority order
    pub fn move_back(&mut self, from: &mut Tokenizer) {
        self.tokens.append(&mut from.tokens);
    }

    pub fn find_token(&self, token: &str) -> Option<&AtomConstr> {
        self.tokens.iter().rfind(|descr| {
            match descr.regex.find_at(token, 0) {
                Some(m) => m.start() == 0 && m.end() == token.len(),
                None => false,
            }
        }).map(|descr| &*(descr.constr))
    }

    /// Registers the regex-function pair, for a function that's already wrapped in an RC pointer
    pub(crate) fn register_token_with_func_ptr(&mut self, regex: Regex, constr: Rc<AtomConstr>) {
        self.tokens.push(TokenDescr{ regex, constr: constr })
    }

    #[allow(unused)]
    /// Returns the constructor function associated with an exact regex string, or None if the Tokenizer
    /// does not contain the specified regex
    pub(crate) fn find_exact(&self, regex_str: &str) -> Option<Rc<AtomConstr>> {
        self.tokens.iter().rfind(|descr| {
            descr.regex.as_str() == regex_str
        }).map(|descr| descr.constr.clone())
    }

}

/// The meaning of a parsed syntactic element, generated from a substring in the input text
#[derive(Clone, Copy, Debug)]
pub enum SyntaxNodeType {
    /// Comment line.  All text between a non-escaped ';' and a newline
    Comment,
    /// Variable.  A symbol immediately preceded by a '$' sigil
    VariableToken,
    /// String Literal.  All text between non-escaped '"' (double quote) characters
    StringToken,
    /// Word Token.  Any other whitespace-delimited token that isn't a [Variable](SyntaxNodeType::VariableToken),
    ///   or [StringToken](SyntaxNodeType::StringToken)
    WordToken,
    /// Open Parenthesis.  A non-escaped '(' character indicating the beginning of an expression
    OpenParen,
    /// Close Parenthesis.  A non-escaped ')' character indicating the end of an expression
    CloseParen,
    /// Whitespace. One or more whitespace chars
    Whitespace,
    /// Text that remains unparsed after a parse error has occurred
    LeftoverText,
    /// A Group of [SyntaxNode]s between an [OpenParen](SyntaxNodeType::OpenParen) and a matching
    ///   [CloseParen](SyntaxNodeType::CloseParen)
    ExpressionGroup,
    /// Syntax Nodes that cannot be combined into a coherent atom due to a parse error, even if some
    /// of the individual nodes could represent valid atoms
    ErrorGroup,
}

impl SyntaxNodeType {
    /// Returns `true` is the SyntaxNodeType is a leaf (incapable of hosting sub-nodes).  Returns `false`
    ///   for "group" node tyes.
    pub fn is_leaf(&self) -> bool {
        match self {
            Self::ExpressionGroup |
            Self::ErrorGroup => false,
            _ => true
        }
    }
}

#[derive(Clone, Debug)]
pub struct SyntaxNode {
    pub node_type: SyntaxNodeType,
    pub src_range: Range<usize>,
    pub sub_nodes: Vec<SyntaxNode>,
    pub parsed_text: Option<String>,
    pub message: Option<String>,
    pub is_complete: bool,
}

impl SyntaxNode {
    fn new(node_type: SyntaxNodeType, src_range: Range<usize>, sub_nodes: Vec<SyntaxNode>) -> SyntaxNode {
        Self {
            node_type,
            src_range,
            parsed_text: None,
            sub_nodes,
            message: None,
            is_complete: true
        }
    }

    fn new_token_node(node_type: SyntaxNodeType, src_range: Range<usize>, parsed_text: String) -> SyntaxNode {
        let mut node = SyntaxNode::new(node_type, src_range, vec![]);
        node.parsed_text = Some(parsed_text);
        node
    }

    fn incomplete_with_message(node_type: SyntaxNodeType, src_range: Range<usize>, sub_nodes: Vec<SyntaxNode>, message: String) -> SyntaxNode {
        let mut node = SyntaxNode::new(node_type, src_range, sub_nodes);
        node.message = Some(message);
        node.is_complete = false;
        node
    }

    /// Creates a new error group.  Gets the error message associated with the last node
    fn new_error_group(src_range: Range<usize>, sub_nodes: Vec<SyntaxNode>) -> SyntaxNode {
        let message = sub_nodes[sub_nodes.len()-1].message.clone();
        let mut node = SyntaxNode::new(SyntaxNodeType::ErrorGroup, src_range, sub_nodes);
        node.message = message;
        node.is_complete = false;
        node
    }

    /// Transforms a root SyntaxNode into an [Atom]
    pub fn as_atom(&self, tokenizer: &Tokenizer) -> Result<Option<Atom>, String> {

        //If we have an incomplete node, it's an error
        if !self.is_complete {
            return Err(self.message.clone().unwrap())
        }

        match self.node_type {
            SyntaxNodeType::Comment |
            SyntaxNodeType::Whitespace => Ok(None),
            SyntaxNodeType::OpenParen |
            SyntaxNodeType::CloseParen => Ok(None),
            SyntaxNodeType::VariableToken => {
                let token_text = self.parsed_text.as_ref().unwrap();
                let new_var_atom = Atom::var(token_text);
                Ok(Some(new_var_atom))
            },
            SyntaxNodeType::StringToken |
            SyntaxNodeType::WordToken => {
                let token_text = self.parsed_text.as_ref().unwrap();
                let constr = tokenizer.find_token(token_text);
                if let Some(constr) = constr {
                    let new_atom = constr(token_text)
                        .map_err(|e| format!("byte range = ({:?}) | {e}", self.src_range))?;
                    Ok(Some(new_atom))
                } else {
                    let new_atom = Atom::sym(token_text);
                    Ok(Some(new_atom))
                }
            },
            SyntaxNodeType::ExpressionGroup => {
                let mut err_encountered = Ok(());
                let expr_children: Vec<Atom> = self.sub_nodes.iter().filter_map(|node| {
                    match node.as_atom(tokenizer) {
                        Err(err) => {
                            err_encountered = Err(err);
                            None
                        },
                        Ok(atom) => atom
                    }
                }).collect();
                match err_encountered {
                    Ok(_) => {
                        let new_expr_atom = Atom::expr(expr_children);
                        Ok(Some(new_expr_atom))
                    },
                    Err(err) => Err(err)
                }
            },
            SyntaxNodeType::LeftoverText |
            SyntaxNodeType::ErrorGroup => {unreachable!()}
        }
    }

    /// Visits all the nodes in a parsed syntax tree in a depth-first order
    pub fn visit_depth_first<C>(&self, mut callback: C)
        where C: FnMut(&SyntaxNode)
    {
        self.visit_depth_first_internal(&mut callback);
    }

    fn visit_depth_first_internal<C>(&self, callback: &mut C)
        where C: FnMut(&SyntaxNode)
    {
        for sub_node in self.sub_nodes.iter() {
            sub_node.visit_depth_first_internal(callback);
        }
        callback(self);
    }
}

/// Implemented on a type that yields atoms to be interpreted as MeTTa code.  Typically
/// by parsing source text
pub trait Parser {
    fn next_atom(&mut self, tokenizer: &Tokenizer) -> Result<Option<Atom>, String>;
}

impl Parser for SExprParser<'_> {
    fn next_atom(&mut self, tokenizer: &Tokenizer) -> Result<Option<Atom>, String> {
        self.parse(tokenizer)
    }
}

impl Parser for &mut (dyn Parser + '_) {
    fn next_atom(&mut self, tokenizer: &Tokenizer) -> Result<Option<Atom>, String> {
        (**self).next_atom(tokenizer)
    }
}

/// Provides a parser for MeTTa code written in S-Expression Syntax
///
/// NOTE: The SExprParser type is short-lived, and can be created cheaply to evaluate a specific block
/// of MeTTa source code.
#[derive(Clone)]
pub struct SExprParser<'a> {
    text: &'a str,
    it: Peekable<CharIndices<'a>>,
}

impl<'a> SExprParser<'a> {
    pub fn new(text: &'a str) -> Self {
        Self{ text, it: text.char_indices().peekable() }
    }

    pub fn parse(&mut self, tokenizer: &Tokenizer) -> Result<Option<Atom>, String> {
        loop {
            match self.parse_to_syntax_tree() {
                Some(node) => {
                    if let Some(atom) = node.as_atom(tokenizer)? {
                        return Ok(Some(atom))
                    }
                },
                None => {
                    return Ok(None);
                },
            }
        }
    }

    pub fn parse_to_syntax_tree(&mut self) -> Option<SyntaxNode> {
        if let Some((idx, c)) = self.it.peek().cloned() {
            match c {
                ';' => {
                    let comment_node = self.parse_comment().unwrap();
                    return Some(comment_node);
                },
                _ if c.is_whitespace() => {
                    let whispace_node = SyntaxNode::new(SyntaxNodeType::Whitespace, idx..idx+1, vec![]);
                    self.it.next();
                    return Some(whispace_node);
                },
                '$' => {
                    let var_node = self.parse_variable();
                    return Some(var_node);
                },
                '(' => {
                    let expr_node = self.parse_expr();
                    return Some(expr_node);
                },
                ')' => {
                    let close_paren_node = SyntaxNode::new(SyntaxNodeType::CloseParen, idx..idx+1, vec![]);
                    self.it.next();
                    let leftover_text_node = self.parse_leftovers("Unexpected right bracket".to_string());
                    let error_group_node = SyntaxNode::new_error_group(idx..self.cur_idx(), vec![close_paren_node, leftover_text_node]);
                    return Some(error_group_node);
                },
                _ => {
                    let token_node = self.parse_token();
                    return token_node;
                },
            }
        }
        None
    }

    ///WARNING: may be (often is) == to text.len(), and thus can't be used as an index to read a char
    fn cur_idx(&mut self) -> usize {
        if let Some((idx, _)) = self.it.peek() {
            *idx
        } else {
            self.text.len()
        }
    }

    /// Parse to the next `\n` newline
    fn parse_comment(&mut self) -> Option<SyntaxNode> {
        if let Some((start_idx, _c)) = self.it.peek().cloned() {
            while let Some((_idx, c)) = self.it.peek() {
                match c {
                    '\n' => break,
                    _ => { self.it.next(); }
                }
            }
            let range = start_idx..self.cur_idx();
            Some(SyntaxNode::new(SyntaxNodeType::Comment, range, vec![]))
        } else {
            None
        }
    }

    fn parse_leftovers(&mut self, message: String) -> SyntaxNode {
        let start_idx = self.cur_idx();
        while let Some(_) = self.it.next() {}
        let range = start_idx..self.cur_idx();
        SyntaxNode::incomplete_with_message(SyntaxNodeType::LeftoverText, range, vec![], message)
    }

    fn parse_expr(&mut self) -> SyntaxNode {
        let start_idx = self.cur_idx();
        let mut child_nodes: Vec<SyntaxNode> = Vec::new();

        let open_paren_node = SyntaxNode::new(SyntaxNodeType::OpenParen, start_idx..start_idx+1, vec![]);
        child_nodes.push(open_paren_node);
        self.it.next();

        while let Some((idx, c)) = self.it.peek().cloned() {
            match c {
                ';' => {
                    let comment_node = self.parse_comment().unwrap();
                    child_nodes.push(comment_node);
                },
                _ if c.is_whitespace() => {
                    let whitespace_node = SyntaxNode::new(SyntaxNodeType::Whitespace, idx..idx+1, vec![]);
                    child_nodes.push(whitespace_node);
                    self.it.next();
                },
                ')' => {
                    let close_paren_node = SyntaxNode::new(SyntaxNodeType::CloseParen, idx..idx+1, vec![]);
                    child_nodes.push(close_paren_node);
                    self.it.next();

                    let expr_node = SyntaxNode::new(SyntaxNodeType::ExpressionGroup, start_idx..self.cur_idx(), child_nodes);
                    return expr_node;
                },
                _ => {
                    if let Some(parsed_node) = self.parse_to_syntax_tree() {
                        let is_err = !parsed_node.is_complete;
                        child_nodes.push(parsed_node);

                        //If we hit an error parsing a child, then bubble it up
                        if is_err {
                            let error_group_node = SyntaxNode::new_error_group(start_idx..self.cur_idx(), child_nodes);
                            return error_group_node;
                        }
                    } else {
                        let leftover_node = SyntaxNode::incomplete_with_message(SyntaxNodeType::ErrorGroup, start_idx..self.cur_idx(), child_nodes, "Unexpected end of expression member".to_string());
                        return leftover_node;
                    }
                },
            }
        }
        let leftover_node = SyntaxNode::incomplete_with_message(SyntaxNodeType::ErrorGroup, start_idx..self.cur_idx(), child_nodes, "Unexpected end of expression".to_string());
        leftover_node
    }

    fn parse_token(&mut self) -> Option<SyntaxNode> {
        match self.it.peek().cloned() {
            Some((_idx, '"')) => {
                let string_node = self.parse_string();
                Some(string_node)
            },
            Some((_idx, _)) => {
                let word_node = self.parse_word();
                Some(word_node)
            },
            None => None
        }
    }

    fn parse_string(&mut self) -> SyntaxNode {
        let mut token = String::new();
        let start_idx = self.cur_idx();

        if let Some((_idx, '"')) = self.it.next() {
            token.push('"');
        } else {
            let leftover_text_node = SyntaxNode::incomplete_with_message(SyntaxNodeType::LeftoverText, start_idx..self.cur_idx(), vec![], "Double quote expected".to_string());
            return leftover_text_node;
        }
        while let Some((char_idx, c)) = self.it.next() {
            if c == '"' {
                token.push('"');
                let string_node = SyntaxNode::new_token_node(SyntaxNodeType::StringToken, start_idx..self.cur_idx(), token);
                return string_node;
            }
            if c == '\\' {
                let escape_err = |cur_idx| { SyntaxNode::incomplete_with_message(SyntaxNodeType::StringToken, char_idx..cur_idx, vec![], "Invalid escape sequence".to_string()) };

                match self.it.next() {
                    Some((_idx, c)) => {
                        let val = match c {
                            '\'' | '\"' | '\\' => c, //single quote, double quote, & backslash
                            'n' => '\n', // newline
                            'r' => '\r', // carriage return
                            't' => '\t', // tab
                            'x' => { // hex sequence
                                match self.parse_2_digit_radix_value(16) {
                                    Some(code_val) => code_val.into(),
                                    None => {return escape_err(self.cur_idx()); }
                                }
                            },
                            _ => {
                                return escape_err(self.cur_idx());
                            }
                        };
                        token.push(val);
                    },
                    None => {
                        let leftover_text_node = SyntaxNode::incomplete_with_message(SyntaxNodeType::StringToken, start_idx..self.cur_idx(), vec![], "Escaping sequence is not finished".to_string());
                        return leftover_text_node;
                    },
                }
            } else {
                token.push(c);
            }
        }
        let unclosed_string_node = SyntaxNode::incomplete_with_message(SyntaxNodeType::StringToken, start_idx..self.cur_idx(), vec![], "Unclosed String Literal".to_string());
        unclosed_string_node
    }

    /// Parses a 2-digit value from the parser at the current location
    fn parse_2_digit_radix_value(&mut self, radix: u32) -> Option<u8> {
        self.it.next()
            .and_then(|(_, digit1)| digit1.is_digit(radix).then(|| digit1))
            .and_then(|digit1| TryInto::<u8>::try_into(digit1).ok())
            .and_then(|byte1| self.it.next().map(|(_, digit2)| (byte1, digit2)))
            .and_then(|(byte1, digit2)| digit2.is_digit(radix).then(|| (byte1, digit2)))
            .and_then(|(byte1, digit2)| TryInto::<u8>::try_into(digit2).ok().map(|byte2| (byte1, byte2)))
            .and_then(|(byte1, byte2)| {
                let digits_buf = &[byte1, byte2];
                u8::from_str_radix(core::str::from_utf8(digits_buf).unwrap(), radix).ok()
            }).and_then(|code_val| (code_val <= 0x7F).then(|| code_val))
    }

    fn parse_word(&mut self) -> SyntaxNode {
        let mut token = String::new();
        let start_idx = self.cur_idx();

        while let Some((_idx, c)) = self.it.peek() {
            if c.is_whitespace() || *c == '(' || *c == ')' {
                break;
            }
            token.push(*c);
            self.it.next();
        }

        let word_node = SyntaxNode::new_token_node(SyntaxNodeType::WordToken, start_idx..self.cur_idx(), token);
        word_node
    }

    fn parse_variable(&mut self) -> SyntaxNode {
        let (start_idx, _c) = self.it.peek().cloned().unwrap();
        let mut tmp_it = self.it.clone();
        tmp_it.next();

        let mut token = String::new();
        while let Some((_idx, c)) = tmp_it.peek() {
            if c.is_whitespace() || *c == '(' || *c == ')' {
                break;
            }
            if *c == '#' {
                let leftover_node = self.parse_leftovers("'#' char is reserved for internal usage".to_string());
                return leftover_node;
            }
            token.push(*c);
            tmp_it.next();
        }
        self.it = tmp_it;
        let var_token_node = SyntaxNode::new_token_node(SyntaxNodeType::VariableToken, start_idx..self.cur_idx(), token);
        var_token_node
    }

}

/// An version of [SExprParser] that owns its input text buffer so it has a `'static` lifetime
#[derive(Clone)]
pub struct OwnedSExprParser {
    text: String,
    last_pos: usize,
}

impl OwnedSExprParser {
    pub fn new(text: String) -> Self {
        Self{text, last_pos: 0}
    }
}

impl Parser for OwnedSExprParser {
    fn next_atom(&mut self, tokenizer: &Tokenizer) -> Result<Option<Atom>, String> {
        if self.last_pos >= self.text.len() {
            return Ok(None);
        }
        let slice = &self.text[self.last_pos..self.text.len()];
        let mut parser = SExprParser::new(slice);
        let result = parser.parse(tokenizer);
        self.last_pos = self.last_pos + parser.cur_idx();
        result
    }
}

impl Parser for &[Atom] {
    fn next_atom(&mut self, _tokenizer: &Tokenizer) -> Result<Option<Atom>, String> {
        if let Some((atom, rest)) = self.split_first() {
            *self = rest;
            Ok(Some(atom.clone()))
        } else {
            Ok(None)
        }
    }
}

