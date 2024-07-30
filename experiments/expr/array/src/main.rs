#[derive(Copy, Clone)]
struct Breadcrumb {
    parent: u32,
    arity: u8,
    seen: u8,
}

#[derive(Copy, Clone)]
pub enum Item {
    NewVar,
    VarRef(u8),
    Symbol(u32),
    Arity(u8),
}

pub struct Expr {
    pub ptr: *mut Item,
}

pub struct ExprZipper {
    pub root: Expr,
    loc: usize,
    trace: Vec<Breadcrumb>,
}

impl ExprZipper {
    pub fn new(e: Expr) -> Self {
        match unsafe { *e.ptr } { // todo, should a zipper be allowed on a single item?
            Item::NewVar => { Self { root: e, loc: 0, trace: vec![] } }
            Item::VarRef(r) => { Self { root: e, loc: 0, trace: vec![] } }
            Item::Symbol(s) => { Self { root: e, loc: 0, trace: vec![] } }
            Item::Arity(a) => {
                Self {
                    root: e,
                    loc: 0,
                    trace: vec![Breadcrumb { parent: 0, arity: a, seen: 0 }],
                }
            }
        }
    }

    fn value(&self) -> Item { unsafe { *self.root.ptr.add(self.loc) } }
    fn subexpr(&self) -> Expr { unsafe { Expr { ptr: self.root.ptr.add(self.loc) } } }

    fn write_arity(&mut self, arity: u8) -> bool {
        unsafe {
            *self.root.ptr.add(self.loc) = Item::Arity(arity);
            true
        }
    }
    fn write_symbol(&mut self, value: u32) -> bool {
        unsafe {
            *self.root.ptr.add(self.loc) = Item::Symbol(value);
            true
        }
    }
    fn write_new_var(&mut self) -> bool {
        unsafe {
            *self.root.ptr.add(self.loc) = Item::NewVar;
            true
        }
    }
    fn write_var_ref(&mut self, index: u8) -> bool {
        unsafe {
            *self.root.ptr.add(self.loc) = Item::VarRef(index);
            true
        }
    }

    fn loc_str(&self) -> String {
        match self.value() {
            Item::NewVar => { "$".to_string() }
            Item::VarRef(r) => { format!("_{}", r + 1) }
            Item::Symbol(s) => { format!("{}", s) }
            Item::Arity(a) => { format!("[{}]", a) }
        }
    }

    fn next(&mut self) -> bool {
        match self.trace.last_mut() {
            None => { false }
            Some(&mut Breadcrumb { parent: p, arity: a, seen: ref mut s }) => {
                if *s < a {
                    self.loc += 1;
                    *s += 1;
                    if let Item::Arity(a) = self.value() {
                        self.trace.push(Breadcrumb { parent: self.loc as u32, arity: a, seen: 0 })
                    }
                    true
                } else {
                    self.trace.pop();
                    self.next()
                }
            }
        }
    }

    fn parent(&mut self) -> bool {
        let Some(Breadcrumb { parent: p, arity: a, seen: s }) = self.trace.last() else { return false; };
        self.loc = *p as usize;
        self.trace.pop();
        true
    }

    fn next_child(&mut self) -> bool {
        loop {
            if !self.next() { return false; }
            let l = self.trace.len() - 1;
            let parent = self.trace[l].parent;
            if let Item::Arity(_) = self.value() {
                if parent == self.loc as u32 && self.trace[l - 1].parent == 0 {
                    return true;
                }
            } else {
                if parent == 0 {
                    return true;
                }
            }
        }
    }

    /// Debug traversal
    fn traverse(&self, i: usize) -> usize {
        match unsafe { *self.root.ptr.add(self.loc + i) } {
            Item::NewVar => { print!("$"); 1 }
            Item::VarRef(r) => { print!("_{}", r + 1); 1 }
            Item::Symbol(s) => { print!("{}", s); 1 }
            Item::Arity(a) => {
                print!("(");
                let mut offset = 1;
                for k in 0..a {
                    offset += self.traverse(i + offset);
                    if k != (a - 1) { print!(" ") }
                }
                print!(")");
                offset
            }
        }
    }
}

fn traverse(ez: &mut ExprZipper) {
    loop {
        let d = ez.trace.len();
        // println!("{:?}", ez.parents);
        match ez.value() {
            Item::NewVar => { println!("{}", " ".repeat(4 * d) + "$") }
            Item::VarRef(r) => { println!("{}", " ".repeat(4 * d) + format!("_{}", r + 1).as_str()) }
            Item::Symbol(s) => { println!("{}", " ".repeat(4 * d) + format!("{}", s).as_str()) }
            Item::Arity(a) => {} // println!("{}", " ".repeat(4*d) + format!("[{}]", a).as_str())
        };

        if !ez.next() { break; }
    }
    // println!("{:?}", ez.parents);
}


fn subexpr() {
    // (100 $ (200 201))
    let mut e = vec![Item::Arity(3), Item::Symbol(100), Item::NewVar, Item::Arity(2), Item::Symbol(200), Item::Symbol(201)];
    let mut ez = ExprZipper::new(Expr { ptr: e.as_mut_ptr() });
    ez.next();
    ez.next();
    ez.next();
    println!("{}", ez.loc_str());
    let mut sez = ExprZipper::new(ez.subexpr());
    traverse(&mut sez);
}

fn children() {
    // (100 (101 $) (200 (201 _1)))
    let mut e = vec![Item::Arity(3), Item::Symbol(100),
                                     Item::Arity(2), Item::Symbol(101),
                                                     Item::NewVar,
                                     Item::Arity(2), Item::Symbol(200),
                                                     Item::Arity(2), Item::Symbol(201),
                                                                     Item::VarRef(0)];
    let mut ecz = ExprZipper::new(Expr { ptr: e.as_mut_ptr() });
    println!("{} {}", ecz.loc_str(), ecz.loc);
    assert!(ecz.next_child());
    println!("{} {}", ecz.loc_str(), ecz.loc);
    assert!(ecz.next_child());
    println!("{} {}", ecz.loc_str(), ecz.loc);
    assert!(ecz.next_child());
    println!("{} {}", ecz.loc_str(), ecz.loc);
    assert!(!ecz.next_child());
}

fn main() {
    assert!(std::mem::size_of::<Item>() == 8 && std::mem::size_of::<Breadcrumb>() == 8);
    // (100 $ (200 201))
    // let mut e = vec![Item::Arity(3), Item::Symbol(100), Item::NewVar, Item::Arity(2), Item::Symbol(200), Item::Symbol(201)];
    // (100 (101 $) (200 (201 _1)))
    let mut e = vec![Item::Arity(3), Item::Symbol(100),
                                     Item::Arity(2), Item::Symbol(101),
                                                     Item::NewVar,
                                     Item::Arity(2), Item::Symbol(200),
                                                     Item::Arity(2), Item::Symbol(201),
                                                                     Item::VarRef(0)];
    let mut ez = ExprZipper::new(Expr { ptr: e.as_mut_ptr() });
    traverse(&mut ez);

    println!("---");
    subexpr();

    println!("---");
    children();
}