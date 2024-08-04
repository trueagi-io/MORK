use std::ptr::slice_from_raw_parts;

#[derive(Copy, Clone, Debug)]
pub struct Breadcrumb {
    parent: u32,
    arity: u8,
    seen: u8,
}

#[derive(Copy, Clone)]
pub enum Tag {
    NewVar,
    VarRef(u8),
    SymbolSize(u8),
    Arity(u8),
}

pub fn item_byte(b: Tag) -> u8 {
    match b {
        Tag::NewVar => { 0b1100_0000 | 0 }
        Tag::SymbolSize(s) => { debug_assert!(s > 0 && s < 64); 0b1100_0000 | s }
        Tag::VarRef(i) => { debug_assert!(i < 64); 0b1000_0000 | i }
        Tag::Arity(a) => { debug_assert!(a < 64); 0b0000_0000 | a }
    }
}

pub fn byte_item(b: u8) -> Tag {
    if b == 0b1100_0000 { return Tag::NewVar; }
    else if (b & 0b1100_0000) == 0b1100_0000 { return Tag::SymbolSize(b & 0b0011_1111) }
    else if (b & 0b1100_0000) == 0b1000_0000 { return Tag::VarRef(b & 0b0011_1111) }
    else if (b & 0b1100_0000) == 0b0000_0000 { return Tag::Arity(b & 0b0011_1111) }
    else { panic!("reserved {}", b) }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Expr {
    pub ptr: *mut u8,
}

impl Expr {
    pub fn span(self) -> *const [u8] {
        let root = self.ptr;
        let mut ez = ExprZipper::new(self);
        loop {
            if !ez.next() {
                let size = ez.loc + match ez.tag() {
                    Tag::NewVar => { 1 }
                    Tag::VarRef(r) => { 1 }
                    Tag::SymbolSize(s) => { 1 + (s as usize) }
                    Tag::Arity(a) => { unreachable!() /* expression can't end in arity */ }
                };
                return slice_from_raw_parts(root, size)
            }
        }
    }
}

#[derive(Clone)]
pub struct ExprZipper {
    pub root: Expr,
    pub loc: usize,
    pub trace: Vec<Breadcrumb>,
}

impl ExprZipper {
    pub fn new(e: Expr) -> Self {
        match unsafe { byte_item(*e.ptr) } {
            Tag::NewVar => { Self { root: e, loc: 0, trace: vec![] } }
            Tag::VarRef(r) => { Self { root: e, loc: 0, trace: vec![] } }
            Tag::SymbolSize(s) => { Self { root: e, loc: 0, trace: vec![] } }
            Tag::Arity(a) => {
                Self {
                    root: e,
                    loc: 0,
                    trace: vec![Breadcrumb { parent: 0, arity: a, seen: 0 }],
                    // trace: vec![],
                }
            }
        }
    }

    pub fn tag(&self) -> Tag { unsafe { byte_item(*self.root.ptr.byte_add(self.loc)) } }
    fn item(&self) -> Result<Tag, &[u8]> {
        let tag = self.tag();
        if let Tag::SymbolSize(n) = tag { return unsafe { Err(&*slice_from_raw_parts(self.root.ptr.byte_add(self.loc + 1), n as usize)) } }
        else { return Ok(tag) }
    }
    pub fn subexpr(&self) -> Expr { unsafe { Expr { ptr: self.root.ptr.byte_add(self.loc) } } }

    pub fn write_arity(&mut self, arity: u8) -> bool {
        unsafe {
            *self.root.ptr.byte_add(self.loc) = item_byte(Tag::Arity(arity));
            true
        }
    }
    pub fn write_move(&mut self, value: &[u8]) -> bool {
        unsafe {
            let l = value.len();
            std::ptr::copy_nonoverlapping(value.as_ptr(), self.root.ptr.byte_add(self.loc), l);
            self.loc += l;
            true
        }
    }
    pub fn write_symbol(&mut self, value: &[u8]) -> bool {
        unsafe {
            let l = value.len();
            debug_assert!(l < 64);
            let w = self.root.ptr.byte_add(self.loc);
            *w = item_byte(Tag::SymbolSize(l as u8));
            std::ptr::copy_nonoverlapping(value.as_ptr(), w.byte_add(1), l);
            true
        }
    }
    pub fn write_new_var(&mut self) -> bool {
        unsafe {
            *self.root.ptr.byte_add(self.loc) = item_byte(Tag::NewVar);
            true
        }
    }
    pub fn write_var_ref(&mut self, index: u8) -> bool {
        unsafe {
            *self.root.ptr.byte_add(self.loc) = item_byte(Tag::VarRef(index));
            true
        }
    }

    pub fn tag_str(&self) -> String {
        match self.tag() {
            Tag::NewVar => { "$".to_string() }
            Tag::VarRef(r) => { format!("_{}", r + 1) }
            Tag::SymbolSize(s) => { format!("({})", s) }
            Tag::Arity(a) => { format!("[{}]", a) }
        }
    }

    pub fn item_str(&self) -> String {
        match self.item() {
            Ok(tag) => {
                match tag {
                    Tag::NewVar => { "$".to_string() }
                    Tag::VarRef(r) => { format!("_{}", r + 1) }
                    Tag::Arity(a) => { format!("[{}]", a) }
                    _ => { unreachable!() }
                }
            }
            Err(s) => {
                match std::str::from_utf8(s) {
                    Ok(string) => { format!("{}", string) }
                    Err(_) => { format!("{:?}", s) }
                }
            }
        }
    }

    pub fn next(&mut self) -> bool {
        // let t = self.tag();
        // let ct = self.tag_str();
        match self.trace.last_mut() {
            None => { false }
            Some(&mut Breadcrumb { parent: p, arity: a, seen: ref mut s }) => {
                // println!("parent {} loc {} tag {}", p, self.loc, ct);
                // println!("{} < {}", s, a);
                if *s < a {
                    *s += 1;

                    self.loc += if let Tag::SymbolSize(n) = self.tag() { n as usize + 1 } else { 1 };

                    if let Tag::Arity(a) = self.tag() {
                        self.trace.push(Breadcrumb { parent: self.loc as u32, arity: a, seen: 0 })
                    }

                    // println!("returned true");
                    true
                } else {
                    self.trace.pop();
                    self.next()
                }
            }
        }
    }

    pub fn parent(&mut self) -> bool {
        let Some(Breadcrumb { parent: p, arity: a, seen: s }) = self.trace.last() else { return false; };
        self.loc = *p as usize;
        self.trace.pop();
        true
    }

    pub fn next_child(&mut self) -> bool {
        loop {
            // println!("#");
            if !self.next() { return false; }
            let l = self.trace.len() - 1;
            let parent = self.trace[l].parent;
            if let Tag::Arity(_) = self.tag() {
                if l > 0 && self.trace[l - 1].parent == 0 {
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
    pub fn traverse(&self, i: usize) -> usize {
        match unsafe { byte_item(*self.root.ptr.byte_add(self.loc + i)) } {
            Tag::NewVar => { print!("$"); 1 }
            Tag::VarRef(r) => { print!("_{}", r + 1); 1 }
            Tag::SymbolSize(s) => {
                let slice = unsafe { &*slice_from_raw_parts(self.root.ptr.byte_add(self.loc + i + 1), s as usize) };
                match std::str::from_utf8(slice) {
                    Ok(string) => { print!("{}", string) }
                    Err(_) => { for b in slice { print!("\\x{:x}", b) } }
                }
                s as usize + 1
            }
            Tag::Arity(a) => {
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
