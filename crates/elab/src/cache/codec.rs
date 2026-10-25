//! The check cache's byte encoding (docs/proposals/check-cache.md §5.3):
//! variable-length integers, strings, and core terms.
//!
//! Terms are written as a table of nodes, each after the nodes it points
//! to, so a node's children are always earlier entries: writing walks a
//! term with a work list and reading is one loop over the table, so neither
//! recurses, however deeply a term nests. A sub-term shared through an `Rc`
//! is written once and read back shared.

use std::rc::Rc;

use num_bigint::BigUint;
use stitchwort_core::chars::Chars;
use stitchwort_core::collections::HashMap;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::{DataId, DefId, Icit, Name, QuotForm, Sort, Term};
use stitchwort_syntax::Span;

/// Why an entry can't be read: it is corrupt, or doesn't fit this session.
/// Either way it is a miss.
#[derive(Debug)]
pub struct Bad(pub String);

pub type Read<T> = Result<T, Bad>;

pub fn bad<T>(why: impl Into<String>) -> Read<T> {
    Err(Bad(why.into()))
}

/// Bytes being written.
#[derive(Default)]
pub struct Writer {
    pub bytes: Vec<u8>,
}

impl Writer {
    pub fn u8(&mut self, b: u8) {
        self.bytes.push(b);
    }

    pub fn bool(&mut self, b: bool) {
        self.u8(u8::from(b));
    }

    /// LEB128.
    pub fn uint(&mut self, mut n: u64) {
        loop {
            let low = (n & 0x7f) as u8;
            n >>= 7;
            if n == 0 {
                self.u8(low);
                return;
            }
            self.u8(low | 0x80);
        }
    }

    pub fn usize(&mut self, n: usize) {
        self.uint(n as u64);
    }

    pub fn raw(&mut self, bytes: &[u8]) {
        self.bytes.extend_from_slice(bytes);
    }

    /// A length, then the bytes.
    pub fn blob(&mut self, bytes: &[u8]) {
        self.usize(bytes.len());
        self.raw(bytes);
    }

    pub fn str(&mut self, s: &str) {
        self.blob(s.as_bytes());
    }
}

/// Bytes being read.
pub struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Reader { bytes, at: 0 }
    }

    pub fn done(&self) -> bool {
        self.at == self.bytes.len()
    }

    pub fn u8(&mut self) -> Read<u8> {
        let Some(&b) = self.bytes.get(self.at) else {
            return bad("the entry ends early");
        };
        self.at += 1;
        Ok(b)
    }

    pub fn bool(&mut self) -> Read<bool> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => bad("a flag that isn't 0 or 1"),
        }
    }

    pub fn uint(&mut self) -> Read<u64> {
        let mut n: u64 = 0;
        let mut shift = 0;
        loop {
            let b = self.u8()?;
            if shift >= 64 || (shift == 63 && b > 1) {
                return bad("a number too large");
            }
            n |= u64::from(b & 0x7f) << shift;
            if b & 0x80 == 0 {
                return Ok(n);
            }
            shift += 7;
        }
    }

    pub fn usize(&mut self) -> Read<usize> {
        usize::try_from(self.uint()?).or_else(|_| bad("a number too large"))
    }

    pub fn u32(&mut self) -> Read<u32> {
        u32::try_from(self.uint()?).or_else(|_| bad("a number too large"))
    }

    pub fn raw(&mut self, n: usize) -> Read<&'a [u8]> {
        let end = self.at.checked_add(n).filter(|e| *e <= self.bytes.len());
        let Some(end) = end else {
            return bad("the entry ends early");
        };
        let out = &self.bytes[self.at..end];
        self.at = end;
        Ok(out)
    }

    pub fn array<const N: usize>(&mut self) -> Read<[u8; N]> {
        let mut out = [0; N];
        out.copy_from_slice(self.raw(N)?);
        Ok(out)
    }

    pub fn blob(&mut self) -> Read<&'a [u8]> {
        let n = self.usize()?;
        self.raw(n)
    }

    pub fn string(&mut self) -> Read<String> {
        String::from_utf8(self.blob()?.to_vec()).or_else(|_| bad("text that isn't UTF-8"))
    }

    /// A count of items each at least `min` bytes long: refused if the rest
    /// of the entry is too short to hold them, so a corrupt count can't ask
    /// for a huge allocation.
    pub fn count(&mut self, min: usize) -> Read<usize> {
        let n = self.usize()?;
        if n.saturating_mul(min.max(1)) > self.bytes.len() - self.at {
            return bad("a count larger than the entry");
        }
        Ok(n)
    }
}

/// How the entry refers to declarations and files: written by the caller,
/// which knows which declarations are the entry's own.
pub trait Refs {
    fn def(&mut self, w: &mut Writer, id: DefId);
    fn data(&mut self, w: &mut Writer, id: DataId);
    fn span(&mut self, w: &mut Writer, span: Span);
}

/// How to read them back.
pub trait ReadRefs {
    fn def(&self, r: &mut Reader) -> Read<DefId>;
    fn data(&self, r: &mut Reader) -> Read<DataId>;
    fn span(&self, r: &mut Reader) -> Read<Span>;
}

// Node tags.
const VAR: u8 = 0;
const DEF: u8 = 1;
const DATA: u8 = 2;
const CTOR: u8 = 3;
const NAT: u8 = 4;
const CHARS: u8 = 5;
const SORT: u8 = 6;
const PI: u8 = 7;
const LAM: u8 = 8;
const APP: u8 = 9;
const ANN: u8 = 10;
const LET: u8 = 11;
const CASE: u8 = 12;
const NUMCASE: u8 = 13;
const EQ: u8 = 14;
const REFL: u8 = 15;
const J: u8 = 16;
const LOC: u8 = 17;
const QUOT: u8 = 18;

/// The byte a quotient form is written as.
fn quot_form_tag(form: QuotForm) -> u8 {
    match form {
        QuotForm::Type => 0,
        QuotForm::Mk => 1,
        QuotForm::Lift => 2,
        QuotForm::Ind => 3,
        QuotForm::Sound => 4,
    }
}

fn read_quot_form(tag: u8) -> Option<QuotForm> {
    QuotForm::ALL.into_iter().find(|f| quot_form_tag(*f) == tag)
}

/// Writes terms into a node table, and names into a string table, shared
/// by everything in one entry.
#[derive(Default)]
pub struct TermWriter {
    pub nodes: Writer,
    count: u32,
    ids: HashMap<*const Term, u32>,
    pub strings: Vec<String>,
    string_ids: HashMap<String, u32>,
}

/// A term that can't be written: one with a metavariable, which never
/// reaches the kernel.
#[derive(Debug)]
pub struct Unwritable;

impl TermWriter {
    /// The index of `s` in the string table.
    pub fn string(&mut self, s: &str) -> u32 {
        if let Some(&i) = self.string_ids.get(s) {
            return i;
        }
        let i = self.strings.len() as u32;
        self.strings.push(s.to_string());
        self.string_ids.insert(s.to_string(), i);
        i
    }

    /// How many nodes are written.
    pub fn node_count(&self) -> usize {
        self.count as usize
    }

    /// Writes `root` and everything under it not written yet; its node
    /// number.
    pub fn term(&mut self, refs: &mut dyn Refs, root: &Term) -> Result<u32, Unwritable> {
        let mut stack: Vec<(&Term, bool)> = vec![(root, false)];
        while let Some((t, expanded)) = stack.pop() {
            if self.ids.contains_key(&std::ptr::from_ref(t)) {
                continue;
            }
            if !expanded {
                stack.push((t, true));
                let mut children = Vec::new();
                each_child(t, &mut |c| children.push(c));
                for c in children.into_iter().rev() {
                    if !self.ids.contains_key(&std::ptr::from_ref(c)) {
                        stack.push((c, false));
                    }
                }
                continue;
            }
            self.node(refs, t)?;
            self.ids.insert(std::ptr::from_ref(t), self.count);
            self.count += 1;
        }
        Ok(self.ids[&std::ptr::from_ref(root)])
    }

    fn id(&self, t: &Rc<Term>) -> u64 {
        u64::from(self.ids[&std::ptr::from_ref(t.as_ref())])
    }

    fn name(&mut self, n: &Name) {
        let i = self.string(n);
        self.nodes.uint(u64::from(i));
    }

    /// One node, whose children are written already.
    fn node(&mut self, refs: &mut dyn Refs, t: &Term) -> Result<(), Unwritable> {
        let icit = |i: Icit| match i {
            Icit::Explicit => 0,
            Icit::Implicit => 1,
            Icit::Auto => 2,
        };
        match t {
            Term::Var(i) => {
                self.nodes.u8(VAR);
                self.nodes.usize(*i);
            }
            Term::Def(id) => {
                self.nodes.u8(DEF);
                refs.def(&mut self.nodes, *id);
            }
            Term::Data(d, args) => {
                self.nodes.u8(DATA);
                refs.data(&mut self.nodes, *d);
                self.nodes.usize(args.len());
                for a in args {
                    let id = self.id(a);
                    self.nodes.uint(id);
                }
            }
            Term::Ctor(d, c, args) => {
                self.nodes.u8(CTOR);
                refs.data(&mut self.nodes, *d);
                self.nodes.usize(*c);
                self.nodes.usize(args.len());
                for a in args {
                    let id = self.id(a);
                    self.nodes.uint(id);
                }
            }
            Term::Nat(n) => {
                self.nodes.u8(NAT);
                self.nodes.blob(&n.to_bytes_le());
            }
            Term::Chars(chars) => {
                self.nodes.u8(CHARS);
                let s: String = chars.as_slice().iter().collect();
                self.nodes.str(&s);
            }
            Term::Sort(s) => {
                self.nodes.u8(SORT);
                sort(&mut self.nodes, *s);
            }
            Term::Pi(x, i, a, b) => {
                self.nodes.u8(PI);
                self.name(x);
                self.nodes.u8(icit(*i));
                let (a, b) = (self.id(a), self.id(b));
                self.nodes.uint(a);
                self.nodes.uint(b);
            }
            Term::Lam(x, i, b) => {
                self.nodes.u8(LAM);
                self.name(x);
                self.nodes.u8(icit(*i));
                let b = self.id(b);
                self.nodes.uint(b);
            }
            Term::App(f, a, i) => {
                self.nodes.u8(APP);
                self.nodes.u8(icit(*i));
                let (f, a) = (self.id(f), self.id(a));
                self.nodes.uint(f);
                self.nodes.uint(a);
            }
            Term::Ann(a, b) => {
                self.nodes.u8(ANN);
                let (a, b) = (self.id(a), self.id(b));
                self.nodes.uint(a);
                self.nodes.uint(b);
            }
            Term::Let(x, ty, v, b, erased) => {
                self.nodes.u8(LET);
                self.name(x);
                self.nodes.bool(*erased);
                let (ty, v, b) = (self.id(ty), self.id(v), self.id(b));
                self.nodes.uint(ty);
                self.nodes.uint(v);
                self.nodes.uint(b);
            }
            Term::Case(x, d, branches) => {
                self.nodes.u8(CASE);
                self.nodes.usize(*x);
                refs.data(&mut self.nodes, *d);
                self.nodes.usize(branches.len());
                for branch in branches.iter() {
                    self.nodes.usize(branch.names.len());
                    for n in &branch.names {
                        self.name(n);
                    }
                    match &branch.body {
                        None => self.nodes.uint(0),
                        Some(b) => {
                            let b = self.id(b);
                            self.nodes.uint(b + 1);
                        }
                    }
                }
            }
            Term::NumCase(x, arms, default) => {
                self.nodes.u8(NUMCASE);
                self.nodes.usize(*x);
                self.nodes.usize(arms.len());
                for arm in arms.iter() {
                    self.nodes.blob(&arm.value.to_bytes_le());
                    let b = self.id(&arm.body);
                    self.nodes.uint(b);
                }
                let d = self.id(default);
                self.nodes.uint(d);
            }
            Term::Eq(ty, a, b) => {
                self.nodes.u8(EQ);
                match ty {
                    None => self.nodes.uint(0),
                    Some(ty) => {
                        let ty = self.id(ty);
                        self.nodes.uint(ty + 1);
                    }
                }
                let (a, b) = (self.id(a), self.id(b));
                self.nodes.uint(a);
                self.nodes.uint(b);
            }
            Term::Refl => self.nodes.u8(REFL),
            Term::J(m, b, p) => {
                self.nodes.u8(J);
                let (m, b, p) = (self.id(m), self.id(b), self.id(p));
                self.nodes.uint(m);
                self.nodes.uint(b);
                self.nodes.uint(p);
            }
            // The form, D921's erasure flag (kept, as `let`'s is, so a
            // loaded term runs as the checked one did), and the arguments.
            Term::Quot(form, args, erased) => {
                self.nodes.u8(QUOT);
                self.nodes.u8(quot_form_tag(*form));
                self.nodes.bool(*erased);
                self.nodes.usize(args.len());
                for a in args {
                    let a = self.id(a);
                    self.nodes.uint(a);
                }
            }
            Term::Loc(span, b) => {
                self.nodes.u8(LOC);
                refs.span(&mut self.nodes, *span);
                let b = self.id(b);
                self.nodes.uint(b);
            }
            Term::Meta(_) => return Err(Unwritable),
        }
        Ok(())
    }
}

/// Calls `f` on each direct sub-term of `t`.
fn each_child<'t>(t: &'t Term, f: &mut dyn FnMut(&'t Term)) {
    match t {
        Term::Pi(_, _, a, b) | Term::App(a, b, _) | Term::Ann(a, b) => {
            f(a);
            f(b);
        }
        Term::Lam(_, _, b) | Term::Loc(_, b) => f(b),
        Term::Let(_, a, v, b, _) => {
            f(a);
            f(v);
            f(b);
        }
        Term::Data(_, args) | Term::Ctor(_, _, args) => args.iter().for_each(|a| f(a)),
        Term::Eq(ty, a, b) => {
            if let Some(ty) = ty {
                f(ty);
            }
            f(a);
            f(b);
        }
        Term::J(m, b, p) => {
            f(m);
            f(b);
            f(p);
        }
        Term::Quot(_, args, _) => args.iter().for_each(|a| f(a)),
        Term::Case(_, _, branches) => {
            for branch in branches.iter() {
                if let Some(b) = &branch.body {
                    f(b);
                }
            }
        }
        Term::NumCase(_, arms, default) => {
            for arm in arms.iter() {
                f(&arm.body);
            }
            f(default);
        }
        Term::Var(_)
        | Term::Def(_)
        | Term::Nat(_)
        | Term::Chars(_)
        | Term::Sort(_)
        | Term::Refl
        | Term::Meta(_) => {}
    }
}

/// Every declaration a term refers to, without recursing: what replay
/// waits for before it submits the term.
pub fn references(t: &Term, defs: &mut dyn FnMut(DefId), datas: &mut dyn FnMut(DataId)) {
    let mut seen: stitchwort_core::collections::HashSet<*const Term> =
        stitchwort_core::collections::HashSet::default();
    let mut stack = vec![t];
    while let Some(t) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(t)) {
            continue;
        }
        match t {
            Term::Def(id) => defs(*id),
            Term::Data(d, _) | Term::Ctor(d, _, _) | Term::Case(_, d, _) => datas(*d),
            _ => {}
        }
        each_child(t, &mut |c| stack.push(c));
    }
}

pub fn sort(w: &mut Writer, s: Sort) {
    match s {
        Sort::Prop => w.uint(0),
        Sort::Type(i) => w.uint(u64::from(i) + 1),
    }
}

pub fn read_sort(r: &mut Reader) -> Read<Sort> {
    match r.uint()? {
        0 => Ok(Sort::Prop),
        n => Ok(Sort::Type(
            u32::try_from(n - 1).or_else(|_| bad("a universe too large"))?,
        )),
    }
}

/// The node table and string table, read back.
pub struct Terms {
    pub nodes: Vec<Rc<Term>>,
    pub strings: Vec<Name>,
}

impl Terms {
    pub fn read_strings(r: &mut Reader) -> Read<Vec<Name>> {
        let n = r.count(1)?;
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            out.push(Name::from(r.string()?));
        }
        Ok(out)
    }

    pub fn name(&self, r: &mut Reader) -> Read<Name> {
        let i = r.usize()?;
        match self.strings.get(i) {
            Some(s) => Ok(s.clone()),
            None => bad("a string out of range"),
        }
    }

    /// A term by its node number.
    pub fn term(&self, r: &mut Reader) -> Read<Term> {
        Ok(Term::clone(&*self.rc(r)?))
    }

    pub fn rc(&self, r: &mut Reader) -> Read<Rc<Term>> {
        let i = r.usize()?;
        match self.nodes.get(i) {
            Some(t) => Ok(t.clone()),
            None => bad("a term out of range"),
        }
    }

    /// Reads `count` nodes.
    pub fn read_nodes(&mut self, r: &mut Reader, refs: &dyn ReadRefs, count: usize) -> Read<()> {
        self.nodes.reserve(count);
        let read_icit = |r: &mut Reader| match r.u8()? {
            0 => Ok(Icit::Explicit),
            1 => Ok(Icit::Implicit),
            2 => Ok(Icit::Auto),
            _ => bad("an unknown kind of parameter"),
        };
        for _ in 0..count {
            let t = match r.u8()? {
                VAR => Term::Var(r.usize()?),
                DEF => Term::Def(refs.def(r)?),
                DATA => {
                    let d = refs.data(r)?;
                    let n = r.count(1)?;
                    let args = (0..n).map(|_| self.rc(r)).collect::<Read<_>>()?;
                    Term::Data(d, args)
                }
                CTOR => {
                    let d = refs.data(r)?;
                    let c = r.usize()?;
                    let n = r.count(1)?;
                    let args = (0..n).map(|_| self.rc(r)).collect::<Read<_>>()?;
                    Term::Ctor(d, c, args)
                }
                NAT => Term::Nat(Rc::new(BigUint::from_bytes_le(r.blob()?))),
                CHARS => {
                    let s = r.string()?;
                    Term::Chars(Chars::whole(s.chars().collect()))
                }
                SORT => Term::Sort(read_sort(r)?),
                PI => {
                    let x = self.name(r)?;
                    let i = read_icit(r)?;
                    Term::Pi(x, i, self.rc(r)?, self.rc(r)?)
                }
                LAM => {
                    let x = self.name(r)?;
                    let i = read_icit(r)?;
                    Term::Lam(x, i, self.rc(r)?)
                }
                APP => {
                    let i = read_icit(r)?;
                    Term::App(self.rc(r)?, self.rc(r)?, i)
                }
                ANN => Term::Ann(self.rc(r)?, self.rc(r)?),
                LET => {
                    let x = self.name(r)?;
                    let erased = r.bool()?;
                    Term::Let(x, self.rc(r)?, self.rc(r)?, self.rc(r)?, erased)
                }
                CASE => {
                    let x = r.usize()?;
                    let d = refs.data(r)?;
                    let n = r.count(2)?;
                    let mut branches = Vec::with_capacity(n);
                    for _ in 0..n {
                        let k = r.count(1)?;
                        let names = (0..k).map(|_| self.name(r)).collect::<Read<_>>()?;
                        let body = match r.usize()? {
                            0 => None,
                            i => match self.nodes.get(i - 1) {
                                Some(t) => Some(t.clone()),
                                None => return bad("a term out of range"),
                            },
                        };
                        branches.push(Branch { names, body });
                    }
                    Term::Case(x, d, branches.into())
                }
                NUMCASE => {
                    let x = r.usize()?;
                    let n = r.count(2)?;
                    let mut arms = Vec::with_capacity(n);
                    for _ in 0..n {
                        let value = Rc::new(BigUint::from_bytes_le(r.blob()?));
                        arms.push(NumArm {
                            value,
                            body: self.rc(r)?,
                        });
                    }
                    Term::NumCase(x, arms.into(), self.rc(r)?)
                }
                EQ => {
                    let ty = match r.usize()? {
                        0 => None,
                        i => match self.nodes.get(i - 1) {
                            Some(t) => Some(t.clone()),
                            None => return bad("a term out of range"),
                        },
                    };
                    Term::Eq(ty, self.rc(r)?, self.rc(r)?)
                }
                REFL => Term::Refl,
                J => Term::J(self.rc(r)?, self.rc(r)?, self.rc(r)?),
                QUOT => {
                    let Some(form) = read_quot_form(r.u8()?) else {
                        return bad("an unknown quotient form");
                    };
                    let erased = r.bool()?;
                    let n = r.count(1)?;
                    let args = (0..n).map(|_| self.rc(r)).collect::<Read<_>>()?;
                    Term::Quot(form, args, erased)
                }
                LOC => {
                    let span = refs.span(r)?;
                    Term::Loc(span, self.rc(r)?)
                }
                _ => return bad("an unknown kind of term"),
            };
            self.nodes.push(Rc::new(t));
        }
        Ok(())
    }
}
