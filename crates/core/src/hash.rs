//! Content hashes of checked declarations (DESIGN.md §11).
//!
//! A definition's hash covers its kind, type and body. A reference to another
//! declaration is hashed as that declaration's hash, so a hash covers
//! everything a definition depends on, transitively. A recursive reference is
//! hashed as a fixed marker, which keeps recursion from looping.
//!
//! Left out, so they don't affect identity: the definition's own name, binder
//! names, local variable names (variables are de Bruijn indices) and source
//! locations. Data types are nominal, so their names *are* included, along
//! with their constructors' names.

use crate::globals::{Globals, HashKey};
use crate::term::{DataId, DefId, Icit, Sort, Term};
use std::rc::Rc;

/// A 256-bit content hash.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ContentHash(pub [u8; 32]);

impl ContentHash {
    pub fn hex(&self) -> String {
        self.0.iter().map(|b| format!("{b:02x}")).collect()
    }
}

impl std::fmt::Debug for ContentHash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "#{}", &self.hex()[..12])
    }
}

/// What a declaration refers to itself as, inside its own hash.
#[derive(Clone, Copy)]
enum Itself {
    Def(DefId),
    Data(DataId),
}

pub fn def_hash(g: &Globals, id: DefId) -> Option<ContentHash> {
    if let Some(hash) = g.hashes.borrow().get(&HashKey::Def(id)) {
        return Some(*hash);
    }
    let def = g.def(id);
    let body = def.body.as_ref()?;
    let mut h = Hasher::new(g, Itself::Def(id));
    h.tag("def");
    h.bool(def.theorem);
    h.term(&def.ty);
    h.term(body);
    let hash = h.finish();
    g.hashes.borrow_mut().insert(HashKey::Def(id), hash);
    Some(hash)
}

pub fn data_hash(g: &Globals, id: DataId) -> ContentHash {
    if let Some(hash) = g.hashes.borrow().get(&HashKey::Data(id)) {
        return *hash;
    }
    let data = g.data(id);
    let mut h = Hasher::new(g, Itself::Data(id));
    h.tag("data");
    h.str(&data.name);
    h.sort(data.sort);
    h.usize(data.params.len());
    for (_, ty) in &data.params {
        h.term(ty);
    }
    h.usize(data.ctors.len());
    for ctor in &data.ctors {
        h.str(&ctor.name);
        h.usize(ctor.fields.len());
        for (_, ty) in &ctor.fields {
            h.term(ty);
        }
    }
    let hash = h.finish();
    // Only remember it once the constructors are in (a type with none, like
    // `Void`, is cheap to recompute).
    if !data.ctors.is_empty() {
        g.hashes.borrow_mut().insert(HashKey::Data(id), hash);
    }
    hash
}

struct Hasher<'g> {
    g: &'g Globals,
    itself: Itself,
    inner: blake3::Hasher,
}

impl<'g> Hasher<'g> {
    fn new(g: &'g Globals, itself: Itself) -> Self {
        Hasher {
            g,
            itself,
            inner: blake3::Hasher::new(),
        }
    }

    fn finish(&self) -> ContentHash {
        ContentHash(*self.inner.finalize().as_bytes())
    }

    fn bytes(&mut self, bytes: &[u8]) {
        self.inner.update(bytes);
    }

    fn usize(&mut self, n: usize) {
        self.bytes(&(n as u64).to_le_bytes());
    }

    fn bool(&mut self, b: bool) {
        self.bytes(&[u8::from(b)]);
    }

    /// A length-prefixed string, so adjacent strings can't run together.
    fn str(&mut self, s: &str) {
        self.usize(s.len());
        self.bytes(s.as_bytes());
    }

    fn tag(&mut self, tag: &str) {
        self.str(tag);
    }

    fn sort(&mut self, sort: Sort) {
        match sort {
            Sort::Prop => self.tag("prop"),
            Sort::Type(i) => {
                self.tag("type");
                self.usize(i as usize);
            }
        }
    }

    fn icit(&mut self, icit: Icit) {
        self.tag(match icit {
            Icit::Explicit => "explicit",
            Icit::Implicit => "implicit",
            Icit::Auto => "auto",
        });
    }

    fn def_ref(&mut self, id: DefId) {
        match self.itself {
            Itself::Def(me) if me == id => self.tag("self"),
            _ => {
                let hash = def_hash(self.g, id).map_or([0; 32], |h| h.0);
                self.tag("ref");
                self.bytes(&hash);
            }
        }
    }

    fn data_ref(&mut self, id: DataId) {
        match self.itself {
            Itself::Data(me) if me == id => self.tag("self"),
            _ => {
                let hash = data_hash(self.g, id);
                self.tag("ref");
                self.bytes(&hash.0);
            }
        }
    }

    fn terms(&mut self, terms: &[Rc<Term>]) {
        self.usize(terms.len());
        for t in terms {
            self.term(t);
        }
    }

    fn term(&mut self, term: &Term) {
        match term {
            Term::Loc(_, t) => self.term(t),
            Term::Var(ix) => {
                self.tag("var");
                self.usize(*ix);
            }
            Term::Def(id) => self.def_ref(*id),
            Term::Data(d, args) => {
                self.tag("data");
                self.data_ref(*d);
                self.terms(args);
            }
            Term::Ctor(d, c, args) => {
                self.tag("ctor");
                self.data_ref(*d);
                self.usize(*c);
                self.terms(args);
            }
            Term::Nat(n) => {
                self.tag("nat");
                let bytes = n.to_bytes_le();
                self.usize(bytes.len());
                self.bytes(&bytes);
            }
            Term::Sort(s) => self.sort(*s),
            Term::Pi(_, icit, a, b) => {
                self.tag("pi");
                self.icit(*icit);
                self.term(a);
                self.term(b);
            }
            Term::Lam(_, icit, b) => {
                self.tag("lam");
                self.icit(*icit);
                self.term(b);
            }
            Term::App(f, a, icit) => {
                self.tag("app");
                self.icit(*icit);
                self.term(f);
                self.term(a);
            }
            Term::Ann(e, t) => {
                self.tag("ann");
                self.term(e);
                self.term(t);
            }
            Term::Case(ix, d, branches) => {
                self.tag("case");
                self.usize(*ix);
                self.data_ref(*d);
                self.usize(branches.len());
                for b in branches.iter() {
                    self.usize(b.names.len());
                    self.term(&b.body);
                }
            }
            Term::Eq(ty, a, b) => {
                self.tag("eq");
                match ty {
                    Some(t) => self.term(t),
                    None => self.tag("none"),
                }
                self.term(a);
                self.term(b);
            }
            Term::Refl => self.tag("refl"),
            Term::J(m, b, p) => {
                self.tag("j");
                self.term(m);
                self.term(b);
                self.term(p);
            }
            Term::Meta(_) => panic!("internal error: hashing an unsolved metavariable"),
        }
    }
}
