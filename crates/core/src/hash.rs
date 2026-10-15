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
//!
//! A term is walked with a work list, since it can nest more deeply than
//! recursion could follow. Hashing a reference hashes the declaration it
//! refers to first (if it hasn't been yet), which does recurse, once per
//! declaration in a chain of dependencies: that's guarded like the other
//! recursive passes, and needs an operation to be running.

use crate::budget::Result;
use crate::globals::{Globals, HashKey, State};
use crate::term::{DataId, DefId, Icit, Sort, Term};

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

/// The name the hasher's depth guard reports.
const PASS: &str = "hasher";

/// `None` for a definition that isn't final (pending, or failed).
pub fn def_hash(g: &Globals, id: DefId) -> Result<Option<ContentHash>> {
    if let Some(hash) = g.hashes.borrow().get(&HashKey::Def(id)) {
        return Ok(Some(*hash));
    }
    g.budget.nesting(PASS)?;
    let def = g.def(id);
    let (State::Final, Some(body)) = (def.state, def.body.as_ref()) else {
        return Ok(None);
    };
    let mut h = Hasher::new(g, Itself::Def(id));
    h.tag("def");
    h.bool(def.theorem);
    h.term(&def.ty)?;
    h.term(body)?;
    let hash = h.finish();
    g.hashes.borrow_mut().insert(HashKey::Def(id), hash);
    Ok(Some(hash))
}

/// `None` for a data type that isn't final: without its constructors, it
/// isn't yet the type it will be.
pub fn data_hash(g: &Globals, id: DataId) -> Result<Option<ContentHash>> {
    if let Some(hash) = g.hashes.borrow().get(&HashKey::Data(id)) {
        return Ok(Some(*hash));
    }
    g.budget.nesting(PASS)?;
    let data = g.data(id);
    if data.state != State::Final {
        return Ok(None);
    }
    let mut h = Hasher::new(g, Itself::Data(id));
    h.tag("data");
    h.str(&data.name);
    h.sort(data.sort);
    h.usize(data.params.len());
    for (_, ty) in &data.params {
        h.term(ty)?;
    }
    h.usize(data.ctors.len());
    for ctor in &data.ctors {
        h.str(&ctor.name);
        h.usize(ctor.fields.len());
        for (_, ty) in &ctor.fields {
            h.term(ty)?;
        }
    }
    let hash = h.finish();
    g.hashes.borrow_mut().insert(HashKey::Data(id), hash);
    Ok(Some(hash))
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

    fn def_ref(&mut self, id: DefId) -> Result<()> {
        match self.itself {
            Itself::Def(me) if me == id => self.tag("self"),
            _ => {
                let hash = def_hash(self.g, id)?.map_or([0; 32], |h| h.0);
                self.tag("ref");
                self.bytes(&hash);
            }
        }
        Ok(())
    }

    fn data_ref(&mut self, id: DataId) -> Result<()> {
        match self.itself {
            Itself::Data(me) if me == id => self.tag("self"),
            _ => {
                // Final declarations only refer to final ones.
                let hash = data_hash(self.g, id)?.map_or([0; 32], |h| h.0);
                self.tag("ref");
                self.bytes(&hash);
            }
        }
        Ok(())
    }

    /// Hashes `term` in the order a recursive walk would: each node, then its
    /// parts left to right. The work list holds the parts still to hash, and
    /// the counts and tags that go between them, last first.
    fn term(&mut self, term: &Term) -> Result<()> {
        enum Item<'t> {
            Term(&'t Term),
            Usize(usize),
            Tag(&'static str),
        }
        let mut pending = vec![Item::Term(term)];
        while let Some(item) = pending.pop() {
            let term = match item {
                Item::Term(term) => term,
                Item::Usize(n) => {
                    self.usize(n);
                    continue;
                }
                Item::Tag(tag) => {
                    self.tag(tag);
                    continue;
                }
            };
            // The parts of `term`, in order; reversed onto `pending` below.
            let first = pending.len();
            match term {
                Term::Loc(_, t) => pending.push(Item::Term(t)),
                Term::Var(ix) => {
                    self.tag("var");
                    self.usize(*ix);
                }
                Term::Def(id) => self.def_ref(*id)?,
                Term::Data(d, args) => {
                    self.tag("data");
                    self.data_ref(*d)?;
                    pending.push(Item::Usize(args.len()));
                    pending.extend(args.iter().map(|t| Item::Term(t)));
                }
                Term::Ctor(d, c, args) => {
                    self.tag("ctor");
                    self.data_ref(*d)?;
                    self.usize(*c);
                    pending.push(Item::Usize(args.len()));
                    pending.extend(args.iter().map(|t| Item::Term(t)));
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
                    pending.extend([Item::Term(a), Item::Term(b)]);
                }
                Term::Lam(_, icit, b) => {
                    self.tag("lam");
                    self.icit(*icit);
                    pending.push(Item::Term(b));
                }
                Term::App(f, a, icit) => {
                    self.tag("app");
                    self.icit(*icit);
                    pending.extend([Item::Term(f), Item::Term(a)]);
                }
                Term::Ann(e, t) => {
                    self.tag("ann");
                    pending.extend([Item::Term(e), Item::Term(t)]);
                }
                Term::Case(ix, d, branches) => {
                    self.tag("case");
                    self.usize(*ix);
                    self.data_ref(*d)?;
                    self.usize(branches.len());
                    for b in branches.iter() {
                        pending.extend([Item::Usize(b.names.len()), Item::Term(&b.body)]);
                    }
                }
                Term::Eq(ty, a, b) => {
                    self.tag("eq");
                    pending.push(match ty {
                        Some(t) => Item::Term(t),
                        None => Item::Tag("none"),
                    });
                    pending.extend([Item::Term(a), Item::Term(b)]);
                }
                Term::Refl => self.tag("refl"),
                Term::J(m, b, p) => {
                    self.tag("j");
                    pending.extend([Item::Term(m), Item::Term(b), Item::Term(p)]);
                }
                Term::Meta(_) => panic!("internal error: hashing an unsolved metavariable"),
            }
            pending[first..].reverse();
        }
        Ok(())
    }
}
