//! Content hashes of checked declarations (DESIGN.md §11).
//!
//! A definition's hash covers its kind, type and body. A reference to another
//! declaration is hashed as that declaration's hash, so a hash covers
//! everything a definition depends on, transitively. A recursive reference is
//! hashed as a fixed marker, which keeps recursion from looping.
//!
//! A group of definitions that call each other (two or more, submitted to
//! `define_group` together) is hashed as a unit, after Unison
//! (docs/proposals/mutual-recursion.md §8.4): the members are put in a
//! canonical order, the group's hash covers every member's full declaration
//! in that order, with references to members hashed as their index in it,
//! and each member's hash is the group's hash and its index. So changing any
//! member changes every member's hash. The order is by each member's *shape*
//! (its hash with every reference to a member replaced by one marker), so
//! moving members around in the source doesn't change their hashes; members
//! with the same shape are ordered as they were submitted. Only final groups
//! are hashed, and the shapes are never stored.
//!
//! A group of data types declared together (two or more, by
//! `declare_data_group`) is hashed as a unit in the same way, ordered by name
//! (data types are nominal, so no shapes are needed), ties broken by
//! declaration order. The group's hash covers the shared parameters and
//! universe, the number of members, and each member's name and constructors;
//! a reference to a member, whether as a type, a constructor or a `case`, is
//! its index in that order (and a constructor's index after it). So changing
//! any constructor of any member changes every member's hash.
//!
//! Left out, so they don't affect identity: the definition's own name, binder
//! names, local variable names (variables are de Bruijn indices) and source
//! locations. Data types are nominal, so their names *are* included, along
//! with their constructors' names, their fields' names, and whether they're
//! records.
//!
//! A term is walked with a work list, since it can nest more deeply than
//! recursion could follow. Hashing a reference hashes the declaration it
//! refers to first (if it hasn't been yet), which does recurse, once per
//! declaration in a chain of dependencies: that's guarded like the other
//! recursive passes, and needs an operation to be running.

use crate::budget::Result;
use crate::globals::{Data, Globals, HashKey, State};
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
enum Itself<'a> {
    Def(DefId),
    Data(DataId),
    /// The members of a group: each is the marker `member` alone (for a
    /// member's shape), or with its index in `order` (`order[i]` is the
    /// position in `members` of the member with index `i`).
    Group {
        members: &'a [DefId],
        order: Option<&'a [usize]>,
    },
    /// The members of a data group: each is the marker `member` with its
    /// index in `order`, as for a group of definitions.
    DataGroup {
        members: &'a [DataId],
        order: &'a [usize],
    },
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
    if def.state == State::Final
        && let Some(prim) = g.builtins.primitive(id)
    {
        // `Delay` and its constants have no body: they're their name and
        // type (docs/proposals/partial.md §7.2).
        let mut h = Hasher::new(g, Itself::Def(id));
        h.tag("primitive");
        h.str(prim.name());
        h.term(&def.ty)?;
        let hash = h.finish();
        g.hashes.borrow_mut().insert(HashKey::Def(id), hash);
        return Ok(Some(hash));
    }
    let (State::Final, Some(body)) = (def.state, def.body.as_ref()) else {
        return Ok(None);
    };
    if let Some(members) = def.group.as_ref().filter(|m| m.len() > 1) {
        group_hashes(g, members)?;
        return Ok(g.hashes.borrow().get(&HashKey::Def(id)).copied());
    }
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
    if data.group.len() > 1 {
        data_group_hashes(g, &data.group)?;
        return Ok(g.hashes.borrow().get(&HashKey::Data(id)).copied());
    }
    let mut h = Hasher::new(g, Itself::Data(id));
    h.tag("data");
    h.str(&data.path);
    h.sort(data.sort);
    h.usize(data.params.len());
    for (_, ty) in &data.params {
        h.term(ty)?;
    }
    h.ctors(data)?;
    let hash = h.finish();
    g.hashes.borrow_mut().insert(HashKey::Data(id), hash);
    Ok(Some(hash))
}

/// Hashes every member of a final group of two or more definitions, and
/// stores their hashes.
fn group_hashes(g: &Globals, members: &[DefId]) -> Result<()> {
    let declaration = |h: &mut Hasher, id: DefId| -> Result<()> {
        let def = g.def(id);
        let body = def
            .body
            .as_ref()
            .expect("internal error: hashing a group that isn't final");
        h.tag("def");
        h.bool(def.theorem);
        h.term(&def.ty)?;
        h.term(body)
    };
    // Every member's shape, then the canonical order: by shape, and as
    // submitted where shapes are the same.
    let mut shapes = Vec::new();
    for &id in members {
        let mut h = Hasher::new(
            g,
            Itself::Group {
                members,
                order: None,
            },
        );
        h.tag("shape");
        declaration(&mut h, id)?;
        shapes.push(h.finish().0);
    }
    let mut order: Vec<usize> = (0..members.len()).collect();
    order.sort_by_key(|&m| (shapes[m], m));
    let mut h = Hasher::new(
        g,
        Itself::Group {
            members,
            order: Some(&order),
        },
    );
    h.tag("group");
    h.usize(members.len());
    for &m in &order {
        declaration(&mut h, members[m])?;
    }
    let group = h.finish();
    for (index, &m) in order.iter().enumerate() {
        let mut h = Hasher::new(g, Itself::Def(members[m]));
        h.tag("member");
        h.bytes(&group.0);
        h.usize(index);
        g.hashes
            .borrow_mut()
            .insert(HashKey::Def(members[m]), h.finish());
    }
    Ok(())
}

/// Hashes every member of a final group of two or more data types, and
/// stores their hashes.
fn data_group_hashes(g: &Globals, members: &[DataId]) -> Result<()> {
    // The canonical order: by name, and as declared where names are the same.
    let mut order: Vec<usize> = (0..members.len()).collect();
    order.sort_by(|&a, &b| {
        let name = |m: usize| &g.data(members[m]).path;
        name(a).cmp(name(b)).then(a.cmp(&b))
    });
    let first = g.data(members[0]);
    let mut h = Hasher::new(
        g,
        Itself::DataGroup {
            members,
            order: &order,
        },
    );
    h.tag("data-group");
    h.usize(members.len());
    // The parameters and universe are the group's, shared by every member.
    h.sort(first.sort);
    h.usize(first.params.len());
    for (_, ty) in &first.params {
        h.term(ty)?;
    }
    for &m in &order {
        let data = g.data(members[m]);
        h.tag("data");
        h.str(&data.path);
        h.ctors(data)?;
    }
    let group = h.finish();
    for (index, &m) in order.iter().enumerate() {
        let mut h = Hasher::new(g, Itself::Data(members[m]));
        h.tag("data-member");
        h.bytes(&group.0);
        h.usize(index);
        g.hashes
            .borrow_mut()
            .insert(HashKey::Data(members[m]), h.finish());
    }
    Ok(())
}

struct Hasher<'g> {
    g: &'g Globals,
    itself: Itself<'g>,
    inner: blake3::Hasher,
}

impl<'g> Hasher<'g> {
    fn new(g: &'g Globals, itself: Itself<'g>) -> Self {
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

    fn nat(&mut self, n: &num_bigint::BigUint) {
        let bytes = n.to_bytes_le();
        self.usize(bytes.len());
        self.bytes(&bytes);
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

    /// Whether a data type is a record, and its constructors: their names,
    /// and their fields' names and types. Field names are hashed because they
    /// change the JS (each field's key) and, for records, which field
    /// `p.name` means (docs/proposals/records.md §12); the record flag
    /// because it changes the JS representation.
    fn ctors(&mut self, data: &Data) -> Result<()> {
        self.bool(data.record);
        self.usize(data.ctors.len());
        for ctor in &data.ctors {
            self.str(&ctor.name);
            self.usize(ctor.fields.len());
            for (name, ty) in &ctor.fields {
                self.str(name);
                self.term(ty)?;
            }
        }
        Ok(())
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
            Itself::Group { members, order } if members.contains(&id) => {
                self.tag("member");
                if let Some(order) = order {
                    let m = members.iter().position(|m| *m == id).expect("a member");
                    let index = order.iter().position(|o| *o == m).expect("ordered");
                    self.usize(index);
                }
            }
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
            Itself::DataGroup { members, order } if members.contains(&id) => {
                let m = members.iter().position(|m| *m == id).expect("a member");
                let index = order.iter().position(|o| *o == m).expect("ordered");
                self.tag("member");
                self.usize(index);
            }
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
            Nat(&'t num_bigint::BigUint),
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
                Item::Nat(n) => {
                    self.nat(n);
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
                    self.nat(n);
                }
                // The logical contents (never the buffer or the offsets), and
                // `List` and `Char`, which the expansion refers to: through
                // `Char`'s fields, they cover `isScalar` too.
                Term::Chars(chars) => {
                    let text = self
                        .g
                        .builtins
                        .text
                        .as_ref()
                        .expect("internal error: a compact list without `List` and `Char`");
                    self.tag("chars");
                    self.data_ref(text.list)?;
                    self.data_ref(text.char)?;
                    self.usize(chars.len());
                    for c in chars.as_slice() {
                        self.bytes(&u32::from(*c).to_le_bytes());
                    }
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
                // Every number, every arm and the default, and `Nat` itself
                // (as a `case` hashes its data type).
                Term::NumCase(ix, arms, default) => {
                    self.tag("numcase");
                    self.usize(*ix);
                    let nat = self
                        .g
                        .builtins
                        .nat
                        .expect("internal error: a number case without `Nat`");
                    self.data_ref(nat)?;
                    self.usize(arms.len());
                    for a in arms.iter() {
                        pending.extend([Item::Nat(&a.value), Item::Term(&a.body)]);
                    }
                    pending.push(Item::Term(default));
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
