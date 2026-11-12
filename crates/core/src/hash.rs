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
//! with the same shape are ordered by full name. Only final groups
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
//! A data type's index telescope and its constructors' result indices, and
//! which branches of a `case` are impossible, are hashed only when present
//! (docs/proposals/indexed-families.md §6.9), so a type without indices and
//! a case without impossible branches hash as they did before indices.
//!
//! A term is walked with a work list, since it can nest more deeply than
//! recursion could follow. Hashing a reference hashes the declaration it
//! refers to first (if it hasn't been yet), which does recurse, once per
//! declaration in a chain of dependencies: that's guarded like the other
//! recursive passes, and needs an operation to be running.

use crate::budget::Result;
use crate::ev::Ev;
use crate::globals::{Assumption, Data, HashKey, State};
use crate::term::{DataId, DefId, Icit, QuotForm, Sort, Term};

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

/// Which hash is being computed: the content hash, or the one without
/// proofs ([`proofless_hash`]).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Content,
    Proofless,
}

impl Mode {
    fn cache<'g>(
        self,
        g: &'g Ev,
    ) -> &'g std::cell::RefCell<crate::collections::HashMap<HashKey, ContentHash>> {
        match self {
            Mode::Content => &g.caches.hashes,
            Mode::Proofless => &g.caches.proofless,
        }
    }
}

/// `None` for a definition that isn't final (pending, or failed).
pub fn def_hash(g: &Ev, id: DefId) -> Result<Option<ContentHash>> {
    def_hash_in(g, id, Mode::Content)
}

/// The content hash of definition `id` with its proofs left out: what a run
/// computes, which never looks at a proof (`erase.rs`). It is [`def_hash`]
/// with every subterm at a proof position hashed as one marker, and every
/// declaration referred to hashed by this hash in turn. A proof position is
/// a subterm the run never computes: an argument at a parameter whose type
/// is a proposition, a call of a definition whose result is a proof (a
/// theorem, applied or not), a constructor's field whose type is a
/// proposition, a data type's proof parameter, `J`'s proof, `Quot.lift`'s
/// proof that its function respects the relation, and `Quot.ind` and
/// `Quot.sound`. A definition whose result is a proof is its type alone.
/// It is the same as [`def_hash`] for a definition with no proofs in it or
/// in what it mentions. Statements (types) are kept, so two definitions
/// with the same hash here have statements that say the same, up to the
/// proofs inside the definitions they mention.
///
/// The refactoring tools compare it to accept a change to a definition's
/// embedded proofs (`Promise::ProofsOnly`); it decides nothing the kernel
/// accepts, and nothing is cached by it. `None` while a declaration it
/// depends on isn't final.
pub fn proofless_hash(g: &Ev, id: DefId) -> Result<Option<ContentHash>> {
    def_hash_in(g, id, Mode::Proofless)
}

/// [`data_hash`] without proofs: see [`proofless_hash`].
pub fn proofless_data_hash(g: &Ev, id: DataId) -> Result<Option<ContentHash>> {
    data_hash_in(g, id, Mode::Proofless)
}

fn def_hash_in(g: &Ev, id: DefId, mode: Mode) -> Result<Option<ContentHash>> {
    if let Some(hash) = mode.cache(g).borrow().get(&HashKey::Def(id)) {
        return Ok(Some(*hash));
    }
    g.machine.budget.nesting(PASS)?;
    let def = g.def(id);
    if def.state == State::Final
        && let Some(prim) = g.env.builtins().primitive(id)
    {
        // `Delay` and its constants have no body: they're their name and
        // type (docs/proposals/partial.md §7.2).
        let mut h = Hasher::new(g, Itself::Def(id), mode);
        h.tag("primitive");
        h.str(prim.name());
        h.term(&def.ty)?;
        let hash = h.finish();
        mode.cache(g).borrow_mut().insert(HashKey::Def(id), hash);
        return Ok(Some(hash));
    }
    if def.state == State::Final && g.env.builtins().float_primitive(id).is_some() {
        let hash = float_primitive_hash_in(g, id, crate::float::FLOAT_CONTRACT, mode)?
            .expect("a float primitive");
        mode.cache(g).borrow_mut().insert(HashKey::Def(id), hash);
        return Ok(Some(hash));
    }
    if def.state == State::Final
        && let Some(label) = def.assumption()
    {
        // An assumption has no body: it's its label and type, the same
        // with or without proofs. The label is the one place a name is
        // hashed, so two `?`s with the same goal stay distinct, a stand-in
        // never hashes as a goal, and filling the gap changes every user's
        // hash (docs/core.md "Assumptions (open goals)").
        let mut h = Hasher::new(g, Itself::Def(id), mode);
        match label.kind {
            crate::globals::AssumptionKind::Goal(hole) => {
                h.tag("assume");
                h.str(&label.owner);
                h.usize(hole as usize);
            }
            crate::globals::AssumptionKind::Error => {
                h.tag("assume-error");
                h.str(&label.owner);
            }
        }
        h.term(&def.ty)?;
        let hash = h.finish();
        mode.cache(g).borrow_mut().insert(HashKey::Def(id), hash);
        return Ok(Some(hash));
    }
    let (State::Final, Some(_)) = (def.state, def.body.as_ref()) else {
        return Ok(None);
    };
    // Without proofs, a group is its members that compute: one whose result
    // is a proof is its statement alone, and the others never mention it
    // (a call of it is a proof, the marker), so it stands apart. A lifted
    // `match` of a recursive theorem is then part of the theorem's proof.
    let members: Option<Vec<DefId>> = def.group.as_ref().map(|m| match mode {
        Mode::Content => m.to_vec(),
        Mode::Proofless => m
            .iter()
            .copied()
            .filter(|&m| !crate::erase::proof_positions(g, m).is_some_and(|p| p.result))
            .collect(),
    });
    if let Some(members) = members.filter(|m| m.len() > 1 && m.contains(&id)) {
        group_hashes(g, &members, mode)?;
        return Ok(mode.cache(g).borrow().get(&HashKey::Def(id)).copied());
    }
    let mut h = Hasher::new(g, Itself::Def(id), mode);
    h.declaration(id)?;
    let hash = h.finish();
    mode.cache(g).borrow_mut().insert(HashKey::Def(id), hash);
    Ok(Some(hash))
}

/// The hash of the type of definition `id` alone, with the hashes of what it
/// mentions: what a statement says, whatever its proof. `None` while a
/// definition it mentions isn't final.
pub fn type_hash(g: &Ev, id: DefId) -> Result<Option<ContentHash>> {
    g.machine.budget.nesting(PASS)?;
    let mut h = Hasher::new(g, Itself::Def(id), Mode::Content);
    h.tag("type");
    h.term(&g.def(id).ty)?;
    Ok((!h.unfinished).then(|| h.finish()))
}

/// The hash of float primitive `id` (`Float.add`, …) under version
/// `contract` of the float contract: `None` if `id` isn't one. A primitive
/// has no body: it's its name, as the operation tag, the contract's version
/// and its type (docs/proposals/float.md §3.3). So two primitives of the same
/// type hash differently, and a change of meaning (a new `FLOAT_CONTRACT`)
/// changes every hash that depends on one. [`def_hash`] uses the current
/// contract; another is for the test that a bump changes the hashes.
pub fn float_primitive_hash(g: &Ev, id: DefId, contract: u32) -> Result<Option<ContentHash>> {
    float_primitive_hash_in(g, id, contract, Mode::Content)
}

fn float_primitive_hash_in(
    g: &Ev,
    id: DefId,
    contract: u32,
    mode: Mode,
) -> Result<Option<ContentHash>> {
    let Some(op) = g.env.builtins().float_primitive(id) else {
        return Ok(None);
    };
    let def = g.def(id);
    let mut h = Hasher::new(g, Itself::Def(id), mode);
    h.tag("primitive");
    h.str(op.name());
    h.tag("float-contract");
    h.usize(contract as usize);
    h.term(&def.ty)?;
    Ok(Some(h.finish()))
}

/// `None` for a data type that isn't final: without its constructors, it
/// isn't yet the type it will be.
pub fn data_hash(g: &Ev, id: DataId) -> Result<Option<ContentHash>> {
    data_hash_in(g, id, Mode::Content)
}

fn data_hash_in(g: &Ev, id: DataId, mode: Mode) -> Result<Option<ContentHash>> {
    if let Some(hash) = mode.cache(g).borrow().get(&HashKey::Data(id)) {
        return Ok(Some(*hash));
    }
    g.machine.budget.nesting(PASS)?;
    let data = g.data(id);
    if data.state != State::Final {
        return Ok(None);
    }
    if data.group.len() > 1 {
        data_group_hashes(g, &data.group, mode)?;
        return Ok(mode.cache(g).borrow().get(&HashKey::Data(id)).copied());
    }
    let mut h = Hasher::new(g, Itself::Data(id), mode);
    h.tag("data");
    h.str(&data.path);
    h.sort(data.sort);
    h.usize(data.params.len());
    for (_, ty) in &data.params {
        h.term(ty)?;
    }
    h.auto_params(data);
    h.no_eta(data);
    h.indices(data)?;
    h.ctors(data)?;
    let hash = h.finish();
    mode.cache(g).borrow_mut().insert(HashKey::Data(id), hash);
    Ok(Some(hash))
}

/// Hashes every member of a final group of two or more definitions, and
/// stores their hashes.
fn group_hashes(g: &Ev, members: &[DefId], mode: Mode) -> Result<()> {
    let declaration = |h: &mut Hasher, id: DefId| h.declaration(id);
    // Every member's shape, then the canonical order: by shape, and by full
    // name where shapes are the same.
    let mut shapes = Vec::new();
    for &id in members {
        let mut h = Hasher::new(
            g,
            Itself::Group {
                members,
                order: None,
            },
            mode,
        );
        h.tag("shape");
        declaration(&mut h, id)?;
        shapes.push(h.finish().0);
    }
    let mut order: Vec<usize> = (0..members.len()).collect();
    order.sort_by(|&a, &b| {
        shapes[a]
            .cmp(&shapes[b])
            .then_with(|| {
                let (pa, pb) = (&g.def(members[a]).path, &g.def(members[b]).path);
                (**pa).cmp(&**pb)
            })
            .then(a.cmp(&b))
    });
    let mut h = Hasher::new(
        g,
        Itself::Group {
            members,
            order: Some(&order),
        },
        mode,
    );
    h.tag("group");
    h.usize(members.len());
    for &m in &order {
        declaration(&mut h, members[m])?;
    }
    let group = h.finish();
    for (index, &m) in order.iter().enumerate() {
        let mut h = Hasher::new(g, Itself::Def(members[m]), mode);
        h.tag("member");
        h.bytes(&group.0);
        h.usize(index);
        mode.cache(g)
            .borrow_mut()
            .insert(HashKey::Def(members[m]), h.finish());
    }
    Ok(())
}

/// Hashes every member of a final group of two or more data types, and
/// stores their hashes.
fn data_group_hashes(g: &Ev, members: &[DataId], mode: Mode) -> Result<()> {
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
        mode,
    );
    h.tag("data-group");
    h.usize(members.len());
    // The parameters and universe are the group's, shared by every member.
    h.sort(first.sort);
    h.usize(first.params.len());
    for (_, ty) in &first.params {
        h.term(ty)?;
    }
    h.auto_params(first);
    for &m in &order {
        let data = g.data(members[m]);
        h.tag("data");
        h.str(&data.path);
        h.no_eta(data);
        h.indices(data)?;
        h.ctors(data)?;
    }
    let group = h.finish();
    for (index, &m) in order.iter().enumerate() {
        let mut h = Hasher::new(g, Itself::Data(members[m]), mode);
        h.tag("data-member");
        h.bytes(&group.0);
        h.usize(index);
        mode.cache(g)
            .borrow_mut()
            .insert(HashKey::Data(members[m]), h.finish());
    }
    Ok(())
}

struct Hasher<'g> {
    g: &'g Ev<'g>,
    itself: Itself<'g>,
    mode: Mode,
    inner: blake3::Hasher,
    /// Whether a reference met a declaration that isn't final, hashed as
    /// zeros: the hash then doesn't say what that declaration is.
    unfinished: bool,
}

impl<'g> Hasher<'g> {
    fn new(g: &'g Ev<'g>, itself: Itself<'g>, mode: Mode) -> Self {
        Hasher {
            g,
            itself,
            mode,
            inner: blake3::Hasher::new(),
            unfinished: false,
        }
    }

    /// Definition `id` (final, with a body) as a whole: its kind, type and
    /// body. Without proofs, one whose result is a proof is its type alone.
    fn declaration(&mut self, id: DefId) -> Result<()> {
        let def = self.g.def(id);
        let body = def
            .body
            .as_ref()
            .expect("internal error: hashing a definition that isn't final");
        if self.mode == Mode::Proofless && self.proof_result(id) {
            self.tag("proof-def");
            self.bool(def.theorem);
            return self.term(&def.ty);
        }
        self.tag("def");
        self.bool(def.theorem);
        if def.instance {
            self.tag("instance");
        }
        self.opacity(def)?;
        self.term(&def.ty)?;
        self.term(body)
    }

    /// Whether definition `id`'s result is a proof. Conservatively not, if
    /// that isn't known.
    fn proof_result(&self, id: DefId) -> bool {
        crate::erase::proof_positions(self.g, id).is_some_and(|p| p.result)
    }

    /// Without proofs: whether `term` as a whole is a proof the hash leaves
    /// out (a call of a definition whose result is a proof, `Quot.ind`,
    /// `Quot.sound`).
    fn is_proof(&self, term: &Term) -> bool {
        if self.mode != Mode::Proofless {
            return false;
        }
        match spine_head(term).0 {
            Term::Def(id) => self.proof_result(*id),
            Term::Quot(QuotForm::Ind | QuotForm::Sound, _, _) => true,
            _ => false,
        }
    }

    /// Without proofs: whether the argument of application `app` is at a
    /// proof position of the definition at the head of its spine.
    fn proof_argument(&self, app: &Term) -> bool {
        if self.mode != Mode::Proofless {
            return false;
        }
        let (head, args) = spine_head(app);
        let Term::Def(id) = head else {
            return false;
        };
        crate::erase::proof_positions(self.g, *id)
            .is_some_and(|p| args > 0 && p.params.get(args - 1).copied().unwrap_or(false))
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
    /// change the JS (each field's default key) and, for records, which field
    /// `p.name` means (docs/proposals/records.md §12); the record flag
    /// because it changes the JS representation. The `js.*` attributes
    /// (the elaborator's `js` table) aren't hashed (D598, docs/proposals/attributes.md §6).
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
            // One per index, so none for a type without indices (whose hash
            // is unchanged).
            // Which fields are implicit, only when some are (a tag no term
            // starts with), so other constructors hash as before.
            if ctor.implicit.contains(&true) {
                self.tag("implicit");
                for i in &ctor.implicit {
                    self.bool(*i);
                }
            }
            // Declared with its fields in braces, only when so: such a
            // constructor reads braces after it differently.
            if ctor.braced {
                self.tag("braced");
            }
            for r in &ctor.result {
                self.term(r)?;
            }
        }
        Ok(())
    }

    /// Which of a data type's parameters are `auto`
    /// (docs/proposals/interfaces.md §7.5): nothing at all when none is, so
    /// other types hash as before.
    fn auto_params(&mut self, data: &Data) {
        if !data.auto_params.contains(&true) {
            return;
        }
        self.tag("auto");
        for a in &data.auto_params {
            self.bool(*a);
        }
    }

    /// Whether a data type is marked as having no eta (`check::mark_no_eta`):
    /// nothing at all when it isn't, so other types hash as before.
    fn no_eta(&mut self, data: &Data) {
        if data.no_eta {
            self.tag("no-eta");
        }
    }

    /// A data type's index telescope (docs/proposals/indexed-families.md
    /// §6.9): nothing at all for a type without indices, so its hash is
    /// what it was before indices existed.
    fn indices(&mut self, data: &Data) -> Result<()> {
        if data.indices.is_empty() {
            return Ok(());
        }
        self.tag("indices");
        self.usize(data.indices.len());
        for (_, ty) in &data.indices {
            self.term(ty)?;
        }
        Ok(())
    }

    /// Whether definition `def` is opaque, and if so its `unfolding` list as
    /// written (docs/proposals/opaque-definitions.md §6.6): each name as its
    /// declaration's hash (a group-mate is never listed), in the order of
    /// those hashes, once each. Nothing for a transparent definition, which
    /// has no list, so the hashes of those don't change.
    fn opacity(&mut self, def: &crate::globals::Def) -> Result<()> {
        if !def.opaque {
            return Ok(());
        }
        self.tag("opaque");
        let mut unfolded = Vec::new();
        for &id in def.unfolding.iter() {
            unfolded.push(def_hash_in(self.g, id, self.mode)?.map_or([0; 32], |h| h.0));
        }
        unfolded.sort_unstable();
        unfolded.dedup();
        self.usize(unfolded.len());
        for hash in &unfolded {
            self.bytes(hash);
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
                let hash = def_hash_in(self.g, id, self.mode)?;
                self.unfinished |= hash.is_none();
                // A stand-in for a declaration with an error is identified
                // by its statement alone, so editing the broken body
                // wouldn't change a key built from it: not final, like the
                // declaration it stands for.
                self.unfinished |= self
                    .g
                    .def(id)
                    .assumption()
                    .is_some_and(Assumption::is_error);
                let hash = hash.map_or([0; 32], |h| h.0);
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
                let hash = data_hash_in(self.g, id, self.mode)?;
                self.unfinished |= hash.is_none();
                let hash = hash.map_or([0; 32], |h| h.0);
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
            if self.is_proof(term) {
                self.tag("proof");
                continue;
            }
            // The parts of `term`, in order; reversed onto `pending` below.
            let first = pending.len();
            let proofless = self.mode == Mode::Proofless;
            // A part at a proof position, without proofs, is the marker.
            let part = |t, proof: bool| {
                if proof {
                    Item::Tag("proof")
                } else {
                    Item::Term(t)
                }
            };
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
                    pending.extend(args.iter().enumerate().map(|(k, t)| {
                        part(t, proofless && crate::value::proof_param(self.g, *d, k))
                    }));
                }
                Term::Ctor(d, c, args) => {
                    self.tag("ctor");
                    self.data_ref(*d)?;
                    self.usize(*c);
                    pending.push(Item::Usize(args.len()));
                    pending.extend(args.iter().enumerate().map(|(k, t)| {
                        part(t, proofless && crate::value::proof_field(self.g, *d, *c, k))
                    }));
                }
                // The value, and `Nat` itself, which the number stands for
                // (as `Chars` does for `List` and `Char`).
                Term::Nat(n) => {
                    let nat = self
                        .g
                        .env
                        .builtins()
                        .nat
                        .expect("internal error: a number without `Nat`");
                    self.tag("nat");
                    self.data_ref(nat)?;
                    self.nat(n);
                }
                // The logical contents (never the buffer or the offsets), and
                // `List` and `Char`, which the expansion refers to: through
                // `Char`'s fields, they cover `isScalar` too.
                Term::Chars(chars) => {
                    let text = self
                        .g
                        .env
                        .builtins()
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
                    pending.extend([Item::Term(f), part(a, self.proof_argument(term))]);
                }
                Term::Ann(e, t) => {
                    self.tag("ann");
                    pending.extend([Item::Term(e), Item::Term(t)]);
                }
                // The name isn't hashed, as for other binders.
                Term::Let(_, a, v, b, _) => {
                    self.tag("let");
                    pending.extend([Item::Term(a), Item::Term(v), Item::Term(b)]);
                }
                Term::Case(ix, d, branches) => {
                    self.tag("case");
                    self.usize(*ix);
                    self.data_ref(*d)?;
                    self.usize(branches.len());
                    // An impossible branch has no body, and is a tag no term
                    // starts with.
                    for b in branches.iter() {
                        pending.push(Item::Usize(b.names.len()));
                        pending.push(match &b.body {
                            Some(body) => Item::Term(body),
                            None => Item::Tag("impossible"),
                        });
                    }
                }
                // Every number, every arm and the default, and `Nat` itself
                // (as a `case` hashes its data type).
                Term::NumCase(ix, arms, default) => {
                    self.tag("numcase");
                    self.usize(*ix);
                    let nat = self
                        .g
                        .env
                        .builtins()
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
                    pending.extend([Item::Term(m), Item::Term(b), part(p, proofless)]);
                }
                Term::Proj(d, i, t) => {
                    self.tag("proj");
                    self.data_ref(*d)?;
                    self.usize(*i);
                    pending.push(Item::Term(t));
                }
                // Each form its own tag (so `Quot.ind` and `Quot.sound` with
                // the same arguments differ), then every argument, implicit
                // ones included. The erasure flag is determined by the rest
                // (the kernel recomputes it), so it isn't hashed, as for
                // `let`.
                // Without proofs, `Quot.lift`'s fifth argument (its proof
                // that the function respects the relation) is the marker.
                Term::Quot(form, args, _) => {
                    self.tag(quot_tag(*form));
                    pending.push(Item::Usize(args.len()));
                    pending.extend(
                        args.iter()
                            .enumerate()
                            .map(|(k, t)| part(t, proofless && *form == QuotForm::Lift && k == 4)),
                    );
                }
                Term::Meta(_) => panic!("internal error: hashing an unsolved metavariable"),
            }
            pending[first..].reverse();
        }
        Ok(())
    }
}

/// The head of `term`'s spine of applications, and how many arguments it's
/// applied to.
fn spine_head(term: &Term) -> (&Term, usize) {
    let mut term = term.strip_loc();
    let mut args = 0;
    while let Term::App(f, _, _) = term {
        args += 1;
        term = f.strip_loc();
    }
    (term, args)
}

/// The tag a quotient form is hashed with.
fn quot_tag(form: QuotForm) -> &'static str {
    match form {
        QuotForm::Type => "quot",
        QuotForm::Mk => "quot-mk",
        QuotForm::Lift => "quot-lift",
        QuotForm::Ind => "quot-ind",
        QuotForm::Sound => "quot-sound",
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;

    /// The hash of a closed term on its own.
    fn hash_term(term: &Term) -> ContentHash {
        let g = crate::globals::Kernel::default();
        let ev = g.ev();
        let mut h = Hasher::new(&ev, Itself::Def(DefId(usize::MAX)), Mode::Content);
        h.term(term).unwrap();
        h.finish()
    }

    fn args(n: usize) -> Vec<Rc<Term>> {
        (0..n)
            .map(|i| Rc::new(Term::Sort(Sort::Type(i as u32))))
            .collect()
    }

    /// A4: each form has its own tag, so two forms with the same arguments
    /// never hash alike (`Quot.ind` and `Quot.sound` take as many).
    #[test]
    fn quotient_forms_with_the_same_arguments_hash_differently() {
        let ind = hash_term(&Term::Quot(QuotForm::Ind, args(5), false));
        let sound = hash_term(&Term::Quot(QuotForm::Sound, args(5), false));
        assert_ne!(ind, sound);
        let hashes: Vec<ContentHash> = QuotForm::ALL
            .into_iter()
            .map(|f| hash_term(&Term::Quot(f, args(3), false)))
            .collect();
        for (i, a) in hashes.iter().enumerate() {
            for b in &hashes[i + 1..] {
                assert_ne!(a, b);
            }
        }
        // Every argument counts.
        let mut other = args(5);
        other[4] = Rc::new(Term::Sort(Sort::Prop));
        assert_ne!(ind, hash_term(&Term::Quot(QuotForm::Ind, other, false)));
    }

    /// A4: D921's erasure flag isn't hashed.
    #[test]
    fn the_erasure_flag_isnt_hashed() {
        for form in [QuotForm::Mk, QuotForm::Lift] {
            let n = form.arity();
            assert_eq!(
                hash_term(&Term::Quot(form, args(n), false)),
                hash_term(&Term::Quot(form, args(n), true))
            );
        }
    }
}
