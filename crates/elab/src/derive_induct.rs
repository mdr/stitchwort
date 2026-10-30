//! Induction principles and a size for a nested data type
//! (docs/proposals/nested-data-types.md §9, §10 stage 3; D1823): for `type
//! Packet = | Number (value: Nat) | Packets (items: List Packet)`,
//!
//! - `Packet.induct`, one case per constructor, where a field that holds
//!   the type inside a container gets the container's `All` of the motive as
//!   its hypothesis:
//!
//!   ```text
//!   theorem Packet.induct (motive: Packet → Prop)
//!       (number: (value: Nat) → motive (Number value))
//!       (packets: (items: List Packet) → List.All motive items → motive (Packets items)):
//!       (p: Packet) → motive p
//!   ```
//!
//!   A nesting composes: `List (Option T)` gives `List.All (Option.All
//!   motive) xs`, a pair `Pair.All motive (x => Unit)`. It's proved by a
//!   helper theorem for each container the type is in (`Packet.%m1%induct`,
//!   `(items: List Packet) → List.All motive items`), all defined together
//!   by recursion on the value, which termination accepts as it accepts
//!   `size`/`sizeList` (§6.4). Nothing is trusted: the kernel checks them.
//! - `Packet.inductMem`, when a field is a `List T` or an `Option T`
//!   itself: the same, with "every member" hypotheses, `(q: Packet) →
//!   List.Mem q items → motive q` (`o = Some q` for an option), from
//!   `induct` with `List.memOfAll` and `Option.memOfAll`.
//! - `Packet.size`, structural: one more than the sizes of the fields that
//!   hold the type, through a helper for each container (`Packet.%m1%size`,
//!   one more than the sizes of its own such fields, so `Cons y ys` is
//!   `Succ (size y + %m1%size ys)`). And for each field that's a `List T`
//!   itself, a lemma that a member is smaller than the node,
//!   `Packet.%Packets%0%sizeMem`, which `auto` uses for a `decreasing
//!   Packet.size p` obligation once a membership proof of the element is in
//!   scope, such as an `attach`ed element's `isIn` (`auto.rs`,
//!   `size_from_member`).
//! - `D.All` for a container `D` of the program declared in the same module
//!   (a definition by recursion, one predicate per nestable parameter, in
//!   the shape of `List.All`); for one declared elsewhere, the same under a
//!   hidden name in `T`'s namespace, `T.%D%All`.
//!
//! All are made as kernel terms (case trees), not as source: their types
//! need the fields' types, which source can't always name. Each generated
//! user-facing name (`T.size`, `T.induct`, `T.inductMem`, `D.All`) is
//! skipped if the program declares it itself; nothing that depends on it is
//! made then.
//!
//! Generated for a type in `Type` on its own (not defined together with
//! others) that holds itself inside `List`, `Option`, a pair, or a data type
//! on its own whose `All` can be made (one that isn't itself nested), at
//! any depth, with parameters and indices: the motive takes the indices.
//! Not for a proposition, for types defined together (`Expr`/`Stmt`), for a
//! type inside a member of a group (`Tree Big`, `Tree` and `Forest`), or for
//! a field that holds it inside a function's result: nothing is generated
//! for those.

use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::term::Branch;
use stitchwort_core::value::{conv, eval, quote};
use stitchwort_core::{DataId, DefId, Icit, Name, Sort, Term, Value};
use stitchwort_syntax::Diagnostic;

use crate::{Elaborator, Global, kernel};

/// Why generation stops: a shape it doesn't cover (nothing is generated),
/// or an error.
enum Stop {
    Unsupported,
    Error(Diagnostic),
}

impl From<Diagnostic> for Stop {
    fn from(d: Diagnostic) -> Stop {
        Stop::Error(d)
    }
}

impl From<stitchwort_core::budget::ResourceError> for Stop {
    fn from(e: stitchwort_core::budget::ResourceError) -> Stop {
        Stop::Error(e.into())
    }
}

type R<T> = std::result::Result<T, Stop>;

/// An extra binder for `member_pi`: its name, and its type built at the
/// depth it's given.
type Extra<'a> = (Name, &'a dyn Fn(usize) -> R<Term>);

/// An `Extra` that owns its type builder.
type OwnedExtra = (Name, Box<dyn Fn(usize) -> R<Term>>);

/// How a field's type holds the type being looked at (the *owner*: `T` for
/// its induction principle, a container `D` for its `All`), read from the
/// type in its generic context: the owner's parameters, then the earlier
/// fields. Terms are in that context.
#[derive(Clone)]
enum Shape {
    /// The owner's parameter `j` itself (only where parameters have
    /// predicates: a container's `All`).
    Param(usize),
    /// The owner again, with these indices.
    Rec(Vec<Term>),
    /// Inside container `data`, with these parameters and indices: for each
    /// of its parameters, how that argument holds the owner, if it does.
    In {
        data: DataId,
        params: Vec<Term>,
        subs: Vec<Option<Shape>>,
        indices: Vec<Term>,
    },
}

/// A predicate on the values of a type, with values in some context.
#[derive(Clone)]
enum Pred {
    /// Nothing to show: `x => Unit`.
    Unit,
    /// The variable at this level: a predicate parameter of an `All`.
    Var(usize),
    /// `motive is…`.
    Motive(Vec<Value>),
    /// `D.All [params] preds… [indices]`.
    All {
        all: DefId,
        data: DataId,
        params: Vec<Value>,
        preds: Vec<Pred>,
        indices: Vec<Value>,
    },
}

impl Pred {
    /// Whether it says anything about the type being inducted on.
    fn involves_motive(&self) -> bool {
        match self {
            Pred::Unit | Pred::Var(_) => false,
            Pred::Motive(_) => true,
            Pred::All { preds, .. } => preds.iter().any(Pred::involves_motive),
        }
    }
}

/// What the owner of a [`Shape`] reads as itself (`Shape::Rec`).
enum Me {
    Motive,
    All {
        all: DefId,
        data: DataId,
        params: Vec<Value>,
        preds: Vec<Pred>,
    },
}

/// A container instance `T` is in, with the predicate its `All` gets: one
/// helper each (`T.%m1%induct`, `T.%m1%size`). Values are in the member's
/// context, `T`'s parameters and then `scope`'s fields.
struct Member {
    data: DataId,
    all: DefId,
    params: Vec<Value>,
    preds: Vec<Pred>,
    /// When its type mentions fields of a constructor of `T` (`List (Ranked
    /// n)`): that constructor, and how many of its first fields the helpers
    /// take (all those before the field it came from).
    scope: Option<(usize, usize)>,
}

impl Member {
    fn scope_len(&self) -> usize {
        self.scope.map_or(0, |(_, n)| n)
    }
}

/// A user-facing generated name, or a hidden one.
const INDUCT: &str = "induct";
const INDUCT_MEM: &str = "inductMem";
const SIZE: &str = "size";

/// The library's declarations the generated terms use.
struct Lib {
    unit: DataId,
    and: DataId,
    nat: DataId,
    void: DataId,
    or: DataId,
    list: DataId,
    option: DataId,
    pair: DataId,
    add: DefId,
    less_than: DefId,
    less_eq: DefId,
    le_refl: DefId,
    less_le: DefId,
    add_left: DefId,
    add_right: DefId,
    list_mem: DefId,
    list_all: DefId,
    option_all: DefId,
    pair_all: DefId,
    list_mem_of_all: DefId,
    option_mem_of_all: DefId,
}

/// The state of one type's generation.
struct Gen {
    d: DataId,
    np: usize,
    lib: Lib,
    /// Each constructor's fields' shapes (`None`: it doesn't hold `T`).
    shapes: Vec<Vec<Option<Shape>>>,
    members: Vec<Member>,
    /// The `All`s made for containers of the program, by data type.
    alls: Vec<(DataId, DefId)>,
    /// The sizes, once defined, for their lemmas.
    sizes: Option<Sizes>,
    /// `T.induct`, once defined, for `T.inductMem`.
    induct: Option<DefId>,
}

fn var(depth: usize, level: usize) -> Term {
    Term::Var(depth - 1 - level)
}

fn vars(range: std::ops::Range<usize>) -> Vec<Value> {
    range.map(Value::var).collect()
}

fn apps(head: Term, args: impl IntoIterator<Item = (Term, Icit)>) -> Term {
    args.into_iter()
        .fold(head, |f, (a, icit)| Term::app_icit(f, a, icit))
}

fn implicit(args: Vec<Term>) -> Vec<(Term, Icit)> {
    args.into_iter().map(|a| (a, Icit::Implicit)).collect()
}

fn explicit(args: Vec<Term>) -> Vec<(Term, Icit)> {
    args.into_iter().map(|a| (a, Icit::Explicit)).collect()
}

fn pi(x: &str, icit: Icit, dom: Term, cod: Term) -> Term {
    Term::Pi(x.into(), icit, Rc::new(dom), Rc::new(cod))
}

fn lam(x: &str, icit: Icit, body: Term) -> Term {
    Term::Lam(x.into(), icit, Rc::new(body))
}

/// Whether `term`, in a context of `depth` variables, mentions a variable
/// at level `lo` or later, or data type `d`.
fn mentions(term: &Term, depth: usize, lo: usize, d: Option<DataId>) -> bool {
    term.subterms().any(|(t, under)| match t {
        Term::Var(ix) | Term::Case(ix, ..) | Term::NumCase(ix, ..) => {
            *ix >= under && depth + under - 1 - ix >= lo && *ix - under < depth
        }
        Term::Data(e, _) | Term::Ctor(e, _, _) => Some(*e) == d,
        _ => false,
    })
}

/// Whether `term`, in a context of `depth` variables, mentions a variable at
/// a level in `levels`.
fn mentions_level(term: &Term, depth: usize, wanted: &dyn Fn(usize) -> bool) -> bool {
    term.subterms().any(|(t, under)| match t {
        Term::Var(ix) => *ix >= under && wanted(depth + under - 1 - ix),
        _ => false,
    })
}

impl Elaborator {
    /// After data type `d` is admitted: its induction principles and size,
    /// if it's nested (module header).
    pub(crate) fn derive_nested(&mut self, d: DataId) -> crate::Result<()> {
        if self.loading_prelude {
            return Ok(());
        }
        let data = self.globals.data(d);
        if data.group.len() != 1 || data.sort != Sort::Type(0) || data.ctors.is_empty() {
            return Ok(());
        }
        let Some(lib) = self.nested_lib() else {
            return Ok(());
        };
        let mut st = Gen {
            d,
            np: data.params.len(),
            lib,
            shapes: Vec::new(),
            members: Vec::new(),
            alls: Vec::new(),
            sizes: None,
            induct: None,
        };
        match self.derive_nested_in(&mut st) {
            Ok(()) | Err(Stop::Unsupported) => Ok(()),
            Err(Stop::Error(e)) if e.code == "E-RESOURCE" => Err(e),
            Err(Stop::Error(e)) => {
                let name = self.globals.data(d).name.to_string();
                Err(Diagnostic::error(
                    "E-INTERNAL",
                    format!(
                        "internal error: the induction principle generated for `{name}` was refused: {}",
                        e.message
                    ),
                )
                .with_label(self.globals.data(d).span, "generated for this type")
                .with_note(
                    "this is a bug in the compiler (docs/proposals/nested-data-types.md, stage 3)",
                ))
            }
        }
    }

    /// The declarations the generated terms use, once the core has them.
    fn nested_lib(&self) -> Option<Lib> {
        let reg = &self.globals.registry;
        let def = |name: &str| match self.named(name) {
            Some((Global::Def(id), _)) => Some(*id),
            _ => None,
        };
        Some(Lib {
            unit: reg.data(Builtin::Unit)?,
            and: reg.data(Builtin::And)?,
            nat: reg.data(Builtin::Nat)?,
            void: reg.data(Builtin::Void)?,
            or: reg.data(Builtin::Or)?,
            list: reg.data(Builtin::List)?,
            option: reg.data(Builtin::Option)?,
            pair: reg.data(Builtin::Pair)?,
            add: reg.def(Builtin::Add)?,
            less_than: reg.def(Builtin::LessThan)?,
            less_eq: reg.def(Builtin::LessEq)?,
            le_refl: reg.def(Builtin::LeRefl)?,
            less_le: def("Std.Nat.lessLe")?,
            add_left: def("Std.Nat.leAddOfLeLeft")?,
            add_right: def("Std.Nat.leAddOfLeRight")?,
            list_mem: def("Std.List.Mem")?,
            list_all: def("Std.List.All")?,
            option_all: def("Std.Option.All")?,
            pair_all: def("Std.Pair.All")?,
            list_mem_of_all: def("Std.List.memOfAll")?,
            option_mem_of_all: def("Std.Option.memOfAll")?,
        })
    }

    fn derive_nested_in(&mut self, st: &mut Gen) -> R<()> {
        let d = st.d;
        let np = st.np;
        // How each field holds `T`.
        let ctor_count = self.globals.data(d).ctors.len();
        let nestable_t = self.view(d, false);
        let mut nested = false;
        for c in 0..ctor_count {
            let fields = self.globals.data(d).ctors[c].fields.len();
            let mut row = Vec::new();
            for i in 0..fields {
                if self.globals.data(d).ctors[c].field_erased[i] {
                    row.push(None);
                    continue;
                }
                let ty = self.field_type(d, c, i)?;
                let shape = self.classify(d, &nestable_t, &ty, np + i)?;
                nested |= matches!(shape, Some(Shape::In { .. }));
                row.push(shape);
            }
            st.shapes.push(row);
        }
        if !nested {
            return Ok(());
        }
        // The containers, from each field that holds `T` inside one, and
        // then from theirs.
        for c in 0..ctor_count {
            for i in 0..st.shapes[c].len() {
                let Some(shape) = st.shapes[c][i].clone() else {
                    continue;
                };
                let env = vars(0..np + i);
                let pred = self.inst(st, &shape, &env, &[], &Me::Motive)?;
                if let Pred::All { .. } = pred {
                    let scope = Some((c, i));
                    self.add_member(st, &pred, scope, np + i)?;
                }
            }
        }
        let mut next = 0;
        while next < st.members.len() {
            self.member_parts(st, next)?;
            next += 1;
        }
        let size = !self.has_member(d, SIZE);
        let induct = !self.has_member(d, INDUCT);
        if size {
            self.define_sizes(st)?;
            self.define_size_lemmas(st)?;
        }
        if induct {
            self.define_inducts(st)?;
            if !self.has_member(d, INDUCT_MEM) {
                self.define_induct_mem(st)?;
            }
        }
        Ok(())
    }

    /// Which of `d`'s parameters get a predicate in its `All` (`preds`):
    /// the nestable ones that are types.
    fn view(&self, d: DataId, preds: bool) -> Vec<bool> {
        let data = self.globals.data(d);
        data.params
            .iter()
            .enumerate()
            .map(|(j, (_, ty))| {
                preds
                    && data.nestable.get(j).is_some_and(|n| n.is_ok())
                    && matches!(ty.strip_loc(), Term::Sort(Sort::Type(0)))
            })
            .collect()
    }

    /// Field `i` of constructor `c` of `d`, its type in normal form in the
    /// generic context (parameters, then the earlier fields).
    fn field_type(&self, d: DataId, c: usize, i: usize) -> R<Term> {
        let g = &self.globals;
        let data = g.data(d);
        let depth = data.params.len() + i;
        let value = eval(g, &vars(0..depth), &data.ctors[c].fields[i].1)?;
        Ok(quote(g, depth, &value)?)
    }

    /// How `ty` (in a context of `depth` variables, `owner`'s parameters
    /// first) holds `owner`, with `preds` saying which parameters count.
    fn classify(&self, owner: DataId, preds: &[bool], ty: &Term, depth: usize) -> R<Option<Shape>> {
        let g = &self.globals;
        let np = g.data(owner).params.len();
        let counted = |l: usize| l < np && preds[l];
        let relevant =
            |t: &Term| mentions(t, depth, depth, Some(owner)) || mentions_level(t, depth, &counted);
        let ty = ty.strip_loc();
        match ty {
            Term::Var(ix) if counted(depth - 1 - ix) => Ok(Some(Shape::Param(depth - 1 - ix))),
            Term::Data(e, args) if *e == owner => {
                // A nested occurrence is at the owner's own parameters.
                for (j, a) in args.iter().take(np).enumerate() {
                    if !matches!(a.strip_loc(), Term::Var(ix) if depth - 1 - ix == j) {
                        return Err(Stop::Unsupported);
                    }
                }
                let indices: Vec<Term> = args[np..].iter().map(|a| (**a).clone()).collect();
                if indices.iter().any(relevant) {
                    return Err(Stop::Unsupported);
                }
                Ok(Some(Shape::Rec(indices)))
            }
            Term::Data(e, args) => {
                if !relevant(ty) {
                    return Ok(None);
                }
                let inner = g.data(*e);
                let ne = inner.params.len();
                if inner.group.len() != 1 || inner.sort != Sort::Type(0) {
                    return Err(Stop::Unsupported);
                }
                let can = self.view(*e, true);
                let mut subs = Vec::new();
                for (j, a) in args.iter().take(ne).enumerate() {
                    if can[j] {
                        subs.push(self.classify(owner, preds, a, depth)?);
                    } else if relevant(a) {
                        return Err(Stop::Unsupported);
                    } else {
                        subs.push(None);
                    }
                }
                let indices: Vec<Term> = args[ne..].iter().map(|a| (**a).clone()).collect();
                if indices.iter().any(relevant) {
                    return Err(Stop::Unsupported);
                }
                if subs.iter().all(Option::is_none) {
                    return Err(Stop::Unsupported);
                }
                Ok(Some(Shape::In {
                    data: *e,
                    params: args[..ne].iter().map(|a| (**a).clone()).collect(),
                    subs,
                    indices,
                }))
            }
            _ if relevant(ty) => Err(Stop::Unsupported),
            _ => Ok(None),
        }
    }

    /// `shape` read in a context whose generic variables are `env`, with
    /// `params` the predicates of the owner's parameters and `me` what the
    /// owner itself is.
    fn inst(
        &mut self,
        st: &mut Gen,
        shape: &Shape,
        env: &[Value],
        params: &[Pred],
        me: &Me,
    ) -> R<Pred> {
        let g = &self.globals;
        let ev = |ts: &[Term]| -> R<Vec<Value>> {
            ts.iter()
                .map(|t| Ok(eval(g, env, t)?))
                .collect::<R<Vec<Value>>>()
        };
        Ok(match shape {
            Shape::Param(j) => params[*j].clone(),
            Shape::Rec(indices) => {
                let indices = ev(indices)?;
                match me {
                    Me::Motive => Pred::Motive(indices),
                    Me::All {
                        all,
                        data,
                        params,
                        preds,
                    } => Pred::All {
                        all: *all,
                        data: *data,
                        params: params.clone(),
                        preds: preds.clone(),
                        indices,
                    },
                }
            }
            Shape::In {
                data,
                params: ps,
                subs,
                indices,
            } => {
                let ps = ev(ps)?;
                let indices = ev(indices)?;
                let all = self.all_of(st, *data)?;
                let mut preds = Vec::new();
                for sub in subs {
                    preds.push(match sub {
                        Some(s) => self.inst(st, s, env, params, me)?,
                        None => Pred::Unit,
                    });
                }
                Pred::All {
                    all,
                    data: *data,
                    params: ps,
                    preds,
                    indices,
                }
            }
        })
    }

    /// Records the container `pred` (an `All`, with values in a context of
    /// `depth` variables: `T`'s parameters, then `scope`'s fields) as a
    /// member, if it isn't one: its index.
    fn add_member(
        &mut self,
        st: &mut Gen,
        pred: &Pred,
        scope: Option<(usize, usize)>,
        depth: usize,
    ) -> R<usize> {
        let Pred::All {
            all,
            data,
            params,
            preds,
            ..
        } = pred
        else {
            unreachable!("a member is a container")
        };
        let np = st.np;
        // Only the scope's fields, if any: not `T`'s fields after them, nor
        // the container's own (a container's parameter that depends on its
        // own fields isn't covered).
        let g = &self.globals;
        let probe = Pred::All {
            all: *all,
            data: *data,
            params: params.clone(),
            preds: preds.clone(),
            indices: Vec::new(),
        };
        let mut highest = None;
        self.pred_levels(&probe, depth, &mut |l| {
            highest = Some(highest.map_or(l, |h: usize| h.max(l)));
        })?;
        let scope = match (highest, scope) {
            (Some(l), Some((c, n))) if l >= np => {
                if l >= np + n {
                    return Err(Stop::Unsupported);
                }
                Some((c, n))
            }
            _ => None,
        };
        let level = np + scope.map_or(0, |(_, n)| n);
        for (m, member) in st.members.iter().enumerate() {
            if member.data == *data
                && member.scope == scope
                && member.params.len() == params.len()
                && pred_eq_all(g, level, &member.params, params)?
                && preds_eq(g, level, &member.preds, preds)?
            {
                return Ok(m);
            }
        }
        st.members.push(Member {
            data: *data,
            all: *all,
            params: params.clone(),
            preds: preds.clone(),
            scope,
        });
        Ok(st.members.len() - 1)
    }

    /// Calls `found` with each variable level `pred`'s values mention.
    fn pred_levels(&self, pred: &Pred, depth: usize, found: &mut dyn FnMut(usize)) -> R<()> {
        let g = &self.globals;
        let value = |v: &Value, found: &mut dyn FnMut(usize)| -> R<()> {
            let t = quote(g, depth, v)?;
            for (s, under) in t.subterms() {
                if let Term::Var(ix) = s
                    && *ix >= under
                {
                    found(depth + under - 1 - ix);
                }
            }
            Ok(())
        };
        match pred {
            Pred::Unit => {}
            Pred::Var(l) => found(*l),
            Pred::Motive(is) => {
                for v in is {
                    value(v, found)?;
                }
            }
            Pred::All {
                params,
                preds,
                indices,
                ..
            } => {
                for v in params.iter().chain(indices) {
                    value(v, found)?;
                }
                for p in preds {
                    self.pred_levels(p, depth, found)?;
                }
            }
        }
        Ok(())
    }

    /// The members member `m`'s constructors' fields are in, recorded.
    fn member_parts(&mut self, st: &mut Gen, m: usize) -> R<()> {
        let (data, scope) = (st.members[m].data, st.members[m].scope);
        let base = st.np + st.members[m].scope_len();
        let ctors = self.globals.data(data).ctors.len();
        for c in 0..ctors {
            let parts = self.member_fields_preds(st, m, c, base)?;
            for pred in parts.into_iter().flatten() {
                if let Pred::All { .. } = pred {
                    let depth = base + self.globals.data(data).ctors[c].fields.len();
                    self.add_member(st, &pred, scope, depth)?;
                }
            }
        }
        Ok(())
    }

    /// For constructor `c` of member `m`'s container, each field's
    /// predicate in its `All` (`None` where it has none), with the fields
    /// bound at levels `base…`.
    fn member_fields_preds(
        &mut self,
        st: &mut Gen,
        m: usize,
        c: usize,
        base: usize,
    ) -> R<Vec<Option<Pred>>> {
        let data = st.members[m].data;
        let ne = self.globals.data(data).params.len();
        let view = self.view(data, true);
        let fields = self.globals.data(data).ctors[c].fields.len();
        let params = st.members[m].params.clone();
        let preds = st.members[m].preds.clone();
        let me = Me::All {
            all: st.members[m].all,
            data,
            params: params.clone(),
            preds: preds.clone(),
        };
        let mut out = Vec::new();
        for i in 0..fields {
            if self.globals.data(data).ctors[c].field_erased[i] {
                out.push(None);
                continue;
            }
            let ty = self.field_type(data, c, i)?;
            let Some(shape) = self.classify(data, &view, &ty, ne + i)? else {
                out.push(None);
                continue;
            };
            let env: Vec<Value> = params
                .iter()
                .cloned()
                .chain((0..i).map(|k| Value::var(base + k)))
                .collect();
            out.push(Some(self.inst(st, &shape, &env, &preds, &me)?));
        }
        Ok(out)
    }

    /// The `All` of container `e`: the library's for `List`, `Option` and
    /// pairs, else one generated (`D.All`, or `T.%D%All`).
    fn all_of(&mut self, st: &mut Gen, e: DataId) -> R<DefId> {
        let lib = &st.lib;
        if e == lib.list {
            return Ok(lib.list_all);
        }
        if e == lib.option {
            return Ok(lib.option_all);
        }
        if e == lib.pair {
            return Ok(lib.pair_all);
        }
        if let Some((_, id)) = st.alls.iter().find(|(x, _)| *x == e) {
            return Ok(*id);
        }
        if let Some(id) = self.generated_alls.get(&e) {
            return Ok(*id);
        }
        let data = self.globals.data(e);
        if data.group.len() != 1 || data.sort != Sort::Type(0) {
            return Err(Stop::Unsupported);
        }
        let ours = !data.path.starts_with("Std.") && data.defs_before >= self.module.first_def;
        let (owner, member) = if ours && !self.has_member(e, "All") {
            (e, "All".to_string())
        } else {
            (st.d, format!("%{}%All", data.name))
        };
        let id = self.define_all(st, e, owner, &member)?;
        if owner == e {
            self.generated_alls.insert(e, id);
        }
        Ok(id)
    }

    /// `D.All [params] (p…) [indices] (x: D params indices): Prop`, by
    /// recursion on `x`: each constructor's fields' predicates, joined by
    /// `And` (`Unit` for none), as `List.All` is written.
    fn define_all(&mut self, st: &mut Gen, e: DataId, owner: DataId, member: &str) -> R<DefId> {
        let data = self.globals.data(e);
        let np = data.params.len();
        let ni = data.indices.len();
        let view = self.view(e, true);
        let preds: Vec<usize> = (0..np).filter(|j| view[*j]).collect();
        let names = ["p", "q", "r", "s", "t", "u", "v", "w"];
        if preds.len() > names.len() {
            return Err(Stop::Unsupported);
        }
        // Each constructor's fields' shapes, checked before anything is
        // declared: a container that's nested itself isn't covered.
        let ctors = data.ctors.len();
        let mut shapes = Vec::new();
        for c in 0..ctors {
            let mut row = Vec::new();
            for i in 0..self.globals.data(e).ctors[c].fields.len() {
                if self.globals.data(e).ctors[c].field_erased[i] {
                    row.push(None);
                    continue;
                }
                let ty = self.field_type(e, c, i)?;
                let shape = self.classify(e, &view, &ty, np + i)?;
                if let Some(Shape::In { subs, .. }) = &shape
                    && subs.iter().flatten().any(has_rec)
                {
                    return Err(Stop::Unsupported);
                }
                row.push(shape);
            }
            shapes.push(row);
        }
        let g = &self.globals;
        let data = g.data(e);
        // [params] (p: a → Prop)… [indices] (x: D params indices) → Prop
        let pred_level = |k: usize| np + k;
        let x_level = np + preds.len() + ni;
        let mut ty = Term::Sort(Sort::Prop);
        {
            let depth = x_level;
            let mut args: Vec<Term> = (0..np).map(|j| var(depth, j)).collect();
            args.extend((0..ni).map(|k| var(depth, np + preds.len() + k)));
            ty = pi("x", Icit::Explicit, Term::data(e, args), ty);
        }
        let index_env = |k: usize| -> Vec<Value> {
            (0..np)
                .map(Value::var)
                .chain((0..k).map(|j| Value::var(np + preds.len() + j)))
                .collect()
        };
        for k in (0..ni).rev() {
            let value = eval(g, &index_env(k), &data.indices[k].1)?;
            let dom = quote(g, np + preds.len() + k, &value)?;
            ty = pi(&data.indices[k].0, Icit::Implicit, dom, ty);
        }
        for (k, &j) in preds.iter().enumerate().rev() {
            let depth = np + k;
            let dom = pi("x", Icit::Explicit, var(depth, j), Term::Sort(Sort::Prop));
            ty = pi(names[k], Icit::Explicit, dom, ty);
        }
        for (x, t) in data.params.iter().rev() {
            ty = pi(x, Icit::Implicit, t.clone(), ty);
        }
        let name: Name = format!("{}.{member}", g.data(owner).name).into();
        let span = g.data(st.d).span;
        let id = kernel::declare_def(&mut self.globals, &name, &ty, false, false, span)?;
        // The body.
        let params_v = vars(0..np);
        let mut pred_of_param = vec![Pred::Unit; np];
        for (k, &j) in preds.iter().enumerate() {
            pred_of_param[j] = Pred::Var(pred_level(k));
        }
        let me = Me::All {
            all: id,
            data: e,
            params: params_v.clone(),
            preds: pred_of_param.clone(),
        };
        st.alls.push((e, id));
        let depth0 = x_level + 1;
        let mut branches = Vec::new();
        for (c, row) in shapes.iter().enumerate() {
            let ctor = &self.globals.data(e).ctors[c];
            let names: Vec<Name> = ctor.fields.iter().map(|(x, _)| x.clone()).collect();
            let depth = depth0 + names.len();
            let mut parts = Vec::new();
            for (i, shape) in row.iter().enumerate() {
                let Some(shape) = shape else { continue };
                let env: Vec<Value> = params_v
                    .iter()
                    .cloned()
                    .chain((0..i).map(|k| Value::var(depth0 + k)))
                    .collect();
                let pred = self.inst(st, shape, &env, &pred_of_param, &me)?;
                parts.push(self.apply_pred(st, &pred, var(depth, depth0 + i), depth, None)?);
            }
            branches.push(Branch {
                names,
                body: Some(Rc::new(self.conjunction(st, parts))),
            });
        }
        let mut body = Term::Case(0, e, branches.into());
        body = lam("x", Icit::Explicit, body);
        for k in (0..ni).rev() {
            body = lam(&self.globals.data(e).indices[k].0, Icit::Implicit, body);
        }
        for k in (0..preds.len()).rev() {
            body = lam(names_at(k), Icit::Explicit, body);
        }
        for (x, _) in self.globals.data(e).params.iter().rev() {
            body = lam(x, Icit::Implicit, body);
        }
        kernel::define_group(&mut self.globals, &[(id, body)])?;
        self.bind_generated(owner, member, id);
        Ok(id)
    }

    /// Makes `T.member` name `id`.
    fn bind_generated(&mut self, owner: DataId, member: &str, id: DefId) {
        let key = Self::member_key(&self.data_key(owner), member);
        let span = self.globals.data(owner).span;
        self.scope.insert(&key, Global::Def(id), span, false);
    }

    /// `And a (And b …)`, or `Unit` for none.
    fn conjunction(&self, st: &Gen, parts: Vec<Term>) -> Term {
        let mut parts = parts;
        let Some(last) = parts.pop() else {
            return Term::data(st.lib.unit, Vec::new());
        };
        parts
            .into_iter()
            .rev()
            .fold(last, |rest, p| Term::data(st.lib.and, vec![p, rest]))
    }

    /// The proof of `And a (And b …)` from the parts' proofs (`Trivial`
    /// for none).
    fn both(&self, st: &Gen, parts: Vec<Term>) -> Term {
        let mut parts = parts;
        let Some(last) = parts.pop() else {
            return Term::ctor(st.lib.unit, 0, Vec::new());
        };
        parts
            .into_iter()
            .rev()
            .fold(last, |rest, p| Term::ctor(st.lib.and, 0, vec![p, rest]))
    }

    /// The predicate as a function, in a context of `depth` variables with
    /// the motive at level `motive`.
    fn pred_term(&self, st: &Gen, pred: &Pred, depth: usize, motive: Option<usize>) -> R<Term> {
        let g = &self.globals;
        Ok(match pred {
            Pred::Unit => lam("x", Icit::Explicit, Term::data(st.lib.unit, Vec::new())),
            Pred::Var(l) => var(depth, *l),
            Pred::Motive(is) => {
                let mut args = Vec::new();
                for v in is {
                    args.push(quote(g, depth, v)?);
                }
                apps(var(depth, motive.expect("a motive")), explicit(args))
            }
            Pred::All {
                all,
                params,
                preds,
                indices,
                ..
            } => {
                let mut t = Term::Def(*all);
                for v in params {
                    t = Term::app_icit(t, quote(g, depth, v)?, Icit::Implicit);
                }
                let view = self.view(pred_data(pred), true);
                for (j, p) in preds.iter().enumerate() {
                    if view[j] {
                        t = Term::app(t, self.pred_term(st, p, depth, motive)?);
                    }
                }
                for v in indices {
                    t = Term::app_icit(t, quote(g, depth, v)?, Icit::Implicit);
                }
                t
            }
        })
    }

    /// The proposition `pred arg`.
    fn apply_pred(
        &self,
        st: &Gen,
        pred: &Pred,
        arg: Term,
        depth: usize,
        motive: Option<usize>,
    ) -> R<Term> {
        Ok(match pred {
            Pred::Unit => Term::data(st.lib.unit, Vec::new()),
            _ => Term::app(self.pred_term(st, pred, depth, motive)?, arg),
        })
    }

    // ------------------------------------------------------------- size

    /// `T.size` and each member's `T.%m{m}%size`, defined together.
    fn define_sizes(&mut self, st: &mut Gen) -> R<()> {
        let d = st.d;
        let np = st.np;
        let g = &self.globals;
        let data = g.data(d);
        let ni = data.indices.len();
        let nat = Term::data(st.lib.nat, Vec::new());
        let span = data.span;
        // T.size : [params] → [indices] → (x: T params indices) → Nat
        let mut ty = nat.clone();
        ty = pi(
            "x",
            Icit::Explicit,
            self.self_type(st, np, ni, np + ni)?,
            ty,
        );
        ty = self.wrap_indices_pi(st, d, np, ty)?;
        ty = self.wrap_params_pi(d, ty);
        let name: Name = format!("{}.{SIZE}", data.name).into();
        let size_id = kernel::declare_def(&mut self.globals, &name, &ty, false, false, span)?;
        let sized: Vec<usize> = (0..st.members.len())
            .filter(|m| st.members[*m].preds.iter().any(Pred::involves_motive))
            .collect();
        let mut member_ids = vec![None; st.members.len()];
        for &m in &sized {
            let ty = self.member_size_type(st, m)?;
            let name: Name = format!("{}.%m{}%{SIZE}", self.globals.data(d).name, m + 1).into();
            let id = kernel::declare_def(&mut self.globals, &name, &ty, false, false, span)?;
            member_ids[m] = Some(id);
        }
        let sizes = Sizes {
            size: size_id,
            members: member_ids,
        };
        // T.size's body.
        let mut bodies = Vec::new();
        {
            let depth0 = np + ni + 1;
            let mut branches = Vec::new();
            for c in 0..self.globals.data(d).ctors.len() {
                let names = self.ctor_names(d, c);
                let depth = depth0 + names.len();
                let mut parts = Vec::new();
                for i in 0..names.len() {
                    let Some(shape) = st.shapes[c][i].clone() else {
                        continue;
                    };
                    let env: Vec<Value> = vars(0..np)
                        .into_iter()
                        .chain((0..i).map(|k| Value::var(depth0 + k)))
                        .collect();
                    let pred = self.inst(st, &shape, &env, &[], &Me::Motive)?;
                    if pred.involves_motive() {
                        let f = Field {
                            ctor: c,
                            field_levels: (0..names.len()).map(|k| depth0 + k).collect(),
                        };
                        parts.push(self.size_of(
                            st,
                            &sizes,
                            &pred,
                            depth0 + i,
                            depth,
                            Some(&f),
                            &[],
                        )?);
                    }
                }
                branches.push(Branch {
                    names,
                    body: Some(Rc::new(self.succ_sum(st, parts))),
                });
            }
            let body = Term::Case(0, d, branches.into());
            let body = self.wrap_lams(d, ni, None, body);
            bodies.push((size_id, body));
        }
        for &m in &sized {
            let body = self.member_size_body(st, &sizes, m)?;
            bodies.push((sizes.members[m].expect("declared"), body));
        }
        kernel::define_group(&mut self.globals, &bodies)?;
        self.bind_generated(d, SIZE, size_id);
        for &m in &sized {
            let member = format!("%m{}%{SIZE}", m + 1);
            self.bind_generated(d, &member, sizes.members[m].expect("declared"));
        }
        st.sizes = Some(sizes);
        Ok(())
    }

    /// The constructor's fields' names.
    fn ctor_names(&self, d: DataId, c: usize) -> Vec<Name> {
        self.globals.data(d).ctors[c]
            .fields
            .iter()
            .map(|(x, _)| x.clone())
            .collect()
    }

    /// `T params indices`, with the parameters at levels `0..np` and the
    /// indices at `first..first + ni`, in a context of `depth` variables.
    fn self_type(&self, st: &Gen, first: usize, ni: usize, depth: usize) -> R<Term> {
        let mut args: Vec<Term> = (0..st.np).map(|j| var(depth, j)).collect();
        args.extend((0..ni).map(|k| var(depth, first + k)));
        Ok(Term::data(st.d, args))
    }

    /// `[indices…] → rest`, the indices' types with `d`'s parameters at
    /// levels `0..np` and the first index at `first`; `rest` is under them.
    fn wrap_indices_pi(&self, st: &Gen, d: DataId, first: usize, rest: Term) -> R<Term> {
        let g = &self.globals;
        let data = g.data(d);
        let np = st.np;
        let mut ty = rest;
        for k in (0..data.indices.len()).rev() {
            let env: Vec<Value> = vars(0..np)
                .into_iter()
                .chain((0..k).map(|j| Value::var(first + j)))
                .collect();
            let value = eval(g, &env, &data.indices[k].1)?;
            let dom = quote(g, first + k, &value)?;
            ty = pi(&data.indices[k].0, Icit::Implicit, dom, ty);
        }
        Ok(ty)
    }

    /// `[params…] → ty`.
    fn wrap_params_pi(&self, d: DataId, ty: Term) -> Term {
        let mut ty = ty;
        for (x, t) in self.globals.data(d).params.iter().rev() {
            ty = pi(x, Icit::Implicit, t.clone(), ty);
        }
        ty
    }

    /// `[params…] (extra…) [indices…] (x) => body`: lambdas for a
    /// definition over `d` (or a container's indices, `ni`), with `extra`
    /// explicit binders between.
    fn wrap_lams(&self, d: DataId, ni: usize, extra: Option<&[Name]>, body: Term) -> Term {
        let mut body = lam("x", Icit::Explicit, body);
        for k in (0..ni).rev() {
            body = lam(&self.globals.data(d).indices[k].0, Icit::Implicit, body);
        }
        if let Some(extra) = extra {
            for x in extra.iter().rev() {
                body = lam(x, Icit::Explicit, body);
            }
        }
        for (x, _) in self.globals.data(d).params.iter().rev() {
            body = lam(x, Icit::Implicit, body);
        }
        body
    }

    /// `Succ (a + (b + …))`, or `1` for none.
    fn succ_sum(&self, st: &Gen, parts: Vec<Term>) -> Term {
        Term::ctor(st.lib.nat, 1, vec![self.sum(st, &parts)])
    }

    fn sum(&self, st: &Gen, parts: &[Term]) -> Term {
        match parts {
            [] => Term::Nat(Rc::new(0u32.into())),
            [last] => last.clone(),
            [first, rest @ ..] => apps(
                Term::Def(st.lib.add),
                explicit(vec![first.clone(), self.sum(st, rest)]),
            ),
        }
    }

    /// The size of the value at level `at` with predicate `pred` (one that
    /// involves `T`), in a context of `depth` variables. `here` gives `T`'s
    /// constructor's fields when that's the context (for a member's scope);
    /// otherwise `scope_levels` are the levels of the current scope's fields.
    #[allow(clippy::too_many_arguments)]
    fn size_of(
        &self,
        st: &Gen,
        sizes: &Sizes,
        pred: &Pred,
        at: usize,
        depth: usize,
        here: Option<&Field>,
        scope_levels: &[usize],
    ) -> R<Term> {
        let g = &self.globals;
        let np = st.np;
        let ps: Vec<Term> = (0..np).map(|j| var(depth, j)).collect();
        Ok(match pred {
            Pred::Motive(is) => {
                let mut args = implicit(ps);
                for v in is {
                    args.push((quote(g, depth, v)?, Icit::Implicit));
                }
                args.push((var(depth, at), Icit::Explicit));
                apps(Term::Def(sizes.size), args)
            }
            Pred::All { indices, .. } => {
                let m = self.find_member(st, pred, here)?;
                let id = sizes.members[m].expect("a member with `T` has a size");
                let mut args = implicit(ps);
                args.extend(explicit(self.scope_args(st, m, depth, here, scope_levels)));
                for v in indices {
                    args.push((quote(g, depth, v)?, Icit::Implicit));
                }
                args.push((var(depth, at), Icit::Explicit));
                apps(Term::Def(id), args)
            }
            _ => unreachable!("only a predicate with `T` has a size"),
        })
    }

    /// Member `m`'s scope's fields, as arguments in a context of `depth`
    /// variables: `here`'s fields, or the current scope's.
    fn scope_args(
        &self,
        st: &Gen,
        m: usize,
        depth: usize,
        here: Option<&Field>,
        scope_levels: &[usize],
    ) -> Vec<Term> {
        match st.members[m].scope {
            None => Vec::new(),
            Some((_, n)) => match here {
                Some(f) => f.field_levels[..n].iter().map(|l| var(depth, *l)).collect(),
                None => scope_levels[..n].iter().map(|l| var(depth, *l)).collect(),
            },
        }
    }

    /// Which member `pred` (an `All`) is, seen from `here` (a constructor
    /// of `T`, whose fields the scope's values would mention) or from a
    /// member's helper (whose scope it shares).
    fn find_member(&self, st: &Gen, pred: &Pred, here: Option<&Field>) -> R<usize> {
        let Pred::All {
            data,
            params,
            preds,
            ..
        } = pred
        else {
            unreachable!()
        };
        let g = &self.globals;
        let np = st.np;
        // Seen from a constructor of `T`, the pred's values have the fields
        // at their levels there; a member's are at `np…`. Bring them over.
        let (params, preds) = match here {
            None => (params.clone(), preds.clone()),
            Some(f) => {
                let move_to = |v: &Value| -> R<Value> {
                    let depth = f.field_levels.last().map_or(np, |l| l + 1).max(np);
                    let t = quote(g, depth, v)?;
                    let mut env: Vec<Value> = vec![stitchwort_core::value::unused(); depth];
                    for (j, slot) in env.iter_mut().enumerate().take(np) {
                        *slot = Value::var(j);
                    }
                    for (k, l) in f.field_levels.iter().enumerate() {
                        env[*l] = Value::var(np + k);
                    }
                    Ok(eval(g, &env, &t)?)
                };
                let params = params.iter().map(move_to).collect::<R<Vec<_>>>()?;
                let preds = preds
                    .iter()
                    .map(|p| map_pred(p, &move_to))
                    .collect::<R<Vec<_>>>()?;
                (params, preds)
            }
        };
        for (m, member) in st.members.iter().enumerate() {
            let level = np + member.scope_len();
            if member.data == *data
                && member.params.len() == params.len()
                && match (here, member.scope) {
                    (Some(f), Some((c, _))) => c == f.ctor,
                    _ => true,
                }
                && pred_eq_all(g, level, &member.params, &params)?
                && preds_eq(g, level, &member.preds, &preds)?
            {
                return Ok(m);
            }
        }
        Err(Stop::Error(Diagnostic::error(
            "E-INTERNAL",
            "a container of a nested type wasn't found among its members",
        )))
    }

    /// `T.%m{m}%size : [params] (scope…) [indices] (x: D args indices) → Nat`.
    fn member_size_type(&self, st: &Gen, m: usize) -> R<Term> {
        let nat = Term::data(st.lib.nat, Vec::new());
        self.member_pi(st, m, &[], &|_, _| Ok(nat.clone()))
    }

    /// `[params] (scope…) (extra…) [indices] (x: D args indices) → result`,
    /// `extra` given as (name, type at its depth), `result` built at its
    /// depth with `x` at the last level.
    fn member_pi(
        &self,
        st: &Gen,
        m: usize,
        extra: &[Extra<'_>],
        result: &dyn Fn(usize, usize) -> R<Term>,
    ) -> R<Term> {
        let g = &self.globals;
        let member = &st.members[m];
        let np = st.np;
        let ns = member.scope_len();
        let e = g.data(member.data);
        let ne_i = e.indices.len();
        let first_index = np + ns + extra.len();
        let x_level = first_index + ne_i;
        let mut ty = result(x_level + 1, x_level)?;
        // (x: D args indices)
        let mut args = Vec::new();
        for v in &member.params {
            args.push(quote(g, x_level, v)?);
        }
        args.extend((0..ne_i).map(|k| var(x_level, first_index + k)));
        ty = pi("x", Icit::Explicit, Term::data(member.data, args), ty);
        for k in (0..ne_i).rev() {
            let env: Vec<Value> = member
                .params
                .iter()
                .cloned()
                .chain((0..k).map(|j| Value::var(first_index + j)))
                .collect();
            let value = eval(g, &env, &e.indices[k].1)?;
            ty = pi(
                &e.indices[k].0,
                Icit::Implicit,
                quote(g, first_index + k, &value)?,
                ty,
            );
        }
        for (k, (x, dom)) in extra.iter().enumerate().rev() {
            ty = pi(x, Icit::Explicit, dom(np + ns + k)?, ty);
        }
        if let Some((c, n)) = member.scope {
            for k in (0..n).rev() {
                let value = eval(g, &vars(0..np + k), &g.data(st.d).ctors[c].fields[k].1)?;
                let x = &g.data(st.d).ctors[c].fields[k].0;
                ty = pi(x, Icit::Explicit, quote(g, np + k, &value)?, ty);
            }
        }
        Ok(self.wrap_params_pi(st.d, ty))
    }

    /// `[params] (scope…) (extra…) [indices] (x) => body`.
    fn member_lams(&self, st: &Gen, m: usize, extra: &[Name], body: Term) -> Term {
        let g = &self.globals;
        let member = &st.members[m];
        let e = g.data(member.data);
        let mut body = lam("x", Icit::Explicit, body);
        for k in (0..e.indices.len()).rev() {
            body = lam(&e.indices[k].0, Icit::Implicit, body);
        }
        for x in extra.iter().rev() {
            body = lam(x, Icit::Explicit, body);
        }
        if let Some((c, n)) = member.scope {
            for k in (0..n).rev() {
                body = lam(&g.data(st.d).ctors[c].fields[k].0, Icit::Explicit, body);
            }
        }
        for (x, _) in g.data(st.d).params.iter().rev() {
            body = lam(x, Icit::Implicit, body);
        }
        body
    }

    /// `T.%m{m}%size`'s body: by cases on `x`, one more than the sizes of
    /// the fields that hold `T`.
    fn member_size_body(&mut self, st: &mut Gen, sizes: &Sizes, m: usize) -> R<Term> {
        let np = st.np;
        let ns = st.members[m].scope_len();
        let data = st.members[m].data;
        let ne_i = self.globals.data(data).indices.len();
        let depth0 = np + ns + ne_i + 1;
        let scope_levels: Vec<usize> = (np..np + ns).collect();
        let mut branches = Vec::new();
        for c in 0..self.globals.data(data).ctors.len() {
            let names = self.ctor_names(data, c);
            let depth = depth0 + names.len();
            let parts = self.member_fields_preds(st, m, c, depth0)?;
            let mut sized = Vec::new();
            for (i, p) in parts.iter().enumerate() {
                if let Some(p) = p
                    && p.involves_motive()
                {
                    sized.push(self.size_of(
                        st,
                        sizes,
                        p,
                        depth0 + i,
                        depth,
                        None,
                        &scope_levels,
                    )?);
                }
            }
            branches.push(Branch {
                names,
                body: Some(Rc::new(self.succ_sum(st, sized))),
            });
        }
        let body = Term::Case(0, data, branches.into());
        Ok(self.member_lams(st, m, &[], body))
    }

    // ------------------------------------------------------- size lemmas

    /// For each member that's a list of `T` itself, `T.%m{m}%sizeMem`: a
    /// member of the list is smaller than the list. Then for each field of
    /// `T` that's such a list, `T.%C%i%sizeMem`: a member is smaller than
    /// the node, the lemma `auto` uses for `decreasing T.size x`.
    fn define_size_lemmas(&mut self, st: &mut Gen) -> R<()> {
        let Some(sizes) = st.sizes.clone() else {
            return Ok(());
        };
        let mut lemma = vec![None; st.members.len()];
        for (m, slot) in lemma.iter_mut().enumerate() {
            if self
                .list_of_t(st, &st.members[m].data, &st.members[m].preds)
                .is_some()
                && sizes.members[m].is_some()
            {
                *slot = Some(self.define_member_size_mem(st, &sizes, m)?);
            }
        }
        let d = st.d;
        for c in 0..self.globals.data(d).ctors.len() {
            for i in 0..st.shapes[c].len() {
                let Some(shape) = st.shapes[c][i].clone() else {
                    continue;
                };
                let np = st.np;
                let fields = st.shapes[c].len();
                let env: Vec<Value> = vars(0..np + i);
                let pred = self.inst(st, &shape, &env, &[], &Me::Motive)?;
                let Pred::All { data, preds, .. } = &pred else {
                    continue;
                };
                if self.list_of_t(st, data, preds).is_none() {
                    continue;
                }
                let here = Field {
                    ctor: c,
                    field_levels: (0..fields).map(|k| np + k).collect(),
                };
                let m = self.find_member(st, &pred, Some(&here))?;
                let Some(member_lemma) = lemma[m] else {
                    continue;
                };
                self.define_field_size_mem(st, &sizes, c, i, m, member_lemma)?;
            }
        }
        Ok(())
    }

    /// For a `List` member whose element is `T` itself, the element's
    /// indices.
    fn list_of_t<'p>(&self, st: &Gen, data: &DataId, preds: &'p [Pred]) -> Option<&'p [Value]> {
        match preds {
            [Pred::Motive(is)] if *data == st.lib.list => Some(is),
            _ => None,
        }
    }

    /// `T.%m{m}%sizeMem : [params] (scope…) (q: T params is) (xs: List (T
    /// params is)) (h: List.Mem q xs) → T.size q < T.%m{m}%size xs`, by
    /// recursion on `xs`.
    fn define_member_size_mem(&mut self, st: &Gen, sizes: &Sizes, m: usize) -> R<DefId> {
        let g = &self.globals;
        let np = st.np;
        let ns = st.members[m].scope_len();
        let lib = &st.lib;
        let is = self
            .list_of_t(st, &st.members[m].data, &st.members[m].preds)
            .expect("a list of `T`")
            .to_vec();
        let elem = st.members[m].params[0].clone();
        let size_m = sizes.members[m].expect("sized");
        let scope_terms =
            |depth: usize| -> Vec<Term> { (np..np + ns).map(|l| var(depth, l)).collect() };
        // size q, size_m xs at a depth
        let size_t = |g: &stitchwort_core::Globals, depth: usize, at: Term| -> R<Term> {
            let mut args = implicit((0..np).map(|j| var(depth, j)).collect());
            for v in &is {
                args.push((quote(g, depth, v)?, Icit::Implicit));
            }
            args.push((at, Icit::Explicit));
            Ok(apps(Term::Def(sizes.size), args))
        };
        let size_list = |depth: usize, at: Term| -> Term {
            let mut args = implicit((0..np).map(|j| var(depth, j)).collect());
            args.extend(explicit(scope_terms(depth)));
            args.push((at, Icit::Explicit));
            apps(Term::Def(size_m), args)
        };
        let q = np + ns;
        let xs = q + 1;
        let h = xs + 1;
        // The type.
        let mut ty = {
            let depth = h + 1;
            apps(
                Term::Def(lib.less_than),
                explicit(vec![
                    size_t(&self.globals, depth, var(depth, q))?,
                    size_list(depth, var(depth, xs)),
                ]),
            )
        };
        {
            let depth = h;
            let mem = apps(
                Term::Def(lib.list_mem),
                vec![
                    (quote(g, depth, &elem)?, Icit::Implicit),
                    (var(depth, q), Icit::Explicit),
                    (var(depth, xs), Icit::Explicit),
                ],
            );
            ty = pi("h", Icit::Explicit, mem, ty);
        }
        ty = pi(
            "xs",
            Icit::Explicit,
            Term::data(lib.list, vec![quote(g, xs, &elem)?]),
            ty,
        );
        ty = pi("q", Icit::Explicit, quote(g, q, &elem)?, ty);
        if let Some((c, n)) = st.members[m].scope {
            for k in (0..n).rev() {
                let value = eval(g, &vars(0..np + k), &g.data(st.d).ctors[c].fields[k].1)?;
                ty = pi(
                    &g.data(st.d).ctors[c].fields[k].0,
                    Icit::Explicit,
                    quote(g, np + k, &value)?,
                    ty,
                );
            }
        }
        ty = self.wrap_params_pi(st.d, ty);
        let name: Name = format!("{}.%m{}%sizeMem", g.data(st.d).name, m + 1).into();
        let span = g.data(st.d).span;
        let id = kernel::declare_def(&mut self.globals, &name, &ty, true, false, span)?;
        let g = &self.globals;
        // The body: cases on xs, then on h.
        // Nil: h is `Void`.
        let nil = Term::Case(0, lib.void, Vec::<Branch>::new().into());
        // Cons y ys: h : Or (y = q) (List.Mem q ys)
        let (y, ys, hc) = (h + 1, h + 2, h);
        let cons = {
            // Inl e: J (z _ => size z ≤ size y + size_m ys) (leAddOfLeLeft …) e
            let inl = {
                let depth = ys + 2; // e
                let e = ys + 1;
                let motive = {
                    let inner = depth + 2; // z, p
                    let z = depth;
                    lam(
                        "z",
                        Icit::Explicit,
                        lam(
                            "e",
                            Icit::Explicit,
                            apps(
                                Term::Def(lib.less_eq),
                                explicit(vec![
                                    size_t(&self.globals, inner, var(inner, z))?,
                                    apps(
                                        Term::Def(lib.add),
                                        explicit(vec![
                                            size_t(&self.globals, inner, var(inner, y))?,
                                            size_list(inner, var(inner, ys)),
                                        ]),
                                    ),
                                ]),
                            ),
                        ),
                    )
                };
                let sy = size_t(&self.globals, depth, var(depth, y))?;
                let base = apps(
                    Term::Def(lib.add_left),
                    explicit(vec![
                        sy.clone(),
                        sy.clone(),
                        size_list(depth, var(depth, ys)),
                        apps(Term::Def(lib.le_refl), explicit(vec![sy])),
                    ]),
                );
                Term::J(Rc::new(motive), Rc::new(base), Rc::new(var(depth, e)))
            };
            // Inr member: leAddOfLeRight (size q) (size y) (size_m ys) (lessLe … (rec q ys member))
            let inr = {
                let depth = ys + 2;
                let member = ys + 1;
                let sq = size_t(&self.globals, depth, var(depth, q))?;
                let sys = size_list(depth, var(depth, ys));
                let mut rec_args = implicit((0..np).map(|j| var(depth, j)).collect());
                rec_args.extend(explicit(scope_terms(depth)));
                rec_args.extend(explicit(vec![
                    var(depth, q),
                    var(depth, ys),
                    var(depth, member),
                ]));
                let rec = apps(Term::Def(id), rec_args);
                let le = apps(
                    Term::Def(lib.less_le),
                    explicit(vec![sq.clone(), sys.clone(), rec]),
                );
                apps(
                    Term::Def(lib.add_right),
                    explicit(vec![
                        sq,
                        size_t(&self.globals, depth, var(depth, y))?,
                        sys,
                        le,
                    ]),
                )
            };
            // h is at level `hc`, under the two fields.
            let depth = ys + 1;
            Term::Case(
                depth - 1 - hc,
                lib.or,
                vec![
                    Branch {
                        names: vec!["e".into()],
                        body: Some(Rc::new(inl)),
                    },
                    Branch {
                        names: vec!["member".into()],
                        body: Some(Rc::new(inr)),
                    },
                ]
                .into(),
            )
        };
        let body = Term::Case(
            1, // xs, under h
            lib.list,
            vec![
                Branch {
                    names: Vec::new(),
                    body: Some(Rc::new(nil)),
                },
                Branch {
                    names: vec!["y".into(), "ys".into()],
                    body: Some(Rc::new(cons)),
                },
            ]
            .into(),
        );
        let mut body = lam(
            "q",
            Icit::Explicit,
            lam("xs", Icit::Explicit, lam("h", Icit::Explicit, body)),
        );
        if let Some((c, n)) = st.members[m].scope {
            for k in (0..n).rev() {
                body = lam(&g.data(st.d).ctors[c].fields[k].0, Icit::Explicit, body);
            }
        }
        for (x, _) in g.data(st.d).params.iter().rev() {
            body = lam(x, Icit::Implicit, body);
        }
        kernel::define_group(&mut self.globals, &[(id, body)])?;
        let member = format!("%m{}%sizeMem", m + 1);
        self.bind_generated(st.d, &member, id);
        Ok(id)
    }

    /// `T.%C%i%sizeMem : [params] (fields…) (q) (h: List.Mem q f_i) →
    /// T.size q < Succ (sizes of C's fields that hold T)`: a member of
    /// the list in field `i` is smaller than the node. Only the fields the
    /// statement mentions are its parameters, so `auto` can find them all
    /// from the goal.
    fn define_field_size_mem(
        &mut self,
        st: &mut Gen,
        sizes: &Sizes,
        c: usize,
        i: usize,
        m: usize,
        member_lemma: DefId,
    ) -> R<()> {
        let d = st.d;
        let np = st.np;
        let nf = st.shapes[c].len();
        let depth_all = np + nf;
        // The components, in the full context [params, fields].
        let here = Field {
            ctor: c,
            field_levels: (0..nf).map(|k| np + k).collect(),
        };
        let mut parts = Vec::new();
        let mut at = None;
        let mut elem_is = Vec::new();
        for k in 0..nf {
            let Some(shape) = st.shapes[c][k].clone() else {
                continue;
            };
            let pred = self.inst(st, &shape, &vars(0..np + k), &[], &Me::Motive)?;
            if !pred.involves_motive() {
                continue;
            }
            if k == i {
                at = Some(parts.len());
                if let Pred::All { preds, .. } = &pred
                    && let [Pred::Motive(is)] = preds.as_slice()
                {
                    elem_is = is.clone();
                }
            }
            parts.push(self.size_of(st, sizes, &pred, np + k, depth_all, Some(&here), &[])?);
        }
        let Some(at) = at else { return Ok(()) };
        // Which fields the statement needs: those its sizes mention, and
        // what their types mention, closed.
        let g = &self.globals;
        let ctor = &g.data(d).ctors[c];
        let mut needed = vec![false; nf];
        let mark = |t: &Term, depth: usize, needed: &mut Vec<bool>| {
            for (s, under) in t.subterms() {
                if let Term::Var(ix) = s
                    && *ix >= under
                {
                    let l = depth + under - 1 - ix;
                    if l >= np && l < np + nf {
                        needed[l - np] = true;
                    }
                }
            }
        };
        for p in &parts {
            mark(p, depth_all, &mut needed);
        }
        let elem_ty = Term::data(d, {
            let mut a: Vec<Term> = (0..np).map(|j| var(depth_all, j)).collect();
            for v in &elem_is {
                a.push(quote(g, depth_all, v)?);
            }
            a
        });
        mark(&elem_ty, depth_all, &mut needed);
        needed[i] = true;
        for k in (0..nf).rev() {
            if needed[k] {
                let ty = &ctor.fields[k].1;
                mark(ty, np + k, &mut needed);
            }
        }
        let kept: Vec<usize> = (0..nf).filter(|k| needed[*k]).collect();
        // Context of the lemma: [params] (kept fields) (q) (h).
        let new_level = |k: usize| np + kept.iter().position(|x| *x == k).expect("kept");
        let reindex = |t: &Term, from: usize, to: usize| -> R<Term> {
            let mut env = vec![stitchwort_core::value::unused(); from];
            for (j, slot) in env.iter_mut().enumerate().take(np) {
                *slot = Value::var(j);
            }
            for &k in &kept {
                if np + k < from {
                    env[np + k] = Value::var(new_level(k));
                }
            }
            let v = eval(g, &env, t)?;
            Ok(quote(g, to, &v)?)
        };
        let nk = kept.len();
        let q = np + nk;
        let h = q + 1;
        let depth = h + 1;
        let sq = {
            let mut args = implicit((0..np).map(|j| var(depth, j)).collect());
            for v in &elem_is {
                let t = quote(g, depth_all, v)?;
                args.push((reindex(&t, depth_all, depth)?, Icit::Implicit));
            }
            args.push((var(depth, q), Icit::Explicit));
            apps(Term::Def(sizes.size), args)
        };
        let comps: Vec<Term> = parts
            .iter()
            .map(|p| reindex(p, depth_all, depth))
            .collect::<R<_>>()?;
        let total = self.sum(st, &comps);
        let lib = &st.lib;
        let mut ty = apps(
            Term::Def(lib.less_than),
            explicit(vec![sq.clone(), Term::ctor(lib.nat, 1, vec![total])]),
        );
        ty = pi(
            "h",
            Icit::Explicit,
            apps(
                Term::Def(lib.list_mem),
                vec![
                    (reindex(&elem_ty, depth_all, h)?, Icit::Implicit),
                    (var(h, q), Icit::Explicit),
                    (var(h, new_level(i)), Icit::Explicit),
                ],
            ),
            ty,
        );
        ty = pi("q", Icit::Explicit, reindex(&elem_ty, depth_all, q)?, ty);
        for (pos, &k) in kept.iter().enumerate().rev() {
            let t = reindex(&ctor.fields[k].1, np + k, np + pos)?;
            ty = pi(&ctor.fields[k].0, Icit::Explicit, t, ty);
        }
        ty = self.wrap_params_pi(d, ty);
        let ctor_name = ctor.name.to_string();
        let member = format!("%{ctor_name}%{i}%sizeMem");
        let name: Name = format!("{}.{member}", g.data(d).name).into();
        let span = g.data(d).span;
        let field_names: Vec<Name> = kept.iter().map(|k| ctor.fields[*k].0.clone()).collect();
        let id = kernel::declare_def(&mut self.globals, &name, &ty, true, false, span)?;
        // The proof: lessLe of the list's lemma, then into the sum.
        let g = &self.globals;
        let s_i = comps[at].clone();
        let mut lemma_args = implicit((0..np).map(|j| var(depth, j)).collect());
        if let Some((_, n)) = st.members[m].scope {
            lemma_args.extend(explicit((0..n).map(|k| var(depth, new_level(k))).collect()));
        }
        lemma_args.extend(explicit(vec![
            var(depth, q),
            var(depth, new_level(i)),
            var(depth, h),
        ]));
        let lt = apps(Term::Def(member_lemma), lemma_args);
        let mut proof = apps(
            Term::Def(lib.less_le),
            explicit(vec![sq.clone(), s_i.clone(), lt]),
        );
        if at + 1 < comps.len() {
            proof = apps(
                Term::Def(lib.add_left),
                explicit(vec![sq.clone(), s_i, self.sum(st, &comps[at + 1..]), proof]),
            );
        }
        for k in (0..at).rev() {
            proof = apps(
                Term::Def(lib.add_right),
                explicit(vec![
                    sq.clone(),
                    comps[k].clone(),
                    self.sum(st, &comps[k + 1..]),
                    proof,
                ]),
            );
        }
        let mut body = lam("q", Icit::Explicit, lam("h", Icit::Explicit, proof));
        for x in field_names.iter().rev() {
            body = lam(x, Icit::Explicit, body);
        }
        for (x, _) in g.data(d).params.iter().rev() {
            body = lam(x, Icit::Implicit, body);
        }
        kernel::define_group(&mut self.globals, &[(id, body)])?;
        self.bind_generated(d, &member, id);
        Ok(())
    }

    // ---------------------------------------------------------- induct

    /// `T.induct` and each member's `T.%m{m}%induct`, defined together.
    fn define_inducts(&mut self, st: &mut Gen) -> R<()> {
        let d = st.d;
        let np = st.np;
        let data = self.globals.data(d);
        let ni = data.indices.len();
        let nc = data.ctors.len();
        let span = data.span;
        // T.induct : [params] (motive) (cases…) [indices] (x) → motive is x
        let ty = {
            let motive = np;
            let first_index = np + 1 + nc;
            let x = first_index + ni;
            let depth = x + 1;
            let mut args: Vec<Term> = (0..ni).map(|k| var(depth, first_index + k)).collect();
            args.push(var(depth, x));
            let mut ty = apps(var(depth, motive), explicit(args));
            ty = pi(
                "x",
                Icit::Explicit,
                self.self_type(st, first_index, ni, x)?,
                ty,
            );
            ty = self.wrap_indices_pi(st, d, first_index, ty)?;
            ty = self.cases_pi(st, motive, np + 1, ty)?;
            ty = pi("motive", Icit::Explicit, self.motive_type(st, np)?, ty);
            self.wrap_params_pi(d, ty)
        };
        let name: Name = format!("{}.{INDUCT}", self.globals.data(d).name).into();
        let induct = kernel::declare_def(&mut self.globals, &name, &ty, true, false, span)?;
        let mut ids = Vec::new();
        for m in 0..st.members.len() {
            let ty = self.member_induct_type(st, m)?;
            let name: Name = format!("{}.%m{}%{INDUCT}", self.globals.data(d).name, m + 1).into();
            ids.push(kernel::declare_def(
                &mut self.globals,
                &name,
                &ty,
                true,
                false,
                span,
            )?);
        }
        let inducts = Inducts {
            induct,
            members: ids,
        };
        let mut bodies = Vec::new();
        // T.induct's body: cases on x, each case applied to its fields and
        // their hypotheses' proofs.
        {
            let motive = np;
            let cases: Vec<usize> = (np + 1..np + 1 + nc).collect();
            let depth0 = np + 1 + nc + ni + 1;
            let mut branches = Vec::new();
            for c in 0..nc {
                let names = self.ctor_names(d, c);
                let depth = depth0 + names.len();
                let here = Field {
                    ctor: c,
                    field_levels: (0..names.len()).map(|k| depth0 + k).collect(),
                };
                let mut args: Vec<Term> =
                    (0..names.len()).map(|k| var(depth, depth0 + k)).collect();
                for i in 0..names.len() {
                    let Some(shape) = st.shapes[c][i].clone() else {
                        continue;
                    };
                    let env: Vec<Value> = vars(0..np)
                        .into_iter()
                        .chain((0..i).map(|k| Value::var(depth0 + k)))
                        .collect();
                    let pred = self.inst(st, &shape, &env, &[], &Me::Motive)?;
                    let at = Here {
                        depth,
                        motive,
                        cases: &cases,
                        field: Some(&here),
                        scope_levels: &[],
                    };
                    args.push(self.proof_of(st, &inducts, &pred, depth0 + i, &at)?);
                }
                branches.push(Branch {
                    names,
                    body: Some(Rc::new(apps(var(depth, cases[c]), explicit(args)))),
                });
            }
            let body = Term::Case(0, d, branches.into());
            let mut extra: Vec<Name> = vec!["motive".into()];
            extra.extend(self.case_names(d));
            bodies.push((induct, self.wrap_lams(d, ni, Some(&extra), body)));
        }
        for m in 0..st.members.len() {
            let body = self.member_induct_body(st, &inducts, m)?;
            bodies.push((inducts.members[m], body));
        }
        kernel::define_group(&mut self.globals, &bodies)?;
        self.bind_generated(d, INDUCT, induct);
        for m in 0..st.members.len() {
            let member = format!("%m{}%{INDUCT}", m + 1);
            self.bind_generated(d, &member, inducts.members[m]);
        }
        st.induct = Some(induct);
        Ok(())
    }

    /// The cases' names: each constructor's, starting lower case.
    fn case_names(&self, d: DataId) -> Vec<Name> {
        self.globals
            .data(d)
            .ctors
            .iter()
            .map(|c| {
                let name = c.name.to_string();
                let mut chars = name.chars();
                let lower = match chars.next() {
                    Some(f) => f.to_lowercase().chain(chars).collect::<String>(),
                    None => name.clone(),
                };
                lower.into()
            })
            .collect()
    }

    /// The motive's type, at `depth`: `(indices…) → T params indices →
    /// Prop`.
    fn motive_type(&self, st: &Gen, depth: usize) -> R<Term> {
        let d = st.d;
        let ni = self.globals.data(d).indices.len();
        let x = depth + ni;
        let ty = pi(
            "x",
            Icit::Explicit,
            self.self_type(st, depth, ni, x)?,
            Term::Sort(Sort::Prop),
        );
        // The indices, explicit.
        let g = &self.globals;
        let data = g.data(d);
        let mut ty = ty;
        for k in (0..ni).rev() {
            let env: Vec<Value> = vars(0..st.np)
                .into_iter()
                .chain((0..k).map(|j| Value::var(depth + j)))
                .collect();
            let value = eval(g, &env, &data.indices[k].1)?;
            ty = pi(
                &data.indices[k].0,
                Icit::Explicit,
                quote(g, depth + k, &value)?,
                ty,
            );
        }
        Ok(ty)
    }

    /// `(case₀: …) → … → rest`, the cases starting at level `first`, the
    /// motive at `motive`.
    fn cases_pi(&mut self, st: &mut Gen, motive: usize, first: usize, rest: Term) -> R<Term> {
        self.cases_pi_with(st, motive, first, rest, false)
    }

    /// [`Self::cases_pi`]; with `mem`, a field that's a list or option of
    /// `T` itself gets a hypothesis for every member instead of its `All`.
    fn cases_pi_with(
        &mut self,
        st: &mut Gen,
        motive: usize,
        first: usize,
        rest: Term,
        mem: bool,
    ) -> R<Term> {
        let d = st.d;
        let nc = self.globals.data(d).ctors.len();
        let names = self.case_names(d);
        let mut tys = Vec::new();
        for c in 0..nc {
            tys.push(self.case_type(st, c, motive, first + c, mem)?);
        }
        let mut ty = rest;
        for c in (0..nc).rev() {
            ty = pi(&names[c], Icit::Explicit, tys[c].clone(), ty);
        }
        Ok(ty)
    }

    /// Case `c`'s type at `depth`: `(fields…) → (hypotheses…) → motive
    /// (result indices) (C fields)`.
    fn case_type(
        &mut self,
        st: &mut Gen,
        c: usize,
        motive: usize,
        depth: usize,
        mem: bool,
    ) -> R<Term> {
        let d = st.d;
        let np = st.np;
        let fields = self.ctor_names(d, c);
        let nf = fields.len();
        let mut preds = Vec::new();
        for i in 0..nf {
            preds.push(match st.shapes[c][i].clone() {
                Some(shape) => {
                    let env: Vec<Value> = vars(0..np)
                        .into_iter()
                        .chain((0..i).map(|k| Value::var(depth + k)))
                        .collect();
                    Some(self.inst(st, &shape, &env, &[], &Me::Motive)?)
                }
                None => None,
            });
        }
        let hyps: Vec<(usize, Pred)> = preds
            .iter()
            .enumerate()
            .filter_map(|(i, p)| p.clone().map(|p| (i, p)))
            .collect();
        let g = &self.globals;
        let data = g.data(d);
        let ctor = &data.ctors[c];
        let end = depth + nf + hyps.len();
        // motive (result indices) (C fields)
        let env: Vec<Value> = vars(0..np)
            .into_iter()
            .chain((0..nf).map(|k| Value::var(depth + k)))
            .collect();
        let mut args = Vec::new();
        for t in &ctor.result {
            args.push(quote(g, end, &eval(g, &env, t)?)?);
        }
        args.push(Term::ctor(
            d,
            c,
            (0..nf).map(|k| var(end, depth + k)).collect(),
        ));
        let mut ty = apps(var(end, motive), explicit(args));
        for (h, (i, p)) in hyps.iter().enumerate().rev() {
            let at = depth + nf + h;
            let dom = match (mem, self.member_form(st, p)) {
                (true, Some(form)) => self.mem_hypothesis(st, form, p, depth + i, at, motive)?,
                _ => self.apply_pred(st, p, var(at, depth + i), at, Some(motive))?,
            };
            ty = pi(&format!("{}Ih", fields[*i]), Icit::Explicit, dom, ty);
        }
        let g = &self.globals;
        let ctor = &g.data(d).ctors[c];
        for k in (0..nf).rev() {
            let env: Vec<Value> = vars(0..np)
                .into_iter()
                .chain((0..k).map(|j| Value::var(depth + j)))
                .collect();
            let value = eval(g, &env, &ctor.fields[k].1)?;
            ty = pi(&fields[k], Icit::Explicit, quote(g, depth + k, &value)?, ty);
        }
        Ok(ty)
    }

    /// Whether a field with predicate `pred` is a `List` or an `Option` of
    /// `T` itself: which, with the element's indices.
    fn member_form<'p>(&self, st: &Gen, pred: &'p Pred) -> Option<(bool, &'p [Value])> {
        match pred {
            Pred::All { data, preds, .. } => match preds.as_slice() {
                [Pred::Motive(is)] if *data == st.lib.list => Some((true, is)),
                [Pred::Motive(is)] if *data == st.lib.option => Some((false, is)),
                _ => None,
            },
            _ => None,
        }
    }

    /// `(q: T params is) → List.Mem q f → motive is q` (`f = Some q` for an
    /// option), at `depth`, with the field at level `f`.
    fn mem_hypothesis(
        &self,
        st: &Gen,
        form: (bool, &[Value]),
        pred: &Pred,
        f: usize,
        depth: usize,
        motive: usize,
    ) -> R<Term> {
        let g = &self.globals;
        let (list, is) = form;
        let Pred::All { params, .. } = pred else {
            unreachable!()
        };
        let elem = &params[0];
        let q = depth;
        let inner = depth + 2;
        let mut margs = Vec::new();
        for v in is {
            margs.push(quote(g, inner, v)?);
        }
        margs.push(var(inner, q));
        let result = apps(var(inner, motive), explicit(margs));
        let member = if list {
            apps(
                Term::Def(st.lib.list_mem),
                vec![
                    (quote(g, depth + 1, elem)?, Icit::Implicit),
                    (var(depth + 1, q), Icit::Explicit),
                    (var(depth + 1, f), Icit::Explicit),
                ],
            )
        } else {
            let opt = Term::data(st.lib.option, vec![quote(g, depth + 1, elem)?]);
            Term::Eq(
                Some(Rc::new(opt)),
                Rc::new(var(depth + 1, f)),
                Rc::new(Term::ctor(st.lib.option, 1, vec![var(depth + 1, q)])),
            )
        };
        Ok(pi(
            "q",
            Icit::Explicit,
            quote(g, depth, elem)?,
            pi("member", Icit::Explicit, member, result),
        ))
    }

    /// The proof of `pred` for the value at level `at`.
    fn proof_of(
        &self,
        st: &Gen,
        inducts: &Inducts,
        pred: &Pred,
        at: usize,
        here: &Here,
    ) -> R<Term> {
        let g = &self.globals;
        let depth = here.depth;
        let np = st.np;
        let common = |head: DefId, scope: Vec<Term>, indices: &[Value]| -> R<Term> {
            let mut args = implicit((0..np).map(|j| var(depth, j)).collect());
            args.extend(explicit(scope));
            args.push((var(depth, here.motive), Icit::Explicit));
            args.extend(explicit(
                here.cases.iter().map(|l| var(depth, *l)).collect(),
            ));
            for v in indices {
                args.push((quote(g, depth, v)?, Icit::Implicit));
            }
            args.push((var(depth, at), Icit::Explicit));
            Ok(apps(Term::Def(head), args))
        };
        Ok(match pred {
            Pred::Unit => Term::ctor(st.lib.unit, 0, Vec::new()),
            Pred::Motive(is) => common(inducts.induct, Vec::new(), is)?,
            Pred::All { indices, .. } => {
                let m = self.find_member(st, pred, here.field)?;
                let scope = self.scope_args(st, m, depth, here.field, here.scope_levels);
                common(inducts.members[m], scope, indices)?
            }
            Pred::Var(_) => unreachable!("no predicate variables in a proof"),
        })
    }

    /// `T.%m{m}%induct : [params] (scope…) (motive) (cases…) [indices] (x:
    /// D args indices) → D.All args preds indices x`.
    fn member_induct_type(&mut self, st: &mut Gen, m: usize) -> R<Term> {
        let np = st.np;
        let ns = st.members[m].scope_len();
        let nc = self.globals.data(st.d).ctors.len();
        let motive = np + ns;
        // The extra binders' types, built ahead (they need `&mut self`).
        let motive_ty = self.motive_type(st, motive)?;
        let mut case_tys = Vec::new();
        for c in 0..nc {
            case_tys.push(self.case_type(st, c, motive, motive + 1 + c, false)?);
        }
        let names = self.case_names(st.d);
        let mut extra: Vec<OwnedExtra> = Vec::new();
        {
            let t = motive_ty.clone();
            extra.push(("motive".into(), Box::new(move |_| Ok(t.clone()))));
        }
        for c in 0..nc {
            let t = case_tys[c].clone();
            extra.push((names[c].clone(), Box::new(move |_| Ok(t.clone()))));
        }
        let extra_refs: Vec<Extra<'_>> =
            extra.iter().map(|(x, f)| (x.clone(), f.as_ref())).collect();
        let member = &st.members[m];
        let probe = Pred::All {
            all: member.all,
            data: member.data,
            params: member.params.clone(),
            preds: member.preds.clone(),
            indices: Vec::new(),
        };
        let ne_i = self.globals.data(member.data).indices.len();
        let first_index = np + ns + 1 + nc;
        let result = |depth: usize, x: usize| -> R<Term> {
            let Pred::All {
                all,
                data,
                params,
                preds,
                ..
            } = &probe
            else {
                unreachable!()
            };
            let p = Pred::All {
                all: *all,
                data: *data,
                params: params.clone(),
                preds: preds.clone(),
                indices: (0..ne_i).map(|k| Value::var(first_index + k)).collect(),
            };
            self.apply_pred(st, &p, var(depth, x), depth, Some(motive))
        };
        self.member_pi(st, m, &extra_refs, &result)
    }

    /// `T.%m{m}%induct`'s body: by cases on `x`, each constructor's parts'
    /// proofs, joined by `Both`.
    fn member_induct_body(&mut self, st: &mut Gen, inducts: &Inducts, m: usize) -> R<Term> {
        let np = st.np;
        let ns = st.members[m].scope_len();
        let nc = self.globals.data(st.d).ctors.len();
        let data = st.members[m].data;
        let ne_i = self.globals.data(data).indices.len();
        let motive = np + ns;
        let cases: Vec<usize> = (motive + 1..motive + 1 + nc).collect();
        let depth0 = motive + 1 + nc + ne_i + 1;
        let scope_levels: Vec<usize> = (np..np + ns).collect();
        let mut branches = Vec::new();
        for c in 0..self.globals.data(data).ctors.len() {
            let names = self.ctor_names(data, c);
            let depth = depth0 + names.len();
            let parts = self.member_fields_preds(st, m, c, depth0)?;
            let mut proofs = Vec::new();
            for (i, p) in parts.iter().enumerate() {
                if let Some(p) = p {
                    let here = Here {
                        depth,
                        motive,
                        cases: &cases,
                        field: None,
                        scope_levels: &scope_levels,
                    };
                    proofs.push(self.proof_of(st, inducts, p, depth0 + i, &here)?);
                }
            }
            branches.push(Branch {
                names,
                body: Some(Rc::new(self.both(st, proofs))),
            });
        }
        let body = Term::Case(0, data, branches.into());
        let mut extra: Vec<Name> = vec!["motive".into()];
        extra.extend(self.case_names(st.d));
        Ok(self.member_lams(st, m, &extra, body))
    }

    /// `T.inductMem`, when a field is a list or option of `T` itself: the
    /// cases take "every member" hypotheses, turned into `T.induct`'s by
    /// `List.memOfAll` and `Option.memOfAll`.
    fn define_induct_mem(&mut self, st: &mut Gen) -> R<()> {
        let d = st.d;
        let np = st.np;
        let nc = self.globals.data(d).ctors.len();
        let ni = self.globals.data(d).indices.len();
        // Is there such a field?
        let mut any = false;
        for c in 0..nc {
            for i in 0..st.shapes[c].len() {
                if let Some(shape) = st.shapes[c][i].clone() {
                    let p = self.inst(st, &shape, &vars(0..np + i), &[], &Me::Motive)?;
                    any |= self.member_form(st, &p).is_some();
                }
            }
        }
        if !any {
            return Ok(());
        }
        let Some(induct) = st.induct else {
            return Ok(());
        };
        let ty = {
            let motive = np;
            let first_index = np + 1 + nc;
            let x = first_index + ni;
            let depth = x + 1;
            let mut args: Vec<Term> = (0..ni).map(|k| var(depth, first_index + k)).collect();
            args.push(var(depth, x));
            let mut ty = apps(var(depth, motive), explicit(args));
            ty = pi(
                "x",
                Icit::Explicit,
                self.self_type(st, first_index, ni, x)?,
                ty,
            );
            ty = self.wrap_indices_pi(st, d, first_index, ty)?;
            ty = self.cases_pi_with(st, motive, np + 1, ty, true)?;
            ty = pi("motive", Icit::Explicit, self.motive_type(st, np)?, ty);
            self.wrap_params_pi(d, ty)
        };
        let span = self.globals.data(d).span;
        let name: Name = format!("{}.{INDUCT_MEM}", self.globals.data(d).name).into();
        let id = kernel::declare_def(&mut self.globals, &name, &ty, true, false, span)?;
        // induct [params] motive (case adapters…) [indices] x
        let motive = np;
        let first_index = np + 1 + nc;
        let x = first_index + ni;
        let depth = x + 1;
        let mut args = implicit((0..np).map(|j| var(depth, j)).collect());
        args.push((var(depth, motive), Icit::Explicit));
        for c in 0..nc {
            args.push((
                self.case_adapter(st, c, depth, motive, np + 1 + c)?,
                Icit::Explicit,
            ));
        }
        args.extend(implicit(
            (0..ni).map(|k| var(depth, first_index + k)).collect(),
        ));
        args.push((var(depth, x), Icit::Explicit));
        let body = apps(Term::Def(induct), args);
        let mut extra: Vec<Name> = vec!["motive".into()];
        extra.extend(self.case_names(d));
        let body = self.wrap_lams(d, ni, Some(&extra), body);
        kernel::define_group(&mut self.globals, &[(id, body)])?;
        self.bind_generated(d, INDUCT_MEM, id);
        Ok(())
    }

    /// `fields… hyps… => case fields… hyps'…`, at `depth`, where a list or
    /// option field's hypothesis becomes "every member" by `memOfAll`.
    fn case_adapter(
        &mut self,
        st: &mut Gen,
        c: usize,
        depth: usize,
        motive: usize,
        case: usize,
    ) -> R<Term> {
        let d = st.d;
        let np = st.np;
        let names = self.ctor_names(d, c);
        let nf = names.len();
        let mut preds = Vec::new();
        for i in 0..nf {
            if let Some(shape) = st.shapes[c][i].clone() {
                let env: Vec<Value> = vars(0..np)
                    .into_iter()
                    .chain((0..i).map(|k| Value::var(depth + k)))
                    .collect();
                preds.push((i, self.inst(st, &shape, &env, &[], &Me::Motive)?));
            }
        }
        let nh = preds.len();
        let inner = depth + nf + nh;
        let g = &self.globals;
        let mut args: Vec<Term> = (0..nf).map(|k| var(inner, depth + k)).collect();
        for (h, (i, p)) in preds.iter().enumerate() {
            let hyp = var(inner, depth + nf + h);
            args.push(match self.member_form(st, p) {
                None => hyp,
                Some((list, is)) => {
                    // q member => memOfAll [elem] (motive is) f hyp q member
                    let Pred::All { params, .. } = p else {
                        unreachable!()
                    };
                    let d2 = inner + 2;
                    let mut margs = Vec::new();
                    for v in is {
                        margs.push(quote(g, d2, v)?);
                    }
                    let pred = apps(var(d2, motive), explicit(margs));
                    let lemma = if list {
                        st.lib.list_mem_of_all
                    } else {
                        st.lib.option_mem_of_all
                    };
                    let call = apps(
                        Term::Def(lemma),
                        vec![
                            (quote(g, d2, &params[0])?, Icit::Implicit),
                            (pred, Icit::Explicit),
                            (var(d2, depth + i), Icit::Explicit),
                            (var(d2, depth + nf + h), Icit::Explicit),
                            (var(d2, inner), Icit::Explicit),
                            (var(d2, inner + 1), Icit::Explicit),
                        ],
                    );
                    lam("q", Icit::Explicit, lam("member", Icit::Explicit, call))
                }
            });
        }
        let mut body = apps(var(inner, case), explicit(args));
        for (i, _) in preds.iter().rev() {
            body = lam(&format!("{}Ih", names[*i]), Icit::Explicit, body);
        }
        for x in names.iter().rev() {
            body = lam(x, Icit::Explicit, body);
        }
        Ok(body)
    }
}

/// Where a proof is built: the context's size, the motive's and cases'
/// levels, and the fields a member's scope takes (`T`'s constructor's, or
/// the current helper's own scope).
struct Here<'a> {
    depth: usize,
    motive: usize,
    cases: &'a [usize],
    field: Option<&'a Field>,
    scope_levels: &'a [usize],
}

/// A constructor of `T` being matched, with its fields' levels.
struct Field {
    ctor: usize,
    field_levels: Vec<usize>,
}

/// The size definitions.
#[derive(Clone)]
struct Sizes {
    size: DefId,
    members: Vec<Option<DefId>>,
}

/// The induction theorems.
struct Inducts {
    induct: DefId,
    members: Vec<DefId>,
}

fn names_at(k: usize) -> &'static str {
    ["p", "q", "r", "s", "t", "u", "v", "w"][k]
}

fn has_rec(shape: &Shape) -> bool {
    match shape {
        Shape::Param(_) => false,
        Shape::Rec(_) => true,
        Shape::In { subs, .. } => subs.iter().flatten().any(has_rec),
    }
}

fn pred_data(pred: &Pred) -> DataId {
    match pred {
        Pred::All { data, .. } => *data,
        _ => unreachable!(),
    }
}

fn map_pred(pred: &Pred, f: &dyn Fn(&Value) -> R<Value>) -> R<Pred> {
    Ok(match pred {
        Pred::Unit => Pred::Unit,
        Pred::Var(l) => Pred::Var(*l),
        Pred::Motive(is) => Pred::Motive(is.iter().map(f).collect::<R<_>>()?),
        Pred::All {
            all,
            data,
            params,
            preds,
            indices,
        } => Pred::All {
            all: *all,
            data: *data,
            params: params.iter().map(f).collect::<R<_>>()?,
            preds: preds.iter().map(|p| map_pred(p, f)).collect::<R<_>>()?,
            indices: indices.iter().map(f).collect::<R<_>>()?,
        },
    })
}

fn pred_eq_all(g: &stitchwort_core::Globals, level: usize, a: &[Value], b: &[Value]) -> R<bool> {
    for (x, y) in a.iter().zip(b) {
        if !conv(g, level, x, y)? {
            return Ok(false);
        }
    }
    Ok(a.len() == b.len())
}

fn preds_eq(g: &stitchwort_core::Globals, level: usize, a: &[Pred], b: &[Pred]) -> R<bool> {
    if a.len() != b.len() {
        return Ok(false);
    }
    for (x, y) in a.iter().zip(b) {
        let same = match (x, y) {
            (Pred::Unit, Pred::Unit) => true,
            (Pred::Var(l), Pred::Var(k)) => l == k,
            (Pred::Motive(p), Pred::Motive(q)) => pred_eq_all(g, level, p, q)?,
            (
                Pred::All {
                    all: a1,
                    params: p1,
                    preds: s1,
                    indices: i1,
                    ..
                },
                Pred::All {
                    all: a2,
                    params: p2,
                    preds: s2,
                    indices: i2,
                    ..
                },
            ) => {
                a1 == a2
                    && pred_eq_all(g, level, p1, p2)?
                    && preds_eq(g, level, s1, s2)?
                    && pred_eq_all(g, level, i1, i2)?
            }
            _ => false,
        };
        if !same {
            return Ok(false);
        }
    }
    Ok(true)
}
