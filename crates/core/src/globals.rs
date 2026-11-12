//! Checked top-level declarations.

use std::rc::Rc;

use stitchwort_syntax::Span;

use crate::term::{DataId, DefId, Name, Sort, Term};
use crate::value::Value;

/// Where a declaration is in its admission (docs/proposals/kernel-admission.md).
/// Only the kernel's declaration functions change it, and only from
/// `Pending`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    /// Declared, but its body or constructors haven't been admitted.
    Pending,
    /// Admitted, together with everything it refers to.
    Final,
    /// Refused, or refers to something failed. It never becomes final.
    Failed,
}

#[derive(Clone)]
pub struct Def {
    /// Its name as written from the root of its module: `List.length`.
    pub(crate) name: Name,
    /// Its full logical name, unique in the environment: `Std.List.length`,
    /// `Main.List.length` (see [`Data::path`]). Not hashed: a definition's
    /// identity doesn't include its name. Extraction names it by this.
    pub(crate) path: Name,
    pub(crate) ty: Term,
    pub(crate) ty_value: Value,
    /// Set exactly when the definition is final. So it's `None` while its own
    /// body is being checked (recursive references don't unfold), and if
    /// checking it failed.
    pub(crate) body: Option<Rc<Term>>,
    pub(crate) state: State,
    /// The definition-entry arity: the number of leading lambdas in the
    /// submitted body (`Term::count_lams`), set by `define_group` before any
    /// body of the group is checked. Recursive occurrences must be applied to at least
    /// this many arguments, and termination relates calls to these
    /// parameters; the definition unfolds once it's applied to this many
    /// arguments and its case tree can make progress.
    pub(crate) arity: usize,
    /// The function group this definition was submitted in (`define_group`),
    /// in submission order, including itself: `None` until then. Set once,
    /// when the group is submitted, and never changed. Hashing and extraction
    /// treat members of a group of two or more as one unit.
    pub(crate) group: Option<Rc<[DefId]>>,
    pub(crate) theorem: bool,
    /// Declared with `instance`, so `auto` finds it by its type
    /// (docs/proposals/interfaces.md §9.3). Hashed when set; nothing in
    /// checking depends on it.
    pub(crate) instance: bool,
    /// A dictionary (an instance, or another definition whose result is an
    /// interface): applied to all its parameters it stays folded, by name,
    /// until something takes it apart (a `case`, or a comparison that the
    /// name alone can't settle), and then unfolds as usual
    /// (docs/proposals/interfaces.md, "As built (stage 1)" item 13). So
    /// solutions, messages and elaborated terms keep the name. It changes
    /// only when things are computed, never what's equal, so it isn't hashed;
    /// and while a program runs (erasure in effect) it unfolds at once.
    pub(crate) fold: bool,
    /// Opaque to the checker (docs/proposals/opaque-definitions.md §6.4):
    /// outside the declarations whose transparency set holds it
    /// ([`crate::machine::Machine::transparent`]), it has a type and no body, so a call of
    /// it is neutral, like a variable applied to arguments. Running a
    /// program still uses the body. Set on a pending definition
    /// ([`crate::check::mark_opaque`]); hashed when set.
    pub(crate) opaque: bool,
    /// The opaque definitions its body may unfold, as written (its
    /// `unfolding` clause): set on a pending definition
    /// ([`crate::check::set_unfolding`]), checked by `define_group` (a
    /// definition with any must itself be opaque, and each must be final,
    /// opaque and outside its group), and hashed in a canonical order.
    pub(crate) unfolding: Rc<[DefId]>,
    /// Its transparency set: the closure of [`Def::unfolding`], in which
    /// each opaque definition brings its own set and its opaque
    /// group-mates (D1267), sorted. Computed by `define_group` before the
    /// body is checked under it, and never changed after. Determined by the
    /// hashed list and the declarations it names, so not hashed itself.
    pub(crate) transparent: Rc<[DefId]>,
    /// Its case tree has a `Quot.lift` leaf, so applied to all its
    /// parameters it may stay folded on a quotient that isn't a `Quot.mk`
    /// (`value::is_folded`, docs/proposals/map-equality.md §7.2). Set with
    /// the body, from it; like `fold`, it changes only when things are
    /// computed, never what's equal, so it isn't hashed.
    pub(crate) lift_leaf: bool,
    /// Whether it may call itself: it's one of a group of two or more, or
    /// its body mentions it. Set with the body (and `true` until then). A
    /// definition that isn't recursive, stuck on a `case`, can be compared
    /// with another by its case tree (`value::same_stuck_trees`). Determined
    /// by the body, so it isn't hashed.
    pub(crate) recursive: bool,
    /// For each parameter below [`Def::arity`], whether it's *inert*: a
    /// proof the body never computes with, so comparison skips it in calls
    /// (`crate::inert`; docs/proposals/proof-irrelevance.md §7.1, §7.3).
    /// Empty (every argument compared) until the body is installed, and for
    /// a group whose marks couldn't be computed. Set with the body, from
    /// it, on the checked and the trusted paths alike; determined by the
    /// body, so it isn't hashed.
    pub(crate) inert_params: Rc<[bool]>,
    pub(crate) export: bool,
    /// For an export: how to check each proof parameter at runtime.
    pub(crate) validators: Vec<Validator>,
    /// What the untrusted runtimes (`crates/rt`, JS) run instead of the body,
    /// if set ([`crate::check::set_run_body`]): for a definition with
    /// `decreasing`, the recursion as written, without the fuel the body
    /// recurses on (docs/proposals/well-founded-recursion.md §6.5); for a
    /// lifted `match`, its body using the `let`s its caller passes instead of
    /// computing them again (`lift.rs` in the elaborator). Checked to
    /// have the definition's type and arity, but not for termination; never
    /// unfolded by the kernel, and not hashed (it's determined by the body).
    pub(crate) run_body: Option<Rc<Term>>,
    /// It's the helper of a definition's parameter default. A constant one
    /// stays folded while gluing, as a constant written in the source does,
    /// so a call that left the default out reads back as written. Set by
    /// [`crate::check::mark_param_default`] while it is pending, for the
    /// helpers of the elaborator's parameter defaults; never hashed.
    pub(crate) param_default: bool,
    /// Declared `@[tailrec]` (docs/proposals/tailrec.md): the elaborator has
    /// checked that every recursive call is a tail call, and the JavaScript
    /// backend must make a loop of it. Set once, on a pending definition
    /// ([`crate::check::mark_tailrec`]); never hashed (it changes no term).
    pub(crate) tailrec: bool,
    /// Set for an assumption ([`crate::check::assume`], docs/core.md
    /// "Assumptions (open goals)"), an open goal's or an error's stand-in:
    /// a constant final at once, with no body, run body or native, which
    /// never unfolds. Hashed.
    pub(crate) assumption: Option<Rc<Assumption>>,
    /// Where it was declared; for an assumption, where its `?` or error is.
    pub(crate) span: Span,
}

/// What an assumption stands for: the label that, with its type, is its
/// identity in hashes (docs/core.md "Assumptions (open goals)"). Its
/// location is the declaration's span, which isn't hashed, so editing
/// above a `?` changes no hash.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Assumption {
    /// The full logical name of the declaration the gap is in
    /// (`Main.Demo.addComm`). For an open goal that declaration is pending,
    /// or not yet declared, when its assumptions are made, so it's named,
    /// not referred to; for an error's stand-in it has failed.
    pub owner: Name,
    pub kind: AssumptionKind,
}

/// The two kinds of gap an assumption stands for. Part of the label, so
/// hashed: a user of an error's stand-in never shares a hash with a user
/// of a goal of the same type, or with one of the finished declaration.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AssumptionKind {
    /// An open goal `?`: its number in its owner, in source order, from 1.
    Goal(u32),
    /// A stand-in (docs/proposals/tests-with-errors.md §3.3): the owner's
    /// statement checked but its body didn't, so the assumption is the
    /// statement itself. At most one per owner.
    Error,
}

impl Assumption {
    /// The label of open goal `hole` of `owner`.
    pub fn goal(owner: Name, hole: u32) -> Assumption {
        Assumption {
            owner,
            kind: AssumptionKind::Goal(hole),
        }
    }

    /// The label of the stand-in for `owner`, which has an error.
    pub fn error(owner: Name) -> Assumption {
        Assumption {
            owner,
            kind: AssumptionKind::Error,
        }
    }

    /// Whether it stands for a declaration with an error.
    pub fn is_error(&self) -> bool {
        self.kind == AssumptionKind::Error
    }
}

/// How a call of an update's helper is shown ([`crate::ev::Shown::update_shown`]):
/// the record updated and each field's new value, in the order written, as
/// terms in the helper's parameters (all explicit, the innermost last).
#[derive(Clone, Debug)]
pub struct UpdateShown {
    /// How many parameters the helper takes.
    pub params: usize,
    pub base: Term,
    pub fields: Vec<(Name, Term)>,
}

/// A definition's parameter defaults: one entry per parameter of its type,
/// up to the last of its header's, each the default's helper and the
/// earlier parameters (by level) it takes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParamDefaults {
    /// How many of the type's parameters are the header's (with the
    /// implicitly bound ones in front): those after it are the result
    /// type's.
    pub header: usize,
    pub params: Vec<Option<FieldDefault>>,
}

impl Def {
    /// Its name as written from the root of its module.
    pub fn name(&self) -> &Name {
        &self.name
    }

    /// Its full logical name, unique in the environment.
    pub fn path(&self) -> &Name {
        &self.path
    }

    /// Its type, as a term.
    pub fn ty(&self) -> &Term {
        &self.ty
    }

    /// Its type, evaluated.
    pub fn ty_value(&self) -> &Value {
        &self.ty_value
    }

    /// The definition-entry arity: the number of leading lambdas in the
    /// submitted body.
    pub fn arity(&self) -> usize {
        self.arity
    }

    /// The function group it was submitted in, including itself: `None`
    /// until then.
    pub fn group(&self) -> &Option<Rc<[DefId]>> {
        &self.group
    }

    /// Whether it is a theorem.
    pub fn theorem(&self) -> bool {
        self.theorem
    }

    /// Whether it was declared with `instance`.
    pub fn instance(&self) -> bool {
        self.instance
    }

    /// Whether it is a dictionary that stays folded (see the field's doc).
    pub fn fold(&self) -> bool {
        self.fold
    }

    /// Whether it is opaque to the checker.
    pub fn opaque(&self) -> bool {
        self.opaque
    }

    /// The opaque definitions its body may unfold, as written.
    pub fn unfolding(&self) -> &Rc<[DefId]> {
        &self.unfolding
    }

    /// Whether it is exported.
    pub fn export(&self) -> bool {
        self.export
    }

    /// For an export: how to check each proof parameter at runtime.
    pub fn validators(&self) -> &[Validator] {
        &self.validators
    }

    /// Whether it is the helper of a definition's parameter default.
    pub fn param_default(&self) -> bool {
        self.param_default
    }

    /// Whether it is declared `@[tailrec]`.
    pub fn tailrec(&self) -> bool {
        self.tailrec
    }

    /// The gap it stands for, if it's an assumption.
    pub fn assumption(&self) -> Option<&Assumption> {
        self.assumption.as_deref()
    }

    /// Where it was declared.
    pub fn span(&self) -> Span {
        self.span
    }

    /// The definition's body, once it has been admitted.
    pub fn body(&self) -> Option<&Rc<Term>> {
        self.body.as_ref()
    }

    /// What a runtime runs for it: [`Def::run_body`] if set, else its body.
    pub fn run_body(&self) -> Option<&Rc<Term>> {
        self.run_body.as_ref().or(self.body.as_ref())
    }

    /// The run body, only if one was set.
    pub fn own_run_body(&self) -> Option<&Rc<Term>> {
        self.run_body.as_ref()
    }

    /// Where the definition is in its admission.
    pub fn state(&self) -> State {
        self.state
    }

    /// What admission worked out besides the body, read-only: its
    /// transparency set, `lift_leaf`, `recursive` and its inert parameters.
    /// For the check cache's differential test, which compares a trusted
    /// replay with a full check.
    pub fn admitted_metadata(&self) -> (&[DefId], bool, bool, &[bool]) {
        (
            &self.transparent,
            self.lift_leaf,
            self.recursive,
            &self.inert_params,
        )
    }

    /// Which of its parameters below the arity are inert proofs (see the
    /// field): empty if none is known to be.
    pub fn inert_params(&self) -> &[bool] {
        &self.inert_params
    }

    /// Whether parameter `i` is an inert proof.
    pub fn is_inert(&self, i: usize) -> bool {
        self.inert_params.get(i).copied().unwrap_or(false)
    }

    /// Bypasses admission: for tests that build deliberately broken states only.
    #[cfg(feature = "test-bypass")]
    pub fn set_body_unchecked_for_tests(&mut self, body: Option<Rc<Term>>) {
        self.body = body;
    }

    /// Bypasses admission: for tests that build deliberately broken states only.
    #[cfg(feature = "test-bypass")]
    pub fn set_state_unchecked_for_tests(&mut self, state: State) {
        self.state = state;
    }

    /// Bypasses admission: for tests that build deliberately broken states only.
    #[cfg(feature = "test-bypass")]
    pub fn set_arity_unchecked_for_tests(&mut self, arity: usize) {
        self.arity = arity;
    }

    /// Bypasses the inert analysis: for tests that build deliberately
    /// broken states only (a mark the validator must refuse).
    #[cfg(feature = "test-bypass")]
    pub fn set_inert_params_unchecked_for_tests(&mut self, marks: Rc<[bool]>) {
        self.inert_params = marks;
    }
}

/// A decision procedure for an exported function's proof parameter `param`,
/// in the context of the parameters before it. Extracted JS runs it on the
/// decoded inputs, and rejects them unless its test is `True`.
#[derive(Clone)]
pub struct Validator {
    pub param: usize,
    pub decision: Term,
}

/// One field's or parameter's default: its helper, and the variables it
/// takes, by level. For a field, the variables of the constructor's
/// context (the type's parameters, then its fields) the helper takes, by
/// level, in order: a level below the number of parameters is that
/// parameter, any other is field `level - parameters`. The type's
/// parameters are implicit parameters of the helper, and its fields
/// explicit ones. For a definition's parameter, the definition's earlier
/// parameters, each taken as the definition takes it (implicit or
/// explicit).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldDefault {
    pub helper: DefId,
    pub captures: Vec<usize>,
}

/// A data type's defaults: one list per constructor, one entry per field.
pub type FieldDefaults = Vec<Vec<Option<FieldDefault>>>;

/// Why a data group's parameter isn't nestable: why a later data type
/// can't contain itself inside a member of the group applied to it there
/// (docs/proposals/nested-data-types.md §5.1). Each names the first problem
/// found, reading the group in order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NotNestable {
    /// Its type isn't `Type`, `Prop`, or a function type ending in one.
    NotAType,
    /// The type of a later parameter (this one, by position) mentions it.
    LaterParameter(usize),
    /// The type of `data`'s index `index` mentions it.
    IndexType { data: DataId, index: usize },
    /// The result indices of `data`'s constructor `ctor` mention it.
    ResultIndex { data: DataId, ctor: usize },
    /// Field `field` of `data`'s constructor `ctor` uses it `how`.
    Field {
        data: DataId,
        ctor: usize,
        field: usize,
        how: ParamUse,
    },
}

/// How a field uses a parameter, when that keeps the parameter from being
/// nestable ([`NotNestable::Field`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamUse {
    /// In the input of a function.
    Input,
    /// Inside something that isn't a data type (a definition, an equality,
    /// a quotient), or with itself among its own arguments.
    NotStored,
    /// At parameter `param` of the data type `outer`, which isn't nestable.
    AtParameter { outer: DataId, param: usize },
    /// In the indices of a data type.
    InIndex,
    /// The field mentions the earlier field `earlier` (by position), whose
    /// type mentions the parameter.
    DependsOn(usize),
}

pub struct Data {
    /// Its name as written from the root of its module: `List`,
    /// `Effect.Comp`, `Geometry.Shape`.
    pub(crate) name: Name,
    /// Its full logical name, which is hashed (types are nominal): `name`
    /// within its module's root, `Std.List` or `Main.Geometry.Shape`
    /// (docs/proposals/namespaces.md §7.4). Never a file-system path.
    pub(crate) path: Name,
    /// Parameter types, each in the context of the previous parameters.
    pub(crate) params: Vec<(Name, Term)>,
    /// Which parameters are `auto`, `[auto ord: Ord k]`, for the elaborator,
    /// which fills them in by instance search wherever the type is written
    /// (docs/proposals/interfaces.md §7.5). The kernel sees ordinary
    /// parameters. Empty when none is; hashed only when one is.
    pub(crate) auto_params: Vec<bool>,
    /// Index types (docs/proposals/indexed-families.md §6.1), each in the
    /// context of the parameters and the previous indices. Empty for a type
    /// without indices. `Term::Data` and `Value::Data` hold the parameters
    /// then the indices. Unlike the parameters, each member of a group has
    /// its own.
    pub(crate) indices: Vec<(Name, Term)>,
    pub(crate) sort: Sort,
    pub(crate) ctors: Vec<Ctor>,
    /// Whether it was declared as a record (docs/proposals/records.md): one
    /// constructor, represented in JS without a tag. Fixed when declared, and
    /// hashed; checking never depends on it.
    pub(crate) record: bool,
    /// Decision procedures for proof fields, which extracted JS runs to
    /// establish them for decoded input. Added once the type is final.
    pub(crate) validators: Vec<FieldValidator>,
    /// The data group this type was declared in (`declare_data_group`), in
    /// declaration order, including itself: a group of one for a type on its
    /// own. Every member has the same parameters and universe. Set once, when
    /// the group is declared, and never changed. Positivity, the termination
    /// checker's recursive function fields, elimination from `Prop` and
    /// hashing read it.
    pub(crate) group: Rc<[DataId]>,
    /// For each parameter of its group, whether it's nestable, or why not
    /// (docs/proposals/nested-data-types.md §5.1): whether a later data
    /// type may contain itself inside a member of this group applied to it
    /// there, as `Packet` is inside `List Packet`. The same for every member.
    /// Computed from the final constructors when the group is installed,
    /// checked or trusted (so the check cache needn't store it), and read
    /// only by later groups' positivity checks. Empty until then. Not
    /// hashed: it's a function of what is.
    pub(crate) nestable: Rc<[Result<(), NotNestable>]>,
    /// For each parameter, whether its declared type is a proposition, so
    /// comparison skips it (docs/proposals/proof-irrelevance.md §7.1): a
    /// parameter `p: Prop` is a proposition, not a proof, and isn't marked.
    /// Indices are never marked. Computed from the checked parameters when
    /// the group is declared, on both paths; empty if that ran out of budget.
    /// Not hashed: a function of what is.
    pub(crate) proof_params: Rc<[bool]>,
    /// Whether the elaborator marked it as having no eta
    /// ([`crate::check::mark_no_eta`]): interface dictionaries, which are
    /// folded by name and compared by instance (D2502). Only removes
    /// equalities, so nothing about soundness rests on it; hashed when set,
    /// since what's accepted depends on it.
    pub(crate) no_eta: bool,
    /// Whether it has record eta (docs/proposals/record-eta.md §6.1): set
    /// when the group becomes final, from the declaration alone
    /// (`check::qualifies_for_eta`), on both admission paths. Not hashed: a function
    /// of what is.
    pub(crate) eta: bool,
    /// How many definitions, and data types, existed when this type's group
    /// was declared. Its fields may only use those (and its group's
    /// members), since anything declared later could mention this type and
    /// hide a negative occurrence.
    pub(crate) defs_before: usize,
    pub(crate) datas_before: usize,
    /// Final once its constructors are defined (they can be only once).
    /// Until then it isn't empty: it can't be matched on or hashed.
    pub(crate) state: State,
    pub(crate) span: Span,
}

impl Data {
    /// Its name as written from the root of its module.
    pub fn name(&self) -> &Name {
        &self.name
    }

    /// Its full logical name, which is hashed.
    pub fn path(&self) -> &Name {
        &self.path
    }

    /// Parameter types, each in the context of the previous parameters.
    pub fn params(&self) -> &[(Name, Term)] {
        &self.params
    }

    /// Which parameters are `auto`.
    pub fn auto_params(&self) -> &[bool] {
        &self.auto_params
    }

    /// Index types, each in the context of the parameters and the previous
    /// indices.
    pub fn indices(&self) -> &[(Name, Term)] {
        &self.indices
    }

    /// The universe it lives in.
    pub fn sort(&self) -> Sort {
        self.sort
    }

    /// Its constructors.
    pub fn ctors(&self) -> &[Ctor] {
        &self.ctors
    }

    /// Whether it was declared as a record.
    pub fn record(&self) -> bool {
        self.record
    }

    /// Decision procedures for proof fields.
    pub fn validators(&self) -> &[FieldValidator] {
        &self.validators
    }

    /// The data group it was declared in, including itself.
    pub fn group(&self) -> &Rc<[DataId]> {
        &self.group
    }

    /// For each parameter of its group, whether it's nestable, or why not.
    pub fn nestable(&self) -> &[Result<(), NotNestable>] {
        &self.nestable
    }

    /// Which parameters are proofs (see the field).
    pub fn proof_params(&self) -> &[bool] {
        &self.proof_params
    }

    /// Whether it has record eta: a value of it is convertible with the
    /// constructor applied to its projections, and a `case` on an unknown
    /// value of it takes its only branch (docs/proposals/record-eta.md).
    pub fn eta(&self) -> bool {
        self.eta
    }

    /// Whether the elaborator marked it as having no eta (see the field).
    pub fn no_eta(&self) -> bool {
        self.no_eta
    }

    /// Whether parameter `i` is a proof (see the field).
    pub fn is_proof_param(&self, i: usize) -> bool {
        self.proof_params.get(i).copied().unwrap_or(false)
    }

    /// How many definitions existed when its group was declared.
    pub fn defs_before(&self) -> usize {
        self.defs_before
    }

    /// How many data types existed when its group was declared.
    pub fn datas_before(&self) -> usize {
        self.datas_before
    }

    /// Where it was declared.
    pub fn span(&self) -> Span {
        self.span
    }

    /// The one run-time field of a record that is stored as that field
    /// itself, with no box around it (D866, D1067;
    /// docs/proposals/map-equality.md §13.1): a record (in `Type`, not a
    /// proposition) whose fields are all erased (proofs and types,
    /// `Ctor::field_erased`) but one. Every backend that runs programs (the
    /// Rust runtime, the JS backend and its boundary codecs) decides by this
    /// one function, so they agree on the layout: building such a record
    /// gives the field's value, and matching on it binds the field to the
    /// value matched. Only how a value is stored changes: nothing about the
    /// type, its checking or its hash.
    pub fn unboxed_field(&self) -> Option<usize> {
        if !self.record || self.sort == Sort::Prop || self.ctors.len() != 1 {
            return None;
        }
        let mut runtime = self.ctors[0]
            .field_erased
            .iter()
            .enumerate()
            .filter(|(_, erased)| !**erased);
        match (runtime.next(), runtime.next()) {
            (Some((i, _)), None) => Some(i),
            _ => None,
        }
    }

    /// Whether values of it are stored as natural numbers, and how
    /// (docs/proposals/nat-shaped-types.md, D3423, D3424): a data type (in
    /// `Type`, not a proposition, alone in its group) with two constructors
    /// where one stores no fields and the other exactly one, whose type is
    /// the type itself at any parameters and indices. `stored(c)` says, for
    /// each field of constructor `c`, whether the backend stores it: not
    /// erased, and for the fast runtime not determined by the constructor's
    /// indices either ([`crate::determined::ctor_stored`]), which is what
    /// makes `Fin` one. `Nat` is one, with the same layout. The zero
    /// constructor is 0, and the successor of `x` is `x + 1`. Every backend
    /// that stores it so decides by this one function, as for
    /// [`unboxed_field`](Self::unboxed_field), so construction and matching
    /// agree. Only how a value is stored changes: nothing about the type,
    /// its checking or its hash.
    pub fn nat_shape(&self, stored: impl Fn(usize) -> Vec<bool>) -> Option<NatShape> {
        if self.record || self.sort == Sort::Prop || self.ctors.len() != 2 || self.group.len() != 1
        {
            return None;
        }
        let runtime = |c: usize| -> Vec<usize> {
            stored(c)
                .iter()
                .enumerate()
                .filter(|(_, stored)| **stored)
                .map(|(i, _)| i)
                .collect()
        };
        let (zero, succ, field) = match (runtime(0).as_slice(), runtime(1).as_slice()) {
            ([], [field]) => (0, 1, *field),
            ([field], []) => (1, 0, *field),
            _ => return None,
        };
        let mut ty = &self.ctors[succ].fields[field].1;
        while let Term::Loc(_, inner) | Term::Ann(inner, _) = ty {
            ty = inner;
        }
        match ty {
            Term::Data(d, _) if *d == self.group[0] => Some(NatShape { zero, succ, field }),
            _ => None,
        }
    }

    /// Where the type is in its admission.
    pub fn state(&self) -> State {
        self.state
    }

    /// Bypasses admission: for tests that build deliberately broken states only.
    #[cfg(feature = "test-bypass")]
    pub fn set_state_unchecked_for_tests(&mut self, state: State) {
        self.state = state;
    }
}

/// How a data type shaped like `Nat` is stored as a number
/// ([`Data::nat_shape`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NatShape {
    /// The constructor that is 0, which has no run-time fields.
    pub zero: usize,
    /// The constructor that is one more than its field.
    pub succ: usize,
    /// That field's index among all of the successor's fields, erased ones
    /// included.
    pub field: usize,
}

/// A decision procedure for proof field `field` of constructor `ctor`, in the
/// context of the type's parameters and the constructor's earlier fields.
pub struct FieldValidator {
    pub ctor: usize,
    pub field: usize,
    pub decision: Term,
}

pub struct Ctor {
    pub name: Name,
    /// Field types, each in the context of the parameters and previous fields.
    pub fields: Vec<(Name, Term)>,
    /// The universe each field's type lives in.
    pub field_sorts: Vec<Sort>,
    /// Whether each field is erased at runtime (a proof or a type).
    pub field_erased: Vec<bool>,
    /// The result's indices, in the context of the parameters and the
    /// fields: one per index of the data type, so empty for a type without
    /// indices. The result's parameters are always the type's own.
    pub result: Vec<Term>,
    /// Whether each field is implicit, `[n: T]`: only the elaborator reads it
    /// (it fills implicit fields in, and patterns skip them). Hashed when any
    /// is.
    pub implicit: Vec<bool>,
    /// Whether the explicit fields were declared in braces, `| C { f: T }`:
    /// then braces after `C` name its fields; otherwise they are an ordinary
    /// record argument. Only the elaborator reads it. Hashed when set.
    pub braced: bool,
}

/// The kernel's side of a session: the declarations admitted, the
/// evaluator's machine and what is derived from the declarations. It holds
/// no metavariables and no printing hints: the elaborator's are its own
/// (its `state::MetaStore`), and reach the evaluator only through an
/// [`Ev`](crate::ev::Ev) it builds. So the kernel's admission, which takes
/// a `&mut Kernel`, can never see a solution (docs/proposals/globals-split.md
/// §3.6, §4).
#[derive(Default)]
pub struct Kernel {
    /// The declarations admitted so far.
    pub env: crate::env::Env,
    /// The evaluator's modes and operation state (`machine.rs`).
    pub machine: crate::machine::Machine,
    /// What is derived from the environment, and can be worked out again
    /// (`caches.rs`).
    pub caches: crate::caches::EvalCaches,
}

/// How the printer shows an unfilled placeholder of a queued check
/// ([`crate::ev::Shown::placeholder`]): the names of the variables it is applied
/// to when made, and the source its check stands for.
pub type PlaceholderSyntax = (Rc<[Name]>, PlaceholderText);

/// The source an unfilled placeholder stands for ([`PlaceholderSyntax`]).
#[derive(Clone, Debug)]
pub enum PlaceholderText {
    /// As written (`r.items`, a record literal).
    Source(Rc<str>),
    /// A number literal waiting for its type, shown as the number: kept as
    /// the number, so that queuing one (a list of thousands) writes no text.
    Number(Rc<num_bigint::BigUint>),
}

/// A call the printer shows by a local name
/// ([`crate::ev::Shown::print_label`]): `head` applied first to the variables at
/// `levels` (by level, outermost first) is shown as `name` applied to the
/// rest. For a metavariable, those first arguments are hidden whatever
/// they are.
pub struct PrintLabel {
    pub head: Term,
    pub name: Name,
    pub levels: Vec<usize>,
    /// The local definition's parameter defaults, if it has any.
    pub defaults: Option<Rc<CallDefaults>>,
}

/// How the printer finds the defaults a call filled: an argument that is
/// exactly its parameter's default call is left out (`range a b`), and a
/// defaulted parameter's given argument is shown by name (`(step := 2)`).
#[derive(Clone, Debug)]
pub struct CallDefaults {
    /// How many of the function's parameters are its header's.
    pub header: usize,
    /// Each of the header's parameters: its name, and the call its default
    /// fills it with, if it has one.
    pub params: Vec<(Name, Option<DefaultCall>)>,
}

/// The call a parameter's default fills it with: `head` applied to the
/// variables at `levels` (by level, outermost first), then to the
/// function's parameters at `captures` (by index).
#[derive(Clone, Debug)]
pub struct DefaultCall {
    pub head: Term,
    pub levels: Vec<usize>,
    pub captures: Vec<usize>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum HashKey {
    Def(DefId),
    Data(DataId),
}

impl Kernel {
    /// What the evaluator reads, with no metavariables and no hints: for
    /// hosts that run or inspect checked declarations. The elaborator
    /// builds its own, over its meta store (`Elaborator::ev`).
    pub fn ev(&self) -> crate::ev::Ev<'_> {
        crate::ev::Ev::kernel(&self.env, &self.machine, &self.caches)
    }

    pub fn def(&self, id: DefId) -> &Def {
        self.env.def(id)
    }

    pub fn data(&self, id: DataId) -> &Data {
        self.env.data(id)
    }

    pub fn find_data(&self, name: &str) -> Option<DataId> {
        self.env
            .datas()
            .iter()
            .position(|d| &*d.name == name)
            .map(DataId)
    }

    /// Where the environment is now, for [`Kernel::forget_since`] and
    /// [`Kernel::rewind`]. Taken between declarations, or inside one by
    /// the elaborator's equations and induction (`rewind_globals`) and by
    /// a check cache replay, which may run inside another operation.
    pub fn mark(&self) -> KernelMark {
        KernelMark {
            defs: self.env.defs().len(),
            datas: self.env.datas().len(),
            builtins: self.env.builtins().mark(),
        }
    }

    /// Puts the declarations back as they were at `mark`: the definitions
    /// and data types declared since are removed, with everything recorded
    /// about them (registry entries, built-ins bound, natives, primitives
    /// and Float bindings registered, hashes, erasure). Declarations from
    /// before the mark are never changed after they are final, so nothing
    /// else needs undoing; the elaborator undoes its own state.
    ///
    /// The running operation's budget (step limit, stack floor,
    /// cancellation) is left alone, so this is safe partway through an
    /// operation: a check cache replay refused by the kernel undoes with it
    /// while a namespace that needs the file may be elaborating
    /// (docs/proposals/check-cache-trust.md §3). The settings (the
    /// `disable_*` switches, erasure's) stay as they are too.
    ///
    /// Every field is named here, so a new one can't be forgotten.
    pub fn forget_since(&mut self, mark: &KernelMark) {
        let Kernel {
            env,
            // The running operation's, not the declarations'.
            machine: _,
            caches,
        } = self;
        assert!(
            mark.defs <= env.defs().len() && mark.datas <= env.datas().len(),
            "a mark from after the point the session was rewound to"
        );
        env.rewind(mark.defs, mark.datas, &mark.builtins);
        caches.forget_from(mark.defs, mark.datas);
    }

    /// [`Kernel::forget_since`], then the budget is cleared, as if no
    /// operation were running: for rewinding a session between checks (the
    /// language server), when none is. The noted cancellation is cleared with
    /// the rest of the budget; the shared flag itself is not (its owner
    /// clears it).
    pub fn rewind(&mut self, mark: &KernelMark) {
        self.forget_since(mark);
        self.machine.reset();
    }

    /// The bindings that [`Kernel::forget_since`] must undo, as text: how
    /// many declarations there are, the registry and every field of
    /// [`Builtins`](crate::native::Builtins). Cheap, unlike a dump of the
    /// declarations themselves: for checking an undo, compared with the
    /// same taken at the mark.
    pub fn bindings_dump(&self) -> String {
        let mut out = format!(
            "defs {} datas {}\n",
            self.env.defs().len(),
            self.env.datas().len()
        );
        self.env.registry().dump(&mut out);
        self.env.builtins().dump(&mut out);
        out
    }

    /// What the derived caches still hold for declarations from `mark` on,
    /// which [`Kernel::forget_since`] removed: content hashes (read by pin
    /// checks and cache keys, so one left for a removed id would be read
    /// again once the id is reused, and those without proofs) and erasure
    /// (and proof positions), and reliance on open goals. `None` if nothing.
    pub fn derived_state_since(&self, mark: &KernelMark) -> Option<String> {
        let past = |k: &HashKey| match k {
            HashKey::Def(id) => id.0 >= mark.defs,
            HashKey::Data(d) => d.0 >= mark.datas,
        };
        let hashes = (self.caches.hashes.borrow().keys())
            .filter(|k| past(k))
            .count()
            + (self.caches.proofless.borrow().keys())
                .filter(|k| past(k))
                .count();
        let erasure = (self.caches.erasure_defs.borrow().len()).saturating_sub(mark.defs)
            + (self.caches.proof_positions.borrow().len()).saturating_sub(mark.defs);
        let reliance = (self.caches.reliance.borrow().iter())
            .filter(|(d, a)| {
                let key = match **d {
                    crate::assumption::Decl::Def(id) => HashKey::Def(id),
                    crate::assumption::Decl::Data(d) => HashKey::Data(d),
                };
                past(&key) || a.is_some_and(|a| a.0 >= mark.defs)
            })
            .count();
        (hashes + erasure + reliance > 0).then(|| {
            format!(
                "{hashes} content hashes, {erasure} erasure slots and {reliance} reliance \
                 entries past the mark"
            )
        })
    }
}

/// Whether undos are checked against a dump taken at their mark: in builds
/// with the reference evaluator, which every dev and test build has
/// (`stitchwort-dev-features`).
pub const CHECK_UNDOS: bool = cfg!(feature = "reference");

/// A point [`Kernel::forget_since`] and [`Kernel::rewind`] go back to.
#[derive(Clone)]
pub struct KernelMark {
    defs: usize,
    datas: usize,
    builtins: crate::native::BuiltinsMark,
}

impl KernelMark {
    /// How many definitions there were.
    pub fn defs(&self) -> usize {
        self.defs
    }

    /// How many data types there were.
    pub fn datas(&self) -> usize {
        self.datas
    }
}
