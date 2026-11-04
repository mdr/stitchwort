//! Checked top-level declarations.

use std::cell::{Cell, RefCell};
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
    /// ([`Globals::transparent`]), it has a type and no body, so a call of
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
    pub(crate) span: Span,
}

/// How a call of an update's helper is shown (see [`PrintHints`]):
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
    /// transparency set, `lift_leaf` and `recursive`. For the check cache's
    /// differential test, which compares a trusted replay with a full check.
    pub fn admitted_metadata(&self) -> (&[DefId], bool, bool) {
        (&self.transparent, self.lift_leaf, self.recursive)
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
}

/// A decision procedure for an exported function's proof parameter `param`,
/// in the context of the parameters before it. Extracted JS runs it on the
/// decoded inputs, and rejects them unless it says `Yes`.
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
}

/// A metavariable created by the elaborator. Solutions are closed values
/// (functions of the variables in scope where the metavariable was created).
#[derive(Clone)]
pub struct Meta {
    pub solution: Option<Value>,
    /// Where it was created, for "can't work out" errors.
    pub span: Span,
    /// For the unknown proof of an `auto` argument, one entry per argument
    /// it's applied to (the variables in scope where it was made): whether
    /// neither its statement nor the type of a later variable depends on
    /// that one. Unification may solve it ignoring such an argument where
    /// that argument isn't a variable (SW-323: a proof inside a lambda,
    /// once the lambda is applied to a term).
    pub ignorable: Option<Rc<[bool]>>,
    /// Its type, where whoever made it knew it: the type of the unknown
    /// applied to the first `.1` arguments of its spine (the variables in
    /// scope where it was made), in that context. Unification reads it only
    /// to refuse pairing values whose types plainly differ (SW-919), so it
    /// may be missing.
    pub ty: Option<(Value, usize)>,
}

#[derive(Default)]
pub struct Globals {
    /// The declarations admitted so far.
    pub env: crate::env::Env,
    /// The elaborator's metavariables. Empty whenever the kernel runs.
    pub metas: RefCell<Vec<Meta>>,
    /// Every metavariable solution made, newest last, with what it replaced:
    /// how the elaborator undoes a failed attempt (its `undo.rs`). Cleared
    /// with `metas`.
    pub meta_trail: RefCell<Vec<(usize, Option<Value>)>>,
    /// Metavariables standing for a lifted `match` whose helper isn't made
    /// yet (docs/proposals/syntax-conveniences.md §4.10): unification never
    /// solves them, so each is equal only to itself. The elaborator solves
    /// them directly once the helpers are declared. Few, so a list; cleared
    /// with `metas`. Never seen by the kernel.
    pub frozen_metas: RefCell<Vec<usize>>,
    /// For a frozen metavariable once solved with its helper's call: how many
    /// variables the call is a function of, and the call itself (a term in
    /// them). Zonking puts this term in, instead of reading the solution
    /// value back, which would write out what the arguments of the call
    /// unfold to. The elaborator's queued checks keep the term each filled
    /// its placeholder with here too, for the same reason. Cleared with
    /// `metas`.
    pub lifted_calls: RefCell<crate::collections::HashMap<usize, (usize, Rc<Term>)>>,
    /// The placeholders of the elaborator's queued checks that their checks
    /// haven't filled yet (its `queue.rs`): frozen to unification, as
    /// `frozen_metas` are, until filled (docs/proposals/postponement.md,
    /// D2016, stage 6). Kept in step with the queue; cleared with `metas`.
    pub unfilled_placeholders: RefCell<crate::collections::HashSet<usize>>,
    /// How the printer shows a placeholder of those while it is unfilled:
    /// as the source its check stands for (`r.items`, a record literal),
    /// not as an unknown (D2091), with the names of the variables it is
    /// applied to: it is shown so only while applied to those, which then
    /// aren't shown. Kept in step with the queue; cleared with `metas`.
    /// Only affects messages.
    pub placeholder_syntax: RefCell<crate::collections::HashMap<usize, PlaceholderSyntax>>,
    /// The unfilled placeholders of number literals waiting for their type
    /// (K4, step 4.3): the literal, and the type it waits on. A comparison
    /// meeting one against the same numeral at a known type takes that type
    /// (D2110; `unify`). Kept in step with the queue; cleared with `metas`.
    pub waiting_literals:
        RefCell<crate::collections::HashMap<usize, (Rc<num_bigint::BigUint>, crate::value::Value)>>,
    /// How the printer shows calls of local definitions while their owner
    /// is checked (docs/proposals/syntax-conveniences.md §2.5): `go a b`,
    /// not the lifted call with its captures. Cleared with `metas`. Only
    /// affects messages.
    pub print_labels: RefCell<Vec<PrintLabel>>,
    /// The elaborator's facts the printer reads (see [`PrintHints`]).
    pub print_hints: PrintHints,
    /// The evaluator's modes and operation state (`machine.rs`).
    pub machine: crate::machine::Machine,
    /// What is derived from the environment, and can be worked out again
    /// (`caches.rs`).
    pub caches: crate::caches::EvalCaches,
    /// Whether an error message has shown a term that uses a failed
    /// definition since the elaborator last cleared this: its errors are
    /// then fallout of that failure, not the declaration's own. The elaborator's
    /// `Decl` owns it; this handle is shared with the printer, which sets
    /// it (until it takes the hints as an argument, globals-split.md §3.5).
    pub failed_mentioned: FailedMention,
    /// Counts the times metavariable solutions were taken back (undone or
    /// cleared). A call's kept unfolding records the count it was computed
    /// at, and is computed again if the count has moved since: it may have
    /// used a solution that's gone.
    pub meta_epoch: Cell<u64>,
}

/// The flag [`Globals::failed_mentioned`]: a handle on one shared cell.
#[derive(Clone, Default)]
pub struct FailedMention(Rc<Cell<bool>>);

impl FailedMention {
    pub fn get(&self) -> bool {
        self.0.get()
    }

    pub fn set(&self, mentioned: bool) {
        self.0.set(mentioned);
    }
}

/// The elaborator's facts about declarations that the printer reads, for
/// messages: how a call of a defaulted function and of a record update's
/// helper are shown. The rows belong to the elaborator's `Tables`
/// (`OwnedBy` tables, keyed by definition), which share these maps, so
/// that the printer finds them through `&Globals`; they go when the
/// printer takes its hints as an argument (globals-split.md §3.5).
#[derive(Clone, Default)]
pub struct PrintHints {
    /// The default values of a definition's header's parameters,
    /// `(step: Nat := 1)` (docs/proposals/signature-defaults.md §7.1).
    pub param_defaults: Rc<RefCell<crate::collections::HashMap<DefId, Rc<ParamDefaults>>>>,
    /// For the helper a record update `{ x | f = s }` of a type with several
    /// constructors is lifted to: how a call of it is shown, as the update.
    pub update_shown: Rc<RefCell<crate::collections::HashMap<DefId, Rc<UpdateShown>>>>,
}

/// How the printer shows an unfilled placeholder (see
/// [`Globals::placeholder_syntax`]): the names of the variables it is applied
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

/// A call the printer shows by a local name (see
/// [`Globals::print_labels`]): `head` applied first to the variables at
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

impl Globals {
    pub fn def(&self, id: DefId) -> &Def {
        self.env.def(id)
    }

    pub fn data(&self, id: DataId) -> &Data {
        self.env.data(id)
    }

    /// Removes the definitions from `defs` on and the data types from
    /// `datas` on, with the registry entries and cached hashes of them: for
    /// undoing declarations a check cache entry added before the kernel
    /// refused part of it. Nothing may refer to them yet.
    pub fn forget_declarations_from(&mut self, defs: usize, datas: usize) {
        self.env.truncate(defs, datas);
        self.caches.forget_from(defs, datas);
    }

    pub fn find_data(&self, name: &str) -> Option<DataId> {
        self.env
            .datas()
            .iter()
            .position(|d| &*d.name == name)
            .map(DataId)
    }

    pub fn meta_solution(&self, m: usize) -> Option<Value> {
        self.metas.borrow()[m].solution.clone()
    }

    pub fn new_meta(&self, span: Span) -> usize {
        let mut metas = self.metas.borrow_mut();
        metas.push(Meta {
            solution: None,
            span,
            ignorable: None,
            ty: None,
        });
        metas.len() - 1
    }

    /// Records metavariable `m`'s type (see [`Meta::ty`]): `ty`, the type
    /// of `m` applied to its first `arity` arguments.
    pub fn set_meta_type(&self, m: usize, ty: Value, arity: usize) {
        self.metas.borrow_mut()[m].ty = Some((ty, arity));
    }

    /// See [`Meta::ty`].
    pub fn meta_type(&self, m: usize) -> Option<(Value, usize)> {
        self.metas.borrow()[m].ty.clone()
    }

    /// Records which arguments metavariable `m` may ignore (see
    /// [`Meta::ignorable`]).
    pub fn set_meta_ignorable(&self, m: usize, ignorable: Rc<[bool]>) {
        self.metas.borrow_mut()[m].ignorable = Some(ignorable);
    }

    /// See [`Meta::ignorable`].
    pub fn meta_ignorable(&self, m: usize) -> Option<Rc<[bool]>> {
        self.metas.borrow()[m].ignorable.clone()
    }

    /// Whether metavariable `m` is frozen (see [`Globals::frozen_metas`]).
    pub fn meta_frozen(&self, m: usize) -> bool {
        self.frozen_metas.borrow().contains(&m)
    }

    /// Freezes metavariable `m` (see [`Globals::frozen_metas`]).
    pub fn freeze_meta(&self, m: usize) {
        self.frozen_metas.borrow_mut().push(m);
    }

    pub fn solve_meta(&self, m: usize, solution: Value) {
        let old = self.metas.borrow_mut()[m].solution.replace(solution);
        self.meta_trail.borrow_mut().push((m, old));
    }

    /// Records that metavariable solutions have been taken back (see
    /// [`Globals::meta_epoch`]).
    pub fn metas_taken_back(&self) {
        self.meta_epoch.set(self.meta_epoch.get() + 1);
    }

    /// Forgets every metavariable (and the record of their solutions).
    pub fn clear_metas(&self) {
        self.metas_taken_back();
        self.metas.borrow_mut().clear();
        self.frozen_metas.borrow_mut().clear();
        self.lifted_calls.borrow_mut().clear();
        self.unfilled_placeholders.borrow_mut().clear();
        self.placeholder_syntax.borrow_mut().clear();
        self.waiting_literals.borrow_mut().clear();
        self.meta_trail.borrow_mut().clear();
        self.print_labels.borrow_mut().clear();
    }

    /// Where the environment is now, for [`Globals::rewind`]. Taken between
    /// declarations (no operation running, no metavariables): the
    /// elaborator's `mark` is the only caller.
    pub fn mark(&self) -> GlobalsMark {
        GlobalsMark {
            defs: self.env.defs().len(),
            datas: self.env.datas().len(),
            builtins: self.env.builtins().mark(),
        }
    }

    /// Puts the environment back as it was at `mark`: the definitions and
    /// data types declared since are removed, with everything recorded
    /// about them (built-ins bound, natives registered, hashes, erasure),
    /// and the metavariables and the budget are cleared, as if no operation
    /// were running. Declarations from before the mark are never changed
    /// after they are final, so nothing else needs undoing; the elaborator
    /// rewinds its own tables. The settings (the `disable_*` switches,
    /// erasure's) and the cancellation flag stay as they are.
    ///
    /// Every field is named here, so a new one can't be forgotten.
    pub fn rewind(&mut self, mark: &GlobalsMark) {
        let Globals {
            env,
            metas: _,
            meta_trail: _,
            frozen_metas: _,
            lifted_calls: _,
            unfilled_placeholders: _,
            placeholder_syntax: _,
            waiting_literals: _,
            print_labels: _,
            // Rows of the elaborator's tables, which it rewinds.
            print_hints: _,
            machine,
            caches,
            // The elaborator's `Decl` owns it, and its rewind empties it.
            failed_mentioned: _,
            meta_epoch: _,
        } = self;
        assert!(
            mark.defs <= env.defs().len() && mark.datas <= env.datas().len(),
            "a mark from after the point the session was rewound to"
        );
        env.rewind(mark.defs, mark.datas, &mark.builtins);
        caches.forget_from(mark.defs, mark.datas);
        machine.reset();
        // Bumps the epoch, so no kept unfolding is trusted.
        self.clear_metas();
    }
}

/// A point [`Globals::rewind`] goes back to.
#[derive(Clone)]
pub struct GlobalsMark {
    defs: usize,
    datas: usize,
    builtins: crate::native::BuiltinsMark,
}

impl GlobalsMark {
    /// How many definitions there were.
    pub fn defs(&self) -> usize {
        self.defs
    }

    /// How many data types there were.
    pub fn datas(&self) -> usize {
        self.datas
    }
}
