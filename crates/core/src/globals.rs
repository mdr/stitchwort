//! Checked top-level declarations.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use stitchwort_syntax::Span;

use crate::native::Builtins;
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
    pub name: Name,
    /// Its full logical name, unique in the environment: `Std.List.length`,
    /// `Main.List.length` (see [`Data::path`]). Not hashed: a definition's
    /// identity doesn't include its name. Extraction names it by this.
    pub path: Name,
    pub ty: Term,
    pub ty_value: Value,
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
    pub arity: usize,
    /// The function group this definition was submitted in (`define_group`),
    /// in submission order, including itself: `None` until then. Set once,
    /// when the group is submitted, and never changed. Hashing and extraction
    /// treat members of a group of two or more as one unit.
    pub group: Option<Rc<[DefId]>>,
    pub theorem: bool,
    /// Declared with `instance`, so `auto` finds it by its type
    /// (docs/proposals/interfaces.md §9.3). Hashed when set; nothing in
    /// checking depends on it.
    pub instance: bool,
    /// A dictionary (an instance, or another definition whose result is an
    /// interface): applied to all its parameters it stays folded, by name,
    /// until something takes it apart (a `case`, or a comparison that the
    /// name alone can't settle), and then unfolds as usual
    /// (docs/proposals/interfaces.md, "As built (stage 1)" item 13). So
    /// solutions, messages and elaborated terms keep the name. It changes
    /// only when things are computed, never what's equal, so it isn't hashed;
    /// and while a program runs (erasure in effect) it unfolds at once.
    pub fold: bool,
    /// Opaque to the checker (docs/proposals/opaque-definitions.md §6.4):
    /// outside the declarations whose transparency set holds it
    /// ([`Globals::transparent`]), it has a type and no body, so a call of
    /// it is neutral, like a variable applied to arguments. Running a
    /// program still uses the body. Set on a pending definition
    /// ([`crate::check::mark_opaque`]); hashed when set.
    pub opaque: bool,
    /// The opaque definitions its body may unfold, as written (its
    /// `unfolding` clause): set on a pending definition
    /// ([`crate::check::set_unfolding`]), checked by `define_group` (a
    /// definition with any must itself be opaque, and each must be final,
    /// opaque and outside its group), and hashed in a canonical order.
    pub unfolding: Rc<[DefId]>,
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
    pub export: bool,
    /// For an export: how to check each proof parameter at runtime.
    pub validators: Vec<Validator>,
    /// What the untrusted runtimes (`crates/rt`, JS) run instead of the body,
    /// if set ([`crate::check::set_run_body`]): for a definition with
    /// `decreasing`, the recursion as written, without the fuel the body
    /// recurses on (docs/proposals/well-founded-recursion.md §6.5); for a
    /// lifted `match`, its body using the `let`s its caller passes instead of
    /// computing them again (`lift.rs` in the elaborator). Checked to
    /// have the definition's type and arity, but not for termination; never
    /// unfolded by the kernel, and not hashed (it's determined by the body).
    pub(crate) run_body: Option<Rc<Term>>,
    /// The default values of its header's parameters, `(step: Nat := 1)`,
    /// if any has one (docs/proposals/signature-defaults.md §7.1). Kept by
    /// declaration and never hashed, as [`Data::defaults`] is: the kernel
    /// never reads it; the elaborator fills calls that leave a defaulted
    /// parameter out with its helper.
    pub param_defaults: Option<Rc<ParamDefaults>>,
    /// It's the helper of a definition's parameter default. A constant one
    /// stays folded while gluing, as a constant written in the source does,
    /// so a call that left the default out reads back as written. Set with
    /// the owner's [`Def::param_defaults`]; never hashed.
    pub param_default: bool,
    /// For the helper a record update `{ x | f = s }` of a type with several
    /// constructors is lifted to: how the printer shows a call of it, as the
    /// update. Only messages read it, so it isn't hashed.
    pub update_shown: Option<Rc<UpdateShown>>,
    pub span: Span,
}

/// How a call of an update's helper is shown (see [`Def::update_shown`]):
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

    /// Bypasses admission: for tests that build deliberately broken states only.
    #[doc(hidden)]
    pub fn set_body_unchecked_for_tests(&mut self, body: Option<Rc<Term>>) {
        self.body = body;
    }

    /// Bypasses admission: for tests that build deliberately broken states only.
    #[doc(hidden)]
    pub fn set_state_unchecked_for_tests(&mut self, state: State) {
        self.state = state;
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

pub struct Data {
    /// Its name as written from the root of its module: `List`,
    /// `Effect.Comp`, `Geometry.Shape`.
    pub name: Name,
    /// Its full logical name, which is hashed (types are nominal): `name`
    /// within its module's root, `Std.List` or `Main.Geometry.Shape`
    /// (docs/proposals/namespaces.md §7.4). Never a file-system path.
    pub path: Name,
    /// Parameter types, each in the context of the previous parameters.
    pub params: Vec<(Name, Term)>,
    /// Which parameters are `auto`, `[auto ord: Ord k]`, for the elaborator,
    /// which fills them in by instance search wherever the type is written
    /// (docs/proposals/interfaces.md §7.5). The kernel sees ordinary
    /// parameters. Empty when none is; hashed only when one is.
    pub auto_params: Vec<bool>,
    /// Index types (docs/proposals/indexed-families.md §6.1), each in the
    /// context of the parameters and the previous indices. Empty for a type
    /// without indices. `Term::Data` and `Value::Data` hold the parameters
    /// then the indices. Unlike the parameters, each member of a group has
    /// its own.
    pub indices: Vec<(Name, Term)>,
    pub sort: Sort,
    pub ctors: Vec<Ctor>,
    /// Whether it was declared as a record (docs/proposals/records.md): one
    /// constructor, represented in JS without a tag. Fixed when declared, and
    /// hashed; checking never depends on it.
    pub record: bool,
    /// Decision procedures for proof fields, which extracted JS runs to
    /// establish them for decoded input. Added once the type is final.
    pub validators: Vec<FieldValidator>,
    /// How the type crosses the JS boundary, when `js.*` attributes on it
    /// say (docs/proposals/attributes.md §4.6): resolved and checked by the
    /// elaborator once the type is final. `None` for a type without them,
    /// whose default the JS backend resolves when an export reaches it.
    /// Only the JS backend reads it; it isn't hashed (D598) and the kernel
    /// never sees it.
    pub js: Option<std::rc::Rc<crate::js_repr::JsRepr>>,
    /// Its fields' default values (docs/proposals/named-arguments.md §5.1,
    /// §5.2): for each constructor and field, the generated helper that
    /// computes the default, if the field has one. Set by the elaborator once
    /// the type is admitted (or loaded from the check cache); `None` for a
    /// type without defaults. Kept by declaration, never hashed (D1099), and
    /// never seen by the kernel: the elaborator reads it for literals that
    /// leave fields out, and the JS backend for decoders that fill absent
    /// properties (§5.3).
    pub defaults: Option<Rc<FieldDefaults>>,
    /// The data group this type was declared in (`declare_data_group`), in
    /// declaration order, including itself: a group of one for a type on its
    /// own. Every member has the same parameters and universe. Set once, when
    /// the group is declared, and never changed. Positivity, the termination
    /// checker's recursive function fields, elimination from `Prop` and
    /// hashing read it.
    pub group: Rc<[DataId]>,
    /// How many definitions, and data types, existed when this type's group
    /// was declared. Its fields may only use those (and its group's
    /// members), since anything declared later could mention this type and
    /// hide a negative occurrence.
    pub defs_before: usize,
    pub datas_before: usize,
    /// Final once its constructors are defined (they can be only once).
    /// Until then it isn't empty: it can't be matched on or hashed.
    pub(crate) state: State,
    pub span: Span,
}

impl Data {
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
    #[doc(hidden)]
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
}

#[derive(Default)]
pub struct Globals {
    pub defs: Vec<Def>,
    pub datas: Vec<Data>,
    /// `Nat` and the definitions with native implementations.
    pub builtins: Builtins,
    /// The prelude declarations the compiler refers to, by identity.
    pub registry: crate::registry::Registry,
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
    /// unfold to. Cleared with `metas`.
    pub lifted_calls: RefCell<crate::collections::HashMap<usize, (usize, Rc<Term>)>>,
    /// How the printer shows calls of local definitions while their owner
    /// is checked (docs/proposals/syntax-conveniences.md §2.5): `go a b`,
    /// not the lifted call with its captures. Cleared with `metas`. Only
    /// affects messages.
    pub print_labels: RefCell<Vec<PrintLabel>>,
    /// Content hashes computed so far. Declarations never change once
    /// checked, so these never go stale.
    pub hashes: RefCell<crate::collections::HashMap<HashKey, crate::hash::ContentHash>>,
    /// Resource limits for the operation in progress.
    pub budget: crate::budget::Budget,
    /// Whether an error message has shown a term that uses a failed
    /// definition since the elaborator last cleared this: its errors are
    /// then fallout of that failure, not the declaration's own.
    pub failed_mentioned: Cell<bool>,
    /// The failed declarations the elaborator gave up on because they, or
    /// something they use, have an open goal (`?`,
    /// docs/proposals/lsp-goal-holes.md) rather than an error. To the
    /// kernel they're failed like any other, and it never reads this: only
    /// how they're reported differs (*unfinished*, not "has errors").
    pub unfinished: RefCell<crate::collections::HashSet<HashKey>>,
    /// Whether running erases proofs and types, and what each definition
    /// erases (`erase.rs`). Never in effect while checking.
    pub erasure: crate::erase::Erasure,
    /// The logical name of the module whose data types are being declared
    /// (`Std` for the prelude, `Main` for a program), which their [`Data::path`]
    /// starts with. Empty: the path is the name.
    pub module: Name,
    /// Whether evaluation keeps a definition applied to all its arguments
    /// as the call, a [`Value::Call`], unfolding it only when something
    /// looks inside (glued evaluation, docs/proposals/folded-calls.md).
    /// Off unless the elaborator turns it on; the kernel is entered with it
    /// off and turns it on only to check a definition's body (D483,
    /// `check.rs` `admit_group`); never while a program runs.
    pub glue: Cell<bool>,
    /// Counts the times metavariable solutions were taken back (undone or
    /// cleared). A call's kept unfolding records the count it was computed
    /// at, and is computed again if the count has moved since: it may have
    /// used a solution that's gone.
    pub meta_epoch: Cell<u64>,
    /// The opaque definitions whose bodies may be used now, sorted: the
    /// transparency set of the declaration being checked
    /// (docs/proposals/opaque-definitions.md §6.4). Any other opaque
    /// definition is neutral while checking ([`crate::value::hidden`]). The
    /// kernel sets it for each check it makes ([`Transparency::set`]), and puts
    /// back what was there. Shared, so a guard can hold it while `Globals` is
    /// borrowed mutably.
    pub transparent: Transparency,
    /// The sets of numbers a variable is known not to be, which
    /// [`crate::value::Apart`] names: in a number case's default arm, the
    /// matched variable is none of its arms' numbers
    /// (docs/proposals/literal-match-facts.md). Only added to, so a name
    /// never changes what it stands for. Each set is sorted.
    pub apart_sets: RefCell<Vec<Rc<[num_bigint::BigUint]>>>,
}

/// The current transparency set ([`Globals::transparent`]).
#[derive(Clone, Default)]
pub struct Transparency(Rc<RefCell<Rc<[DefId]>>>);

impl Transparency {
    /// Makes `set` (sorted) the transparency set until the guard returned is
    /// dropped, when the set there was comes back.
    #[must_use]
    pub fn set(&self, set: Rc<[DefId]>) -> TransparencyGuard {
        let was = self.0.replace(set);
        TransparencyGuard {
            cell: self.clone(),
            was: Some(was),
        }
    }

    /// Whether the set is empty now: every opaque definition is hidden.
    pub fn is_empty(&self) -> bool {
        self.0.borrow().is_empty()
    }

    /// Whether `id` is in the set now.
    pub fn contains(&self, id: DefId) -> bool {
        self.0.borrow().binary_search(&id).is_ok()
    }
}

/// Puts back the transparency set there was ([`Transparency::set`]).
pub struct TransparencyGuard {
    cell: Transparency,
    was: Option<Rc<[DefId]>>,
}

impl Drop for TransparencyGuard {
    fn drop(&mut self) {
        if let Some(was) = self.was.take() {
            *self.cell.0.borrow_mut() = was;
        }
    }
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
        &self.defs[id.0]
    }

    pub fn data(&self, id: DataId) -> &Data {
        &self.datas[id.0]
    }

    /// Gives definition `id` its parameter defaults `table`, marking each
    /// default's helper ([`Def::param_default`]).
    pub fn set_param_defaults(&mut self, id: DefId, table: ParamDefaults) {
        for default in table.params.iter().flatten() {
            self.defs[default.helper.0].param_default = true;
        }
        self.defs[id.0].param_defaults = Some(Rc::new(table));
    }

    /// The full logical name of a declaration named `name` in the module
    /// being declared.
    pub fn path(&self, name: &Name) -> Name {
        if self.module.is_empty() {
            name.clone()
        } else {
            format!("{}.{name}", self.module).into()
        }
    }

    pub fn find_data(&self, name: &str) -> Option<DataId> {
        self.datas.iter().position(|d| &*d.name == name).map(DataId)
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
        });
        metas.len() - 1
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
        self.meta_trail.borrow_mut().clear();
        self.print_labels.borrow_mut().clear();
    }

    /// Where the environment is now, for [`Globals::rewind`]. Taken between
    /// declarations (no operation running, no metavariables): the
    /// elaborator's `mark` is the only caller.
    pub fn mark(&self) -> GlobalsMark {
        GlobalsMark {
            defs: self.defs.len(),
            datas: self.datas.len(),
            builtins: self.builtins.mark(),
            failed_mentioned: self.failed_mentioned.get(),
            module: self.module.clone(),
            glue: self.glue.get(),
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
            defs,
            datas,
            builtins,
            registry,
            metas: _,
            meta_trail: _,
            frozen_metas: _,
            lifted_calls: _,
            print_labels: _,
            hashes,
            budget,
            failed_mentioned,
            unfinished,
            erasure,
            module,
            glue,
            meta_epoch: _,
            transparent,
            // Kept: a name never changes what it stands for, and a variable
            // apart from some numbers only lives while a case is checked.
            apart_sets: _,
        } = self;
        assert!(
            mark.defs <= defs.len() && mark.datas <= datas.len(),
            "a mark from after the point the session was rewound to"
        );
        defs.truncate(mark.defs);
        datas.truncate(mark.datas);
        builtins.rewind(&mark.builtins, mark.defs);
        registry.forget_from(mark.defs, mark.datas);
        hashes.borrow_mut().retain(|k, _| match k {
            HashKey::Def(id) => id.0 < mark.defs,
            HashKey::Data(d) => d.0 < mark.datas,
        });
        unfinished.borrow_mut().retain(|k| match k {
            HashKey::Def(id) => id.0 < mark.defs,
            HashKey::Data(d) => d.0 < mark.datas,
        });
        budget.reset();
        failed_mentioned.set(mark.failed_mentioned);
        erasure.forget_from(mark.defs);
        *module = mark.module.clone();
        glue.set(mark.glue);
        *transparent.0.borrow_mut() = Rc::default();
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
    failed_mentioned: bool,
    module: Name,
    glue: bool,
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
