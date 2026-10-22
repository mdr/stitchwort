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
    pub export: bool,
    /// For an export: how to check each proof parameter at runtime.
    pub validators: Vec<Validator>,
    pub span: Span,
}

impl Def {
    /// The definition's body, once it has been admitted.
    pub fn body(&self) -> Option<&Rc<Term>> {
        self.body.as_ref()
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
    /// How the printer shows calls of local definitions while their owner
    /// is checked (docs/proposals/syntax-conveniences.md §2.5): `go a b`,
    /// not the lifted call with its captures. Cleared with `metas`. Only
    /// affects messages.
    pub print_labels: RefCell<Vec<PrintLabel>>,
    /// Content hashes computed so far. Declarations never change once
    /// checked, so these never go stale.
    pub hashes: RefCell<std::collections::HashMap<HashKey, crate::hash::ContentHash>>,
    /// Resource limits for the operation in progress.
    pub budget: crate::budget::Budget,
    /// Whether an error message has shown a term that uses a failed
    /// definition since the elaborator last cleared this: its errors are
    /// then fallout of that failure, not the declaration's own.
    pub failed_mentioned: Cell<bool>,
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
    /// Off unless the elaborator turns it on, and always off while the
    /// kernel checks (D483) or a program runs.
    pub glue: Cell<bool>,
    /// Counts the times metavariable solutions were taken back (undone or
    /// cleared). A call's kept unfolding records the count it was computed
    /// at, and is computed again if the count has moved since: it may have
    /// used a solution that's gone.
    pub meta_epoch: Cell<u64>,
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
        });
        metas.len() - 1
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
        self.meta_trail.borrow_mut().clear();
        self.print_labels.borrow_mut().clear();
    }
}
