//! Checked top-level declarations.

use std::cell::RefCell;
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
    pub body: Option<Rc<Term>>,
    pub state: State,
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
    pub export: bool,
    /// For an export: how to check each proof parameter at runtime.
    pub validators: Vec<Validator>,
    pub span: Span,
}

/// A decision procedure for an exported function's proof parameter `param`,
/// in the context of the parameters before it. Extracted JS runs it on the
/// decoded inputs, and rejects them unless it says `Yes`.
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
    pub state: State,
    pub span: Span,
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
    /// Content hashes computed so far. Declarations never change once
    /// checked, so these never go stale.
    pub hashes: RefCell<std::collections::HashMap<HashKey, crate::hash::ContentHash>>,
    /// Resource limits for the operation in progress.
    pub budget: crate::budget::Budget,
    /// The logical name of the module whose data types are being declared
    /// (`Std` for the prelude, `Main` for a program), which their [`Data::path`]
    /// starts with. Empty: the path is the name.
    pub module: Name,
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

    pub fn solve_meta(&self, m: usize, solution: Value) {
        self.metas.borrow_mut()[m].solution = Some(solution);
    }
}
