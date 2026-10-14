//! Checked top-level declarations.

use std::cell::RefCell;

use stitchwort_syntax::Span;

use crate::term::{DataId, DefId, Name, Sort, Term};
use crate::value::Value;

pub struct Def {
    pub name: Name,
    pub ty: Term,
    pub ty_value: Value,
    /// `None` while the definition's own body is being checked (so recursive
    /// references don't unfold), or if checking it failed.
    pub body: Option<Term>,
    /// Number of leading lambdas in `body`. The definition unfolds once it's
    /// applied to this many arguments and its case tree can make progress.
    pub arity: usize,
    pub theorem: bool,
    pub export: bool,
    pub span: Span,
}

pub struct Data {
    pub name: Name,
    /// Parameter types, each in the context of the previous parameters.
    pub params: Vec<(Name, Term)>,
    pub sort: Sort,
    pub ctors: Vec<Ctor>,
    pub span: Span,
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
    /// The elaborator's metavariables. Empty whenever the kernel runs.
    pub metas: RefCell<Vec<Meta>>,
}

impl Globals {
    pub fn def(&self, id: DefId) -> &Def {
        &self.defs[id.0]
    }

    pub fn data(&self, id: DataId) -> &Data {
        &self.datas[id.0]
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
