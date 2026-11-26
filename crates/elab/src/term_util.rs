//! Small `Term` builders shared across the tactics.

use stitchwort_core::{Icit, Term};

/// An argument to [`apps`]: a term, explicit unless it carries its mode.
pub(crate) trait AppArg {
    fn into_parts(self) -> (Term, Icit);
}

impl AppArg for Term {
    fn into_parts(self) -> (Term, Icit) {
        (self, Icit::Explicit)
    }
}

impl AppArg for (Term, Icit) {
    fn into_parts(self) -> (Term, Icit) {
        self
    }
}

/// `f a b c`, each argument explicit or with its mode.
pub(crate) fn apps<A: AppArg>(head: Term, args: impl IntoIterator<Item = A>) -> Term {
    args.into_iter().fold(head, |f, arg| {
        let (a, icit) = arg.into_parts();
        Term::app_icit(f, a, icit)
    })
}
