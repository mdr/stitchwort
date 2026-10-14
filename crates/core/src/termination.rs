//! Structural termination checking for recursive definitions.
//!
//! A definition is accepted if there is one parameter position `i` such that
//! every recursive call passes, at position `i`, a variable bound as a field of
//! a constructor pattern-matched (directly or transitively) from parameter `i`.

use stitchwort_syntax::{Diagnostic, Span};

use crate::term::{DefId, Term};

pub fn check(body: &Term, self_id: DefId, name: &str, span: Span) -> Result<(), Diagnostic> {
    let arity = body.count_lams();
    let mut walker = Walker {
        self_id,
        infos: (0..arity)
            .map(|i| Info {
                param: Some(i),
                smaller_than: None,
            })
            .collect(),
        calls: Vec::new(),
        span,
    };
    walker.walk(body.peel_lams(arity));

    let Some((first, rest)) = walker.calls.split_first() else {
        return Ok(());
    };
    let common: Vec<usize> = first
        .0
        .iter()
        .copied()
        .filter(|i| rest.iter().all(|(candidates, _)| candidates.contains(i)))
        .collect();
    if !common.is_empty() {
        return Ok(());
    }
    let (_, call_span) = walker
        .calls
        .iter()
        .find(|(candidates, _)| candidates.is_empty())
        .unwrap_or(first);
    Err(Diagnostic::error(
        "E-TERMINATION",
        format!("can't show that `{name}` terminates"),
    )
    .with_label(*call_span, "this recursive call might not terminate")
    .with_note(
        "every recursive call must pass a structurally smaller argument (a field of a \
         pattern-matched constructor) in the same parameter position",
    )
    .with_note("non-terminating definitions are rejected; `{Partial}` isn't implemented yet"))
}

struct Info {
    /// This variable is parameter `i` of the definition.
    param: Option<usize>,
    /// This variable is structurally smaller than parameter `i`.
    smaller_than: Option<usize>,
}

struct Walker {
    self_id: DefId,
    /// Indexed by de Bruijn level.
    infos: Vec<Info>,
    /// For each recursive call: the parameter positions where it passes a
    /// smaller argument, and where the call is.
    calls: Vec<(Vec<usize>, Span)>,
    span: Span,
}

impl Walker {
    fn walk(&mut self, term: &Term) {
        match term {
            Term::Loc(span, inner) => {
                let saved = self.span;
                self.span = *span;
                self.walk(inner);
                self.span = saved;
            }
            Term::Var(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => {}
            Term::Def(id) => {
                if *id == self.self_id {
                    self.calls.push((Vec::new(), self.span));
                }
            }
            Term::App(..) => {
                let (head, args) = term.spine();
                if let Term::Def(id) = head
                    && *id == self.self_id
                {
                    let level = self.infos.len();
                    let candidates = args
                        .iter()
                        .enumerate()
                        .filter(|(i, arg)| {
                            matches!(arg.strip_loc(), Term::Var(ix)
                                if self.infos[level - 1 - ix].smaller_than == Some(*i))
                        })
                        .map(|(i, _)| i)
                        .collect();
                    self.calls.push((candidates, self.span));
                } else {
                    self.walk(head);
                }
                for arg in args {
                    self.walk(arg);
                }
            }
            Term::Lam(_, _, body) => self.under(1, None, body),
            Term::Pi(_, _, dom, cod) => {
                self.walk(dom);
                self.under(1, None, cod);
            }
            Term::Data(_, args) | Term::Ctor(_, _, args) => {
                for arg in args {
                    self.walk(arg);
                }
            }
            Term::Ann(e, t) => {
                self.walk(e);
                self.walk(t);
            }
            Term::Case(ix, _, branches) => {
                let scrutinee = &self.infos[self.infos.len() - 1 - ix];
                let source = scrutinee.param.or(scrutinee.smaller_than);
                for branch in branches.iter() {
                    self.under(branch.names.len(), source, &branch.body);
                }
            }
            Term::Eq(ty, a, b) => {
                if let Some(ty) = ty {
                    self.walk(ty);
                }
                self.walk(a);
                self.walk(b);
            }
            Term::J(m, b, p) => {
                self.walk(m);
                self.walk(b);
                self.walk(p);
            }
        }
    }

    fn under(&mut self, binders: usize, smaller_than: Option<usize>, body: &Term) {
        for _ in 0..binders {
            self.infos.push(Info {
                param: None,
                smaller_than,
            });
        }
        self.walk(body);
        self.infos.truncate(self.infos.len() - binders);
    }
}
