//! Structural termination checking for recursive definitions.
//!
//! A definition is accepted if there is one parameter position `i` such that
//! every recursive call passes, at position `i`, a variable bound as a field of
//! a constructor pattern-matched (directly or transitively) from parameter `i`.
//! Rebuilding a matched value counts as that value: in the branch where `m` is
//! `Succ n`, the argument `Succ n` is `m`.
//!
//! A *recursive function field* (a field whose type is a function returning
//! the data type being matched, like `rest : res o -> Comp op res a`) applied
//! to arguments is smaller too, as in Rocq: each result is a child in the
//! well-founded tree. Only the field variable itself counts, not some other
//! function that happens to return the same type.

use stitchwort_syntax::{Diagnostic, Span};

use crate::globals::Globals;
use crate::term::{DataId, DefId, Term};

pub fn check(
    g: &Globals,
    body: &Term,
    self_id: DefId,
    name: &str,
    span: Span,
) -> Result<(), Diagnostic> {
    let arity = body.count_lams();
    let mut walker = Walker {
        g,
        self_id,
        infos: (0..arity)
            .map(|i| Info {
                param: Some(i),
                smaller_than: None,
                recursive_fn: false,
            })
            .collect(),
        calls: Vec::new(),
        matched: Vec::new(),
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
    /// This variable is a recursive function field of a matched constructor.
    recursive_fn: bool,
}

struct Walker<'g> {
    g: &'g Globals,
    self_id: DefId,
    /// Indexed by de Bruijn level.
    infos: Vec<Info>,
    /// For each recursive call: the parameter positions where it passes a
    /// smaller argument, and where the call is.
    calls: Vec<(Vec<usize>, Span)>,
    /// The case branches we're inside: the variable matched (a level), and
    /// the constructor and the levels of its fields in this branch.
    matched: Vec<Matched>,
    span: Span,
}

struct Matched {
    scrutinee: usize,
    data: DataId,
    ctor: usize,
    fields: std::ops::Range<usize>,
}

/// Whether a constructor field's type is a function returning data type `d`.
fn is_recursive_fn(ty: &Term, d: DataId) -> bool {
    let mut ty = ty.strip_loc();
    let mut arrows = 0;
    while let Term::Pi(_, _, _, cod) = ty {
        arrows += 1;
        ty = cod.strip_loc();
    }
    arrows > 0 && matches!(ty, Term::Data(d2, _) if *d2 == d)
}

impl Walker<'_> {
    fn walk(&mut self, term: &Term) {
        match term {
            Term::Loc(span, inner) => {
                let saved = self.span;
                self.span = *span;
                self.walk(inner);
                self.span = saved;
            }
            Term::Var(_) | Term::Nat(_) | Term::Sort(_) | Term::Refl | Term::Meta(_) => {}
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
                    let candidates = args
                        .iter()
                        .enumerate()
                        .filter(|(i, arg)| self.smaller_than(arg) == Some(*i))
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
            Term::Lam(_, _, body) => self.under(&[false], None, body),
            Term::Pi(_, _, dom, cod) => {
                self.walk(dom);
                self.under(&[false], None, cod);
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
            Term::Case(ix, d, branches) => {
                let scrutinee = &self.infos[self.infos.len() - 1 - ix];
                let source = scrutinee.param.or(scrutinee.smaller_than);
                let level = self.infos.len();
                let g = self.g;
                for (c, branch) in branches.iter().enumerate() {
                    self.matched.push(Matched {
                        scrutinee: level - 1 - ix,
                        data: *d,
                        ctor: c,
                        fields: level..level + branch.names.len(),
                    });
                    let recursive: Vec<bool> = g.data(*d).ctors[c]
                        .fields
                        .iter()
                        .map(|(_, ty)| is_recursive_fn(ty, *d))
                        .collect();
                    self.under(&recursive, source, &branch.body);
                    self.matched.pop();
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

    /// The parameter `arg` is structurally smaller than, if any: a variable
    /// matched from it, a recursive function field applied to arguments, or a
    /// constructor rebuilding a matched value.
    fn smaller_than(&self, arg: &Term) -> Option<usize> {
        let level = self.infos.len();
        match arg.strip_loc() {
            Term::Var(ix) => self.infos.get(level.checked_sub(ix + 1)?)?.smaller_than,
            Term::App(..) => {
                let Term::Var(ix) = arg.spine().0 else {
                    return None;
                };
                let info = self.infos.get(level.checked_sub(ix + 1)?)?;
                if info.recursive_fn {
                    info.smaller_than
                } else {
                    None
                }
            }
            Term::Ctor(d, c, args) => {
                let fields: Option<Vec<usize>> = args
                    .iter()
                    .map(|a| match a.strip_loc() {
                        Term::Var(ix) => level.checked_sub(ix + 1),
                        _ => None,
                    })
                    .collect();
                let fields = fields?;
                let m = self.matched.iter().rev().find(|m| {
                    m.data == *d && m.ctor == *c && m.fields.clone().eq(fields.iter().copied())
                })?;
                self.infos[m.scrutinee].smaller_than
            }
            _ => None,
        }
    }

    /// Walks `body` under new binders, one per entry of `recursive_fn`.
    fn under(&mut self, recursive_fn: &[bool], smaller_than: Option<usize>, body: &Term) {
        for &recursive_fn in recursive_fn {
            self.infos.push(Info {
                param: None,
                smaller_than,
                recursive_fn,
            });
        }
        self.walk(body);
        self.infos.truncate(self.infos.len() - recursive_fn.len());
    }
}
