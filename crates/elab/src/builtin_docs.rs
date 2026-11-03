//! The built-in names that have no declaration of their own (`rfl`, `J` and
//! the quotient forms), documented by `std/core/Builtins.sw` (SW-1146).
//!
//! The elaborator treats these names as the kernel's forms wherever it meets
//! them. That file declares each one with its signature, no body, so that
//! navigation, hover and `stitchwort doc` have a declaration to show. Here
//! the core's loading gives each such declaration the body its name stands
//! for: the kernel form, abstracted over the signature's parameters. The
//! kernel checks that body against the signature when it admits the
//! definition, so a signature that drifts from the built-in is an error
//! (`E-BUILTIN`) as the core loads. A use of the name never refers to the
//! definition: the form is recognised first. The definition is an ordinary
//! one, sound because of that check, and is only reached by navigation.

use std::rc::Rc;

use stitchwort_core::term::QuotForm;
use stitchwort_core::{Icit, Term};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::Decl;

use crate::{Elaborator, Global, kernel, scope};

/// The names `Builtins.sw` documents.
pub(crate) const DOCUMENTED: &[&str] = &[
    "rfl",
    "J",
    "Quot",
    "Quot.mk",
    "Quot.lift",
    "Quot.ind",
    "Quot.sound",
];

/// The kernel form named `name`, applied to the `params` parameters of its
/// signature, which are the innermost `params` variables.
fn form(name: &str, params: usize) -> Option<Term> {
    let var = |i: usize| Rc::new(Term::Var(params - 1 - i));
    if let Some(form) = QuotForm::ALL.into_iter().find(|f| f.name() == name) {
        let args = (0..params).map(var).collect();
        return (params == form.arity()).then(|| Term::Quot(form, args, false));
    }
    match (name, params) {
        ("rfl", 2) => Some(Term::Refl),
        // `[a] [x y] motive base p`; the motive is `y' p' => motive y' p'`.
        ("J", 6) => {
            let app = |f: Rc<Term>, a: usize| {
                Rc::new(Term::App(f, Rc::new(Term::Var(a)), Icit::Explicit))
            };
            let motive = Term::Lam(
                "y".into(),
                Icit::Explicit,
                Rc::new(Term::Lam(
                    "p".into(),
                    Icit::Explicit,
                    app(app(Rc::new(Term::Var(4)), 1), 0),
                )),
            );
            Some(Term::J(Rc::new(motive), var(4), var(5)))
        }
        _ => None,
    }
}

impl Elaborator {
    /// Whether `name` is reserved for the built-in: not while the core's
    /// `Builtins.sw` is declaring it.
    pub(crate) fn is_reserved(&self, name: &str) -> bool {
        crate::RESERVED.contains(&name) && !(self.loading_prelude && DOCUMENTED.contains(&name))
    }

    /// If the group is one of `Builtins.sw`'s declarations: admits it, with
    /// the built-in as its body, and returns the diagnostics.
    pub(crate) fn builtin_group(
        &mut self,
        members: &[(usize, &Decl, &[Decl])],
    ) -> Option<Vec<(usize, Diagnostic)>> {
        let [(item, signature @ Decl::Signature { name, span, .. }, [])] = members else {
            return None;
        };
        if !self.loading_prelude || !DOCUMENTED.contains(&name.text.as_str()) {
            return None;
        }
        self.module.item = Some(*item);
        let admitted = (|| {
            let Decl::Signature { ty, .. } = signature else {
                unreachable!()
            };
            let key = self.declaration_key(name)?;
            self.clear_metas();
            self.module.phase = crate::module::Phase::Signature;
            let (ty, _) = self.signature_type(ty, false, *span, &key)?;
            // The parameters: the signature's `Pi`s, under source locations.
            let mut binders = Vec::new();
            let mut rest = &ty;
            loop {
                match rest {
                    Term::Loc(_, inner) => rest = inner,
                    Term::Pi(x, icit, _, next) => {
                        binders.push((x.clone(), *icit));
                        rest = next;
                    }
                    _ => break,
                }
            }
            let params = binders.len();
            let mut body = form(&name.text, params).ok_or_else(|| {
                Diagnostic::error(
                    "E-BUILTIN",
                    format!(
                        "`{}` is documented with {params} parameters, which isn't its form's",
                        name.text
                    ),
                )
            })?;
            for (x, icit) in binders.into_iter().rev() {
                body = Term::Lam(x, icit, Rc::new(body));
            }
            let id = kernel::declare_def(
                &mut self.globals,
                &scope::display(&key).into(),
                &ty,
                false,
                false,
                *span,
            )?;
            self.module.def_items.insert(id, *item);
            self.scope.insert(&key, Global::Def(id), name.span, false);
            kernel::define_def(&mut self.globals, id, &body).map_err(|d| {
                Diagnostic::error(
                    "E-BUILTIN",
                    format!(
                        "the documented signature of `{}` doesn't match the built-in",
                        name.text
                    ),
                )
                .with_note(d.message)
            })
        })();
        Some(match admitted {
            Ok(()) => Vec::new(),
            Err(d) => vec![(*item, d)],
        })
    }
}
