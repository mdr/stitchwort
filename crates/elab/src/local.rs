//! Local definitions: `def`s and `theorem`s in a block
//! (docs/proposals/syntax-conveniences.md §3).
//!
//! Consecutive local definitions are elaborated where they're written, in
//! the block's context, a strongly connected component of them at a time,
//! each after the components it refers to (source order breaking ties).
//! Each becomes a [`Draft`] that `lift.rs` resolves with the owner's other
//! drafts: lifted to a top-level definition `owner.go` taking the variables
//! it captures as leading parameters. Until then its name means a frozen
//! metavariable applied to the variables in scope.
//!
//! **A lemma about a local function** needs the function final, so its
//! type computes with it unfolded (§3.6). Admission needs the kernel, which
//! the elaborator can't reach mid-body; so when an owner's body fails, the
//! local definitions elaborated before the failure that don't refer to the
//! owner are admitted, and the body is elaborated again with their names
//! meaning those definitions (`preadmit`). Elaboration is deterministic, so
//! the second attempt meets them in the same contexts.

use std::rc::Rc;

use stitchwort_core::globals::PrintLabel;
use stitchwort_core::value::force;
use stitchwort_core::{Icit, Term, Value};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{Decl, LocalDef};

use crate::Elaborator;
use crate::check::{Ctx, Result, check_type};
use crate::lift::{Draft, LocalDraft, spine, within};

/// Elaborates `defs`, then `k` with their names in scope.
pub(crate) fn around<T>(
    cx: &mut Ctx,
    defs: &[LocalDef],
    k: impl FnOnce(&mut Ctx) -> Result<T>,
) -> Result<T> {
    let mark = cx.mark();
    let span = cx.span;
    let result = define(cx, defs).and_then(|()| {
        cx.span = span;
        k(cx)
    });
    cx.reset(mark);
    cx.span = span;
    result
}

/// The signature's parts.
fn signature(
    def: &LocalDef,
) -> (
    &stitchwort_syntax::ast::Name,
    &stitchwort_syntax::ast::Expr,
    bool,
    stitchwort_syntax::Span,
) {
    match &def.signature {
        Decl::Signature {
            name,
            ty,
            theorem,
            span,
            ..
        } => (name, ty, *theorem, *span),
        _ => unreachable!("the parser makes a signature"),
    }
}

fn define(cx: &mut Ctx, defs: &[LocalDef]) -> Result<()> {
    let e = cx.e;
    let prefix = e.owner.borrow().join(".");
    if prefix.is_empty() {
        let (name, ..) = signature(&defs[0]);
        return Err(Diagnostic::error(
            "E-LOCAL-DEFINITION",
            "local definitions can only be used in a definition's, theorem's or test's body",
        )
        .with_label(name.span, "here")
        .with_note("define it at top level instead"));
    }
    // Keys: unique within the whole top-level definition (§3.1).
    let mut keys = Vec::new();
    for def in defs {
        let (name, ..) = signature(def);
        if name.text.contains('.') {
            return Err(Diagnostic::error(
                "E-LOCAL-DEFINITION",
                format!(
                    "a local definition's name can't be qualified: `{}`",
                    name.text
                ),
            )
            .with_label(name.span, "here")
            .with_note("give it a short name"));
        }
        let key = format!("{prefix}.{}", name.text);
        if let Some((_, first)) = e.local_keys.borrow().iter().find(|(k, _)| *k == key) {
            let owner = crate::scope::display(&e.owner.borrow()[0]).to_string();
            return Err(Diagnostic::error(
                "E-DUPLICATE",
                format!("`{}` is already a local definition in `{owner}`", name.text),
            )
            .with_label(name.span, "defined again here")
            .with_label(*first, "first defined here")
            .with_note(format!(
                "local definitions are named `{}` from outside, so their names must be \
                 different within the whole definition",
                crate::scope::display(&key)
            )));
        }
        e.local_keys.borrow_mut().push((key.clone(), name.span));
        keys.push(key);
    }
    for component in components(defs) {
        self::component(cx, defs, &keys, &component)?;
    }
    Ok(())
}

/// The strongly connected components of `defs` by which refer to which,
/// each after those it refers to, of those ready the one starting earliest
/// first; members in source order.
fn components(defs: &[LocalDef]) -> Vec<Vec<usize>> {
    let names: Vec<&str> = defs.iter().map(|d| signature(d).0.text.as_str()).collect();
    let edges: Vec<Vec<usize>> = defs
        .iter()
        .map(|d| {
            let refs = crate::module::local_refs(d);
            let mut out: Vec<usize> = (0..defs.len())
                .filter(|&j| refs.iter().any(|r| r == names[j]))
                .collect();
            out.dedup();
            out
        })
        .collect();
    let mut found = crate::module::tarjan(&edges);
    for c in &mut found {
        c.sort_unstable();
    }
    let mut component_of = vec![0; defs.len()];
    for (c, members) in found.iter().enumerate() {
        for &i in members {
            component_of[i] = c;
        }
    }
    let mut done = vec![false; found.len()];
    let mut order = Vec::new();
    while order.len() < found.len() {
        let ready = (0..found.len())
            .filter(|&c| !done[c])
            .filter(|&c| {
                found[c].iter().all(|&i| {
                    edges[i]
                        .iter()
                        .all(|&j| component_of[j] == c || done[component_of[j]])
                })
            })
            .min_by_key(|&c| found[c][0])
            .expect("the components form a DAG");
        done[ready] = true;
        order.push(found[ready].clone());
    }
    order
}

/// Elaborates one component: every signature, then (with every member's
/// name in scope) every body, each recorded as a draft.
fn component(cx: &mut Ctx, defs: &[LocalDef], keys: &[String], members: &[usize]) -> Result<()> {
    let e = cx.e;
    let g = cx.g();
    let base = cx.level();
    let mut todo = Vec::new();
    for &i in members {
        let found = e
            .preadmitted
            .borrow()
            .get(&keys[i])
            .map(|r| (r.id, r.captures.clone()));
        match found {
            Some((id, captures)) => bind_admitted(cx, &signature(&defs[i]).0.text, id, &captures)?,
            None => todo.push(i),
        }
    }
    // The partial translation (`partial.rs`) is for top-level groups.
    let recursive = members.len() > 1 || {
        let name = &signature(&defs[members[0]]).0.text;
        crate::module::local_refs(&defs[members[0]]).contains(name)
    };
    for &i in &todo {
        let (name, ty, ..) = signature(&defs[i]);
        if recursive && crate::mentions_ability(ty, "Partial") {
            return Err(Diagnostic::error(
                "E-LOCAL-DEFINITION",
                format!(
                    "`{}` is recursive and partial, which a local definition can't be yet",
                    name.text
                ),
            )
            .with_label(name.span, "here")
            .with_note("define it at top level instead"));
        }
    }
    let mut elaborated = Vec::new();
    for &i in &todo {
        let (name, ty, _, span) = signature(&defs[i]);
        let ty = local_type(cx, ty, span)?;
        let value = cx.eval(&ty)?;
        let meta = g.new_meta(name.span);
        g.freeze_meta(meta);
        e.local_metas.borrow_mut().insert(meta, name.text.clone());
        let levels = spine(&cx.env, &cx.lets);
        let mut call = Term::Meta(meta);
        for &level in &levels {
            call = Term::app(call, Term::Var(base - 1 - level));
        }
        g.print_labels.borrow_mut().push(PrintLabel {
            head: Term::Meta(meta),
            name: name.text.as_str().into(),
            levels,
        });
        elaborated.push((i, ty, value, meta, call));
    }
    for (i, _, value, _, call) in &elaborated {
        cx.bind_local(&signature(&defs[*i]).0.text, call.clone(), value.clone());
    }
    for (i, ty, value, meta, _) in elaborated {
        let def = &defs[i];
        let (name, _, theorem, span) = signature(def);
        e.owner.borrow_mut().push(name.text.clone());
        let body = e.body_in(cx, value, Some(Rc::new(ty.clone())), name, &def.equations);
        e.owner.borrow_mut().pop();
        let body = body?;
        let whole = def.equations.last().map_or(span, |eq| span.to(eq.span()));
        e.drafts.borrow_mut().push(Draft {
            meta,
            span,
            env: cx.env.clone(),
            types: cx.types.clone(),
            names: cx.names.clone(),
            base,
            extra: Vec::new(),
            body,
            goal: ty,
            kinds: cx.kinds.clone(),
            lets: cx.lets.clone(),
            local: Some(LocalDraft {
                key: keys[i].clone(),
                name: name.text.clone(),
                theorem,
                whole,
            }),
        });
    }
    Ok(())
}

/// A local definition's type, elaborated where it's written: a name already
/// in scope means that, and an unknown one is bound automatically, as in a
/// top-level signature (§3.1).
fn local_type(
    cx: &mut Ctx,
    ty: &stitchwort_syntax::ast::Expr,
    span: stitchwort_syntax::Span,
) -> Result<Term> {
    let auto = crate::autobind::auto_bound_in(cx.e, ty, cx.scope_names())?;
    let mark = cx.mark();
    let saved = cx.span;
    let result = (|| {
        let mut domains = Vec::new();
        for n in &auto.names {
            cx.span = n.span;
            let dom = cx.fresh_meta();
            let value = cx.eval(&dom)?;
            domains.push(dom);
            cx.bind(&n.text, value);
            cx.set_kind(Icit::Implicit);
        }
        cx.span = span;
        let (mut term, _) = check_type(cx, ty)?;
        for (n, dom) in auto.names.iter().zip(domains).rev() {
            term = Term::Pi(
                n.text.as_str().into(),
                Icit::Implicit,
                Rc::new(dom),
                Rc::new(term),
            );
        }
        Ok(term)
    })();
    cx.reset(mark);
    cx.span = saved;
    result.map_err(|d| crate::autobind::explain(&auto, d))
}

/// Makes `name` mean the admitted local definition `id`, applied to its
/// captures (levels of the context it was elaborated in, which is `cx`'s).
fn bind_admitted(
    cx: &mut Ctx,
    name: &str,
    id: stitchwort_core::DefId,
    captures: &[(usize, Icit, stitchwort_core::Name)],
) -> Result<()> {
    let g = cx.g();
    let mut term = Term::Def(id);
    let mut ty = g.def(id).ty_value.clone();
    for (level, icit, x) in captures {
        if *level >= cx.level() || cx.names[*level] != *x {
            return Err(Diagnostic::error(
                "E-INTERNAL",
                format!(
                    "internal error: `{name}` is elaborated in a different context than before"
                ),
            )
            .with_label(cx.span, "here")
            .with_note("this is a bug in the compiler, not in your program"));
        }
        term = Term::app_icit(term, Term::Var(cx.level() - 1 - level), *icit);
        let Value::Pi(_, _, _, cod) = force(g, ty)? else {
            return Err(Diagnostic::error(
                "E-INTERNAL",
                "internal error: a lifted definition takes fewer captures than it was given",
            ));
        };
        ty = cod.apply(g, cx.env[*level].clone())?;
    }
    g.print_labels.borrow_mut().push(PrintLabel {
        head: Term::Def(id),
        name: name.into(),
        levels: captures.iter().map(|(l, _, _)| *l).collect(),
    });
    cx.bind_local(name, term, ty);
    Ok(())
}

impl Elaborator {
    /// After an attempt at `owner`'s body failed: admits the local
    /// definitions it elaborated that don't refer to the owner (or to
    /// anything else not final), with the `match`es inside them, so the next
    /// attempt can use them as final definitions. Whether any were, and the
    /// names of those that weren't because they call the owner (or
    /// something else not final).
    pub(crate) fn preadmit(&mut self, owner: &str) -> Result<(bool, Vec<String>)> {
        // Auto arguments found so far fill in what they can; one that can't
        // be proved is the failure being reported, or unrelated.
        if let Err(d) = self.solve_obligations()
            && crate::undo::fatal(&d)
        {
            return Err(d);
        }
        let drafts = std::mem::take(&mut *self.drafts.borrow_mut());
        let index: std::collections::HashMap<usize, usize> = drafts
            .iter()
            .enumerate()
            .map(|(i, d)| (d.meta, i))
            .collect();
        let frozen = |m: usize| self.globals.meta_frozen(m);
        // A candidate: a local definition, or a `match` inside one; finished
        // except for frozen metavariables; referring to nothing pending.
        let mut candidate = Vec::new();
        let mut pending = Vec::new();
        let mut refers: Vec<Vec<usize>> = Vec::new();
        for d in &drafts {
            let inside = drafts
                .iter()
                .any(|o| o.local.as_ref().is_some_and(|l| within(l.whole, d.span)));
            let n = d.env.len();
            let mut ok = d.local.is_some() || inside;
            let mut waits = false;
            let mut calls = Vec::new();
            for t in [&d.body, &d.goal] {
                match self.zonk_keeping(t, n, &frozen) {
                    Ok(t) => {
                        for (sub, _) in t.subterms() {
                            match sub {
                                Term::Meta(m) => match index.get(m) {
                                    Some(&j) => calls.push(j),
                                    None => ok = false,
                                },
                                Term::Def(id)
                                    if self.globals.def(*id).state()
                                        != stitchwort_core::globals::State::Final =>
                                {
                                    ok = false;
                                    waits = true;
                                }
                                _ => {}
                            }
                        }
                    }
                    Err(d) if crate::undo::fatal(&d) => return Err(d),
                    Err(_) => ok = false,
                }
            }
            candidate.push(ok);
            pending.push(waits);
            refers.push(calls);
        }
        // Only with everything they call, and the definitions they're in.
        loop {
            let mut changed = false;
            for i in 0..drafts.len() {
                if !candidate[i] {
                    continue;
                }
                if refers[i].iter().any(|&j| pending[j]) && !pending[i] {
                    pending[i] = true;
                    changed = true;
                }
                let calls_out = refers[i].iter().any(|&j| !candidate[j]);
                let outer_out = drafts.iter().enumerate().any(|(j, o)| {
                    !candidate[j]
                        && j != i
                        && o.local
                            .as_ref()
                            .is_some_and(|l| within(l.whole, drafts[i].span))
                });
                if calls_out || outer_out {
                    candidate[i] = false;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        let waiting: Vec<String> = drafts
            .iter()
            .zip(&pending)
            .filter_map(|(d, p)| d.local.as_ref().filter(|_| *p).map(|l| l.name.clone()))
            .collect();
        let chosen: Vec<Draft> = drafts
            .into_iter()
            .zip(&candidate)
            .filter_map(|(d, ok)| ok.then_some(d))
            .collect();
        let keys: Vec<Option<String>> = chosen
            .iter()
            .map(|d| d.local.as_ref().map(|l| l.key.clone()))
            .collect();
        if keys.iter().all(Option::is_none) {
            return Ok((false, waiting));
        }
        let (_, resolved) = self.resolve_batch(owner, chosen, false)?;
        for (key, r) in keys.into_iter().zip(resolved) {
            if let Some(key) = key {
                self.preadmitted.borrow_mut().insert(key, r);
            }
        }
        Ok((true, waiting))
    }
}

/// `d`, with a note if it mentions a local definition that isn't final
/// while its owner `owner` is checked, because it calls the owner: such a
/// definition doesn't compute there.
pub(crate) fn unfinished(
    d: Diagnostic,
    waiting: &[String],
    owner: &stitchwort_syntax::ast::Name,
) -> Diagnostic {
    let mentions = |name: &str| {
        let shown = [format!("`{name}`"), format!("`{name} ")];
        let has = |s: &str| shown.iter().any(|x| s.contains(x.as_str()));
        has(&d.message) || d.labels.iter().any(|l| has(&l.message))
    };
    let Some(name) = waiting.iter().find(|n| mentions(n)) else {
        return d;
    };
    let note = format!(
        "`{name}` calls `{0}`, so it's defined together with `{0}` and doesn't compute while \
         `{0}` is checked; a fact about it needs `{0}` finished: state it as a top-level \
         theorem about `{0}.{name}`",
        owner.text
    );
    d.with_note(note)
}
