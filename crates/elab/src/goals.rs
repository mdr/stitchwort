//! Goal holes, `?` (docs/proposals/lsp-goal-holes.md §4).
//!
//! A `?` checked against a type `T` becomes a fresh *frozen* metavariable
//! (`Globals::frozen_metas`) applied to the variables in scope: unification
//! never solves it, so nothing fills the hole in by accident. The goal (where
//! it is, `T`, and the names in scope) is noted, and checking carries on, so
//! every hole in a declaration is reported.
//!
//! The goals are printed at the end of the declaration, while the
//! metavariables in them are solved, as the navigation recorder prints
//! types (`nav.rs`); the ones an undone attempt noted are dropped with it
//! (`undo.rs`), and a hole checked twice keeps the last.
//!
//! A declaration with an open goal can never be finished: zonking a term
//! that still has a goal's metavariable in it fails with
//! [`UNFINISHED`] ([`Elaborator::zonk_around`]), so it's never sent to the
//! kernel. The module then reports the declaration as *unfinished*, not as
//! an error (`module.rs`); what uses it is unfinished too.

use stitchwort_core::globals::HashKey;
use stitchwort_core::globals::State;
use stitchwort_core::pretty::{Declaration, NameScope};
use stitchwort_core::value::{Head, force, quote_shown};
use stitchwort_core::{Globals, Name, Term, Value, pretty};
use stitchwort_syntax::{Diagnostic, GoalData, Hypothesis, Span};

use crate::Elaborator;
use crate::check::Ctx;
use crate::scope::Resolved;

/// The code of the error that stands for "unfinished": a term with an open
/// goal in it, or one that uses an unfinished declaration. The module turns
/// it into the declaration being unfinished, and never reports it as an
/// error; where it can't (an expression typed into `eval`), it reads as
/// one.
pub(crate) const UNFINISHED: &str = "E-UNFINISHED";

/// A goal noted, not printed yet.
#[derive(Clone)]
pub(crate) struct Pending {
    span: Span,
    /// The frozen metavariable standing for the hole.
    meta: usize,
    expected: Value,
    /// The context's display names, for printing.
    names: Vec<Name>,
    /// The entries of the context shown.
    context: Vec<Entry>,
    /// What the hole is in: "`addZero`".
    owner: String,
    /// What a lemma of the goal is named after: the declaration's name less
    /// its namespace (`addZero`); `None` in a test or an expression, or for
    /// a name that isn't a plain one.
    lemma_base: Option<String>,
    /// Whether the goal is a proposition, if that was known when the hole
    /// was checked: a lemma of it is then a `theorem`, else a `def`.
    prop: Option<bool>,
}

#[derive(Clone)]
struct Entry {
    /// As shown: `n`, or `n✝` for one that can't be referred to here.
    name: String,
    ty: Value,
    /// For a `let` of data, its value.
    value: Option<Value>,
    /// Its level in the context.
    level: usize,
}

/// A goal printed: its diagnostic, and the lemma it makes, less the
/// lemma's name ([`Elaborator::take_goals`] numbers them).
#[derive(Clone)]
struct Found {
    span: Span,
    diagnostic: Diagnostic,
    /// [`Pending::lemma_base`].
    base: Option<String>,
    /// The lemma's keyword, and what follows its name.
    lemma: Option<(&'static str, String)>,
}

/// The goals of the declaration being checked.
#[derive(Clone, Default)]
pub(crate) struct Goals {
    pending: Vec<Pending>,
    /// Printed: one per span, the last checked there.
    found: Vec<Found>,
}

/// The goal of a `match reify` `return` clause's `?`, written in terms of
/// the statement: its folded form, with the computation replaced by the
/// variable the clause binds, and the thunk by one that returns it. Only
/// what is shown: the hole's type, as checked, is the computed goal.
fn display_goal(cx: &Ctx) -> Option<Value> {
    let shown = cx.reify_display.as_ref()?;
    if shown.hole != cx.span {
        return None;
    }
    let result = cx.lookup(&shown.result)?;
    let level = cx.level();
    let base = shown.base;
    let done =
        |under: usize| Term::ctor(shown.comp, 0, vec![Term::Var(level + under - 1 - result)]);
    let hook = |t: &Term, under: usize| {
        if crate::matching::same_shifted(&shown.computation, t, under, 0) {
            return Some(done(under));
        }
        // A thunk of the computation: `() => y`.
        let Term::Lam(_, icit, body) = t.strip_loc() else {
            return None;
        };
        let applied_thunk = match (shown.thunk, body.strip_loc()) {
            (Some(thunk), Term::App(f, _, _)) => {
                matches!(f.strip_loc(), Term::Var(ix) if *ix == under + base - thunk)
            }
            _ => false,
        };
        (applied_thunk || crate::matching::same_shifted(&shown.computation, body, under + 1, 0))
            .then(|| Term::Lam("()".into(), *icit, std::rc::Rc::new(done(under + 1))))
    };
    let term = crate::lift::replace_with(
        cx.g(),
        &shown.folded,
        base,
        &|l| Ok(Term::Var(level - 1 - l)),
        &hook,
    )
    .ok()?;
    cx.eval(&term).ok()
}

/// `?` checked against `expected`: the hole's frozen metavariable, applied
/// to the variables in scope (those a case split hasn't replaced), as a
/// term. Notes the goal.
pub(crate) fn hole(cx: &Ctx, expected: &Value) -> Term {
    let g = cx.g();
    let m = g.new_meta(cx.span);
    g.freeze_meta(m);
    let mut term = Term::Meta(m);
    let mut context = Vec::new();
    for (level, value) in cx.env.iter().enumerate() {
        let own =
            matches!(value, Value::Neutral(Head::Var(l, _), s) if *l == level && s.is_empty());
        if own {
            term = Term::app(term, Term::Var(cx.level() - 1 - level));
        }
        let is_let = cx.lets[level].is_some();
        let name = &cx.names[level];
        // A variable a case split has replaced by a constructor is gone; a
        // compiler-made one (`%…`), or one bound as `_`, means nothing to the
        // reader.
        if !(own || is_let) || name.starts_with('%') || &**name == "_" {
            continue;
        }
        let name = match cx.name_of_level(level) {
            Some(n) => n.to_string(),
            None if name.ends_with('✝') => name.to_string(),
            None => format!("{name}✝"),
        };
        let ty = cx.types[level].clone();
        // A proof's value is its proof term: only its statement is shown.
        let shows_value = is_let && !crate::rewrite::is_proof_type(cx, &ty).unwrap_or(false);
        context.push(Entry {
            name,
            ty,
            value: shows_value.then(|| value.clone()),
            level,
        });
    }
    let prop = match force(g, expected.clone()) {
        Ok(Value::Neutral(Head::Meta(_), _)) | Err(_) => None,
        Ok(_) => crate::rewrite::is_proof_type(cx, expected).ok(),
    };
    let shown = display_goal(cx);
    let (owner, lemma_base) = cx.e.goal_owner();
    cx.e.goals.borrow_mut().pending.push(Pending {
        span: cx.span,
        meta: m,
        expected: shown.unwrap_or_else(|| expected.clone()),
        names: cx.names.clone(),
        context,
        owner,
        lemma_base,
        prop,
    });
    term
}

/// The error a term with an open goal in it gives when it's finished
/// ([`UNFINISHED`]).
pub(crate) fn open_goal(span: Span) -> Diagnostic {
    Diagnostic::error(UNFINISHED, "this isn't finished: it has an open goal, `?`")
        .with_label(span, "write what goes here in place of the `?`")
}

/// The error for something that uses an unfinished declaration, at `span`
/// if known ([`UNFINISHED`]).
pub(crate) fn uses_unfinished(span: Option<Span>) -> Diagnostic {
    let d = Diagnostic::error(
        UNFINISHED,
        "this isn't finished: it uses a declaration with an open goal, `?`",
    );
    match span {
        Some(span) => d.with_label(span, "this uses a declaration that isn't finished"),
        None => d,
    }
}

/// The kernel refused a declaration because `terms` (its body, or type)
/// use a failed declaration: if every failed declaration they use is
/// unfinished, the refusal becomes [`UNFINISHED`]. `own` are the
/// declarations being admitted, failed by the refusal itself.
pub(crate) fn unfinished_dependency<'t>(
    g: &Globals,
    terms: impl IntoIterator<Item = &'t Term>,
    own: &[HashKey],
    error: Diagnostic,
) -> Diagnostic {
    if error.code != "E-FAILED-DEPENDENCY" || g.unfinished.borrow().is_empty() {
        return error;
    }
    let unfinished = g.unfinished.borrow();
    let mut any = false;
    for term in terms {
        for (t, _) in term.subterms() {
            let (key, state) = match t {
                Term::Def(id) if id.0 < g.defs.len() => (HashKey::Def(*id), g.def(*id).state()),
                Term::Data(d, _) | Term::Ctor(d, _, _) | Term::Case(_, d, _)
                    if d.0 < g.datas.len() =>
                {
                    (HashKey::Data(*d), g.data(*d).state())
                }
                _ => continue,
            };
            if state != State::Failed || own.contains(&key) {
                continue;
            }
            if !unfinished.contains(&key) {
                return error;
            }
            any = true;
        }
    }
    if any {
        uses_unfinished(error.primary_span())
    } else {
        error
    }
}

impl Elaborator {
    /// Whether metavariable `m` is an open goal's.
    pub(crate) fn is_goal(&self, m: usize) -> bool {
        self.goals.borrow().pending.iter().any(|p| p.meta == m)
    }

    /// Whether a goal noted, not printed yet, is at `span`.
    pub(crate) fn has_goal_at(&self, span: Span) -> bool {
        self.goals.borrow().pending.iter().any(|p| p.span == span)
    }

    /// How many goals are noted and not printed: a
    /// [`crate::undo::Snapshot`] keeps it, to drop the ones an undone
    /// attempt noted.
    pub(crate) fn pending_goals(&self) -> usize {
        self.goals.borrow().pending.len()
    }

    /// Drops the goals noted after the first `len`: their attempt was
    /// undone, and their metavariables with it.
    pub(crate) fn drop_goals_since(&self, len: usize) {
        self.goals.borrow_mut().pending.truncate(len);
    }

    /// What a goal noted now is in, for its heading; and what a lemma of it
    /// is named after (`Pending::lemma_base`).
    fn goal_owner(&self) -> (String, Option<String>) {
        let item = self.module.item.or(self.module.current.first().copied());
        match item.and_then(|i| self.module.items.get(i)) {
            Some(item) if item.kind == crate::module::Kind::Test => (item.name.clone(), None),
            Some(item) => {
                let last = item.name.rsplit('.').next().unwrap_or(&item.name);
                let base = is_identifier(last).then(|| last.to_string());
                (format!("`{}`", item.name), base)
            }
            None => ("this expression".to_string(), None),
        }
    }

    /// Prints the goals noted, while the metavariables in them still have
    /// their solutions. A goal at a span already printed replaces it.
    pub(crate) fn flush_goals(&self) {
        let pending = std::mem::take(&mut self.goals.borrow_mut().pending);
        if pending.is_empty() {
            return;
        }
        let g = &self.globals;
        // Printing a goal that mentions a failed declaration isn't an error
        // message showing it (`Globals::failed_mentioned`).
        let mentioned = g.failed_mentioned.get();
        let printed: Vec<Found> = pending
            .iter()
            .map(|p| {
                // With gluing, as while checking: calls stay folded, also
                // under binders.
                let was = g.glue.replace(self.glue);
                let printed = self.print_goal(p);
                g.glue.set(was);
                printed
            })
            .collect();
        g.failed_mentioned.set(mentioned);
        let mut goals = self.goals.borrow_mut();
        for found in printed {
            goals.found.retain(|f| f.span != found.span);
            goals.found.push(found);
        }
    }

    fn print_goal(&self, p: &Pending) -> Found {
        let g = &self.globals;
        let show = |v: &Value| pretty::value_for_goal(g, self, &p.names, v);
        let hypotheses: Vec<Hypothesis> = p
            .context
            .iter()
            .map(|e| Hypothesis {
                name: e.name.clone(),
                ty: show(&e.ty),
                value: e.value.as_ref().map(show),
            })
            .collect();
        let mut lines: Vec<String> = hypotheses
            .iter()
            .map(|h| match &h.value {
                Some(value) => format!("{}: {} := {}", h.name, h.ty, value),
                None => format!("{}: {}", h.name, h.ty),
            })
            .collect();
        // Forcing leaves a metavariable only if it's unsolved.
        let known = !matches!(
            force(g, p.expected.clone()),
            Ok(Value::Neutral(Head::Meta(_), _))
        );
        let target = if known {
            show(&p.expected)
        } else {
            "(the type here isn't known yet)".to_string()
        };
        lines.push(format!("⊢ {target}"));
        let lemma = if known {
            self.lemma_of(p, &hypotheses, &target).ok()
        } else {
            None
        };
        let mut diagnostic =
            Diagnostic::goal(format!("in {}", p.owner)).with_label(p.span, lines.join("\n"));
        diagnostic.goal = Some(Box::new(GoalData {
            hypotheses,
            target,
            lemma: None,
        }));
        Found {
            span: p.span,
            diagnostic,
            base: p.lemma_base.clone(),
            lemma,
        }
    }

    /// The goal `p`, printed as `hypotheses` and `target`, as a declaration
    /// of its own less its name: its keyword, and what follows the name
    /// (` (n: Nat): n + 0 = n := ?`). Or why not, if it might not mean the
    /// same at the top level of the file (docs/proposals/code-navigation.md,
    /// "Goals"): a `let` of data is in scope (its value would be lost); a
    /// name in it can't be written there (`n✝`, a compiler-made `%x`, a
    /// declaration or constructor that needs an import); it mentions a
    /// variable the goal doesn't show (a `_`), or a hypothesis mentions a
    /// later one; a part isn't shown in full (`…`) or isn't known (`?`);
    /// or whether it's a proposition wasn't known.
    fn lemma_of(
        &self,
        p: &Pending,
        hypotheses: &[Hypothesis],
        target: &str,
    ) -> Result<(&'static str, String), &'static str> {
        let keyword = match p.prop {
            Some(true) => "theorem",
            Some(false) => "def",
            None => return Err("prop unknown"),
        };
        if p.context.iter().any(|e| e.value.is_some()) {
            return Err("let of data");
        }
        if !hypotheses.iter().all(|h| is_identifier(&h.name)) {
            return Err("unwritable hypothesis name");
        }
        // `%` before a name: a compiler-made one (`n % 2` is fine).
        let unwritable = |text: &str| {
            text.contains(['✝', '?', '…', '\n'])
                || text.contains("(body of ")
                || text
                    .split('%')
                    .skip(1)
                    .any(|after| after.starts_with(|c: char| c.is_alphanumeric() || c == '_'))
        };
        if unwritable(target) || hypotheses.iter().any(|h| unwritable(&h.ty)) {
            return Err("unwritable text");
        }
        // Every variable the goal mentions is one it shows, a hypothesis's
        // type mentioning only those before it (a case split can refine an
        // earlier one's type with a later one).
        let g = &self.globals;
        let level = p.names.len();
        let levels: Vec<usize> = p.context.iter().map(|e| e.level).collect();
        let mut declarations = Vec::new();
        let mut ctors = Vec::new();
        let mut writable = |v: &Value, shown: &[usize]| {
            let Ok(term) = quote_shown(g, level, v) else {
                return false;
            };
            term.subterms().all(|(t, binders)| match t {
                Term::Var(i) | Term::Case(i, ..) | Term::NumCase(i, ..) => {
                    *i < binders
                        || (i - binders < level && shown.contains(&(level - 1 - (i - binders))))
                }
                Term::Meta(_) => false,
                Term::Def(id) if id.0 < g.defs.len() => {
                    declarations.push(Declaration::Def(*id));
                    true
                }
                Term::Data(d, _) if d.0 < g.datas.len() => {
                    declarations.push(Declaration::Data(*d));
                    true
                }
                Term::Ctor(d, c, _) if d.0 < g.datas.len() => {
                    ctors.push((*d, *c));
                    true
                }
                Term::Def(_) | Term::Data(..) | Term::Ctor(..) => false,
                _ => true,
            })
        };
        if !writable(&p.expected, &levels) {
            return Err("target mentions a hidden variable");
        }
        if !(p.context.iter().enumerate()).all(|(k, e)| writable(&e.ty, &levels[..k])) {
            return Err("hypothesis mentions a hidden or later variable");
        }
        // Every declaration it names, it names as the top level of the file
        // can. The printer names one by the shortest part of its name that
        // means it here, else by its whole name, which may need an import
        // there (`List.count`, of `Std.List.count`). One shown as notation
        // (`+`, a record update) isn't named.
        let text: Vec<&str> = std::iter::once(target)
            .chain(hypotheses.iter().map(|h| h.ty.as_str()))
            .collect();
        for declaration in declarations {
            let full = match declaration {
                Declaration::Def(id) => &*g.def(id).name,
                Declaration::Data(d) => &*g.data(d).name,
            };
            let parts: Vec<&str> = full.split('.').collect();
            let resolves = (0..parts.len()).any(|start| {
                let written = parts[start..].join(".");
                self.names(&written, declaration)
                    && matches!(self.resolve(&written), Resolved::Found { .. })
            });
            let shown = |t: &&str| {
                (0..parts.len()).any(|start| mentions_name(t, &parts[start..].join(".")))
            };
            if !resolves && text.iter().any(shown) {
                return Err("names a declaration it can't");
            }
        }
        // A constructor is shown by its own name (`Done y`), unless as a
        // literal or a record.
        for (d, c) in ctors {
            let name = &*g.data(d).ctors[c].name;
            let resolves = matches!(
                self.resolve(name),
                Resolved::Found { global: crate::Global::Ctor(e, k), .. } if e == d && k == c
            );
            if !resolves && text.iter().any(|t| mentions_name(t, name)) {
                return Err("names a constructor it can't");
            }
        }
        // A type that starts with a record update, `{ p | gold = 3 } = p`,
        // reads after a `:` as a block: it goes in brackets.
        let bracketed = |ty: &str| {
            if ty.starts_with('{') {
                format!("({ty})")
            } else {
                ty.to_string()
            }
        };
        let mut rest = String::new();
        for h in hypotheses {
            rest.push_str(&format!(" ({}: {})", h.name, bracketed(&h.ty)));
        }
        rest.push_str(&format!(": {} := ?", bracketed(target)));
        Ok((keyword, rest))
    }

    /// The goals printed since this was last called, in source order, each
    /// lemma named after its declaration and its place among the
    /// declaration's goals (`addZeroGoal2`; `goal1` in a test).
    pub(crate) fn take_goals(&self) -> Vec<Diagnostic> {
        self.flush_goals();
        let mut found = std::mem::take(&mut self.goals.borrow_mut().found);
        found.sort_by_key(|f| (f.span.file.index(), f.span.start));
        let mut counts: Vec<(Option<String>, usize)> = Vec::new();
        found
            .into_iter()
            .map(|f| {
                let n = match counts.iter_mut().find(|(b, _)| *b == f.base) {
                    Some((_, n)) => {
                        *n += 1;
                        *n
                    }
                    None => {
                        counts.push((f.base.clone(), 1));
                        1
                    }
                };
                let mut d = f.diagnostic;
                if let (Some((keyword, rest)), Some(goal)) = (f.lemma, d.goal.as_mut()) {
                    let name = match &f.base {
                        Some(base) => format!("{base}Goal{n}"),
                        None => format!("goal{n}"),
                    };
                    goal.lemma = Some(format!("{keyword} {name}{rest}"));
                }
                d
            })
            .collect()
    }

    /// Forgets every goal, noted or printed.
    pub(crate) fn clear_goals(&self) {
        *self.goals.borrow_mut() = Goals::default();
    }
}

/// Whether `text` has `name` in it as a whole name: `List.count` is in
/// `List.count xs`, but not in `Std.List.counts`.
fn mentions_name(text: &str, name: &str) -> bool {
    let part_of_name = |c: char| c.is_alphanumeric() || matches!(c, '_' | '\'' | '.' | '%');
    text.match_indices(name).any(|(at, _)| {
        !text[..at].ends_with(part_of_name) && !text[at + name.len()..].starts_with(part_of_name)
    })
}

/// Whether `name` can be written as a plain name: `n`, `xs'`, `h_1`.
fn is_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    chars.next().is_some_and(|c| c.is_alphabetic() || c == '_')
        && chars.all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
        && name != "_"
}
