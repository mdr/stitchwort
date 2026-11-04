//! `@[tailrec]` (docs/proposals/tailrec.md): the check that every recursive
//! call of a marked definition is a tail call.
//!
//! It runs on the elaborated core terms the runtimes run, once the
//! definition's group is admitted, so it sees what the backends see: `if` is
//! `Bool.ifThenElse` with a lambda for each branch, `&&` is an `if`, a dot
//! call is an application, and a block of effects is a chain of
//! `Effect.bind`s. A call is in **tail position** when its result is the
//! definition's result with nothing left to do: it is reached from the body
//! through the arms of a case tree, the branches of an `if`, the body of a
//! `let`, the continuation of a `bind`, or a `match` lifted out of the
//! definition (`f.%match1`, which is part of `f`). Anything else holding the
//! call (an argument, an operand, a constructor's field, a `let`'s value, a
//! lambda, a handler, a scrutinee) makes it not one.
//!
//! The recursive function is the definition itself, or, for a definition by
//! `decreasing`, the `%rec` parameter of `f.%step` (and of the `match`es
//! lifted from it), which stands for `f`. Calls to another member of a
//! mutual group are not covered yet (D2312).

use stitchwort_core::collections::HashSet;

use stitchwort_core::registry::Builtin;
use stitchwort_core::{DefId, Ev, Term};
use stitchwort_syntax::{Diagnostic, Span};

use crate::{Elaborator, Result};

/// What holds a call that is not in tail position, for the label.
#[derive(Clone)]
enum Why {
    /// An operand of an operator (`+`), or an argument of a named function.
    Argument { callee: String, operator: bool },
    /// A field of a constructor.
    Field { constructor: String },
    /// The condition of an `if`.
    Condition,
    /// What a `match` is on (the argument of a lifted `match`).
    Scrutinee,
    /// The value of a `let`, bound to a name; `returned` if the body is just
    /// that name.
    Let { name: String, returned: bool },
    /// The first part of a block of effects; the rest goes on after it. With
    /// `returned`, the rest only returns its result.
    Effect { returned: bool },
    /// Inside a function, which runs when something calls it.
    Lambda { passed_to: Option<String> },
    /// Inside `handle … with`.
    Handler,
    /// Converted to the caller's effect row.
    Conversion,
    /// Used as a value, not called.
    Value,
    /// Wrapped as an effectful function's result.
    Done,
    /// Used by the code around it, which runs after it returns.
    Used,
    /// Inside a `match` that is not in tail position.
    Match(Box<Why>),
}

#[derive(Clone)]
enum Pos {
    Tail,
    Not(Why),
}

impl Why {
    fn label(&self) -> String {
        match self {
            Why::Argument {
                callee,
                operator: true,
            } => format!("its result is an operand of {callee}, which runs after it returns"),
            Why::Argument { callee, .. } => {
                format!("its result is passed to {callee}, which runs after it returns")
            }
            Why::Field { constructor } => format!(
                "its result goes into a field of `{constructor}`, which is built after it returns"
            ),
            Why::Condition => "its result decides an `if`, which is tested after it returns".into(),
            Why::Scrutinee => "its result is matched on after it returns".into(),
            Why::Let {
                name,
                returned: false,
            } => format!("its result is bound to `{name}`, and the block goes on after it"),
            Why::Let {
                name,
                returned: true,
            } => format!(
                "its result is bound to `{name}` and then returned: write the call itself as \
                 the result"
            ),
            Why::Effect { returned: false } => {
                "the rest of the block goes on after this call returns, using its result".into()
            }
            Why::Effect { returned: true } => {
                "its result is bound and then returned: make the call itself the last \
                 statement"
                    .into()
            }
            Why::Lambda {
                passed_to: Some(callee),
            } => format!(
                "it's inside a function passed to {callee}: it runs when {callee} calls it, \
                 not as a turn of this loop"
            ),
            Why::Lambda { passed_to: None } => {
                "it's inside a function (`x => …`): it runs when something calls that function, \
                 not as a turn of this loop"
                    .into()
            }
            Why::Handler => "it's inside `handle … with`: the handler waits for its result, so \
                 each call adds a handler"
                .into(),
            Why::Conversion => {
                "its result is converted to this function's effect row after it returns".into()
            }
            Why::Value => "it's used as a value here, not called".into(),
            Why::Used => {
                "its result is used by the expression around it, which runs after it returns".into()
            }
            Why::Done => "its result is wrapped as this function's result after it returns".into(),
            Why::Match(inner) => format!(
                "this `match` is not the last thing done, and {}",
                inner.label()
            ),
        }
    }

    /// Whether the call is a statement of a block of effects.
    fn in_block(&self) -> bool {
        match self {
            Why::Effect { .. } => true,
            Why::Match(inner) => inner.in_block(),
            _ => false,
        }
    }

    fn is_field(&self) -> bool {
        match self {
            Why::Field { .. } => true,
            Why::Match(inner) => inner.is_field(),
            _ => false,
        }
    }
}

/// The operator a library function is written as.
fn operator(name: &str) -> Option<&'static str> {
    Some(match name {
        "Nat.add" | "Int.add" | "Float.add" => "+",
        "Nat.sub" | "Int.sub" | "Float.sub" => "-",
        "Nat.mul" | "Int.mul" | "Float.mul" => "*",
        "Nat.div" | "Int.div" => "/",
        "Nat.mod" | "Int.mod" => "%",
        "List.append" | "Text.append" => "++",
        _ => return None,
    })
}

/// What the walk found.
struct Walk<'a> {
    g: &'a Ev<'a>,
    /// The marked definition.
    root: DefId,
    /// Its name, for messages.
    name: String,
    /// `f.%step`'s `%rec` stands for the definition (`decreasing`).
    by_param: bool,
    /// The level of the `%rec` parameter of the unit being walked.
    rec_level: Option<usize>,
    /// The definition (or `f.%step`) whose `match`es are walked as part of it.
    unit_path: String,
    /// Members of the group that call back into the definition, other than
    /// its own `match`es: a mutual group.
    mutual: HashSet<DefId>,
    /// The helpers walked, and in which position.
    visited: HashSet<(DefId, bool)>,
    /// A recursive call was met.
    found: bool,
    cur: Span,
    errors: Vec<(Span, Why)>,
    mutual_calls: Vec<(Span, String)>,
}

impl Elaborator {
    /// Checks that definition `id`, marked `@[tailrec]`, calls itself only in
    /// tail position (`E-TAILREC`).
    pub(crate) fn check_tailrec(&self, id: DefId) -> Result<()> {
        let g = &self.ev();
        let def = g.def(id);
        let path = def.path().to_string();
        let name = def.name().to_string();
        // A definition by `decreasing` runs `f.%step`, whose `%rec` stands for
        // `f`.
        let step_path = format!("{path}.%step");
        let step = (0..g.env.defs().len())
            .map(DefId)
            .find(|d| &**g.def(*d).path() == step_path.as_str());
        let (unit, by_param) = match step {
            Some(step) if def.own_run_body().is_some() => (step, true),
            _ => (id, false),
        };
        let unit_path = g.def(unit).path().to_string();
        let group: Vec<DefId> = match g.def(id).group() {
            Some(group) => group.to_vec(),
            None => vec![id],
        };
        let mutual = reaching(g, id, &group, &unit_path);
        let mut walk = Walk {
            g,
            root: id,
            name,
            by_param,
            rec_level: None,
            unit_path,
            mutual,
            visited: HashSet::default(),
            found: false,
            cur: def.span(),
            errors: Vec::new(),
            mutual_calls: Vec::new(),
        };
        walk.visit(unit, &Pos::Tail);
        walk.finish(def.span())
    }
}

/// The members of `group` that reach `root` through calls among the group's
/// members, other than the `match`es lifted out of `unit_path`.
fn reaching(g: &Ev, root: DefId, group: &[DefId], unit_path: &str) -> HashSet<DefId> {
    let calls = |m: DefId| -> Vec<DefId> {
        let Some(body) = g.def(m).run_body() else {
            return Vec::new();
        };
        body.subterms()
            .filter_map(|(t, _)| match t {
                Term::Def(d) if group.contains(d) => Some(*d),
                _ => None,
            })
            .collect()
    };
    let mut reaches: HashSet<DefId> = HashSet::default();
    reaches.insert(root);
    loop {
        let before = reaches.len();
        for &m in group {
            if !reaches.contains(&m) && calls(m).iter().any(|d| reaches.contains(d)) {
                reaches.insert(m);
            }
        }
        if reaches.len() == before {
            break;
        }
    }
    reaches.remove(&root);
    reaches.retain(|m| !is_part(g.def(*m).path(), unit_path));
    reaches
}

/// Whether `path` is a `match` lifted out of the definition at `unit`
/// (`unit.%match1`, or one nested in it).
fn is_part(path: &str, unit: &str) -> bool {
    path.strip_prefix(unit)
        .and_then(|rest| rest.strip_prefix('.'))
        .is_some_and(|rest| rest.split('.').all(|part| part.starts_with("%match")))
}

/// A term without its locations and annotations.
fn peel(t: &Term) -> &Term {
    let mut t = t;
    loop {
        match t {
            Term::Loc(_, inner) | Term::Ann(inner, _) => t = inner,
            _ => return t,
        }
    }
}

/// An application's head and arguments, with whether each is implicit.
fn spine(t: &Term) -> (&Term, Vec<(&Term, bool)>) {
    let mut args = Vec::new();
    let mut head = peel(t);
    while let Term::App(f, a, icit) = head {
        args.push((a.as_ref(), icit.is_implicit()));
        head = peel(f);
    }
    args.reverse();
    (head, args)
}

impl Walk<'_> {
    fn finish(self, def_span: Span) -> Result<()> {
        if !self.mutual_calls.is_empty() {
            let mut d = Diagnostic::error(
                "E-TAILREC",
                format!(
                    "`{}` is marked @[tailrec], but calls a definition that calls it back",
                    self.name
                ),
            );
            for (span, callee) in &self.mutual_calls {
                d = d.with_label(*span, format!("`{callee}` calls `{}` back", self.name));
            }
            return Err(d.with_note(
                "calls between mutually recursive definitions aren't covered by @[tailrec] yet; \
                 write the recursion as one function",
            ));
        }
        if !self.found {
            return Err(Diagnostic::error(
                "E-TAILREC",
                format!(
                    "`{}` is marked @[tailrec], but never calls itself",
                    self.name
                ),
            )
            .with_label(def_span, "marked @[tailrec]")
            .with_note(
                "if the recursion moved into a helper, mark the helper; otherwise remove \
                 @[tailrec]",
            ));
        }
        if self.errors.is_empty() {
            return Ok(());
        }
        let many = self.errors.len() > 1;
        let mut d = Diagnostic::error(
            "E-TAILREC",
            if many {
                format!(
                    "`{}` is marked @[tailrec], but {} recursive calls aren't in tail position",
                    self.name,
                    self.errors.len()
                )
            } else {
                format!(
                    "`{}` is marked @[tailrec], but a recursive call isn't in tail position",
                    self.name
                )
            },
        );
        for (span, why) in &self.errors {
            d = d.with_label(*span, why.label());
        }
        d = d.with_note(
            "a call is in tail position when its result is the function's result, with nothing \
             left to do after it returns; then each call is a turn of a loop, not a new frame",
        );
        if self.errors.iter().any(|(_, why)| why.is_field()) {
            d = d.with_note(
                "building a list or a tree around the call is cheap on `stitchwort run` and in \
                 JavaScript, but @[tailrec] promises only true tail calls: carry the result in \
                 an extra parameter and reverse it at the end",
            );
        } else if self.errors.iter().any(|(_, why)| {
            matches!(
                why,
                Why::Argument { .. }
                    | Why::Let {
                        returned: false,
                        ..
                    }
                    | Why::Effect { .. }
            )
        }) {
            d = d.with_note(
                "to use the result, carry it along in an extra parameter (an accumulator) that \
                 the call updates",
            );
        }
        Err(d)
    }

    /// Walks the helper or definition `id`, whose body is part of the one
    /// being checked, with its result at `pos`.
    fn visit(&mut self, id: DefId, pos: &Pos) {
        let tail = matches!(pos, Pos::Tail);
        if !self.visited.insert((id, tail)) {
            return;
        }
        let def = self.g.def(id);
        let Some(body) = def.run_body() else {
            return;
        };
        let arity = def.arity();
        let mut params = Vec::new();
        let mut t = body.strip_loc();
        let mut span = def.span();
        for _ in 0..arity {
            match t {
                Term::Lam(x, _, inner) => {
                    params.push(x.clone());
                    t = inner.strip_loc();
                }
                Term::Loc(s, inner) => {
                    span = *s;
                    t = inner;
                }
                _ => break,
            }
        }
        let saved = (self.rec_level, self.cur);
        self.rec_level = params.iter().position(|x| &**x == "%rec");
        self.cur = span;
        self.walk(t, pos, params.len());
        (self.rec_level, self.cur) = saved;
    }

    fn is_target(&self, t: &Term, depth: usize) -> bool {
        match peel(t) {
            Term::Def(d) => !self.by_param && *d == self.root,
            Term::Var(i) => {
                self.by_param
                    && self
                        .rec_level
                        .is_some_and(|l| depth.checked_sub(1 + i) == Some(l))
            }
            _ => false,
        }
    }

    /// Records a recursive call at `pos`. `arguments` is where its arguments
    /// are written: a call the elaborator made out of a block of effects has
    /// no location of its own (its location is the whole block), so then the
    /// label is put on them.
    fn note(&mut self, pos: &Pos, arguments: Option<Span>) {
        self.found = true;
        if let Pos::Not(why) = pos {
            let span = match (why.in_block(), arguments) {
                (true, Some(arguments)) => arguments,
                _ => self.cur,
            };
            self.errors.push((span, why.clone()));
        }
    }

    fn def_display(&self, d: DefId) -> String {
        let def = self.g.def(d);
        let name = def.name().to_string();
        format!("`{}`", operator(&name).unwrap_or(&name))
    }

    fn walk_all<'t>(
        &mut self,
        args: impl IntoIterator<Item = &'t Term>,
        callee: &str,
        operator: bool,
        depth: usize,
    ) {
        for arg in args {
            let why = Why::Argument {
                callee: callee.to_string(),
                operator,
            };
            self.walk(arg, &Pos::Not(why), depth);
        }
    }

    fn walk(&mut self, t: &Term, pos: &Pos, depth: usize) {
        match t {
            Term::Loc(span, inner) => {
                let saved = self.cur;
                self.cur = *span;
                self.walk(inner, pos, depth);
                self.cur = saved;
            }
            Term::Ann(e, _) => self.walk(e, pos, depth),
            Term::Var(_) => {
                if self.is_target(t, depth) {
                    self.note(&Pos::Not(Why::Value), None);
                }
            }
            Term::Def(d) => {
                if self.is_target(t, depth) {
                    self.note(&Pos::Not(Why::Value), None);
                } else if self.mutual.contains(d) {
                    let callee = self.g.def(*d).name().to_string();
                    self.mutual_calls.push((self.cur, callee));
                }
            }
            Term::App(..) => self.walk_app(t, pos, depth),
            Term::Lam(_, _, body) => {
                let passed_to = match pos {
                    Pos::Not(Why::Argument { callee, .. }) => Some(callee.clone()),
                    _ => None,
                };
                self.walk(body, &Pos::Not(Why::Lambda { passed_to }), depth + 1);
            }
            Term::Let(x, _, value, body, _) => {
                let returned = matches!(peel(body), Term::Var(0));
                // A name the compiler made up means nothing to the reader.
                let why = if x.starts_with('%') {
                    Why::Used
                } else {
                    Why::Let {
                        name: x.to_string(),
                        returned,
                    }
                };
                self.walk(value, &Pos::Not(why), depth);
                self.walk(body, pos, depth + 1);
            }
            Term::Case(_, _, branches) => {
                for branch in branches.iter() {
                    if let Some(body) = &branch.body {
                        self.walk(body, pos, depth + branch.names.len());
                    }
                }
            }
            Term::NumCase(_, arms, default) => {
                for arm in arms.iter() {
                    self.walk(&arm.body, pos, depth);
                }
                self.walk(default, pos, depth);
            }
            Term::Ctor(d, c, args) => {
                let data = self.g.data(*d);
                let done = self.g.env.registry().data(Builtin::Comp) == Some(*d) && *c == 0;
                // `Done v` adds nothing to what already holds the call.
                let why = if done {
                    match pos {
                        Pos::Not(outer) => outer.clone(),
                        Pos::Tail => Why::Done,
                    }
                } else {
                    Why::Field {
                        constructor: data.ctors()[*c].name.to_string(),
                    }
                };
                for arg in args {
                    self.walk(arg, &Pos::Not(why.clone()), depth);
                }
            }
            Term::Quot(_, args, _) => {
                for arg in args {
                    let why = Why::Argument {
                        callee: "`Quot`".into(),
                        operator: false,
                    };
                    self.walk(arg, &Pos::Not(why), depth);
                }
            }
            // Types, proofs and numbers make no calls.
            Term::Data(..)
            | Term::Pi(..)
            | Term::Sort(_)
            | Term::Eq(..)
            | Term::Refl
            | Term::J(..)
            | Term::Nat(_)
            | Term::Chars(_)
            | Term::Meta(_) => {}
        }
    }

    fn walk_app(&mut self, t: &Term, pos: &Pos, depth: usize) {
        let (head, args) = spine(t);
        let explicit: Vec<&Term> = args.iter().filter(|(_, i)| !i).map(|(a, _)| *a).collect();
        let g = self.g;
        if self.is_target(head, depth) {
            let arguments = args
                .iter()
                .filter_map(|(a, _)| match a {
                    Term::Loc(span, _) => Some(*span),
                    _ => None,
                })
                .reduce(|first, last| first.to(last));
            self.note(pos, arguments);
            let name = format!("`{}`", self.name);
            self.walk_all(args.iter().map(|(a, _)| *a), &name, false, depth);
            return;
        }
        let Term::Def(d) = head else {
            if let Term::Lam(_, _, body) = head
                && let [(arg, _)] = args[..]
            {
                // `(x => body) arg`, which the elaborator makes where it
                // generalises a value: like `let x := arg; body`.
                self.walk(arg, &Pos::Not(Why::Used), depth);
                self.walk(body, pos, depth + 1);
                return;
            }
            // A function value applied: its result is used by that call.
            if !matches!(head, Term::Var(_)) {
                self.walk(head, &Pos::Not(Why::Value), depth);
            }
            self.walk_all(args.iter().map(|(a, _)| *a), "a function", false, depth);
            return;
        };
        let d = *d;
        let path = g.def(d).path().to_string();
        let registry = g.env.registry();
        // `if c then a else b` and `if h: c then a else b`.
        if (registry.def(Builtin::IfThenElse) == Some(d)
            || registry.def(Builtin::ElimDec) == Some(d))
            && let [c, a, b] = explicit[..]
            && let (Term::Lam(_, _, a), Term::Lam(_, _, b)) = (peel(a), peel(b))
        {
            self.walk(c, &Pos::Not(Why::Condition), depth);
            self.walk(a, pos, depth + 1);
            self.walk(b, pos, depth + 1);
            return;
        }
        // A block of effects: the computation, then the rest.
        if matches!(
            path.as_str(),
            "Std.Effect.bind" | "Std.Effect.bindIn" | "Std.Effect.bindD" | "Std.Effect.bindDv"
        ) && let [.., computation, next] = explicit[..]
            && let Term::Lam(_, _, rest) = peel(next)
        {
            let returned = matches!(
                peel(rest),
                Term::Ctor(d, 0, fields)
                    if g.env.registry().data(Builtin::Comp) == Some(*d)
                        && matches!(fields[..], [ref v] if matches!(peel(v), Term::Var(0)))
            );
            self.walk(computation, &Pos::Not(Why::Effect { returned }), depth);
            self.walk(rest, pos, depth + 1);
            return;
        }
        if matches!(
            path.as_str(),
            "Std.Effect.foldComp" | "Std.Effect.foldCompD" | "Std.Effect.foldD"
        ) {
            for arg in explicit {
                self.walk(arg, &Pos::Not(Why::Handler), depth);
            }
            return;
        }
        if matches!(
            path.as_str(),
            "Std.Effect.translate" | "Std.Effect.translateD" | "Std.Effect.mapSig"
        ) {
            for arg in explicit {
                self.walk(arg, &Pos::Not(Why::Conversion), depth);
            }
            return;
        }
        // A `match` lifted out of the definition is part of it.
        if is_part(&path, &self.unit_path) {
            let inside = match pos {
                Pos::Tail => Pos::Tail,
                Pos::Not(why) => Pos::Not(Why::Match(Box::new(why.clone()))),
            };
            self.visit(d, &inside);
            for (arg, _) in &args {
                if !matches!(peel(arg), Term::Var(_)) {
                    self.walk(arg, &Pos::Not(Why::Scrutinee), depth);
                }
            }
            return;
        }
        if self.mutual.contains(&d) {
            let callee = g.def(d).name().to_string();
            self.mutual_calls.push((self.cur, callee));
        }
        let operator = operator(g.def(d).name()).is_some();
        let callee = self.def_display(d);
        self.walk_all(args.iter().map(|(a, _)| *a), &callee, operator, depth);
    }
}
