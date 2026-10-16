//! Termination checking for recursive definitions, and groups of definitions
//! that call each other, by size change (docs/proposals/mutual-recursion.md
//! §6).
//!
//! Every call from a member of the group to a member (itself or another) is
//! summarised as a size-change graph ([`crate::sct`]): for each of the
//! callee's parameters (its definition-entry arity, `Def::arity`), whether
//! the argument passed there is strictly smaller than (`<`), or at most
//! (`≤`), one of the caller's parameters, or unknown. The group is accepted
//! if every way of repeating its calls, in any order the calls allow, makes
//! some parameter strictly smaller ([`crate::sct::Group::check`]). So
//! lexicographic recursion (Ackermann's function), swapped arguments and a
//! wrapper that passes its argument on unchanged to a helper that makes it
//! smaller are accepted, as well as recursion that decreases the same
//! parameter in every call. Calls between *different* members are part of
//! the analysis exactly like calls to itself (Rocq's CVE-2026-72703 came from
//! leaving them out).
//!
//! An argument's relation comes only from the terms, never from types:
//!
//! - **`<`**: a variable bound as a field of a constructor matched (directly or
//!   through further matches) out of parameter `i`; a *recursive function
//!   field* (a field whose type is a function returning the matched data type,
//!   or another member of its data group, like `rest : res o -> Comp op res
//!   a`) applied to arguments, as in Rocq:
//!   each result is a child in the well-founded tree, and only the field
//!   variable itself counts, not some other function that happens to return
//!   the same type; and the constructor of such a descendant's match, applied
//!   to exactly the fields that match bound (in the branch where `m` is
//!   `Succ n`, `Succ n` *is* `m`).
//! - **`≤`**: parameter `i` itself, or the constructor of a match on parameter
//!   `i` itself, rebuilt exactly as above. Both are equal to the parameter.
//! - **unknown**: anything else, including lambda-bound variables, other
//!   functions' results, `J` (transport never yields a part) and numbers.
//!   A `NumCase` binds nothing, so it adds no evidence.
//!
//! Each argument is related to at most one parameter, the one it was matched
//! out of, so each graph has at most one arc into each position.
//!
//! **Every occurrence of a member is a call**, wherever it is: under lambdas,
//! inside types and inside the arguments of other calls. Each application
//! spine headed by a member is one call, with its own graph, never merged
//! with another (even one with the same caller and callee); all its
//! arguments are then walked for further calls, including any beyond the
//! arity. **Occurrences of members must be saturated**: applied to at least
//! the callee's entry arity's arguments, so that the call's graph says what
//! every parameter is given. A bare or partial occurrence is refused, with a
//! suggestion to write `\x -> f a x` (§6.3).

use stitchwort_syntax::{Diagnostic, Span};

use crate::budget::ResourceError;
use crate::globals::Globals;
use crate::pretty;
use crate::sct::{self, Label, Outcome};
use crate::term::{DataId, DefId, Icit, Name, Term};

/// Checks that `body`, the checked body of definition `self_id` (which hasn't
/// got a body yet), terminates: a group of one.
pub fn check(
    g: &Globals,
    body: &Term,
    self_id: DefId,
    name: &str,
    span: Span,
) -> Result<(), Diagnostic> {
    check_with_limit(g, body, self_id, name, span, sct::MAX_GRAPHS)
}

/// [`check`], allowing at most `max_graphs` distinct graphs in the closure of
/// the calls.
pub fn check_with_limit(
    g: &Globals,
    body: &Term,
    self_id: DefId,
    name: &str,
    span: Span,
    max_graphs: usize,
) -> Result<(), Diagnostic> {
    check_members(g, &[(self_id, body, name, span)], max_graphs)
}

/// A member of a group being checked: a definition (pending, with its arity
/// set) and its checked body.
pub struct Member<'a> {
    pub id: DefId,
    pub body: &'a Term,
}

/// Checks that the members of a group terminate together: every call from
/// any member to any member is in the analysis. Allows at most `max_graphs`
/// distinct graphs in the closure of the calls.
pub fn check_group(g: &Globals, members: &[Member], max_graphs: usize) -> Result<(), Diagnostic> {
    let members: Vec<(DefId, &Term, &str, Span)> = members
        .iter()
        .map(|m| {
            let def = g.def(m.id);
            (m.id, m.body, &*def.name, def.span)
        })
        .collect();
    check_members(g, &members, max_graphs)
}

/// The parameters of a member: its entry lambdas' names and implicitness.
type Params = Vec<(Name, Icit)>;

/// What the error messages need to know about a member.
struct MemberInfo<'a> {
    name: &'a str,
    params: Params,
    span: Span,
}

fn check_members(
    g: &Globals,
    members: &[(DefId, &Term, &str, Span)],
    max_graphs: usize,
) -> Result<(), Diagnostic> {
    let ids: Vec<DefId> = members.iter().map(|m| m.0).collect();
    let mut infos = Vec::new();
    let mut trees = Vec::new();
    for &(id, body, name, span) in members {
        let arity = g.def(id).arity;
        if body.count_lams() != arity {
            return Err(Diagnostic::error(
                "E-MALFORMED",
                format!(
                    "malformed core term: `{name}`'s body doesn't start with its {arity} \
                     parameters"
                ),
            )
            .with_label(span, "in this definition")
            .with_note("this is a bug in the compiler, not in your program"));
        }
        let mut params = Vec::new();
        let mut tree = body.strip_loc();
        while let Term::Lam(x, icit, inner) = tree {
            params.push((x.clone(), *icit));
            tree = inner.strip_loc();
        }
        infos.push(MemberInfo { name, params, span });
        trees.push(tree);
    }
    let mut calls = Vec::new();
    for (from, tree) in trees.into_iter().enumerate() {
        let params = &infos[from].params;
        let mut walker = Walker {
            g,
            members: &ids,
            infos: &infos,
            from,
            vars: params
                .iter()
                .enumerate()
                .map(|(i, (x, _))| Info {
                    name: x.clone(),
                    param: Some(i),
                    smaller_than: None,
                    recursive_fn: false,
                })
                .collect(),
            calls: Vec::new(),
            matched: Vec::new(),
            span: infos[from].span,
        };
        walker.walk(tree)?;
        calls.extend(walker.calls);
    }

    let mut group = sct::Group::new(infos.iter().map(|m| m.params.len()).collect());
    for call in &calls {
        group
            .call(call.from, call.to, &call.arcs)
            .expect("internal error: a call's arcs are within the arities");
    }
    match group.check(&g.budget, max_graphs) {
        Ok(Outcome::Terminates) => Ok(()),
        Ok(Outcome::NoDescent { path, graph }) => {
            Err(no_descent(&infos, &calls, &path, graph.entries()))
        }
        Err(e) => Err(inconclusive(e, &infos)),
    }
}

/// A call from one member to another (or itself): an arc `(caller position,
/// callee position, label)` for each argument related to a parameter, and
/// where it is.
struct Call {
    from: usize,
    to: usize,
    arcs: Vec<(usize, usize, Label)>,
    span: Span,
}

struct Info {
    name: Name,
    /// This variable is parameter `i` of the definition.
    param: Option<usize>,
    /// This variable is structurally smaller than parameter `i`.
    smaller_than: Option<usize>,
    /// This variable is a recursive function field of a matched constructor.
    recursive_fn: bool,
}

/// Walks the body of member `from`, recording its calls.
struct Walker<'a> {
    g: &'a Globals,
    /// The group's members, by position.
    members: &'a [DefId],
    infos: &'a [MemberInfo<'a>],
    from: usize,
    /// The variables in scope, indexed by de Bruijn level.
    vars: Vec<Info>,
    calls: Vec<Call>,
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

/// Whether a field of a constructor of data type `d` is a function returning
/// `d` or another member of its data group (the group's metadata, fixed when
/// it was declared). Strict positivity across the group makes each result a
/// part of the matched value.
fn is_recursive_fn(g: &Globals, ty: &Term, d: DataId) -> bool {
    let mut ty = ty.strip_loc();
    let mut arrows = 0;
    while let Term::Pi(_, _, _, cod) = ty {
        arrows += 1;
        ty = cod.strip_loc();
    }
    arrows > 0 && matches!(ty, Term::Data(d2, _) if g.data(d).group.contains(d2))
}

impl Walker<'_> {
    fn walk(&mut self, term: &Term) -> Result<(), Diagnostic> {
        self.g.budget.nesting("termination checker")?;
        match term {
            Term::Loc(span, inner) => {
                let saved = self.span;
                self.span = *span;
                let result = self.walk(inner);
                self.span = saved;
                result?;
            }
            // A compact list is closed, and makes no calls. It's never related
            // to a parameter (`relate`): descent comes only from matching,
            // where a range's tail is a field of the `Cons` its expansion
            // has, exactly as for an ordinary list.
            Term::Var(_)
            | Term::Nat(_)
            | Term::Chars(_)
            | Term::Sort(_)
            | Term::Refl
            | Term::Meta(_) => {}
            Term::Def(id) => {
                if let Some(to) = self.member(*id) {
                    self.call(to, &[])?;
                }
            }
            Term::App(..) => {
                let (head, args) = term.spine();
                if let Term::Def(id) = head
                    && let Some(to) = self.member(*id)
                {
                    // One call for the whole spine; the head isn't walked
                    // again, or it would count as a bare reference too.
                    self.call(to, &args)?;
                } else {
                    self.walk(head)?;
                }
                for arg in args {
                    self.walk(arg)?;
                }
            }
            Term::Lam(x, _, body) => self.under(&[(x.clone(), false)], None, body)?,
            Term::Pi(x, _, dom, cod) => {
                self.walk(dom)?;
                self.under(&[(x.clone(), false)], None, cod)?;
            }
            Term::Data(_, args) | Term::Ctor(_, _, args) => {
                for arg in args {
                    self.walk(arg)?;
                }
            }
            Term::Ann(e, t) => {
                self.walk(e)?;
                self.walk(t)?;
            }
            Term::Case(ix, d, branches) => {
                let scrutinee = &self.vars[self.vars.len() - 1 - ix];
                let source = scrutinee.param.or(scrutinee.smaller_than);
                let level = self.vars.len();
                let g = self.g;
                for (c, branch) in branches.iter().enumerate() {
                    self.matched.push(Matched {
                        scrutinee: level - 1 - ix,
                        data: *d,
                        ctor: c,
                        fields: level..level + branch.names.len(),
                    });
                    let fields: Vec<(Name, bool)> = branch
                        .names
                        .iter()
                        .zip(&g.data(*d).ctors[c].fields)
                        .map(|(x, (_, ty))| (x.clone(), is_recursive_fn(g, ty, *d)))
                        .collect();
                    let result = self.under(&fields, source, &branch.body);
                    self.matched.pop();
                    result?;
                }
            }
            // A number case binds nothing and makes nothing smaller, but every
            // arm and the default are walked, keeping what's already known.
            Term::NumCase(_, arms, default) => {
                for arm in arms.iter() {
                    self.walk(&arm.body)?;
                }
                self.walk(default)?;
            }
            Term::Eq(ty, a, b) => {
                if let Some(ty) = ty {
                    self.walk(ty)?;
                }
                self.walk(a)?;
                self.walk(b)?;
            }
            Term::J(m, b, p) => {
                self.walk(m)?;
                self.walk(b)?;
                self.walk(p)?;
            }
        }
        Ok(())
    }

    /// The position in the group of definition `id`, if it's a member.
    fn member(&self, id: DefId) -> Option<usize> {
        self.members.iter().position(|m| *m == id)
    }

    /// Records an occurrence of member `to` applied to `args`: a call, if
    /// it's given all of `to`'s parameters. Arguments beyond them get no
    /// entry in the graph (the caller still walks them).
    fn call(&mut self, to: usize, args: &[&Term]) -> Result<(), Diagnostic> {
        let arity = self.infos[to].params.len();
        if args.len() < arity {
            return Err(self.unsaturated(to, args));
        }
        let arcs = args[..arity]
            .iter()
            .enumerate()
            .filter_map(|(j, arg)| self.relate(arg).map(|(i, label)| (i, j, label)))
            .collect();
        self.calls.push(Call {
            from: self.from,
            to,
            arcs,
            span: self.span,
        });
        Ok(())
    }

    /// The parameter `arg` is related to, and how, if it's one of: a
    /// parameter, a variable matched from one, a recursive function field
    /// applied to arguments, or a constructor rebuilding a matched value.
    fn relate(&self, arg: &Term) -> Option<(usize, Label)> {
        let level = self.vars.len();
        let info = |ix: usize| self.vars.get(level.checked_sub(ix + 1)?);
        let related = |info: &Info| match (info.param, info.smaller_than) {
            (Some(i), _) => Some((i, Label::Le)),
            (None, Some(i)) => Some((i, Label::Lt)),
            (None, None) => None,
        };
        match arg.strip_loc() {
            Term::Var(ix) => related(info(*ix)?),
            Term::App(..) => {
                let Term::Var(ix) = arg.spine().0 else {
                    return None;
                };
                let info = info(*ix)?;
                if info.recursive_fn {
                    info.smaller_than.map(|i| (i, Label::Lt))
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
                related(&self.vars[m.scrutinee])
            }
            _ => None,
        }
    }

    /// Walks `body` under new binders: a name, and whether it's a recursive
    /// function field, for each.
    fn under(
        &mut self,
        binders: &[(Name, bool)],
        smaller_than: Option<usize>,
        body: &Term,
    ) -> Result<(), Diagnostic> {
        for (name, recursive_fn) in binders {
            self.vars.push(Info {
                name: name.clone(),
                param: None,
                smaller_than,
                recursive_fn: *recursive_fn,
            });
        }
        let result = self.walk(body);
        self.vars.truncate(self.vars.len() - binders.len());
        result
    }

    /// The error for an occurrence of member `to` given only `args`,
    /// suggesting a lambda that takes the rest.
    fn unsaturated(&self, to: usize, args: &[&Term]) -> Diagnostic {
        let MemberInfo { name, params, .. } = &self.infos[to];
        let explicit =
            |params: &[(Name, Icit)]| params.iter().filter(|(_, i)| *i == Icit::Explicit).count();
        let (given, missing) = params.split_at(args.len());
        let names: Vec<Name> = self.vars.iter().map(|info| info.name.clone()).collect();
        let mut fresh = Vec::new();
        for _ in 0..explicit(missing) {
            let taken =
                |x: &str| names.iter().any(|n| &**n == x) || fresh.iter().any(|n: &String| n == x);
            let x = ["x", "y", "z"]
                .into_iter()
                .map(String::from)
                .chain((1..).map(|k| format!("x{k}")))
                .find(|x| !taken(x))
                .expect("there's always a fresh name");
            fresh.push(x);
        }
        let mut call = name.to_string();
        for (arg, (_, icit)) in args.iter().zip(given) {
            if *icit == Icit::Explicit {
                // An argument with a space in it needs parentheses here.
                let arg = pretty::term(self.g, &names, arg);
                if arg.contains(' ') {
                    call.push_str(&format!(" ({arg})"));
                } else {
                    call.push_str(&format!(" {arg}"));
                }
            }
        }
        let suggestion = format!("\\{} -> {call} {}", fresh.join(" "), fresh.join(" "));
        let (wanted, got) = (explicit(params), explicit(given));
        let plural = |n: usize| if n == 1 { "argument" } else { "arguments" };
        let label = if args.is_empty() {
            format!(
                "`{name}` takes {wanted} {}; it's given none here",
                plural(wanted)
            )
        } else {
            format!(
                "`{name}` takes {wanted} {}; it's given {got}",
                plural(wanted)
            )
        };
        Diagnostic::error(
            "E-TERMINATION",
            format!("`{name}` is used here without all its arguments"),
        )
        .with_label(self.span, label)
        .with_note(format!("write `{suggestion}` so the call can be checked"))
        .with_note(if self.members.len() > 1 {
            "a call between definitions that call each other must be given all the arguments, so \
             the termination checker can see what each one is"
        } else {
            "a recursive call must be given all the arguments, so the termination checker can \
             see what each one is"
        })
    }
}

/// The error for a cycle of calls (`path`, composing to `entries`) in which
/// no parameter gets smaller.
fn no_descent(
    members: &[MemberInfo],
    calls: &[Call],
    path: &[sct::CallId],
    entries: &[Option<sct::Arc>],
) -> Diagnostic {
    // The members on the cycle, in the order it visits them.
    let mut on_cycle: Vec<usize> = Vec::new();
    for &c in path {
        if !on_cycle.contains(&calls[c].from) {
            on_cycle.push(calls[c].from);
        }
    }
    let quoted = |m: usize| format!("`{}`", members[m].name);
    let message = match &on_cycle[..] {
        [m] => format!("can't show that {} terminates", quoted(*m)),
        ms => {
            let (last, rest) = ms.split_last().expect("a cycle has a member");
            let rest: Vec<String> = rest.iter().map(|m| quoted(*m)).collect();
            format!(
                "can't show that {} and {} terminate",
                rest.join(", "),
                quoted(*last)
            )
        }
    };
    let mut diagnostic = Diagnostic::error("E-TERMINATION", message);
    let single = members.len() == 1;
    let mut labelled: Vec<sct::CallId> = Vec::new();
    for &c in path {
        if labelled.contains(&c) {
            continue;
        }
        let call = &calls[c];
        let (from, to) = (&members[call.from], &members[call.to]);
        let what = if to.params.is_empty() {
            if single {
                format!(
                    "`{}` has no parameters, so nothing can get smaller",
                    to.name
                )
            } else {
                format!(
                    "`{}` takes no arguments, so nothing can get smaller",
                    to.name
                )
            }
        } else {
            describe(from, to, call.from == call.to, &call.arcs)
        };
        // In a group, say where each call goes.
        let call_to = if single {
            "call".to_string()
        } else {
            format!("call to `{}`", to.name)
        };
        let message = if labelled.is_empty() {
            let call_to = if single {
                "recursive call".to_string()
            } else {
                call_to
            };
            format!("this {call_to} might not terminate: {what}")
        } else {
            format!("then this {call_to}: {what}")
        };
        diagnostic = diagnostic.with_label(call.span, message);
        labelled.push(c);
    }
    // A single call's label says it all; otherwise say what going round the
    // cycle does overall.
    let start = &members[calls[path[0]].from];
    if path.len() > 1 && !start.params.is_empty() {
        let round = if on_cycle.len() > 1 {
            let names: Vec<String> = path
                .iter()
                .map(|c| quoted(calls[*c].from))
                .chain([quoted(calls[path[0]].from)])
                .collect();
            format!("going round {}", names.join(" → "))
        } else {
            match (labelled.len(), path.len()) {
                (1, 2) => "making this call twice in a row".to_string(),
                (1, n) => format!("making this call {n} times in a row"),
                _ => "making these calls one after the other".to_string(),
            }
        };
        let overall: Vec<(usize, usize, Label)> = entries
            .iter()
            .enumerate()
            .filter_map(|(j, e)| e.map(|a| (a.from, j, a.label)))
            .collect();
        let note = if overall.iter().any(|(i, j, _)| shown(start, start, *i, *j)) {
            format!(
                "{round}, over and over: {}, so no argument keeps getting smaller",
                describe(start, start, true, &overall)
            )
        } else {
            format!("{round}, over and over, no argument is known to get smaller")
        };
        diagnostic = diagnostic.with_note(note);
    }
    diagnostic
        .with_note(
            "however the recursive calls are repeated, some argument must get smaller (a part of \
             a pattern-matched constructor); an argument passed on unchanged, or rebuilt from its \
             own pattern, is no smaller",
        )
        .with_note("non-terminating definitions are rejected; `{Partial}` isn't implemented yet")
}

/// Says in words what a call (or a cycle of calls) from member `from` to
/// member `to` passes: for each argument position related to a parameter,
/// how. `same` if they're the same member.
fn describe(
    from: &MemberInfo,
    to: &MemberInfo,
    same: bool,
    arcs: &[(usize, usize, Label)],
) -> String {
    let position = |params: &Params, i: usize| {
        let (x, icit) = &params[i];
        if *icit == Icit::Explicit {
            let n = params[..i]
                .iter()
                .filter(|(_, icit)| *icit == Icit::Explicit)
                .count()
                + 1;
            format!("{} argument", ordinal(n))
        } else {
            format!("implicit argument `{x}`")
        }
    };
    let parts: Vec<String> = arcs
        .iter()
        .filter(|(i, j, label)| *label == Label::Lt || shown(from, to, *i, *j))
        .map(|&(i, j, label)| {
            let (theirs, ours) = (position(&to.params, j), position(&from.params, i));
            if same {
                match (label, i == j) {
                    (Label::Lt, true) => format!("the {theirs} gets smaller"),
                    (Label::Le, true) => format!("the {theirs} stays the same"),
                    (Label::Lt, false) => format!("the {theirs} is smaller than the {ours} was"),
                    (Label::Le, false) => format!("the {theirs} is what the {ours} was"),
                }
            } else {
                let (callee, caller) = (to.name, from.name);
                match label {
                    Label::Lt => {
                        format!("`{callee}`'s {theirs} is smaller than `{caller}`'s {ours}")
                    }
                    Label::Le => format!("`{callee}`'s {theirs} is `{caller}`'s {ours}"),
                }
            }
        })
        .collect();
    if parts.is_empty() {
        "no argument is known to be smaller".to_string()
    } else {
        parts.join(", ")
    }
}

/// Whether to mention an arc from parameter `i` of `from` to parameter `j`
/// of `to` that isn't strict: not if both are implicit (a type passed on
/// unchanged, say).
fn shown(from: &MemberInfo, to: &MemberInfo, i: usize, j: usize) -> bool {
    from.params[i].1 == Icit::Explicit || to.params[j].1 == Icit::Explicit
}

fn ordinal(n: usize) -> String {
    let suffix = match (n % 10, n % 100) {
        (1, x) if x != 11 => "st",
        (2, x) if x != 12 => "nd",
        (3, x) if x != 13 => "rd",
        _ => "th",
    };
    format!("{n}{suffix}")
}

/// Running out while deciding the calls: there's no answer, so no member
/// is accepted.
fn inconclusive(e: ResourceError, members: &[MemberInfo]) -> Diagnostic {
    let names: Vec<String> = members.iter().map(|m| format!("`{}`", m.name)).collect();
    let (checking, accepted) = match &names[..] {
        [name] => (
            format!("while checking that {name} terminates"),
            format!("{name} isn't accepted"),
        ),
        _ => {
            let all = names.join(", ");
            (
                format!("while checking that {all} terminate"),
                format!("none of {all} is accepted"),
            )
        }
    };
    Diagnostic::from(e)
        .with_label(members[0].span, checking)
        .with_note(format!(
            "the termination check is inconclusive, so {accepted}"
        ))
}
