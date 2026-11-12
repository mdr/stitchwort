//! Printing core terms in surface-like syntax, for error messages and the REPL.
//!
//! The printer recurses over the term. Within an operation, a part nested
//! too deeply to reach with the stack the operation may use is shown as `…`
//! (docs/proposals/stack-safe-evaluation.md).

use crate::ev::Ev;
use std::cell::{Cell, RefCell};
use std::rc::Rc;

use num_bigint::BigUint;

use crate::budget::Result;
use crate::collections::HashMap;
use crate::globals::{CallDefaults, DefaultCall, PlaceholderText};
use crate::registry::Builtin;
use crate::term::{DataId, DefId, Icit, Name, Sort, Term};
use crate::value::{
    Value, proof_field, proof_param, quote_as_written_shown, quote_shown, quote_unfolded_shown,
    same_term,
};

/// A declaration a printed name stands for.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Declaration {
    Def(DefId),
    Data(DataId),
}

/// The names in scope where a term is printed, so that a declaration is
/// shown by the shortest name that means it there: `everyAdjacentPair`
/// inside its namespace, `Spec.everyAdjacentPair` beside it.
pub trait NameScope {
    /// Whether `written` names `declaration` here.
    fn names(&self, written: &str, declaration: Declaration) -> bool;

    /// `declaration`'s name written from the root, which means it wherever
    /// it is written: `Std.List.count` for the library's (`List.count`
    /// names it only where `List` is imported), else its name from its
    /// module's root.
    fn full_name(&self, declaration: Declaration) -> String;

    /// Other ways to write the full name `full` here than its trailing
    /// parts: through names imported under another name (`import M (x as
    /// y)` gives `y` for `M.x`, and `import P (Spec as S)` gives `S.total`
    /// for `P.Spec.total`). Each is tried like a trailing part.
    fn aliases(&self, _full: &str) -> Vec<String> {
        Vec::new()
    }

    /// What `a == b` decides an equation `a = b` of type `ty` by here, a
    /// closed term applied to `a` and `b`: `Nat.decEq` for `Nat`,
    /// `List.decEq [Nat] (x y => Nat.decEq x y)` for `List Nat`. `None` if
    /// `ty` mentions a variable, or `==` decides it some other way.
    fn eq_decision(&self, _ty: &Term) -> Option<Term> {
        None
    }

    /// If `projection` is an interface's own projection of a field
    /// (`Ord.%compare`, taking the dictionary first), the field's method
    /// (`Ord.compare`, taking it as an `auto` argument) and the name that
    /// argument is passed by (`ord`).
    fn method(&self, _projection: DefId) -> Option<(DefId, String)> {
        None
    }
}

/// Prints `term`, whose free variables are named by `names` (outermost first).
pub fn term(g: &Ev, names: &[Name], term: &Term) -> String {
    let mut names = names.to_vec();
    Printer::new(g, None).print(&mut names, term, Prec::Arrow)
}

/// [`term`], with names as `scope` writes them.
pub fn term_in(g: &Ev, scope: &dyn NameScope, names: &[Name], term: &Term) -> String {
    let mut names = names.to_vec();
    Printer::new(g, Some(scope)).print(&mut names, term, Prec::Arrow)
}

/// [`term`], with every call written as a call: `List.append xs ys`, not
/// `xs ++ ys`, and `List.length xs`, not `xs.length`. For telling apart
/// terms that the sugar prints alike.
pub fn term_calls(g: &Ev, names: &[Name], term: &Term) -> String {
    let mut names = names.to_vec();
    let printer = Printer::new(g, None);
    printer.calls.set(true);
    printer.print(&mut names, term, Prec::Arrow)
}

/// Prints `term` with ASCII operators (`&&`, `!=`, `->`), for text inside
/// exported JavaScript, where the reader writes `!=` and not `≠` (D1223).
pub fn term_ascii(g: &Ev, names: &[Name], term: &Term) -> String {
    let mut names = names.to_vec();
    let printer = Printer::new(g, None);
    printer.ascii.set(true);
    printer.print(&mut names, term, Prec::Arrow)
}

/// Prints `term` with its outermost `p → Void` function type written as
/// that arrow rather than `¬p`: what a hover says a `Not p` unfolds to.
/// Anything inside it keeps the notation.
pub fn term_not_unfolded(g: &Ev, names: &[Name], term: &Term) -> String {
    let mut names = names.to_vec();
    let printer = Printer::new(g, None);
    printer.unfold_not.set(true);
    printer.print(&mut names, term, Prec::Arrow)
}

/// [`term_ascii`] for a value.
pub fn value_ascii(g: &Ev, names: &[Name], value: &Value) -> String {
    match quote_unfolded_shown(g, names.len(), value) {
        Ok(t) => term_ascii(g, names, &t),
        Err(_) => "…".into(),
    }
}

/// Prints all of `term`, or fails if part of it is nested too deeply to
/// print: for showing a result, where `…` would hide part of it.
pub fn term_in_full(g: &Ev, names: &[Name], term: &Term) -> Result<String> {
    let mut names = names.to_vec();
    let printer = Printer::new(g, None);
    let text = printer.print(&mut names, term, Prec::Arrow);
    if printer.elided.get() {
        return Err(g.machine.budget.too_deep(PASS));
    }
    Ok(text)
}

/// The name the printer's depth guard reports.
const PASS: &str = "printer";

/// Prints `value`, whose free variables are named by `names` (outermost first).
/// If the value can't be quoted within the resource limits, it's shown as `…`.
pub fn value(g: &Ev, names: &[Name], value: &Value) -> String {
    match quote_unfolded_shown(g, names.len(), value) {
        Ok(t) => term(g, names, &t),
        Err(_) => "…".into(),
    }
}

/// How a definition's name reads in a message: the generated transparent
/// copy `f.%body` (docs/proposals/opaque-definitions.md §6.3) is "the body
/// of `f`", in parentheses so `(body of f) x` still reads as a call.
fn def_display(name: &str) -> String {
    match name.strip_suffix(".%body") {
        Some(owner) => format!("(body of {owner})"),
        None => name.to_string(),
    }
}

/// The longest a term may be in a message before its inner parts are
/// shown as `…`.
const MESSAGE_LIMIT: usize = 240;

/// Prints `value` for an error message: like [`value`], but a result longer
/// than [`MESSAGE_LIMIT`] characters has its inner parts replaced by `…`,
/// keeping the outermost layers. Calls are shown as written
/// (`List.length xs`), not as what they compute to ([`quote_shown`];
/// docs/proposals/folded-calls.md, stage 3). Setting
/// `STITCHWORT_FULL_TERMS` shows everything.
pub fn value_for_message(g: &Ev, names: &[Name], value: &Value) -> String {
    value_within(g, None, names, value, MESSAGE_LIMIT, Prec::Arrow, None)
}

/// [`value_for_message`], with names as `scope` writes them.
pub fn value_for_message_in(
    g: &Ev,
    scope: &dyn NameScope,
    names: &[Name],
    value: &Value,
) -> String {
    value_within(
        g,
        Some(scope),
        names,
        value,
        MESSAGE_LIMIT,
        Prec::Arrow,
        None,
    )
}

/// [`value_for_message`], showing the arguments the compiler fills in, for
/// two types that print the same without them.
pub fn value_for_message_hidden(g: &Ev, names: &[Name], value: &Value) -> String {
    value_hidden(g, None, names, value)
}

/// [`value_for_message_hidden`], with names as `scope` writes them.
pub fn value_for_message_hidden_in(
    g: &Ev,
    scope: &dyn NameScope,
    names: &[Name],
    value: &Value,
) -> String {
    value_hidden(g, Some(scope), names, value)
}

fn value_hidden(g: &Ev, scope: Option<&dyn NameScope>, names: &[Name], value: &Value) -> String {
    let Ok(t) = quote_shown(g, names.len(), value) else {
        return "…".into();
    };
    let mut ns = names.to_vec();
    let printer = Printer::new(g, scope);
    printer.show_hidden.set(true);
    // As in `term_within`: a huge term is printed only to a depth, not in
    // full and then cut.
    if t.subterms().nth(FULL_PRINT_NODES).is_some() {
        printer.max_depth.set(Some(10));
    }
    let text = printer.print(&mut ns, &t, Prec::Arrow);
    if text.chars().count() <= MESSAGE_LIMIT * 2 {
        return text;
    }
    let mut text: String = text.chars().take(MESSAGE_LIMIT * 2).collect();
    text.push('…');
    text
}

/// Where two terms first differ, printed: the two differing parts (each
/// with the operator or call around it when the parts are as small as a
/// variable or a number), and the nearest call around them, if any.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Difference {
    pub left: String,
    pub right: String,
    pub within: Option<String>,
}

/// The longest each part of a [`Difference`] may be.
const DIFFERENCE_LIMIT: usize = 100;

/// The first place, reading left to right, where `a` and `b` differ outside
/// the arguments the compiler fills in. `None` if that's their outermost
/// layer (which any printing shows), if they differ only in those
/// arguments, or if they're too deeply nested to compare.
pub fn first_difference(g: &Ev, names: &[Name], a: &Term, b: &Term) -> Option<Difference> {
    difference(g, None, names, a, b)
}

/// [`first_difference`], with names as `scope` writes them.
pub fn first_difference_in(
    g: &Ev,
    scope: &dyn NameScope,
    names: &[Name],
    a: &Term,
    b: &Term,
) -> Option<Difference> {
    difference(g, Some(scope), names, a, b)
}

fn difference(
    g: &Ev,
    scope: Option<&dyn NameScope>,
    names: &[Name],
    a: &Term,
    b: &Term,
) -> Option<Difference> {
    let found = match first_mismatch(g, a, b, true, false, &mut Path::new(names)) {
        Ok(Some(found)) if !found.outermost => found,
        _ => return None,
    };
    let show = |names: &[Name], t: &Term| {
        term_within(g, scope, names, t, DIFFERENCE_LIMIT, Prec::Arrow, None)
    };
    let Mismatch {
        mut left,
        mut right,
        mut names,
        mut calls,
        ..
    } = found;
    // A variable or a constant reads better with the operation it's in.
    if is_small(&left)
        && is_small(&right)
        && let Some(call) = calls.pop()
    {
        (left, right, names) = (call.left, call.right, call.names);
    }
    // The nearest call around it that isn't an operator (`+`, `&&`) or a
    // whole side.
    let printer = Printer::new(g, scope);
    let operator =
        |id: DefId| printer.infix(id).is_some() || g.env.registry().is_def(Builtin::IfThenElse, id);
    let within = calls
        .into_iter()
        .rev()
        .find(|call| {
            !call.outermost && matches!(full_spine(&call.left).0, Term::Def(id) if !operator(*id))
        })
        .map(|call| show(&call.names, &call.left));
    Some(Difference {
        left: show(&names, &left),
        right: show(&names, &right),
        within,
    })
}

/// Whether `a` and `b` differ, but only in the arguments the compiler fills
/// in: implicit and `auto` arguments.
pub fn differ_only_in_hidden(g: &Ev, a: &Term, b: &Term) -> bool {
    let compare =
        |explicit_only| first_mismatch(g, a, b, explicit_only, false, &mut Path::new(&[]));
    matches!(compare(true), Ok(None)) && matches!(compare(false), Ok(Some(_)))
}

/// Whether `a` and `b` differ, but only in proof positions: a constructor's
/// proof field, a data type's proof parameter, or a definition's inert
/// argument.
pub fn differ_only_in_proofs(g: &Ev, a: &Term, b: &Term) -> bool {
    let compare = |skip_proofs| first_mismatch(g, a, b, false, skip_proofs, &mut Path::new(&[]));
    matches!(compare(false), Ok(Some(_))) && matches!(compare(true), Ok(None))
}

/// [`value_for_message`], for a term.
pub fn term_for_message(g: &Ev, names: &[Name], term_: &Term) -> String {
    term_within(g, None, names, term_, MESSAGE_LIMIT, Prec::Arrow, None)
}

/// [`term_for_message`], with names as `scope` writes them.
pub fn term_for_message_in(g: &Ev, scope: &dyn NameScope, names: &[Name], term_: &Term) -> String {
    term_within(
        g,
        Some(scope),
        names,
        term_,
        MESSAGE_LIMIT,
        Prec::Arrow,
        None,
    )
}

/// The longest a term may be in a goal (docs/proposals/lsp-goal-holes.md
/// §3.3): a goal is the one place the whole term matters.
const GOAL_LIMIT: usize = 4000;

/// [`value_for_message_in`], with the larger limit of a goal's types.
///
/// `predicates[level]` says whether the context variable at that level has a
/// type ending in `Prop` ([`predicate_flags`]), so that `(n: Nat) → p n` is
/// written as a `∀`; a level past its end is not one.
pub fn value_for_goal(
    g: &Ev,
    scope: &dyn NameScope,
    names: &[Name],
    predicates: &[bool],
    value: &Value,
) -> String {
    value_within(
        g,
        Some(scope),
        names,
        value,
        GOAL_LIMIT,
        Prec::Arrow,
        Some(predicates),
    )
}

/// [`value_for_goal`], but as it was written: every call stays a call, so
/// that `beats Rock Rock = False` isn't printed as `False = False`
/// (D3522). `None` if the value can't be read back.
pub fn value_for_goal_as_written(
    g: &Ev,
    scope: &dyn NameScope,
    names: &[Name],
    predicates: &[bool],
    value: &Value,
) -> Option<String> {
    let t = quote_as_written_shown(g, names.len(), value).ok()?;
    Some(term_within(
        g,
        Some(scope),
        names,
        &t,
        GOAL_LIMIT,
        Prec::Arrow,
        Some(predicates),
    ))
}

/// [`value_for_goal`], for a term already read back: a step's statement as
/// written, where the value's normal form has computed a side away and so
/// can't give the written side back (SW-2942).
pub fn term_for_goal_in(
    g: &Ev,
    scope: &dyn NameScope,
    names: &[Name],
    predicates: &[bool],
    term_: &Term,
) -> String {
    term_within(
        g,
        Some(scope),
        names,
        term_,
        GOAL_LIMIT,
        Prec::Arrow,
        Some(predicates),
    )
}

/// Whether the type `ty` (a value under `level` binders) is
/// `Prop`, or a function type into it: the variable is a predicate, and
/// applied to arguments it is a proposition.
pub fn is_predicate_type(g: &Ev, level: usize, ty: &Value) -> bool {
    let Ok(mut t) = quote_shown(g, level, ty) else {
        return false;
    };
    loop {
        match t.strip_loc() {
            Term::Pi(_, _, _, b) => t = (**b).clone(),
            Term::Sort(Sort::Prop) => return true,
            _ => return false,
        }
    }
}

/// [`value_for_message_in`] for one side of an equation shown as `a = b`:
/// in brackets if it's an operation that binds more loosely than `=`
/// (`(n < n) = True`).
pub fn side_for_message_in(g: &Ev, scope: &dyn NameScope, names: &[Name], value: &Value) -> String {
    value_within(g, Some(scope), names, value, MESSAGE_LIMIT, Prec::Add, None)
}

/// [`term_within`] for a value, with calls shown as written.
fn value_within(
    g: &Ev,
    scope: Option<&dyn NameScope>,
    names: &[Name],
    value: &Value,
    limit: usize,
    prec: Prec,
    goal: Option<&[bool]>,
) -> String {
    let Ok(t) = quote_shown(g, names.len(), value) else {
        return "…".into();
    };
    term_within(g, scope, names, &t, limit, prec, goal)
}

/// [`term_for_message`] at precedence `prec`, with a result longer than
/// `limit` characters shortened; as a `goal` (with its context's
/// `predicates`), writing decided equations ([`Printer::equations`]).
fn term_within(
    g: &Ev,
    scope: Option<&dyn NameScope>,
    names: &[Name],
    term_: &Term,
    limit: usize,
    prec: Prec,
    goal: Option<&[bool]>,
) -> String {
    note_failed_mention(g, names.len(), term_);
    let printer = || {
        let printer = Printer::new(g, scope);
        printer.equations.set(goal.is_some());
        *printer.predicates.borrow_mut() = goal.unwrap_or_default().to_vec();
        printer
    };
    let full_terms = std::env::var_os("STITCHWORT_FULL_TERMS").is_some();
    // Printing a term builds its text from the inside out, so a huge one
    // (a closed list of 130,000 sequences, AoC 2024 day 22) takes minutes
    // and gigabytes; one this big is longer than `limit` anyway.
    let too_big = !full_terms && term_.subterms().nth(FULL_PRINT_NODES).is_some();
    let full = if too_big {
        None
    } else {
        let mut ns = names.to_vec();
        Some(printer().print(&mut ns, term_, prec))
    };
    if let Some(full) = &full
        && (full.chars().count() <= limit || full_terms)
    {
        return full.clone();
    }
    // Reprint with less and less depth until it fits.
    for depth in (1..=10).rev() {
        let mut ns = names.to_vec();
        let printer = printer();
        printer.max_depth.set(Some(depth));
        let text = printer.print(&mut ns, term_, prec);
        if text.chars().count() <= limit {
            return text;
        }
    }
    // Still too wide (a long list, say): cut it off.
    let wide = full.unwrap_or_else(|| {
        let mut ns = names.to_vec();
        let printer = printer();
        printer.max_depth.set(Some(10));
        printer.print(&mut ns, term_, prec)
    });
    let mut text: String = wide.chars().take(limit).collect();
    text.push('…');
    text
}

/// A term of more nodes than this is not printed in full by
/// [`term_within`]: the text would be far longer than any limit.
const FULL_PRINT_NODES: usize = 20_000;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
    Arrow,
    /// `p ↔ q`: between `->` and `||`, not associative (D1202).
    Iff,
    /// `p || q`, then `p && q`: looser than comparisons, grouping to the right.
    Or,
    And,
    Eq,
    /// `a ..< b`, `a ..= b`: between comparisons and `+` and `++`, not
    /// associative.
    Range,
    /// `a ++ b`: looser than `+`, grouping to the right.
    Append,
    Add,
    /// `*`, `/`, `%`: tighter than `+`, looser than a prefix minus.
    Mul,
    /// A prefix minus: tighter than `*`, looser than application.
    Neg,
    App,
    Atom,
}

/// A branch of a `Bool` `if`: its parameter, and a body that doesn't use it
/// (`Printer::bool_if`).
type Branch = (Name, Rc<Term>);

/// What [`Printer::dot_call`] made of a call.
enum Dot {
    /// The dot form.
    Call((String, Prec)),
    /// Not a dot call, and the receiver was printed to find that out
    /// (at [`Prec::Atom`], as an argument is): the plain call reuses it.
    Declined(String),
    /// Not a dot call, nothing printed.
    No,
}

struct Printer<'g> {
    g: &'g Ev<'g>,
    /// Whether something was too deeply nested to print, and shown as `…`.
    elided: Cell<bool>,
    /// For messages: parts nested deeper than this are shown as `…`.
    max_depth: Cell<Option<usize>>,
    depth: Cell<usize>,
    /// Show the arguments the compiler fills in, `f [x] [auto p] y`.
    show_hidden: Cell<bool>,
    /// Write the operators in ASCII (`&&`, `!=`, `->`), for text a
    /// JavaScript developer reads (D1223).
    ascii: Cell<bool>,
    /// Write calls as calls: no dot calls, no `++` for the appends.
    calls: Cell<bool>,
    /// Write a decided equation as the `a == b` that elaborates to it
    /// ([`Printer::decided_equation`]): in a goal, which is pasted back.
    equations: Cell<bool>,
    /// Write the next `p → Void` as an arrow instead of `¬p`
    /// ([`term_not_unfolded`]).
    unfold_not: Cell<bool>,
    /// The names in scope, to shorten declarations' names by; without it,
    /// names are written from the root.
    scope: Option<&'g dyn NameScope>,
    /// By context level, whether the variable's type ends in `Prop`
    /// ([`is_predicate_type`]); empty when the types aren't known.
    predicates: RefCell<Vec<bool>>,
    /// What `scope` said each written name means, by declaration.
    meant: RefCell<HashMap<(Declaration, String), bool>>,
}

impl<'g> Printer<'g> {
    fn new(g: &'g Ev<'g>, scope: Option<&'g dyn NameScope>) -> Self {
        Printer {
            g,
            elided: Cell::new(false),
            max_depth: Cell::new(None),
            depth: Cell::new(0),
            show_hidden: Cell::new(false),
            ascii: Cell::new(false),
            calls: Cell::new(false),
            equations: Cell::new(false),
            unfold_not: Cell::new(false),
            scope,
            predicates: RefCell::new(Vec::new()),
            meant: RefCell::new(HashMap::default()),
        }
    }

    /// The name of `declaration` (`name`, from its module's root) as its
    /// shortest trailing part that means `declaration` in the scope,
    /// skipping a part whose first component is a variable in `names`
    /// (which would mean the variable). Else its whole name as the scope
    /// writes it ([`NameScope::full_name`]: `Std.List.count`, where
    /// `List.count` needs an import); `name` if there is no scope.
    fn short_name(&self, names: &[Name], name: &str, declaration: Declaration) -> String {
        let Some(scope) = self.scope else {
            return name.to_string();
        };
        if name.contains('%') {
            return name.to_string();
        }
        let full = scope.full_name(declaration);
        let parts: Vec<&str> = full.split('.').collect();
        // The trailing parts, shortest first, and the aliases, each after
        // the trailing part with as many components.
        let mut tried: Vec<String> = (1..parts.len())
            .rev()
            .map(|start| parts[start..].join("."))
            .collect();
        for alias in scope.aliases(&full) {
            let n = alias.split('.').count();
            let at = tried
                .iter()
                .position(|t| t.split('.').count() > n)
                .unwrap_or(tried.len());
            tried.insert(at, alias);
        }
        for written in tried {
            let first = written.split('.').next().unwrap_or("");
            if names.iter().any(|x| **x == *first) {
                continue;
            }
            let meant = *self
                .meant
                .borrow_mut()
                .entry((declaration, written.clone()))
                .or_insert_with(|| scope.names(&written, declaration));
            if meant {
                return written;
            }
        }
        full
    }

    /// Definition `id`'s name, as [`Printer::short_name`] writes it.
    fn def_name(&self, names: &[Name], id: DefId) -> String {
        let name = &self.g.def(id).name;
        if name.contains('%') {
            return def_display(name);
        }
        self.short_name(names, name, Declaration::Def(id))
    }

    /// Data type `d`'s name, as [`Printer::short_name`] writes it.
    fn data_name(&self, names: &[Name], d: DataId) -> String {
        self.short_name(names, &self.g.data(d).name, Declaration::Data(d))
    }

    /// Whether `head` is an open goal's assumption.
    fn is_assumed(&self, head: &Term) -> bool {
        matches!(head, Term::Def(id) if self.g.def(*id).assumption.is_some())
    }

    /// `unicode`, or `ascii` when printing for JavaScript.
    fn sym(&self, unicode: &'static str, ascii: &'static str) -> &'static str {
        if self.ascii.get() { ascii } else { unicode }
    }

    fn print(&self, names: &mut Vec<Name>, term: &Term, prec: Prec) -> String {
        let (text, own) = self.go(names, term);
        if own < prec {
            format!("({text})")
        } else {
            text
        }
    }

    /// `{A args, B | e}`, if `ops` is the operation type of a row: a chain of
    /// `Plus` ending in `NoOp` or `rowOp e`.
    fn row(&self, names: &mut Vec<Name>, ops: &Term) -> Option<String> {
        self.row_with(names, ops, false)
    }

    /// [`Printer::row`], with `Partial` last among the abilities if
    /// `partial` (the row of a `Delay`).
    fn row_with(&self, names: &mut Vec<Name>, ops: &Term, partial: bool) -> Option<String> {
        let mut labels = Vec::new();
        let mut ops = ops.strip_loc();
        let tail = loop {
            match ops {
                Term::Data(d, args) if is(self.g, Builtin::Plus, *d) && args.len() == 2 => {
                    labels.push(self.print(names, &args[0], Prec::Arrow));
                    ops = args[1].strip_loc();
                }
                Term::Data(d, _) if is(self.g, Builtin::NoOp, *d) => break None,
                Term::App(f, e, _) if matches!(f.strip_loc(), Term::Def(id) if self.g.env.registry().is_def(Builtin::RowOp, *id)) =>
                {
                    break Some(self.print(names, e, Prec::App));
                }
                _ => return None,
            }
        };
        if partial {
            labels.push("Partial".to_string());
        }
        Some(match (labels.is_empty(), tail) {
            (true, Some(t)) => format!("{{{t}}}"),
            (_, Some(t)) => format!("{{{} | {t}}}", labels.join(", ")),
            (_, None) => format!("{{{}}}", labels.join(", ")),
        })
    }

    /// The last element of an open list: `..xs`, or `…` where the tail is
    /// left out, as the rest of a list too long to show.
    fn spread(&self, names: &mut Vec<Name>, tail: &Term) -> String {
        match self.print(names, tail, Prec::Arrow) {
            left_out if left_out == "…" => left_out,
            shown => format!("..{shown}"),
        }
    }

    fn go(&self, names: &mut Vec<Name>, term: &Term) -> (String, Prec) {
        if matches!(term, Term::Loc(..) | Term::Ann(..)) {
            return self.go_node(names, term);
        }
        let depth = self.depth.get();
        if self.max_depth.get().is_some_and(|m| depth >= m) && !is_atomic(term) {
            return ("…".into(), Prec::Atom);
        }
        self.depth.set(depth + 1);
        let result = self.go_node(names, term);
        self.depth.set(depth);
        result
    }

    #[inline(always)]
    fn go_node(&self, names: &mut Vec<Name>, term: &Term) -> (String, Prec) {
        if self.g.machine.budget.stack_exhausted() {
            self.elided.set(true);
            return ("…".into(), Prec::Atom);
        }
        match term {
            Term::Loc(_, t) | Term::Ann(t, _) => self.go(names, t),
            Term::Var(ix) => {
                let name = names.len().checked_sub(ix + 1).map_or_else(
                    || format!("?{ix}"),
                    |l| readable(&names[l], names).to_string(),
                );
                (name, Prec::Atom)
            }
            // A constant parameter default's helper, outside the call it
            // fills, is shown as its value: `Vec Nat 3`.
            Term::Def(id)
                if self.g.def(*id).param_default
                    && self.g.def(*id).arity == 0
                    && let Some(body) = self.g.def(*id).body() =>
            {
                self.go(names, body)
            }
            Term::Def(id) if self.g.def(*id).assumption.is_some() => ("?".into(), Prec::Atom),
            Term::Def(id) => (self.def_name(names, *id), Prec::Atom),
            Term::Sort(Sort::Prop) => ("Prop".into(), Prec::Atom),
            Term::Sort(Sort::Type(0)) => ("Type".into(), Prec::Atom),
            Term::Sort(Sort::Type(i)) => (format!("Type {i}"), Prec::App),
            Term::Refl => ("rfl".into(), Prec::Atom),
            Term::Nat(n) => (n.to_string(), Prec::Atom),
            // A compact list of characters, as the list literal it stands for.
            Term::Chars(chars) => (show_chars(chars.as_slice()), Prec::Atom),
            Term::Data(d, _) if is(self.g, Builtin::UnitType, *d) => ("()".into(), Prec::Atom),
            // A computation over a row of abilities: `{State Nat | e} a`.
            Term::Data(d, args) if is(self.g, Builtin::Comp, *d) && args.len() == 3 => {
                // The empty row stays `Comp NoOp NoRes a`: `{} a` reads as `a`.
                match self.row(names, &args[0]).filter(|row| row != "{}") {
                    Some(row) => {
                        let result = self.print(names, &args[2], Prec::App);
                        (format!("{row} {result}"), Prec::App)
                    }
                    None => self.applied(names, "Comp".into(), args.iter().map(|a| &**a)),
                }
            }
            // `And p q` and `Or p q` as the operators that write them, in
            // their Unicode spellings (D1204): `p ∧ q`, `p ∨ q`.
            Term::Data(d, args)
                if args.len() == 2
                    && (is(self.g, Builtin::And, *d) || is(self.g, Builtin::Or, *d)) =>
            {
                let (op, prec, left) = if is(self.g, Builtin::And, *d) {
                    (self.sym("∧", "&&"), Prec::And, Prec::Eq)
                } else {
                    (self.sym("∨", "||"), Prec::Or, Prec::And)
                };
                let lhs = self.print(names, &args[0], left);
                let rhs = self.print(names, &args[1], prec);
                (format!("{lhs} {op} {rhs}"), prec)
            }
            // `Iff p q` as `p ↔ q`: not associative.
            Term::Data(d, args) if args.len() == 2 && is_loaded(self.g, Builtin::Iff, *d) => {
                let lhs = self.print(names, &args[0], Prec::Or);
                let rhs = self.print(names, &args[1], Prec::Or);
                (format!("{lhs} {} {rhs}", self.sym("↔", "<->")), Prec::Iff)
            }
            // `Exists T (x => P)` as `∃ (x: T) => P`, when its predicate is
            // a lambda.
            Term::Data(d, args)
                if args.len() == 2
                    && is_loaded(self.g, Builtin::Exists, *d)
                    && matches!(args[1].strip_loc(), Term::Lam(_, Icit::Explicit, _)) =>
            {
                let Term::Lam(x, _, body) = args[1].strip_loc() else {
                    unreachable!("just matched")
                };
                let ty = self.print(names, &args[0], Prec::Arrow);
                let x = binder(x, names, body);
                names.push(x.clone());
                let body = self.print(names, body, Prec::Arrow);
                names.pop();
                (
                    format!("{} ({x}: {ty}) => {body}", self.sym("∃", "exists")),
                    Prec::Arrow,
                )
            }
            // A pair type, as a tuple type: `(Nat, Text)`, nesting to the right.
            Term::Data(d, args) if is(self.g, Builtin::Pair, *d) && args.len() == 2 => {
                let mut items = vec![&*args[0]];
                let mut rest = args[1].strip_loc();
                while let Term::Data(d, args) = rest {
                    if !(is(self.g, Builtin::Pair, *d) && args.len() == 2) {
                        break;
                    }
                    items.push(&args[0]);
                    rest = args[1].strip_loc();
                }
                items.push(rest);
                (self.tuple(names, &items), Prec::Atom)
            }
            Term::Data(d, args) if self.g.data(*d).auto_params.contains(&true) => {
                // An `auto` parameter given by name, `Map Nat Nat [ord := o]`
                // (docs/proposals/interfaces.md §7.5).
                let data = self.g.data(*d);
                let mut text = self.data_name(names, *d);
                for (k, arg) in args.iter().enumerate() {
                    text.push(' ');
                    if data.auto_params.get(k) == Some(&true) {
                        let shown = self.print(names, arg, Prec::Arrow);
                        text.push_str(&format!("[{} := {shown}]", data.params[k].0));
                    } else {
                        text.push_str(&self.print(names, arg, Prec::Atom));
                    }
                }
                (text, Prec::App)
            }
            Term::Data(d, args) => {
                let name = self.data_name(names, *d);
                self.applied(names, name, args.iter().map(|a| &**a))
            }
            Term::Ctor(d, 0, _) if is(self.g, Builtin::UnitType, *d) => ("()".into(), Prec::Atom),
            // A double with known valid bits, as its literal: `1.5`, `-0.0`,
            // `Float.nan`. Whatever its witness: every way of building a
            // `Float` with known bits gives `rfl` (`Float.make`), and a
            // value read back from a runtime has none (SW-1000: a list of
            // them printed as `{ bits = …, valid = ?1 }`).
            Term::Ctor(d, 0, args)
                if Some(*d) == self.g.env.builtins().float.data
                    && let [bits, _witness] = args.as_slice()
                    && let Term::Nat(n) = bits.strip_loc()
                    && let Some(bits) = num_traits::ToPrimitive::to_u64(&**n)
                        .filter(|b| crate::float::is_valid(*b)) =>
            {
                let text = crate::float::source(bits);
                let prec = if text.starts_with('-') {
                    Prec::App
                } else {
                    Prec::Atom
                };
                (text, prec)
            }
            // A `NonEmptyList`, in the brackets that write it where one is
            // expected: `[1, 2]`, `[x, ..xs]` (docs/proposals/non-empty-lists.md §7).
            Term::Ctor(d, 0, args)
                if is_loaded(self.g, Builtin::NonEmptyList, *d) && args.len() == 2 =>
            {
                let mut items = vec![&*args[0]];
                let tail = args[1].strip_loc();
                let rest = if let Some(more) = list_literal(self.g, tail) {
                    items.extend(more);
                    None
                } else if let Some((more, rest)) = open_list(self.g, tail) {
                    items.extend(more);
                    Some(rest)
                } else {
                    Some(tail)
                };
                let mut shown: Vec<String> = items
                    .iter()
                    .map(|t| self.print(names, t, Prec::Arrow))
                    .collect();
                if let Some(rest) = rest {
                    shown.push(self.spread(names, rest));
                }
                (format!("[{}]", shown.join(", ")), Prec::Atom)
            }
            // A record, as a literal: `{ name = "A", age = 3 }`.
            Term::Ctor(d, 0, args) if self.g.data(*d).record => {
                if let Some(update) = self.record_update(names, *d, args) {
                    return (update, Prec::Atom);
                }
                let fields: Vec<String> = self.g.data(*d).ctors[0]
                    .fields
                    .iter()
                    .zip(args)
                    .map(|((f, _), a)| format!("{f} = {}", self.print(names, a, Prec::Arrow)))
                    .collect();
                if fields.is_empty() {
                    return ("{}".into(), Prec::Atom);
                }
                (format!("{{ {} }}", fields.join(", ")), Prec::Atom)
            }
            // A pair, as a tuple: `(1, 2, 3)` is `MkPair 1 (MkPair 2 3)`.
            Term::Ctor(d, 0, args) if is(self.g, Builtin::Pair, *d) && args.len() == 2 => {
                let mut items = vec![&*args[0]];
                let mut rest = args[1].strip_loc();
                while let Term::Ctor(d, 0, args) = rest {
                    if !(is(self.g, Builtin::Pair, *d) && args.len() == 2) {
                        break;
                    }
                    items.push(&args[0]);
                    rest = args[1].strip_loc();
                }
                items.push(rest);
                (self.tuple(names, &items), Prec::Atom)
            }
            Term::Ctor(d, c, args) => {
                if let Some((negative, n)) = int_literal(self.g, term) {
                    return if negative {
                        (format!("-{n}"), Prec::Neg)
                    } else {
                        (n.to_string(), Prec::Atom)
                    };
                }
                // An `Int` that isn't a literal, in the terms it's written
                // in (SW-937): `OfNat n` is `n.toInt`, and `NegSucc n`,
                // `-(n + 1)`, is `-(n + 1).toInt`, which computes to it.
                if is(self.g, Builtin::Int, *d)
                    && let [n] = &args[..]
                    && (self
                        .g
                        .env
                        .registry()
                        .loaded_def(Builtin::NatToInt)
                        .is_some()
                        || self.g.env.registry().library_installed())
                {
                    if *c == 0 {
                        return (self.to_int(names, n), Prec::Atom);
                    }
                    let n = self.print(names, n, Prec::Add);
                    return (format!("-({n} + 1).toInt"), Prec::Neg);
                }
                if let Some(n) = nat_literal(self.g, term) {
                    return (n.to_string(), Prec::Atom);
                }
                if let Some(c) = char_literal(self.g, term) {
                    return (format!("'{}'", escape(&[c], '\'')), Prec::Atom);
                }
                if let Some(chars) = text_literal(self.g, term) {
                    return (format!("\"{}\"", escape(&chars, '"')), Prec::Atom);
                }
                if let Some(items) = list_literal(self.g, term) {
                    let items: Vec<String> = items
                        .iter()
                        .map(|t| self.print(names, t, Prec::Arrow))
                        .collect();
                    return (format!("[{}]", items.join(", ")), Prec::Atom);
                }
                if let Some(chars) = char_list(self.g, term) {
                    return (show_chars(&chars), Prec::Atom);
                }
                // An open chain, `Cons a (Cons b xs)`, as `[a, b, ..xs]`
                // (docs/proposals/list-spread.md).
                if let Some((items, tail)) = open_list(self.g, term) {
                    let mut shown: Vec<String> = items
                        .iter()
                        .map(|t| self.print(names, t, Prec::Arrow))
                        .collect();
                    shown.push(self.spread(names, tail));
                    return (format!("[{}]", shown.join(", ")), Prec::Atom);
                }
                let ctor = &self.g.data(*d).ctors[*c];
                let mut text = ctor.name.to_string();
                // A constructor declared with its fields in braces is shown
                // by field name, as it can be written. (With implicit fields
                // it is shown positionally, which braces can't say.)
                if ctor.braced && !args.is_empty() && !ctor.implicit.contains(&true) {
                    let fields: Vec<String> = ctor
                        .fields
                        .iter()
                        .zip(args)
                        .map(|((f, _), a)| format!("{f} = {}", self.print(names, a, Prec::Arrow)))
                        .collect();
                    return (format!("{text} {{ {} }}", fields.join(", ")), Prec::App);
                }
                // After a constructor declared with brackets, braces are a
                // record argument like any other: `Cons { x = 1 } rest`.
                for arg in args {
                    let shown = self.print(names, arg, Prec::Atom);
                    text.push(' ');
                    text.push_str(&shown);
                }
                let prec = if args.is_empty() {
                    Prec::Atom
                } else {
                    Prec::App
                };
                (text, prec)
            }
            // `p -> Void` is how `Not p` computes; print it the way it's written.
            Term::Pi(_, Icit::Explicit, a, b)
                if !self.unfold_not.get()
                    && !b.mentions(0)
                    && matches!(b.strip_loc(), Term::Data(d, _) if is(self.g, Builtin::Void, *d)) =>
            {
                self.not(names, a)
            }
            // A function type whose result is a proposition, binding a
            // variable the result uses (or an implicit one), as the
            // quantifier: `∀ (n: Nat) => n + 0 = n` (D3458).
            Term::Pi(_, icit, _, b)
                if (icit.is_implicit() || b.mentions(0)) && self.is_proposition(names, b) =>
            {
                self.forall(names, term)
            }
            Term::Pi(x, icit, a, b) => {
                self.unfold_not.set(false);
                let uses = b.mentions(0);
                let dom = if icit.is_implicit() || uses {
                    self.print(names, a, Prec::Arrow)
                } else {
                    self.print(names, a, Prec::Or)
                };
                let x = binder(x, names, b);
                names.push(x.clone());
                let cod = self.print(names, b, Prec::Arrow);
                names.pop();
                let arrow = self.sym("→", "->");
                if icit.is_implicit() {
                    let auto = if *icit == Icit::Auto { "auto " } else { "" };
                    (format!("[{auto}{x}: {dom}] {arrow} {cod}"), Prec::Arrow)
                } else if uses {
                    (format!("({x}: {dom}) {arrow} {cod}"), Prec::Arrow)
                } else {
                    (format!("{dom} {arrow} {cod}"), Prec::Arrow)
                }
            }
            // An operator section or a bare operator is shown as written:
            // `(== id)`, `(k +)`, `(&&)`.
            Term::Lam(..) if let Some(section) = self.section(names, term) => (section, Prec::Atom),
            // Nested lambdas are one run: `x y => body`. A lambda is a whole
            // expression only; everywhere else it gets brackets, since it
            // prints at the loosest precedence (docs/proposals/lambda-syntax.md §8.3).
            // Implicit and auto parameters are written as such (§4.3), with
            // their types left to be worked out, since a lambda doesn't
            // record them: `[a: _] x => x`. A section's hidden parameter,
            // where the lambda isn't shown as the section, gets a readable
            // name; a section inside the run ends it.
            Term::Lam(x, icit, b) => {
                let x = binder(x, names, b);
                let mut params = vec![lambda_param(&x, *icit)];
                names.push(x);
                let mut body = &**b;
                while let Term::Lam(y, icit, inner) = body.strip_loc() {
                    if self.section(names, body).is_some() {
                        break;
                    }
                    let y = binder(y, names, inner);
                    params.push(lambda_param(&y, *icit));
                    names.push(y);
                    body = inner;
                }
                let body = self.print(names, body, Prec::Arrow);
                names.truncate(names.len() - params.len());
                (format!("{} => {body}", params.join(" ")), Prec::Arrow)
            }
            // A `let` an update binds its record or a new value with is
            // shown as the update written, with the value in place.
            Term::Let(x, _, v, b, _)
                if is_update_let(x)
                    && let Ok(body) = b.instantiate(self.g, v) =>
            {
                self.go(names, &body)
            }
            // The annotation isn't shown, as for `Ann`.
            Term::Let(x, _, v, b, _) => {
                let value = self.print(names, v, Prec::Arrow);
                let x = binder(x, names, b);
                names.push(x.clone());
                let body = self.print(names, b, Prec::Arrow);
                names.pop();
                (format!("let {x} := {value}; {body}"), Prec::Arrow)
            }
            Term::Meta(crate::value::ELIDED) => ("…".into(), Prec::Atom),
            // An open goal's assumption, with the variables it was closed
            // over: the `?` the reader wrote.
            Term::App(..) if self.is_assumed(full_spine(term).0) => ("?".into(), Prec::Atom),
            Term::Meta(_) | Term::App(..) if let Some(shown) = self.placeholder(names, term) => {
                shown
            }
            Term::Meta(_) if let Some(name) = self.label(names, term) => name,
            Term::Meta(m) => (format!("?{m}"), Prec::Atom),
            Term::App(..) if let Some(shown) = self.label(names, term) => shown,
            Term::App(..) if let Some(shown) = self.update(names, term) => (shown, Prec::Atom),
            Term::App(..)
                if !self.show_hidden.get()
                    && let Some(shown) = self.call_with_defaults(names, term) =>
            {
                shown
            }
            // Asked for the hidden arguments: shown even where the call has a
            // notation of its own, such as the proof in `c % 7` (SW-323).
            Term::App(..) if self.show_hidden.get() && has_hidden_argument(term) => {
                self.applied_with_hidden(names, term)
            }
            Term::App(..) => {
                // Implicit arguments are filled in by the compiler, so they
                // aren't shown.
                let (head, args) = explicit_spine(term);
                if let Term::Def(id) = head {
                    // At the empty row, a computation is its value: `CompIn
                    // Empty a` is `a`, and `doneIn Empty v` is `v`, as a pure
                    // callback of an effect-polymorphic function has it.
                    if (self.g.env.registry().is_def(Builtin::CompIn, *id)
                        || self.g.env.registry().is_def(Builtin::DoneIn, *id))
                        && let [row, value] = &args[..]
                        && let Term::Ctor(d, c, fields) = row.strip_loc()
                        && fields.is_empty()
                        && self.g.env.registry().ctor(Builtin::RowEmpty) == Some((*d, *c))
                    {
                        return self.go(names, value);
                    }
                    // A value made a computation, `doneIn e v` or `doneD d e
                    // v`, is the value as written: the wrapper is the
                    // compiler's, unless the hidden arguments are asked for.
                    if !self.show_hidden.get()
                        && let Some(value) = match &args[..] {
                            [_, value] if self.g.env.registry().is_def(Builtin::DoneIn, *id) => {
                                Some(value)
                            }
                            [_, _, value] if self.g.env.registry().is_def(Builtin::DoneD, *id) => {
                                Some(value)
                            }
                            _ => None,
                        }
                    {
                        return self.go(names, value);
                    }
                    // A computation in a bare row that may be partial
                    // (docs/proposals/partial-stage-3.md): `CompD d e a` is
                    // `{e} a`, as written; at `Total` it's `CompIn e a`, and
                    // at `MayDiverge` `{Partial | e} a`. `doneD Total e v`
                    // is `doneIn e v`.
                    if (self.g.env.registry().is_def(Builtin::CompD, *id)
                        || self.g.env.registry().is_def(Builtin::DoneD, *id))
                        && let [div, row, result] = &args[..]
                    {
                        let ctor = match div.strip_loc() {
                            Term::Ctor(d, c, fields) if fields.is_empty() => Some((*d, *c)),
                            _ => None,
                        };
                        let empty = matches!(row.strip_loc(), Term::Ctor(d, c, fields)
                            if fields.is_empty()
                                && self.g.env.registry().ctor(Builtin::RowEmpty) == Some((*d, *c)));
                        let total =
                            ctor.is_some() && ctor == self.g.env.registry().ctor(Builtin::DivTotal);
                        let may =
                            ctor.is_some() && ctor == self.g.env.registry().ctor(Builtin::DivMay);
                        if self.g.env.registry().is_def(Builtin::DoneD, *id) {
                            if total && empty {
                                return self.go(names, result);
                            }
                        } else {
                            if total && empty {
                                return self.go(names, result);
                            }
                            let shown = self.print(names, result, Prec::App);
                            if may && empty {
                                return (format!("{{Partial}} {shown}"), Prec::App);
                            }
                            // A row with abilities, `Ops op res`
                            // (docs/proposals/partial-handlers.md §4):
                            // `{A | e} a`, or `{A, Partial | e} a`.
                            if let Term::Ctor(d, c, fields) = row.strip_loc()
                                && self.g.env.registry().ctor(Builtin::RowOps) == Some((*d, *c))
                                && let [op, _] = &fields[..]
                                && let Some(row) = self.row_with(names, op, may)
                            {
                                return (format!("{row} {shown}"), Prec::App);
                            }
                            let row = self.print(names, row, Prec::App);
                            if may {
                                return (format!("{{Partial | {row}}} {shown}"), Prec::App);
                            }
                            return (format!("{{{row}}} {shown}"), Prec::App);
                        }
                    }
                    // A computation in a row variable's row: `{e} a`.
                    if self.g.env.registry().is_def(Builtin::CompIn, *id)
                        && let [row, result] = &args[..]
                    {
                        let row = self.print(names, row, Prec::App);
                        let result = self.print(names, result, Prec::App);
                        return (format!("{{{row}}} {result}"), Prec::App);
                    }
                    // A projection, as written: `x.name` or `p.fst`. Not a
                    // decision's test, which the operator rules below print
                    // as the `==` or `<` it elaborates from where they can.
                    if self.g.env.registry().loaded_def(Builtin::Holds) != Some(*id)
                        && let Some(field) = self.projection_field(*id)
                        && let [arg] = &args[..]
                    {
                        let arg = self.print(names, arg, Prec::Atom);
                        return (format!("{arg}.{field}"), Prec::Atom);
                    }
                    // `-x` and `n.toInt`, as they're written (SW-937).
                    if let [arg] = &args[..] {
                        if self.g.env.registry().loaded_def(Builtin::IntNeg) == Some(*id) {
                            return self.int_negation(names, arg);
                        }
                        if self.g.env.registry().loaded_def(Builtin::NatToInt) == Some(*id) {
                            return (self.to_int(names, arg), Prec::Atom);
                        }
                    }
                    if let Some(shown) = self.bool_logic(names, term) {
                        return shown;
                    }
                    // `if c then a else b`.
                    if self.g.env.registry().is_def(Builtin::IfThenElse, *id)
                        && let [cond, then, otherwise] = &args[..]
                        && let Some(then) = self.unused_branch(names, then)
                        && let Some(otherwise) = self.unused_branch(names, otherwise)
                    {
                        let cond = if matches!(cond.strip_loc(), Term::Lam(..)) {
                            self.print(names, cond, Prec::Or)
                        } else {
                            self.print(names, cond, Prec::Arrow)
                        };
                        return (
                            format!("if {cond} then {then} else {otherwise}"),
                            Prec::Arrow,
                        );
                    }
                    // `if c then a else b` on a decided proposition.
                    if let Some(shown) = self.decided_if(names, term, *id) {
                        return shown;
                    }
                    // A partial computation: `{IO, Partial} a`.
                    if self.g.env.builtins().primitive(*id)
                        == Some(crate::partial::Primitive::Delay)
                        && let [ops, _, result] = &args[..]
                        && let Some(row) = self.row_with(names, ops, true)
                    {
                        let result = self.print(names, result, Prec::App);
                        return (format!("{row} {result}"), Prec::App);
                    }
                    if let Some((op, lhs, rhs)) =
                        self.comparison(term).or_else(|| self.relation(term))
                    {
                        let lhs = self.print(names, lhs, Prec::Range);
                        let rhs = self.print(names, rhs, Prec::Range);
                        return (format!("{lhs} {op} {rhs}"), Prec::Eq);
                    }
                    if let Some((lhs, rhs)) = self.decided_equation(names.len(), term) {
                        let lhs = self.print(names, lhs, Prec::Range);
                        let rhs = self.print(names, rhs, Prec::Add);
                        return (format!("{lhs} == {rhs}"), Prec::Eq);
                    }
                    if let Some(range) = self.range(names, *id, &args) {
                        return (range, Prec::Range);
                    }
                    if let Some((op, prec, lhs, rhs)) = self.arithmetic(*id, &args) {
                        // `+`, `-`, `*`, `/` and `%` associate left;
                        // comparisons don't associate.
                        let (left, right) = match prec {
                            Prec::Add => (Prec::Add, Prec::App),
                            Prec::Mul => (Prec::Mul, Prec::Neg),
                            Prec::Append => (Prec::Add, Prec::Append),
                            _ => (Prec::Add, Prec::Add),
                        };
                        let lhs = self.print(names, lhs, left);
                        let rhs = self.print(names, rhs, right);
                        return (format!("{lhs} {op} {rhs}"), prec);
                    }
                    if self.g.env.registry().is_def(Builtin::Not, *id)
                        && let [prop] = &args[..]
                    {
                        return self.not(names, prop);
                    }
                    // `List.Mem x xs` as `x ∈ xs`.
                    if let Some((x, under, xs)) = self.membership(term) {
                        let x = self.print_under(names, under, x, Prec::Add);
                        let xs = self.print(names, xs, Prec::Range);
                        return (format!("{x} {} {xs}", self.sym("∈", "in")), Prec::Eq);
                    }
                    // An interface's own projection of a field, `Ord.%compare
                    // d x y`, as the method that computes to it (SW-1000):
                    // `Ord.compare x y`, the dictionary given by name unless
                    // it's a variable, a dictionary in scope, which the
                    // method finds itself (`Ord.compare [ord := Nat.instOrd]
                    // x y`).
                    // `(DecEq.%decide d a b).holds`, `d` a dictionary in
                    // scope, is `a == b` as it elaborates there (SW-1000).
                    if self.g.env.registry().loaded_def(Builtin::Holds) == Some(*id)
                        && let [decision] = &args[..]
                        && let Some((lhs, rhs)) = self.decide_in_scope(decision)
                    {
                        let lhs = self.print(names, lhs, Prec::Add);
                        let rhs = self.print(names, rhs, Prec::Add);
                        return (format!("{lhs} == {rhs}"), Prec::Eq);
                    }
                    if let Some(scope) = self.scope
                        && let Some((method, dict)) = scope.method(*id)
                        && let Some((d, rest)) = args.split_first()
                    {
                        let mut head = self.def_name(names, method);
                        if !matches!(d.strip_loc(), Term::Var(_)) {
                            let d = self.print(names, d, Prec::Arrow);
                            head = format!("{head} [{dict} := {d}]");
                        }
                        return self.applied(names, head, rest.iter().copied());
                    }
                }
                if self.show_hidden.get() {
                    return self.applied_with_hidden(names, term);
                }
                if let Term::Def(id) = head {
                    match self.dot_call(names, *id, &args) {
                        Dot::Call(shown) => return shown,
                        // Printing the receiver again would double the work
                        // at each receiver in a chain of such calls.
                        Dot::Declined(receiver) => {
                            let head = self.print(names, head, Prec::App);
                            let head = format!("{head} {receiver}");
                            let (text, _) = self.applied(names, head, args[1..].iter().copied());
                            return (text, Prec::App);
                        }
                        Dot::No => {}
                    }
                }
                // Last, so the notations that print a library helper (`if`
                // on a decision) are tried first.
                if let Some(shown) = self.lifted_match(names, term) {
                    return (shown, Prec::Atom);
                }
                let head = self.print(names, head, Prec::App);
                self.applied(names, head, args.into_iter())
            }
            Term::Case(ix, _, _) | Term::NumCase(ix, _, _) => {
                let scrutinee = self.print(names, &Term::Var(*ix), Prec::Atom);
                (format!("case {scrutinee} of …"), Prec::Arrow)
            }
            // `a < b` and `a <= b` as propositions on `Nat`, `Int` and
            // `Float` compute to the `Bool` comparison being `True`.
            Term::Eq(_, a, b)
                if self.is_ctor(b, Builtin::True)
                    && let Some((op, lhs, rhs)) = self.comparison(a) =>
            {
                let op = if op == "<" { op } else { self.sym("≤", "<=") };
                let lhs = self.print(names, lhs, Prec::Add);
                let rhs = self.print(names, rhs, Prec::Add);
                (format!("{lhs} {op} {rhs}"), Prec::Eq)
            }
            // A test being `True` as the test alone, `c.isDigit`, which reads
            // back to this where a proposition is expected
            // (docs/proposals/bool-as-proposition.md §4.4).
            Term::Eq(_, a, b) if self.bare_test(a, b) => self.go(names, a),
            Term::Eq(_, a, b) => {
                // A side that is a test being `True` keeps its `= True`: a
                // side of `=` isn't read as a proposition.
                let side = |names: &mut Vec<Name>, side: &Term| match side.strip_loc() {
                    Term::Eq(_, test, t) if self.bare_test(test, t) => {
                        let test = self.print(names, test, Prec::Range);
                        format!("({test} = True)")
                    }
                    _ => self.print(names, side, Prec::Range),
                };
                let lhs = side(names, a);
                let rhs = side(names, b);
                (format!("{lhs} = {rhs}"), Prec::Eq)
            }
            Term::J(m, b, p) => self.applied(names, "J".into(), [&**m, &**b, &**p].into_iter()),
            // A projection, as field access is written: `p.row`.
            Term::Proj(d, i, t) => {
                let t = self.print(names, t, Prec::Atom);
                let field = self
                    .g
                    .env
                    .datas()
                    .get(d.0)
                    .and_then(|data| data.ctors.first())
                    .and_then(|ctor| ctor.fields.get(*i))
                    .map_or_else(|| i.to_string(), |(name, _)| name.to_string());
                (format!("{t}.{field}"), Prec::Atom)
            }
            // As written: `Quot.mk a`, the implicit arguments hidden unless
            // asked for (`Quot.mk [Bool] [AllTrue] a`).
            Term::Quot(form, args, _) => {
                let hidden = form.implicit().min(args.len());
                if self.show_hidden.get() {
                    let mut text = form.name().to_string();
                    for arg in &args[..hidden] {
                        text.push_str(" [");
                        text.push_str(&self.print(names, arg, Prec::Arrow));
                        text.push(']');
                    }
                    let (rest, prec) =
                        self.applied(names, String::new(), args[hidden..].iter().map(|a| &**a));
                    text.push_str(&rest);
                    let prec = if hidden > 0 { Prec::App } else { prec };
                    return (text, prec);
                }
                self.applied(
                    names,
                    form.name().into(),
                    args[hidden..].iter().map(|a| &**a),
                )
            }
        }
    }

    /// `∀ (a b: Nat) [c: Nat] => body` for the run of function types at
    /// `term` that [`Printer::go_node`] prints as one: each binder implicit,
    /// or explicit and used by what follows. Neighbouring binders of the same
    /// kind and type share a group, unless the type mentions one before it
    /// in the group. An unused explicit binder, `p → q`, ends the run, so a
    /// hypothesis stays an implication inside the body.
    fn forall(&self, names: &mut Vec<Name>, term: &Term) -> (String, Prec) {
        // Each group: its kind, its type as printed, and its names.
        let mut groups: Vec<(Icit, String, Vec<Name>)> = Vec::new();
        let mut bound = 0;
        let mut body = term.strip_loc();
        while let Term::Pi(x, icit, a, b) = body {
            if !(icit.is_implicit() || b.mentions(0)) {
                break;
            }
            let dom = self.print(names, a, Prec::Arrow);
            let x = binder(x, names, b);
            match groups.last_mut() {
                Some((kind, ty, xs))
                    if kind == icit && *ty == dom && !(0..xs.len()).any(|i| a.mentions(i)) =>
                {
                    xs.push(x.clone());
                }
                _ => groups.push((*icit, dom, vec![x.clone()])),
            }
            names.push(x);
            bound += 1;
            body = b.strip_loc();
        }
        let body = self.print(names, body, Prec::Arrow);
        names.truncate(names.len() - bound);
        let groups: Vec<String> = groups
            .into_iter()
            .map(|(icit, ty, xs)| {
                let xs: Vec<String> = xs.iter().map(|x| x.to_string()).collect();
                let xs = xs.join(" ");
                match icit {
                    Icit::Explicit => format!("({xs}: {ty})"),
                    Icit::Implicit => format!("[{xs}: {ty}]"),
                    Icit::Auto => format!("[auto {xs}: {ty}]"),
                }
            })
            .collect();
        let forall = self.sym("∀", "forall");
        (
            format!("{forall} {} => {body}", groups.join(" ")),
            Prec::Arrow,
        )
    }

    /// Whether the type `ty` is evidently a proposition, from its form
    /// alone (the printer has no types for the variables in scope): after
    /// any function types, an equation, or a data type declared in `Prop`
    /// (`And`, `Exists`, `Void`, a user's `type Even (n: Nat): Prop`)
    /// applied to its arguments, or a call of a definition whose declared
    /// type ends in `Prop` (`Nat.lessEq`, `List.Sorted`), or a context
    /// variable known to be a predicate applied to arguments (`p x`, with
    /// `p: Nat → Prop`; see [`value_for_goal`]). A variable not known to be
    /// one isn't evidently a proposition, nor is an unknown.
    fn is_proposition(&self, names: &[Name], ty: &Term) -> bool {
        let mut ty = ty.strip_loc();
        let mut depth = names.len() + 1;
        while let Term::Pi(_, _, _, b) = ty {
            ty = b.strip_loc();
            depth += 1;
        }
        match ty {
            Term::Eq(..) => true,
            Term::Data(d, _) => self.g.data(*d).sort == Sort::Prop,
            _ => {
                let (head, _) = full_spine(ty);
                if let Term::Var(i) = head {
                    // The level of a variable bound outside the term; those
                    // bound within it are not known to be predicates.
                    let level = depth.checked_sub(i + 1);
                    return level.is_some_and(|l| {
                        self.predicates.borrow().get(l).copied().unwrap_or(false)
                    });
                }
                let Term::Def(id) = head else {
                    return false;
                };
                let mut result = self.g.def(*id).ty.strip_loc();
                while let Term::Pi(_, _, _, b) = result {
                    result = b.strip_loc();
                }
                matches!(result, Term::Sort(Sort::Prop))
            }
        }
    }

    /// `n.toInt`: `Nat.toInt n`, or `OfNat n`, which it computes to. A
    /// number is put in brackets, `(5).toInt`, so the `.` isn't read as
    /// its decimal point.
    fn to_int(&self, names: &mut Vec<Name>, n: &Term) -> String {
        let shown = self.print(names, n, Prec::Atom);
        if shown.starts_with(|c: char| c.is_ascii_digit()) {
            format!("({shown}).toInt")
        } else {
            format!("{shown}.toInt")
        }
    }

    /// `-x`: `Int.neg x`, which `-x` elaborates to on an `Int`. An operand
    /// that starts with a minus itself is put in brackets, `-(-x)`, as
    /// `--` would start a comment.
    fn int_negation(&self, names: &mut Vec<Name>, x: &Term) -> (String, Prec) {
        let shown = self.print(names, x, Prec::Neg);
        if shown.starts_with('-') {
            (format!("-({shown})"), Prec::Neg)
        } else {
            (format!("-{shown}"), Prec::Neg)
        }
    }

    /// `Not p` as the operators that write it, in their Unicode spellings
    /// (D1204): `a ≠ b`, `x ∉ xs`, or `¬p`.
    fn not(&self, names: &mut Vec<Name>, prop: &Term) -> (String, Prec) {
        if let Term::Eq(_, a, b) = prop.strip_loc()
            && !self.bare_test(a, b)
        {
            let a = self.print(names, a, Prec::Range);
            let b = self.print(names, b, Prec::Range);
            return (format!("{a} {} {b}", self.sym("≠", "!=")), Prec::Eq);
        }
        if !self.show_hidden.get()
            && let Some((x, under, xs)) = self.membership(prop)
        {
            let x = self.print_under(names, under, x, Prec::Add);
            let xs = self.print(names, xs, Prec::Range);
            return (format!("{x} {} {xs}", self.sym("∉", "!in")), Prec::Eq);
        }
        // `!` binds more loosely than application: `¬p x` is `¬(p x)`.
        let p = self.print(names, prop, Prec::App);
        (format!("{}{p}", self.sym("¬", "!")), Prec::Neg)
    }

    /// `List.range a b` as `a ..< b`, and as `a ..= b'` when `b` is one more
    /// than `b'` (`List.range a (b' + 1)`): the same term either way, so the
    /// range reads back as it was written, or as the form that says where it
    /// stops (docs/proposals/ranges.md §6.2).
    fn range(&self, names: &mut Vec<Name>, id: DefId, args: &[&Term]) -> Option<String> {
        let [from, until] = *args else {
            return None;
        };
        if &*self.g.def(id).path != "Std.List.range" {
            return None;
        }
        let lhs = self.print(names, from, Prec::Add);
        let (k, base) = self.nat_parts(until);
        if let Some(base) = base
            && k == BigUint::from(1u32)
        {
            let last = self.print(names, base, Prec::Add);
            return Some(format!("{lhs} ..= {last}"));
        }
        let rhs = self.print(names, until, Prec::Add);
        Some(format!("{lhs} ..< {rhs}"))
    }

    /// The operator a call of `id` is shown with, and its precedence.
    fn infix(&self, id: DefId) -> Option<(&'static str, Prec)> {
        match self.g.env.registry().def_builtin(id)? {
            Builtin::Add | Builtin::IntAdd | Builtin::FloatAdd => Some(("+", Prec::Add)),
            Builtin::Sub | Builtin::IntSub | Builtin::FloatSub => Some(("-", Prec::Add)),
            Builtin::Mul | Builtin::IntMul | Builtin::FloatMul => Some(("*", Prec::Mul)),
            Builtin::Div | Builtin::IntDiv | Builtin::FloatDiv => Some(("/", Prec::Mul)),
            Builtin::Mod | Builtin::IntMod | Builtin::FloatRem => Some(("%", Prec::Mul)),
            Builtin::LessEq | Builtin::IntLessEq | Builtin::FloatLessEq => {
                Some((self.sym("≤", "<="), Prec::Eq))
            }
            Builtin::LessThan | Builtin::IntLessThan | Builtin::FloatLessThan => {
                Some(("<", Prec::Eq))
            }
            _ => None,
        }
    }

    /// The operator, its precedence and the operands of a call of `id` on
    /// the explicit arguments `args` shown as an operator: a built-in one
    /// ([`Printer::infix`]), or the library's `Add` or `Mul` method, taking
    /// its dictionary as an `auto` argument (`Add.add x y`), or the
    /// dictionary's field, taking it first (`Add.%add d x y`).
    fn arithmetic<'t>(
        &self,
        id: DefId,
        args: &[&'t Term],
    ) -> Option<(&'static str, Prec, &'t Term, &'t Term)> {
        if let (Some((op, prec)), [lhs, rhs]) = (self.infix(id), args) {
            // `n - n / d * d`, as `Nat.mod` unfolds, is `n % d`.
            if self.g.env.registry().is_def(Builtin::Sub, id)
                && let Term::App(..) = rhs.strip_loc()
                && let (Term::Def(product), factors) = explicit_spine(rhs)
                && self.g.env.registry().is_def(Builtin::Mul, *product)
                && let [quotient, divisor] = factors[..]
                && let Some((n, d)) = self.quotient(quotient)
                && same_term(n, lhs)
                && same_term(d, divisor)
            {
                return Some(("%", Prec::Mul, lhs, d));
            }
            return Some((op, prec, lhs, rhs));
        }
        if let Some((n, d)) = self.quotient_args(id, args) {
            return Some(("/", Prec::Mul, n, d));
        }
        if let [lhs, rhs] = args
            && !self.calls.get()
            && matches!(
                self.g.env.registry().def_builtin(id),
                Some(Builtin::Append | Builtin::TextAppend)
            )
        {
            return Some(("++", Prec::Append, lhs, rhs));
        }
        let path = &self.g.def(id).path;
        let (op, prec, field) = match path.strip_prefix("Std.")? {
            "Add.add" => ("+", Prec::Add, false),
            "Add.%add" => ("+", Prec::Add, true),
            "Mul.mul" => ("*", Prec::Mul, false),
            "Mul.%mul" => ("*", Prec::Mul, true),
            _ => return None,
        };
        match (field, args) {
            (true, [_, lhs, rhs]) | (false, [lhs, rhs]) => Some((op, prec, lhs, rhs)),
            _ => None,
        }
    }

    /// `n` and `d` if `term` is `n / d` in the form `Nat.mod` unfolds to:
    /// `Nat.divFuel n n d`, or `Nat.div n d`.
    fn quotient<'t>(&self, term: &'t Term) -> Option<(&'t Term, &'t Term)> {
        let (head, args) = explicit_spine(term);
        let Term::Def(id) = head else {
            return None;
        };
        if self.g.env.registry().is_def(Builtin::Div, *id)
            && let [n, d] = args[..]
        {
            return Some((n, d));
        }
        self.quotient_args(*id, &args)
    }

    /// `n` and `d` if the explicit arguments of a call of `Nat.divFuel` are
    /// `n n d`: the fuel is the number divided. Or if they're those of a
    /// call of `Nat.divStep` that `n / d` computes to: `Nat.divFuel n n d`,
    /// with `n` one more than something, takes one step, to `Nat.divStep
    /// (Nat.leq d n) f n d` with `f + 1 = n`, which is stuck when the
    /// comparison is (`n` has an unknown part). Then it is shown as the `n /
    /// d` it came from, which reads back to the same value
    /// (docs/proposals/division.md).
    fn quotient_args<'t>(&self, id: DefId, args: &[&'t Term]) -> Option<(&'t Term, &'t Term)> {
        match args {
            [fuel, n, d]
                if self.g.env.registry().is_def(Builtin::DivFuel, id) && same_term(fuel, n) =>
            {
                Some((n, d))
            }
            [fits, fuel, n, d]
                if self.g.env.registry().is_def(Builtin::DivStep, id)
                    && self.first_step(fits, fuel, n, d) =>
            {
                Some((n, d))
            }
            _ => None,
        }
    }

    /// Whether `Nat.divStep fits fuel n d` is the first step of `n / d`:
    /// `fuel + 1` is `n`, and `fits` is `Nat.leq d n`, possibly with the same
    /// number of `Succ`s taken off both sides, as `Nat.leq` computes on them
    /// (`Nat.leq 100 (3 + x)` is `Nat.leq 97 x`).
    fn first_step(&self, fits: &Term, fuel: &Term, n: &Term, d: &Term) -> bool {
        let (kn, bn) = self.nat_parts(n);
        let (kf, bf) = self.nat_parts(fuel);
        if kn != kf + 1u32 || !same_base(bn, bf) {
            return false;
        }
        let (head, compared) = explicit_spine(fits);
        let (Term::Def(leq), [a, b]) = (head, &compared[..]) else {
            return false;
        };
        if !self.g.env.registry().is_def(Builtin::Leq, *leq) {
            return false;
        }
        let (kd, bd) = self.nat_parts(d);
        let (ka, ba) = self.nat_parts(a);
        let (kb, bb) = self.nat_parts(b);
        same_base(bd, ba) && same_base(bn, bb) && kd >= ka && kn >= kb && &kd - &ka == &kn - &kb
    }

    /// A number term as `k + base`: the `Succ`s and literal `+`s around its
    /// base (none for a literal), however they are written (`Succ x`, `3 +
    /// x`, `x + 3`, `3`).
    fn nat_parts<'t>(&self, term: &'t Term) -> (BigUint, Option<&'t Term>) {
        let mut k = BigUint::from(0u32);
        let mut term = term.strip_loc();
        loop {
            match term {
                Term::Nat(n) => return (k + &**n, None),
                Term::Ctor(d, 0, _) if is(self.g, Builtin::Nat, *d) => return (k, None),
                Term::Ctor(d, 1, args) if is(self.g, Builtin::Nat, *d) && args.len() == 1 => {
                    k += 1u32;
                    term = args[0].strip_loc();
                }
                _ => {
                    let (head, args) = explicit_spine(term);
                    match (head, &args[..]) {
                        (Term::Def(add), [x, y])
                            if self.g.env.registry().is_def(Builtin::Add, *add) =>
                        {
                            match (x.strip_loc(), y.strip_loc()) {
                                (Term::Nat(n), rest) | (rest, Term::Nat(n)) => {
                                    k += &**n;
                                    term = rest;
                                }
                                _ => return (k, Some(term)),
                            }
                        }
                        _ => return (k, Some(term)),
                    }
                }
            }
        }
    }

    /// Whether `t` is the constructor `ctor` with no fields.
    /// Whether `test = rhs` is printed as `test` alone: `rhs` is `True`, and
    /// the text of `test` reads back, where a proposition is expected, as
    /// `test = True` and not as some other proposition
    /// (docs/proposals/bool-as-proposition.md §4.4). So not when `test`'s
    /// printed form starts with an operator that is logical where a
    /// proposition is expected (D3486,
    /// docs/proposals/bool-operators-in-propositions.md §5; the
    /// elaborator's half of that rule is `logic::as_prop` in
    /// `stitchwort_elab`):
    ///
    /// - `a && b` and `a || b`, which would read back as `a = True ∧ b =
    ///   True`;
    /// - `Bool.not a` written as a call rather than `a.not`, which would
    ///   read back as `¬(a = True)`;
    /// - `a != b`, which reads back as the proposition `a ≠ b`.
    ///
    /// An `if` or a `match` is printed bare: where a proposition is expected
    /// a test of that shape is read back whole. The constants keep `= True`
    /// too: `False = True` is the familiar shape of a case that can't happen.
    fn bare_test(&self, test: &Term, rhs: &Term) -> bool {
        if !self.is_ctor(rhs, Builtin::True)
            || self.is_ctor(test, Builtin::True)
            || self.is_ctor(test, Builtin::False)
        {
            return false;
        }
        if let Some((_, then, otherwise)) = self.bool_if(test)
            && !self.both_constants(&then, &otherwise)
            && (self.is_ctor(&otherwise.1, Builtin::False) || self.is_ctor(&then.1, Builtin::True))
        {
            return false;
        }
        let (head, args) = full_spine(test.strip_loc());
        let reg = self.g.env.registry();
        match head.strip_loc() {
            Term::Def(id) if reg.is_def(Builtin::BoolNot, *id) => !self.calls.get(),
            Term::Def(id) if reg.loaded_def(Builtin::Holds) == Some(*id) => !matches!(
                args[..],
                [(prop, Icit::Implicit), _] if self.negated(prop).is_some()
            ),
            _ => true,
        }
    }

    fn is_ctor(&self, t: &Term, ctor: Builtin) -> bool {
        matches!(t.strip_loc(), Term::Ctor(d, c, fields)
            if fields.is_empty() && self.g.env.registry().ctor(ctor) == Some((*d, *c)))
    }

    /// `a && b` and `a || b` on `Bool`s, as they elaborate: `if a then b
    /// else False` and `if a then True else b`, each branch a lambda whose
    /// body doesn't use its parameter.
    ///
    /// `if a then True else False` is both `a && True` and `a || False`
    /// (SW-946). As the last operand of a chain it's printed with the
    /// chain's operator (`p && q && True`, `p || q || False`, as a fold of
    /// `List.all` or `List.any` computes); on its own it stays the `if`,
    /// since either operator reads as a slip for the other. Each pastes back
    /// to the same term.
    fn bool_logic(&self, names: &mut Vec<Name>, term: &Term) -> Option<(String, Prec)> {
        let (cond, then, otherwise) = self.bool_if(term)?;
        if self.both_constants(&then, &otherwise) {
            return None;
        }
        // `||` and `&&` group to the right.
        let (op, prec, left, (x, rhs)) = if self.is_ctor(&otherwise.1, Builtin::False) {
            ("&&", Prec::And, Prec::Eq, then)
        } else if self.is_ctor(&then.1, Builtin::True) {
            ("||", Prec::Or, Prec::And, otherwise)
        } else {
            return None;
        };
        let lhs = self.print(names, cond, left);
        names.push(x);
        let rhs = match self.bool_if(&rhs) {
            Some((last, then, otherwise)) if self.both_constants(&then, &otherwise) => {
                let (y, constant) = if op == "&&" { then } else { otherwise };
                let last = self.print(names, last, left);
                names.push(y);
                let constant = self.print(names, &constant, prec);
                names.pop();
                format!("{last} {op} {constant}")
            }
            _ => self.print(names, &rhs, prec),
        };
        names.pop();
        Some((format!("{lhs} {op} {rhs}"), prec))
    }

    /// `if a then … else …` on `Bool`s: `a`, and each branch's parameter
    /// and body, for a branch whose body doesn't use its parameter.
    fn bool_if<'t>(&self, term: &'t Term) -> Option<(&'t Term, Branch, Branch)> {
        let (head, args) = full_spine(term);
        let Term::Def(id) = head else {
            return None;
        };
        if !self.g.env.registry().is_def(Builtin::IfThenElse, *id) {
            return None;
        }
        let [
            (ty, Icit::Implicit),
            (cond, Icit::Explicit),
            (then, Icit::Explicit),
            (otherwise, Icit::Explicit),
        ] = args[..]
        else {
            return None;
        };
        if !matches!(ty.strip_loc(), Term::Data(d, ps) if ps.is_empty() && is(self.g, Builtin::Bool, *d))
        {
            return None;
        }
        let branch = |t: &Term| match t.strip_loc() {
            Term::Lam(x, Icit::Explicit, body) if !body.mentions(0) => {
                Some((x.clone(), body.clone()))
            }
            _ => None,
        };
        Some((cond, branch(then)?, branch(otherwise)?))
    }

    /// Whether the branches are `True` and `False`: `if a then True else
    /// False`.
    fn both_constants(&self, then: &Branch, otherwise: &Branch) -> bool {
        self.is_ctor(&then.1, Builtin::True) && self.is_ctor(&otherwise.1, Builtin::False)
    }

    /// The operator and operands of a `Bool` comparison, as `<` and `<=`
    /// elaborate: on `Nat`, `Nat.leq (Succ a) b` and `Nat.leq a b`; on `Int`
    /// and `Float`, `Int.less a b`, `Int.leq a b` and `Float`'s alike; and
    /// through an `Ord` dictionary, `Decidable.holds (Ord.decLessThan d a
    /// b)` and `Decidable.holds (Ord.decLessEq d a b)`.
    fn comparison<'t>(&self, term: &'t Term) -> Option<(&'static str, &'t Term, &'t Term)> {
        let (head, args) = explicit_spine(term.strip_loc());
        let Term::Def(id) = head else {
            return None;
        };
        if self.g.env.registry().loaded_def(Builtin::Holds) == Some(*id) {
            let [decision] = args[..] else {
                return None;
            };
            return match self.ord_call(decision)? {
                ("decLessThan", lhs, rhs) => Some(("<", lhs, rhs)),
                ("decLessEq", lhs, rhs) => Some(("<=", lhs, rhs)),
                _ => None,
            };
        }
        let [lhs, rhs] = args[..] else {
            return None;
        };
        let op = match self.g.env.registry().def_builtin(*id)? {
            Builtin::Leq => match lhs.strip_loc() {
                Term::Ctor(d, 1, m) if is(self.g, Builtin::Nat, *d) && m.len() == 1 => {
                    return Some(("<", &m[0], rhs));
                }
                _ => "<=",
            },
            Builtin::IntLeq | Builtin::FloatLeq => "<=",
            Builtin::IntLess | Builtin::FloatLess => "<",
            _ => return None,
        };
        // `Float.leq x y` and `Float.less x y` unfolded, comparing the two
        // floats' order keys as `Int`s, are `x <= y` and `x < y` (SW-1000).
        if let (Some(x), Some(y)) = (self.float_key(lhs), self.float_key(rhs)) {
            return Some((op, x, y));
        }
        Some((op, lhs, rhs))
    }

    /// `x`, if `term` is `Float.orderKey x`, or that unfolded one step:
    /// `Float.keyOf x.bits (Nat.leq 9223372036854775808 x.bits)`.
    fn float_key<'t>(&self, term: &'t Term) -> Option<&'t Term> {
        let path = |id: &DefId| &*self.g.def(*id).path;
        match explicit_spine(term) {
            (Term::Def(id), args) if path(id) == "Std.Float.orderKey" => match args[..] {
                [x] => Some(x),
                _ => None,
            },
            (Term::Def(id), args) if path(id) == "Std.Float.keyOf" => {
                let [bits, negative] = args[..] else {
                    return None;
                };
                let of_bits = |t: &'t Term| match explicit_spine(t) {
                    (Term::Def(p), xs) if self.projection_field(*p).as_deref() == Some("bits") => {
                        match xs[..] {
                            [x] => Some(x),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                let x = of_bits(bits)?;
                let (Term::Def(leq), compared) = explicit_spine(negative) else {
                    return None;
                };
                let sign = BigUint::from(1u64 << 63);
                let is_sign = |t: &Term| matches!(t.strip_loc(), Term::Nat(n) if **n == sign);
                (self.g.env.registry().is_def(Builtin::Leq, *leq)
                    && matches!(compared[..], [k, b] if is_sign(k) && of_bits(b).is_some_and(|y| same_term(x, y))))
                .then_some(x)
            }
            _ => None,
        }
    }

    /// The sides of `Decidable.holds {a = b} d`, to be written `a == b`:
    /// only where that elaborates to this term or one it computes to, and
    /// only in a goal. `a == b` elaborates to `holds {a = b} (f a b)`, `f`
    /// what the scope's `==` decides an equation of the type by
    /// ([`NameScope::eq_decision`]). `d` is that, or something it computes
    /// to with the goal's `level` variables unknown, which `a == b` pasted
    /// back checks as the same.
    fn decided_equation<'t>(&self, level: usize, term: &'t Term) -> Option<(&'t Term, &'t Term)> {
        if !self.equations.get() || self.show_hidden.get() {
            return None;
        }
        let scope = self.scope?;
        let (head, args) = full_spine(term);
        let Term::Def(id) = head else {
            return None;
        };
        if self.g.env.registry().loaded_def(Builtin::Holds) != Some(*id) {
            return None;
        }
        let [(prop, Icit::Implicit), (decision, Icit::Explicit)] = args[..] else {
            return None;
        };
        let Term::Eq(Some(ty), a, b) = prop.strip_loc() else {
            return None;
        };
        let f = scope.eq_decision(ty)?;
        let written = Term::app(Term::app(f, (**a).clone()), (**b).clone());
        if same_term(&written, decision) {
            return Some((&**a, &**b));
        }
        // Computed: compare the two with the goal's variables unknown. A
        // goal with a metavariable in it is left as it is.
        if [decision, &**a, &**b]
            .iter()
            .any(|t| t.subterms().any(|(t, _)| matches!(t, Term::Meta(_))))
        {
            return None;
        }
        let env: Vec<Value> = (0..level).map(Value::var).collect();
        let written = crate::value::eval(self.g, &env, &written).ok()?;
        let decision = crate::value::eval(self.g, &env, decision).ok()?;
        crate::value::conv(self.g, level, &written, &decision)
            .ok()?
            .then_some((&**a, &**b))
    }

    /// The operator and operands of `a < b` or `a <= b` as propositions
    /// through an `Ord` dictionary: `Ord.lessThan d a b`, `Ord.lessEq d a b`.
    fn relation<'t>(&self, term: &'t Term) -> Option<(&'static str, &'t Term, &'t Term)> {
        match self.ord_call(term)? {
            ("lessThan", lhs, rhs) => Some(("<", lhs, rhs)),
            ("lessEq", lhs, rhs) => Some((self.sym("≤", "<="), lhs, rhs)),
            _ => None,
        }
    }

    /// A call of a member of the library's `Ord` on two operands: the
    /// member's name and the operands. The member is a method, taking its
    /// dictionary as an `auto` argument (`Ord.lessThan a b`), or the
    /// dictionary's field, taking it first (`Ord.%lessThan d a b`).
    fn ord_call<'t>(&self, term: &'t Term) -> Option<(&'g str, &'t Term, &'t Term)> {
        let (head, args) = explicit_spine(term.strip_loc());
        let Term::Def(id) = head else {
            return None;
        };
        let g: &'g Ev<'g> = self.g;
        let member = g.def(*id).path.strip_prefix("Std.Ord.")?;
        match (member.strip_prefix('%'), &args[..]) {
            (Some(field), [_, lhs, rhs]) => Some((field, *lhs, *rhs)),
            (None, [lhs, rhs]) => Some((member, *lhs, *rhs)),
            _ => None,
        }
    }

    /// A section's lambda as written: `(== id)` for `%section => %section
    /// == id`, `(k +)` for `%section => k + %section`, and `(&&)` for a bare
    /// operator's `%left %right => %left && %right`.
    fn section(&self, names: &mut Vec<Name>, term: &Term) -> Option<String> {
        let Term::Lam(x, Icit::Explicit, body) = term.strip_loc() else {
            return None;
        };
        let is_var = |t: &Term, ix: usize| matches!(t.strip_loc(), Term::Var(i) if *i == ix);
        match &**x {
            SECTION => {
                let (op, operand, lhs, rhs) = self.operation(body)?;
                names.push(x.clone());
                // `(- 1)` is the number, so `x - 1` isn't a section.
                let text = if is_var(lhs, 0) && !rhs.mentions(0) && op != "-" {
                    Some(format!("({op} {})", self.print(names, rhs, operand)))
                } else if is_var(rhs, 0) && !lhs.mentions(0) {
                    Some(format!("({} {op})", self.print(names, lhs, operand)))
                } else {
                    None
                };
                names.pop();
                text
            }
            LEFT => {
                let Term::Lam(y, Icit::Explicit, body) = body.strip_loc() else {
                    return None;
                };
                if &**y != RIGHT {
                    return None;
                }
                let (op, _, lhs, rhs) = self.operation(body)?;
                (is_var(lhs, 1) && is_var(rhs, 0)).then(|| format!("({op})"))
            }
            _ => None,
        }
    }

    /// The operator, the precedence its operand in a section is printed at,
    /// and the two operands of an operation a section can write. Besides the
    /// operators printed everywhere, these include the `Bool` ones as they
    /// are elaborated: `a == b` is `Decidable.holds {a = b} d`, `a != b`
    /// the same with `Not (a = b)`, `a < b` on `Nat` is `Nat.leq (Succ a)
    /// b`, and `a <= b` is `Nat.leq a b`.
    fn operation<'t>(&self, term: &'t Term) -> Option<(&'static str, Prec, &'t Term, &'t Term)> {
        if let Term::Eq(_, a, b) = term.strip_loc() {
            return Some(("=", Prec::Add, a, b));
        }
        if let Some((op, lhs, rhs)) = self.comparison(term) {
            return Some((op, Prec::Add, lhs, rhs));
        }
        let (head, args) = full_spine(term);
        let Term::Def(id) = head else {
            return None;
        };
        let reg = &self.g.env.registry();
        if reg.loaded_def(Builtin::Holds) == Some(*id) {
            let [(prop, Icit::Implicit), (_, Icit::Explicit)] = args[..] else {
                return None;
            };
            if let Term::Eq(_, a, b) = prop.strip_loc() {
                return Some(("==", Prec::Add, a, b));
            }
            if let Some(Term::Eq(_, a, b)) = self.negated(prop).map(Term::strip_loc) {
                return Some(("!=", Prec::Add, a, b));
            }
            return None;
        }
        let explicit: Vec<&Term> = args
            .iter()
            .filter(|(_, icit)| *icit == Icit::Explicit)
            .map(|(arg, _)| *arg)
            .collect();
        let [lhs, rhs] = explicit[..] else {
            return None;
        };
        // An operand binds one step tighter than the operator.
        if let Some((op, prec)) = self.infix(*id) {
            let operand = match prec {
                Prec::Add => Prec::Mul,
                Prec::Mul => Prec::Neg,
                _ => Prec::Add,
            };
            return Some((op, operand, lhs, rhs));
        }
        let op = match reg.def_builtin(*id)? {
            Builtin::Append | Builtin::TextAppend if !self.calls.get() => "++",
            _ => return None,
        };
        Some((op, Prec::Add, lhs, rhs))
    }

    /// `p`, if `prop` is `Not p` or what it computes to, `p → Void`.
    fn negated<'t>(&self, prop: &'t Term) -> Option<&'t Term> {
        match prop.strip_loc() {
            Term::Pi(_, Icit::Explicit, p, void)
                if !void.mentions(0)
                    && matches!(void.strip_loc(), Term::Data(d, _) if is(self.g, Builtin::Void, *d)) =>
            {
                Some(p)
            }
            prop => match explicit_spine(prop) {
                (Term::Def(id), args) if self.g.env.registry().is_def(Builtin::Not, *id) => {
                    match args[..] {
                        [p] => Some(p),
                        _ => None,
                    }
                }
                _ => None,
            },
        }
    }

    /// The sides of `DecEq.%decide d a b` with `d` a variable, a dictionary
    /// in scope: what `a == b` elaborates to there (SW-1000).
    fn decide_in_scope<'t>(&self, term: &'t Term) -> Option<(&'t Term, &'t Term)> {
        let (Term::Def(id), args) = explicit_spine(term) else {
            return None;
        };
        let (method, _) = self.scope?.method(*id)?;
        match args[..] {
            [d, lhs, rhs]
                if &*self.g.def(method).path == "Std.DecEq.decide"
                    && matches!(d.strip_loc(), Term::Var(_)) =>
            {
                Some((lhs, rhs))
            }
            _ => None,
        }
    }

    /// The element and the list of `List.Mem x xs`, or of what it unfolds
    /// to, `List.Any (y => y = x) xs` (SW-1000), with how many binders the
    /// element is under (none, or the lambda's one, which it doesn't
    /// mention).
    fn membership<'t>(&self, term: &'t Term) -> Option<(&'t Term, usize, &'t Term)> {
        let id = self.g.env.registry().loaded_def(Builtin::ListMem)?;
        let (head, args) = explicit_spine(term.strip_loc());
        match (head, &args[..]) {
            (Term::Def(d), [x, xs]) if *d == id => Some((x, 0, xs)),
            (Term::Def(d), [pred, xs]) if &*self.g.def(*d).path == "Std.List.Any" => {
                let Term::Lam(_, Icit::Explicit, body) = pred.strip_loc() else {
                    return None;
                };
                let Term::Eq(_, y, x) = body.strip_loc() else {
                    return None;
                };
                (matches!(y.strip_loc(), Term::Var(0)) && !x.mentions(0)).then_some((&**x, 1, *xs))
            }
            _ => None,
        }
    }

    /// [`Printer::print`] for a term under `under` binders it doesn't
    /// mention.
    fn print_under(&self, names: &mut Vec<Name>, under: usize, term: &Term, prec: Prec) -> String {
        names.extend((0..under).map(|_| Name::from("%unused")));
        let text = self.print(names, term, prec);
        names.truncate(names.len() - under);
        text
    }

    /// An unfilled placeholder of a queued check, as the source it stands
    /// for (`Shown::placeholder`, D2091), if it is applied to the
    /// variables it was made with: those left out, any further arguments
    /// shown. Applied to anything else (a lambda's parameter replaced by an
    /// argument), the source would name the wrong variables: `None`.
    fn placeholder(&self, names: &mut Vec<Name>, term: &Term) -> Option<(String, Prec)> {
        let mut head = term.strip_loc();
        while let Term::App(f, _, _) = head {
            head = f.strip_loc();
        }
        let Term::Meta(m) = head else {
            return None;
        };
        let (context, text) = self.g.shown.placeholder(*m)?;
        let (_, args) = term.spine();
        let depth = names.len();
        let same = context.len() <= args.len()
            && context.iter().zip(&args).all(|(name, arg)| {
                matches!(arg.strip_loc(), Term::Var(ix) if *ix < depth && names[depth - 1 - ix] == *name)
            });
        if !same {
            return None;
        }
        let context = context.len();
        let text = match text {
            PlaceholderText::Number(k) => k.to_string(),
            PlaceholderText::Source(text) if text.contains(' ') && !bracketed(&text) => {
                format!("({text})")
            }
            PlaceholderText::Source(text) => text.to_string(),
        };
        Some(self.applied(names, text, args.into_iter().skip(context)))
    }

    /// A call of a local definition, by its name (`Shown::print_label`).
    fn label(&self, names: &mut Vec<Name>, term: &Term) -> Option<(String, Prec)> {
        if !self.g.shown.has_print_labels() {
            return None;
        }
        let mut args = Vec::new();
        let mut head = term.strip_loc();
        while let Term::App(f, a, icit) = head {
            args.push((a.as_ref(), *icit));
            head = f.strip_loc();
        }
        args.reverse();
        let (name, levels, defaults) = self.g.shown.print_label(&mut |l| match (&l.head, head) {
            (Term::Meta(a), Term::Meta(b)) => a == b && args.len() >= l.levels.len(),
            (Term::Def(a), Term::Def(b)) => {
                let depth = names.len();
                args.len() >= l.levels.len()
                    && l.levels.iter().zip(&args).all(|(level, (arg, _))| {
                        matches!(arg.strip_loc(), Term::Var(ix) if *ix < depth && depth - 1 - ix == *level)
                    })
                    && a == b
            }
            _ => false,
        })?;
        let name = name.to_string();
        let params = &args[levels..];
        let rest: Vec<&Term> = params
            .iter()
            .filter(|(_, icit)| *icit == Icit::Explicit)
            .map(|(a, _)| *a)
            .collect();
        if !self.show_hidden.get()
            && let Some(defaults) = defaults
            && let Some(shown) = self.defaulted(names, name.clone(), params, &defaults)
        {
            return Some(shown);
        }
        Some(self.applied(names, name, rest.into_iter()))
    }

    /// A call of a definition with parameter defaults, as written
    /// ([`Printer::defaulted`]).
    fn call_with_defaults(&self, names: &mut Vec<Name>, term: &Term) -> Option<(String, Prec)> {
        let (head, args) = full_spine(term);
        let Term::Def(id) = head else {
            return None;
        };
        let def = self.g.def(*id);
        let table = self.g.shown.param_defaults(*id)?;
        let mut ty = def.ty.strip_loc();
        let mut params = Vec::with_capacity(table.header);
        for default in table.params.iter().take(table.header) {
            let Term::Pi(x, _, _, cod) = ty else {
                return None;
            };
            let call = default.as_ref().map(|d| DefaultCall {
                head: Term::Def(d.helper),
                levels: Vec::new(),
                captures: d.captures.clone(),
            });
            params.push((x.clone(), call));
            ty = cod.strip_loc();
        }
        let defaults = CallDefaults {
            header: table.header,
            params,
        };
        let head = self.def_name(names, *id);
        self.defaulted(names, head, &args, &defaults)
    }

    /// `head` applied to `args`, the parameters of a function with
    /// `defaults`, as the call is written: an argument that is exactly its
    /// default's call is left out, and one given to a defaulted parameter
    /// is named, `(step := 2)`. Arguments past the header follow a call
    /// that left a default out in brackets, `(scaler 5) x`. `None` if no
    /// argument is a defaulted parameter's.
    fn defaulted(
        &self,
        names: &mut Vec<Name>,
        head: String,
        args: &[(&Term, Icit)],
        defaults: &CallDefaults,
    ) -> Option<(String, Prec)> {
        let header = defaults.header.min(args.len());
        let defaulted = |p: usize| defaults.params.get(p).and_then(|(_, d)| d.as_ref());
        if !(0..header).any(|p| defaulted(p).is_some()) {
            return None;
        }
        let left_out: Vec<bool> = (0..header)
            .map(|p| defaulted(p).is_some_and(|d| self.is_default_call(names, d, args[p].0, args)))
            .collect();
        let mut text = head;
        let mut any = false;
        for (p, (arg, icit)) in args[..header].iter().enumerate() {
            if *icit != Icit::Explicit || left_out[p] {
                continue;
            }
            text.push(' ');
            if defaulted(p).is_some() {
                let x = &defaults.params[p].0;
                let shown = self.print(names, arg, Prec::Arrow);
                text.push_str(&format!("({x} := {shown})"));
            } else {
                text.push_str(&self.print(names, arg, Prec::Atom));
            }
            any = true;
        }
        let rest: Vec<&Term> = args[header..]
            .iter()
            .filter(|(_, icit)| *icit == Icit::Explicit)
            .map(|(a, _)| *a)
            .collect();
        if rest.is_empty() {
            return Some((text, if any { Prec::App } else { Prec::Atom }));
        }
        // A positional argument after a call that left a default out
        // applies its result only in brackets.
        if left_out.contains(&true) {
            text = format!("({text})");
        }
        Some(self.applied(names, text, rest.into_iter()))
    }

    /// Whether `arg` is exactly `default`'s call, given `args`, the
    /// parameters of the call it's an argument of.
    fn is_default_call(
        &self,
        names: &[Name],
        default: &DefaultCall,
        arg: &Term,
        args: &[(&Term, Icit)],
    ) -> bool {
        let (head, given) = full_spine(arg);
        let same_head = match (&default.head, head) {
            (Term::Def(a), Term::Def(b)) => a == b,
            (Term::Meta(a), Term::Meta(b)) => a == b,
            _ => false,
        };
        if !same_head || given.len() != default.levels.len() + default.captures.len() {
            return false;
        }
        let depth = names.len();
        let (outer, taken) = given.split_at(default.levels.len());
        let outer_alike = default.levels.iter().zip(outer).all(|(level, (arg, _))| {
            matches!(arg.strip_loc(), Term::Var(ix) if *ix < depth && depth - 1 - ix == *level)
        });
        outer_alike
            && default.captures.iter().zip(taken).all(|(&p, (arg, _))| {
                args.get(p)
                    .is_some_and(|(param, _)| crate::value::same_term(param, arg))
            })
    }

    /// A call of a lifted `match`'s helper (`Shown::match_columns`), as the
    /// `match` with its scrutinees and the alternatives left out:
    /// `(match s₁, s₂ with …)`. Not source: the alternatives aren't shown,
    /// and written out they would make a different helper.
    fn lifted_match(&self, names: &mut Vec<Name>, term: &Term) -> Option<String> {
        let (head, args) = term.spine();
        let Term::Def(id) = head else {
            return None;
        };
        // Only a `match` written in source: a definition's own clauses
        // (`Bool.ifThenElse`, `Nat.leq`) record columns too, and print as
        // the call or notation they have.
        if !self.g.def(*id).name().contains(".%match") {
            return None;
        }
        let cols = self.g.shown.match_columns(*id)?;
        if args.len() != self.g.def(*id).arity() || cols.iter().any(|&c| c >= args.len()) {
            return None;
        }
        let scrutinees: Vec<String> = cols
            .iter()
            .map(|&c| self.print(names, args[c], Prec::Arrow))
            .collect();
        let shown = format!("(match {} with …)", scrutinees.join(", "));
        self.g.shown.note_match_shown(*id, &shown);
        Some(shown)
    }

    /// A call of an update's helper (`Shown::update_shown`), as the update:
    /// `{ x | f = s, g = t }`.
    fn update(&self, names: &mut Vec<Name>, term: &Term) -> Option<String> {
        let (head, args) = term.spine();
        let Term::Def(id) = head else {
            return None;
        };
        let shown = self.g.shown.update_shown(*id)?;
        if args.len() != shown.params {
            return None;
        }
        // A term in the helper's parameters, with the call's arguments in
        // place of them.
        let depth = names.len();
        let filled = |template: &Term| -> Option<Term> {
            let mut term = template.shift(self.g, depth, shown.params).ok()?;
            for (inner, arg) in args.iter().enumerate().rev() {
                term = term
                    .instantiate(self.g, &arg.shift(self.g, inner, 0).ok()?)
                    .ok()?;
            }
            Some(term)
        };
        let base = filled(&shown.base)?;
        let mut fields = Vec::new();
        for (field, value) in &shown.fields {
            fields.push((field.to_string(), filled(value)?));
        }
        let base = self.print(names, &base, Prec::Arrow);
        let fields: Vec<String> = fields
            .iter()
            .map(|(field, value)| format!("{field} = {}", self.print(names, value, Prec::Arrow)))
            .collect();
        Some(format!("{{ {base} | {} }}", fields.join(", ")))
    }

    /// A value of record `d` whose fields `args` are, except some, those
    /// fields of one record `x`, as the update that makes it:
    /// `{ x | f = s }`. An update of a record elaborates to exactly this, and
    /// a literal written so can't be told from it once evaluated. The `x`
    /// most fields are taken from is the one shown; `None` unless at least
    /// one field is taken from it and at least one isn't.
    fn record_update(&self, names: &mut Vec<Name>, d: DataId, args: &[Rc<Term>]) -> Option<String> {
        let fields = &self.g.data(d).ctors[0].fields;
        if fields.len() != args.len() {
            return None;
        }
        // For each field, the record it's taken from, if it's `x.f` for its
        // own `f`, printed to compare.
        let taken_from: Vec<Option<String>> = fields
            .iter()
            .zip(args)
            .map(|((field, _), arg)| {
                let (head, explicit) = explicit_spine(arg);
                let Term::Def(id) = head else {
                    return None;
                };
                let [record] = &explicit[..] else {
                    return None;
                };
                (self.projection_of(*id) == Some((d, field.to_string())))
                    .then(|| self.print(names, record, Prec::Arrow))
            })
            .collect();
        let base = taken_from
            .iter()
            .flatten()
            .max_by_key(|candidate| {
                taken_from
                    .iter()
                    .filter(|other| other.as_ref() == Some(*candidate))
                    .count()
            })?
            .clone();
        let replaced: Vec<String> = fields
            .iter()
            .zip(args)
            .zip(&taken_from)
            .filter(|(_, from)| from.as_ref() != Some(&base))
            .map(|(((field, _), arg), _)| {
                format!("{field} = {}", self.print(names, arg, Prec::Arrow))
            })
            .collect();
        if replaced.is_empty() {
            return None;
        }
        Some(format!("{{ {base} | {} }}", replaced.join(", ")))
    }

    /// The record type and field of a projection `R.f`, if `id` is one of a
    /// record's.
    fn projection_of(&self, id: DefId) -> Option<(DataId, String)> {
        let field = self.projection_field(id)?;
        let mut ty = self.g.def(id).ty.strip_loc();
        while let Term::Pi(_, Icit::Implicit, _, b) = ty {
            ty = b.strip_loc();
        }
        match ty {
            Term::Pi(_, Icit::Explicit, dom, _) => match dom.strip_loc() {
                Term::Data(d, _) if self.g.data(*d).record => Some((*d, field)),
                _ => None,
            },
            _ => None,
        }
    }

    /// The field name of a projection `R.f`, if `id` is one: a record's
    /// generated projection, a data type's generated accessor for a shared
    /// field (docs/proposals/variant-fields.md §9.3), such as the prelude's
    /// `Pair.fst` or `Pair.snd`.
    fn projection_field(&self, id: DefId) -> Option<String> {
        match self.g.env.registry().def_builtin(id) {
            Some(Builtin::Fst) => return Some("fst".into()),
            Some(Builtin::Snd) => return Some("snd".into()),
            _ => {}
        }
        let def = self.g.def(id);
        let name = def.name.to_string();
        let (owner, field) = name.rsplit_once('.')?;
        // An accessor is declared at its type's declaration.
        let (ix, data) = self
            .g
            .env
            .datas()
            .iter()
            .enumerate()
            .find(|(_, d)| &*d.name == owner && (d.record || d.span == def.span))?;
        let is_field = !data.ctors.is_empty()
            && data
                .ctors
                .iter()
                .all(|c| c.fields.iter().any(|(f, _)| &**f == field));
        if !is_field {
            return None;
        }
        // A projection takes the record as its only explicit argument.
        let mut ty = self.g.def(id).ty.strip_loc();
        while let Term::Pi(_, Icit::Implicit, _, b) = ty {
            ty = b.strip_loc();
        }
        let takes_record = matches!(
            ty,
            Term::Pi(_, Icit::Explicit, dom, _)
                if matches!(dom.strip_loc(), Term::Data(d, _) if *d == DataId(ix))
        );
        takes_record.then(|| field.to_string())
    }

    /// `if p then a else b`, or `if h: p then a else b` where a branch uses
    /// the proof, for `Decidable.elim [p] [r] d (h => a) (h => b)` and for
    /// the call of its helper it computes to (`Decidable.elim.%match1 p r d
    /// (h => a) (h => b) t e`), whose test the decision `d` holds.
    fn decided_if(&self, names: &mut Vec<Name>, term: &Term, id: DefId) -> Option<(String, Prec)> {
        let reg = self.g.env.registry();
        let elim = reg.def(Builtin::ElimDec)?;
        let (_, args) = full_spine(term);
        let whole = (id == elim && args.len() == 5)
            || (args.len() == 7 && Some(id) == elim_helper(self.g, elim));
        if !whole {
            return None;
        }
        let (prop, then, otherwise) = (args[0].0, args[3].0, args[4].0);
        let (Term::Lam(x, _, yes), Term::Lam(y, _, no)) = (then.strip_loc(), otherwise.strip_loc())
        else {
            return None;
        };
        let used = yes.mentions(0) || no.mentions(0);
        let name = if yes.mentions(0) || !no.mentions(0) {
            x
        } else {
            y
        };
        let mut branch = |body: &Term| {
            names.push(name.clone());
            let text = if matches!(body.strip_loc(), Term::Lam(..)) {
                self.print(names, body, Prec::Or)
            } else {
                self.print(names, body, Prec::Arrow)
            };
            names.pop();
            text
        };
        let (yes, no) = (branch(yes), branch(no));
        let prop = self.print(names, prop, Prec::Arrow);
        let binder = if used {
            format!("{name}: ")
        } else {
            String::new()
        };
        Some((
            format!("if {binder}{prop} then {yes} else {no}"),
            Prec::Arrow,
        ))
    }

    /// The body of `t`, if it's a lambda whose body doesn't use its parameter:
    /// one of the branches of `if c then a else b`.
    fn unused_branch(&self, names: &mut Vec<Name>, t: &Term) -> Option<String> {
        let Term::Lam(x, _, body) = t.strip_loc() else {
            return None;
        };
        if body.mentions(0) {
            return None;
        }
        names.push(x.clone());
        // A lambda as a branch keeps its brackets, so that it visibly ends
        // before `else`.
        let text = if matches!(body.strip_loc(), Term::Lam(..)) {
            self.print(names, body, Prec::Or)
        } else {
            self.print(names, body, Prec::Arrow)
        };
        names.pop();
        Some(text)
    }

    fn tuple(&self, names: &mut Vec<Name>, items: &[&Term]) -> String {
        let items: Vec<String> = items
            .iter()
            .map(|t| self.print(names, t, Prec::Arrow))
            .collect();
        format!("({})", items.join(", "))
    }

    /// A saturated call of `Ns.f` whose first explicit parameter has the
    /// type `Ns`, as the dot call that elaborates to it: `coupon.apply
    /// total`. Not for a partial call (`Coupon.apply coupon` stays a call,
    /// as the dot form would read as a different function), nor in ASCII
    /// text, nor when the receiver can't be written before a dot (an
    /// anonymous `x✝`, a number, an elided part, or a bare global name,
    /// which would read as a path).
    fn dot_call(&self, names: &mut Vec<Name>, id: DefId, args: &[&Term]) -> Dot {
        if self.ascii.get() || self.calls.get() {
            return Dot::No;
        }
        let def = self.g.def(id);
        let Some((namespace, last)) = def.path.rsplit_once('.') else {
            return Dot::No;
        };
        if !last.starts_with(|c: char| c.is_alphabetic() || c == '_')
            || !last
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
        {
            return Dot::No;
        }
        let mut parameters = 0;
        let mut first = None;
        let mut ty = def.ty.strip_loc();
        while let Term::Pi(_, icit, domain, codomain) = ty {
            if *icit == Icit::Explicit {
                parameters += 1;
                first.get_or_insert(domain.strip_loc());
            }
            ty = codomain.strip_loc();
        }
        let Some(Term::Data(d, _)) = first else {
            return Dot::No;
        };
        if args.len() < parameters || &*self.g.data(*d).path != namespace {
            return Dot::No;
        }
        let Some((receiver, rest)) = args.split_first() else {
            return Dot::No;
        };
        let text = self.print(names, receiver, Prec::Atom);
        // A number reads better as an argument, `Nat.pow 10 k`, than as
        // `(10).pow k`; an elided receiver is no receiver to read.
        if text.contains('✝') || text == "…" || text.starts_with(|c: char| c.is_ascii_digit()) {
            return Dot::Declined(text);
        }
        // `Tip.size` and `Main.shopping.total` read as name paths, and
        // `(Tip).size` looks odd, so a bare global stays a plain call.
        if matches!(
            receiver.strip_loc(),
            Term::Def(_) | Term::Data(..) | Term::Ctor(..)
        ) && !text.contains([' ', '(', '[', '{'])
        {
            return Dot::Declined(text);
        }
        Dot::Call(self.applied(names, format!("{text}.{last}"), rest.iter().copied()))
    }

    /// An application with every argument, those the compiler fills in
    /// (implicit and `auto`) in brackets.
    fn applied_with_hidden(&self, names: &mut Vec<Name>, term: &Term) -> (String, Prec) {
        let mut args = Vec::new();
        let mut head = term.strip_loc();
        while let Term::App(f, a, icit) = head {
            args.push((a.as_ref(), *icit));
            head = f.strip_loc();
        }
        args.reverse();
        let mut text = self.print(names, head, Prec::App);
        for (arg, icit) in args {
            text.push(' ');
            if icit == Icit::Explicit {
                text.push_str(&self.print(names, arg, Prec::Atom));
            } else {
                text.push('[');
                text.push_str(&self.print(names, arg, Prec::Arrow));
                text.push(']');
            }
        }
        (text, Prec::App)
    }

    fn applied<'t>(
        &self,
        names: &mut Vec<Name>,
        head: String,
        args: impl Iterator<Item = &'t Term>,
    ) -> (String, Prec) {
        let mut text = head;
        let mut any = false;
        for arg in args {
            text.push(' ');
            text.push_str(&self.print(names, arg, Prec::Atom));
            any = true;
        }
        (text, if any { Prec::App } else { Prec::Atom })
    }
}

/// Whether `text` is one bracketed whole, `{ … }`, `( … )` or `[ … ]`: its
/// first bracket closes at its end.
fn bracketed(text: &str) -> bool {
    if !text.starts_with(['{', '(', '[']) {
        return false;
    }
    let mut depth = 0usize;
    for (i, c) in text.char_indices() {
        match c {
            '{' | '(' | '[' => depth += 1,
            '}' | ')' | ']' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return i + c.len_utf8() == text.len();
                }
            }
            _ => {}
        }
    }
    false
}

/// Whether `x` names a `let` a record update binds: its record (`%record`,
/// `%base`) or a field's new value (`%new%f`).
fn is_update_let(x: &str) -> bool {
    x == "%record" || x == "%base" || x.starts_with("%new%")
}

/// The hidden parameter of an operator section, `(== id)`.
const SECTION: &str = "%section";

/// The hidden parameters of a bare operator, `(&&)`.
const LEFT: &str = "%left";
const RIGHT: &str = "%right";

/// A variable `x` as shown: a name the compiler made (starting with `%`)
/// gets a readable one that `names` doesn't use, from the letters after its
/// `%` (`%cond` is `cond`), or `x` if there are none (`%3`). A section's
/// hidden parameters are `x` and `y`.
fn readable(x: &Name, names: &[Name]) -> Name {
    let Some(rest) = x.strip_prefix('%') else {
        return x.clone();
    };
    let letters = &rest[..rest
        .find(|c: char| !c.is_ascii_alphabetic())
        .unwrap_or(rest.len())];
    let base = match &**x {
        SECTION | LEFT => "x",
        RIGHT => "y",
        _ if letters.starts_with(|c: char| c.is_ascii_lowercase()) => letters,
        _ => "x",
    };
    (0..)
        .map(|k| {
            if k == 0 {
                base.to_string()
            } else {
                format!("{base}{k}")
            }
        })
        .find(|candidate| !names.iter().any(|n| **n == **candidate))
        .expect("some name is free")
        .into()
}

/// A binder `x` over `body` as shown, where `names` are the variables in
/// scope: [`readable`], numbered (`y1`) if that name is one of `names` that
/// `body` mentions, which the binder would otherwise capture: `y => y = x`
/// with `x` called `y` is shown `y1 => y1 = y`, not `y => y = y`.
fn binder(x: &Name, names: &[Name], body: &Term) -> Name {
    let x = readable(x, names);
    // Whether `body`, under the binder, mentions a variable of `names`
    // called `candidate`.
    let captures = |candidate: &str| {
        names.iter().any(|n| **n == *candidate)
            && (names.iter().rev().enumerate())
                .any(|(j, n)| **n == *candidate && body.mentions(j + 1))
    };
    if !captures(&x) {
        return x;
    }
    let base = x.trim_end_matches(|c: char| c.is_ascii_digit());
    let base = if base.is_empty() { "x" } else { base };
    (1..)
        .map(|k| format!("{base}{k}"))
        .find(|candidate| !names.iter().any(|n| **n == **candidate))
        .expect("some name is free")
        .into()
}

/// Two corresponding calls around the place being compared, with the names
/// in scope there.
#[derive(Clone)]
struct CallPair {
    left: Term,
    right: Term,
    names: Vec<Name>,
    /// Whether these are the whole terms compared, under their binders.
    outermost: bool,
}

/// Where [`first_mismatch`] is: the names in scope, the calls around it
/// (outermost first), and how many layers in it is, not counting binders.
struct Path {
    names: Vec<Name>,
    calls: Vec<CallPair>,
    depth: usize,
}

impl Path {
    fn new(names: &[Name]) -> Path {
        Path {
            names: names.to_vec(),
            calls: Vec::new(),
            depth: 0,
        }
    }
}

/// Two corresponding parts that differ at their outermost layer.
struct Mismatch {
    left: Term,
    right: Term,
    names: Vec<Name>,
    calls: Vec<CallPair>,
    /// Whether these are the whole terms compared, under their binders.
    outermost: bool,
}

/// Too deeply nested to compare with the stack left.
struct TooDeep;

type Compared = std::result::Result<Option<Mismatch>, TooDeep>;

/// `term` without the source locations and type annotations around it.
fn bare(term: &Term) -> &Term {
    let mut term = term;
    while let Term::Loc(_, t) | Term::Ann(t, _) = term {
        term = t;
    }
    term
}

/// Whether `a` and `b` are the same `Nat.leq` comparison except that one
/// compares the successor of the other's left operand: `x < y` against
/// `x <= y`, whose terms are `Nat.leq (Succ x) y` and `Nat.leq x y`. The
/// printed comparisons hide the `Succ`, so a difference inside it would
/// point at a subterm the reader can't see; the caller reports the whole
/// comparisons instead. A small left operand reads well either way, so it
/// keeps the existing operation around it.
fn leq_succ_pair(g: &Ev, a: &Term, b: &Term) -> bool {
    let (ah, aa) = explicit_spine(a);
    let (bh, ba) = explicit_spine(b);
    let (Term::Def(x), Term::Def(y)) = (ah, bh) else {
        return false;
    };
    let registry = &g.env.registry();
    if !(registry.is_def(Builtin::Leq, *x) && registry.is_def(Builtin::Leq, *y)) {
        return false;
    }
    let ([al, ar], [bl, br]) = (&aa[..], &ba[..]) else {
        return false;
    };
    if !same_term(ar, br) {
        return false;
    }
    let succ_of = |succ: &Term, plain: &Term| match bare(succ) {
        Term::Ctor(d, 1, fields)
            if is(g, Builtin::Nat, *d) && fields.len() == 1 && !is_small(plain) =>
        {
            same_term(&fields[0], plain)
        }
        _ => false,
    };
    succ_of(al, bl) || succ_of(bl, al)
}

/// The first place, in printing order, where `a` and `b` differ; with
/// `explicit_only`, implicit and `auto` arguments aren't compared. A number
/// and the `Succ` it stands for are alike.
fn first_mismatch(
    g: &Ev,
    a: &Term,
    b: &Term,
    explicit_only: bool,
    skip_proofs: bool,
    path: &mut Path,
) -> Compared {
    path.depth += 1;
    let found = mismatch_within(g, a, b, explicit_only, skip_proofs, path);
    path.depth -= 1;
    found
}

/// [`first_mismatch`], one layer in.
fn mismatch_within(
    g: &Ev,
    a: &Term,
    b: &Term,
    explicit_only: bool,
    skip_proofs: bool,
    path: &mut Path,
) -> Compared {
    if g.machine.budget.stack_exhausted() {
        return Err(TooDeep);
    }
    let (a, b) = (bare(a), bare(b));
    let here = |path: &Path| {
        Ok(Some(Mismatch {
            left: a.clone(),
            right: b.clone(),
            names: path.names.clone(),
            calls: path.calls.clone(),
            outermost: path.depth == 1,
        }))
    };
    // Each pair in turn, stopping at the first that differs.
    let pairs = |path: &mut Path, pairs: &mut dyn Iterator<Item = (&Term, &Term)>| -> Compared {
        for (x, y) in pairs {
            if let Some(found) = first_mismatch(g, x, y, explicit_only, skip_proofs, path)? {
                return Ok(Some(found));
            }
        }
        Ok(None)
    };
    // A body under binders, at the same layer: `x => f x` against `x => g x`
    // differ at their outermost layer, which any printing shows.
    let under = |path: &mut Path, binders: &[Name], x: &Term, y: &Term| -> Compared {
        path.names.extend(binders.iter().cloned());
        path.depth -= 1;
        let found = first_mismatch(g, x, y, explicit_only, skip_proofs, path);
        path.depth += 1;
        path.names.truncate(path.names.len() - binders.len());
        found
    };
    let same = match (a, b) {
        (Term::Var(i), Term::Var(j)) => i == j,
        (Term::Def(x), Term::Def(y)) => x == y,
        (Term::Sort(s), Term::Sort(t)) => s == t,
        (Term::Meta(m), Term::Meta(n)) => m == n,
        (Term::Nat(m), Term::Nat(n)) => m == n,
        (Term::Chars(x), Term::Chars(y)) => x.as_slice() == y.as_slice(),
        (Term::Refl, Term::Refl) => true,
        (Term::Nat(n), Term::Ctor(d, c, fields)) | (Term::Ctor(d, c, fields), Term::Nat(n)) => {
            let ctor = Some((*d, *c));
            let registry = &g.env.registry();
            if n.bits() == 0 {
                ctor == registry.loaded_ctor(Builtin::Zero)
            } else if ctor == registry.loaded_ctor(Builtin::Succ)
                && let [field] = &fields[..]
            {
                let pred = Term::Nat(Rc::new(n.as_ref() - 1u32));
                return if matches!(a, Term::Nat(_)) {
                    first_mismatch(g, &pred, field, explicit_only, skip_proofs, path)
                } else {
                    first_mismatch(g, field, &pred, explicit_only, skip_proofs, path)
                };
            } else {
                false
            }
        }
        (Term::Data(d, xs), Term::Data(e, ys)) if d == e && xs.len() == ys.len() => {
            let args = xs.iter().zip(ys).enumerate();
            return pairs(
                path,
                &mut args.filter_map(|(k, (x, y))| {
                    (!skip_proofs || !proof_param(g, *d, k)).then_some((&**x, &**y))
                }),
            );
        }
        (Term::Ctor(d, c, xs), Term::Ctor(e, k, ys))
            if d == e && c == k && xs.len() == ys.len() =>
        {
            let fields = xs.iter().zip(ys).enumerate();
            return pairs(
                path,
                &mut fields.filter_map(|(i, (x, y))| {
                    (!skip_proofs || !proof_field(g, *d, *c, i)).then_some((&**x, &**y))
                }),
            );
        }
        (Term::App(..), Term::App(..)) => {
            // `<` against `<=` differs in a `Succ` the printed comparison
            // hides: report the whole comparisons, not that subterm.
            if leq_succ_pair(g, a, b) {
                return here(path);
            }
            let ((f, xs), (h, ys)) = (full_spine(a), full_spine(b));
            let shape = xs.len() == ys.len() && xs.iter().zip(&ys).all(|(x, y)| x.1 == y.1);
            if !shape || first_mismatch(g, f, h, explicit_only, skip_proofs, path)?.is_some() {
                return here(path);
            }
            let head = match f.strip_loc() {
                Term::Def(id) => Some(*id),
                _ => None,
            };
            path.calls.push(CallPair {
                left: a.clone(),
                right: b.clone(),
                names: path.names.clone(),
                outermost: path.depth == 1,
            });
            let found = pairs(
                path,
                &mut xs
                    .iter()
                    .zip(&ys)
                    .enumerate()
                    .filter(|(i, (x, _))| {
                        !(explicit_only && x.1.is_implicit())
                            && !(skip_proofs && head.is_some_and(|id| g.env.def(id).is_inert(*i)))
                    })
                    .map(|(_, (x, y))| (x.0, y.0)),
            );
            path.calls.pop();
            return found;
        }
        (Term::Lam(x, i, body), Term::Lam(_, j, other)) if i == j => {
            return under(path, std::slice::from_ref(x), body, other);
        }
        (Term::Pi(x, i, s, t), Term::Pi(_, j, u, v)) if i == j => {
            if let Some(found) = first_mismatch(g, s, u, explicit_only, skip_proofs, path)? {
                return Ok(Some(found));
            }
            return under(path, std::slice::from_ref(x), t, v);
        }
        (Term::Let(x, _, v, body, _), Term::Let(_, _, w, other, _)) => {
            if let Some(found) = first_mismatch(g, v, w, explicit_only, skip_proofs, path)? {
                return Ok(Some(found));
            }
            return under(path, std::slice::from_ref(x), body, other);
        }
        (Term::Eq(_, x, y), Term::Eq(_, u, v)) => {
            return pairs(path, &mut [(&**x, &**u), (&**y, &**v)].into_iter());
        }
        (Term::J(m, x, p), Term::J(n, y, q)) => {
            return pairs(
                path,
                &mut [(&**m, &**n), (&**x, &**y), (&**p, &**q)].into_iter(),
            );
        }
        (Term::Proj(d1, i1, x), Term::Proj(d2, i2, y)) if d1 == d2 && i1 == i2 => {
            return pairs(path, &mut [(&**x, &**y)].into_iter());
        }
        (Term::Quot(f, xs, _), Term::Quot(h, ys, _)) if f == h && xs.len() == ys.len() => {
            let skip = if explicit_only { f.implicit() } else { 0 };
            return pairs(
                path,
                &mut xs.iter().zip(ys).skip(skip).map(|(x, y)| (&**x, &**y)),
            );
        }
        (Term::Case(ix, d, xs), Term::Case(iy, e, ys))
            if ix == iy && d == e && xs.len() == ys.len() =>
        {
            for (x, y) in xs.iter().zip(ys.iter()) {
                match (&x.body, &y.body) {
                    (None, None) => {}
                    (Some(s), Some(t)) if x.names.len() == y.names.len() => {
                        if let Some(found) = under(path, &x.names, s, t)? {
                            return Ok(Some(found));
                        }
                    }
                    _ => return here(path),
                }
            }
            true
        }
        (Term::NumCase(ix, xs, s), Term::NumCase(iy, ys, t))
            if ix == iy
                && xs.len() == ys.len()
                && xs.iter().zip(ys.iter()).all(|(x, y)| x.value == y.value) =>
        {
            let arms = xs.iter().zip(ys.iter()).map(|(x, y)| (&*x.body, &*y.body));
            return pairs(path, &mut arms.chain([(&**s, &**t)]));
        }
        _ => false,
    };
    if same { Ok(None) } else { here(path) }
}

/// A variable, a definition's name, or a few constructors around those, such
/// as `2` or `True`.
fn is_small(term: &Term) -> bool {
    fn within(term: &Term, layers: usize) -> bool {
        match bare(term) {
            Term::Ctor(_, _, fields) => layers > 0 && fields.iter().all(|f| within(f, layers - 1)),
            term => is_atomic(term),
        }
    }
    within(term, 4)
}

fn is_atomic(term: &Term) -> bool {
    matches!(
        term,
        Term::Var(_) | Term::Def(_) | Term::Sort(_) | Term::Refl | Term::Nat(_)
    )
}

/// A lambda's parameter `x` as written: `x`, `[x: _]` or `[auto x: _]`.
fn lambda_param(x: &Name, icit: Icit) -> String {
    match icit {
        Icit::Explicit => x.to_string(),
        Icit::Implicit => format!("[{x}: _]"),
        Icit::Auto => format!("[auto {x}: _]"),
    }
}

/// Whether a call has an implicit or auto argument.
fn has_hidden_argument(term: &Term) -> bool {
    let mut head = term.strip_loc();
    while let Term::App(f, _, icit) = head {
        if *icit != Icit::Explicit {
            return true;
        }
        head = f.strip_loc();
    }
    false
}

/// A call's head and all its arguments, each with how it's applied.
fn full_spine(term: &Term) -> (&Term, Vec<(&Term, Icit)>) {
    let mut args = Vec::new();
    let mut head = term.strip_loc();
    while let Term::App(f, a, icit) = head {
        args.push((a.as_ref(), *icit));
        head = f.strip_loc();
    }
    args.reverse();
    (head, args)
}

/// The helper `Decidable.elim` (`elim`) computes to: the head of its body.
fn elim_helper(g: &Ev, elim: DefId) -> Option<DefId> {
    let mut body = g.def(elim).body()?.strip_loc();
    while let Term::Lam(_, _, b) = body {
        body = b.strip_loc();
    }
    let mut head = body;
    while let Term::App(f, _, _) = head {
        head = f.strip_loc();
    }
    match head {
        Term::Def(id) => Some(*id),
        _ => None,
    }
}

fn explicit_spine(term: &Term) -> (&Term, Vec<&Term>) {
    let mut args = Vec::new();
    let mut head = term.strip_loc();
    while let Term::App(f, a, icit) = head {
        if *icit == Icit::Explicit {
            args.push(a.as_ref());
        }
        head = f.strip_loc();
    }
    args.reverse();
    (head, args)
}

/// Whether `d` is the prelude's `b`, which the printer shows specially. By
/// identity, so a user's own `List` prints as written.
fn is(g: &Ev, b: Builtin, d: DataId) -> bool {
    g.env.registry().is_data(b, d)
}

/// Whether `d` is the library built-in `b`, if its file is loaded.
fn is_loaded(g: &Ev, b: Builtin, d: DataId) -> bool {
    g.env.registry().loaded_data(b) == Some(d)
}

/// Whether two bases of [`Printer::nat_parts`] are the same: both absent (the
/// numbers are literals), or the same term.
fn same_base(a: Option<&Term>, b: Option<&Term>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => same_term(a, b),
        _ => false,
    }
}

/// `Succ (Succ Zero)` as `2`.
fn nat_literal(g: &Ev, term: &Term) -> Option<BigUint> {
    let mut n = 0u64;
    let mut term = term.strip_loc();
    loop {
        match term {
            Term::Nat(k) => return Some(&**k + n),
            Term::Ctor(d, 0, _) if is(g, Builtin::Nat, *d) => return Some(n.into()),
            Term::Ctor(d, 1, args) if is(g, Builtin::Nat, *d) && args.len() == 1 => {
                n += 1;
                term = args[0].strip_loc();
            }
            _ => return None,
        }
    }
}

/// `OfNat 5` as `5` and `NegSucc 4` as `-5`: whether it's negative, and the
/// magnitude.
fn int_literal(g: &Ev, term: &Term) -> Option<(bool, BigUint)> {
    match term.strip_loc() {
        Term::Ctor(d, c, args) if is(g, Builtin::Int, *d) && args.len() == 1 => {
            let n = nat_literal(g, &args[0])?;
            match c {
                0 => Some((false, n)),
                _ => Some((true, n + 1u32)),
            }
        }
        _ => None,
    }
}

/// `MkChar 97 _` as `'a'`.
fn char_literal(g: &Ev, term: &Term) -> Option<char> {
    match term.strip_loc() {
        Term::Ctor(d, 0, args) if is(g, Builtin::Char, *d) && args.len() == 2 => {
            let code = u32::try_from(nat_literal(g, &args[0])?).ok()?;
            char::from_u32(code)
        }
        _ => None,
    }
}

/// `MkText ['h', 'i']` as `"hi"`.
fn text_literal(g: &Ev, term: &Term) -> Option<Vec<char>> {
    match term.strip_loc() {
        Term::Ctor(d, 0, args) if is(g, Builtin::Text, *d) && args.len() == 1 => {
            char_list(g, &args[0])
        }
        _ => None,
    }
}

/// A list of character literals, as cons cells, ending in `Nil` or in a
/// compact list (whose characters are literals).
fn char_list(g: &Ev, term: &Term) -> Option<Vec<char>> {
    let mut chars = Vec::new();
    let mut term = term.strip_loc();
    loop {
        match term {
            Term::Chars(rest) => {
                chars.extend_from_slice(rest.as_slice());
                return Some(chars);
            }
            Term::Ctor(d, 0, _) if is(g, Builtin::List, *d) => return Some(chars),
            Term::Ctor(d, 1, args) if is(g, Builtin::List, *d) && args.len() == 2 => {
                chars.push(char_literal(g, &args[0])?);
                term = args[1].strip_loc();
            }
            _ => return None,
        }
    }
}

/// `['h', 'i']`.
fn show_chars(chars: &[char]) -> String {
    let items: Vec<String> = chars
        .iter()
        .map(|c| format!("'{}'", escape(&[*c], '\'')))
        .collect();
    format!("[{}]", items.join(", "))
}

/// Characters as they'd be written in a literal quoted by `quote`. Control
/// and other invisible characters are written as `\u{…}` escapes, so that
/// `"e\u{301}"` isn't shown as if it were `"é"`.
fn escape(chars: &[char], quote: char) -> String {
    let mut out = String::new();
    for &c in chars {
        match c {
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '\r' => out.push_str("\\r"),
            '\\' => out.push_str("\\\\"),
            c if c == quote => {
                out.push('\\');
                out.push(c);
            }
            c if c.is_ascii_graphic() || c == ' ' => out.push(c),
            c if c.is_alphanumeric() => out.push(c),
            c => out.push_str(&format!("\\u{{{:X}}}", u32::from(c))),
        }
    }
    out
}

/// `Cons a (Cons b Nil)` as `[a, b]`.
fn list_literal<'t>(g: &Ev, term: &'t Term) -> Option<Vec<&'t Term>> {
    let mut items = Vec::new();
    let mut term = term.strip_loc();
    loop {
        match term {
            Term::Ctor(d, 0, _) if is(g, Builtin::List, *d) => return Some(items),
            Term::Ctor(d, 1, args) if is(g, Builtin::List, *d) && args.len() == 2 => {
                items.push(&args[0]);
                term = args[1].strip_loc();
            }
            _ => return None,
        }
    }
}

/// `Cons a (Cons b xs)` as the items `a`, `b` and the tail `xs`, where the
/// chain ends in something other than `Nil`.
fn open_list<'t>(g: &Ev, term: &'t Term) -> Option<(Vec<&'t Term>, &'t Term)> {
    let mut items = Vec::new();
    let mut term = term.strip_loc();
    loop {
        match term {
            Term::Ctor(d, 1, args) if is(g, Builtin::List, *d) && args.len() == 2 => {
                items.push(&*args[0]);
                term = args[1].strip_loc();
            }
            _ if items.is_empty() => return None,
            Term::Ctor(d, 0, _) if is(g, Builtin::List, *d) => return None,
            _ => return Some((items, term)),
        }
    }
}

/// Records on `g` that a message showed a term that uses a definition that
/// failed: whatever went wrong then is fallout of that failure (see
/// `Shown::note_failed_mentioned`). Or, failing that, one that is stuck on
/// an open goal's assumption once computed (`Shown::note_stuck_on_goal`):
/// not one that merely calls a definition relying on a goal, which may
/// use the goal only in a proof and compute normally. Looks at the whole
/// term, whatever the message elides; `level` is how many variables it is
/// under.
fn note_failed_mention(g: &Ev, level: usize, term: &Term) {
    if !g.shown.wants_failed_mention() || g.machine.budget.stack_exhausted() {
        return;
    }
    let mut waits = false;
    if let Some(def) = mentions_failed(g, term, &mut waits) {
        g.shown.note_failed_mentioned(def);
    } else if waits && g.shown.wants_stuck_mention() {
        let goals = stuck_on_goal(g, level, term);
        if !goals.is_empty() {
            g.shown.note_stuck_on_goal(&goals);
        }
    }
}

/// The first failed definition `term` uses, if any; `waits` is set if it
/// uses one that may be stuck on an open goal (`Shown::waits_on_goal`).
fn mentions_failed(g: &Ev, term: &Term, waits: &mut bool) -> Option<DefId> {
    // Iteratively: a shown term can be nested far deeper than the stack.
    term.subterms().find_map(|(t, _)| match t {
        Term::Def(d) if g.def(*d).state() == crate::globals::State::Failed => Some(*d),
        Term::Def(d) => {
            *waits = *waits || g.shown.waits_on_goal(*d);
            None
        }
        _ => None,
    })
}

/// The open goals' assumptions `term`, under `level` variables, computed to
/// its normal form, mentions. None if that is too large to read back or
/// can't be computed: the message is then taken at its word.
fn stuck_on_goal(g: &Ev, level: usize, term: &Term) -> Vec<DefId> {
    const CAP: u64 = 10_000;
    // A part a depth-limited readback left out (`ELIDED`) is no
    // metavariable the session has, so can't be computed.
    let in_scope = term.subterms().all(|(t, binders)| match t {
        Term::Var(i) | Term::Case(i, ..) | Term::NumCase(i, ..) => *i < binders + level,
        Term::Meta(m) => *m != crate::value::ELIDED,
        _ => true,
    });
    if !in_scope {
        return Vec::new();
    }
    // On the side, within a small budget of its own: a message mustn't
    // compute deeply (`countDown 100000 []`), nor change how the check it
    // reports on ran out.
    let limits = crate::budget::Limits {
        work: 100_000,
        size: CAP,
        frames: 10_000,
        ..crate::budget::Limits::default()
    };
    g.machine.budget.aside(limits, || {
        let env: Vec<Value> = (0..level).map(Value::var).collect();
        let Ok(value) = crate::value::eval(g, &env, term) else {
            return Vec::new();
        };
        let Ok(Some(normal)) = crate::value::quote_unfolded_shown_at_most(g, level, &value, CAP)
        else {
            return Vec::new();
        };
        let mut found: Vec<DefId> = Vec::new();
        for (t, _) in normal.subterms() {
            if let Term::Def(d) = t
                && g.def(*d).assumption().is_some()
                && !found.contains(d)
            {
                found.push(*d);
            }
        }
        found
    })
}
