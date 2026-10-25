//! Printing core terms in surface-like syntax, for error messages and the REPL.
//!
//! The printer recurses over the term. Within an operation, a part nested
//! too deeply to reach with the stack the operation may use is shown as `…`
//! (docs/proposals/stack-safe-evaluation.md).

use std::cell::Cell;

use num_bigint::BigUint;

use crate::budget::Result;
use crate::globals::Globals;
use crate::registry::Builtin;
use crate::term::{DataId, DefId, Icit, Name, Sort, Term};
use crate::value::{Value, quote, quote_folded};

/// Prints `term`, whose free variables are named by `names` (outermost first).
pub fn term(g: &Globals, names: &[Name], term: &Term) -> String {
    let mut names = names.to_vec();
    Printer::new(g).print(&mut names, term, Prec::Arrow)
}

/// Prints `term` with ASCII operators (`&&`, `!=`, `->`), for text inside
/// exported JavaScript, where the reader writes `!=` and not `≠` (D1223).
pub fn term_ascii(g: &Globals, names: &[Name], term: &Term) -> String {
    let mut names = names.to_vec();
    let printer = Printer::new(g);
    printer.ascii.set(true);
    printer.print(&mut names, term, Prec::Arrow)
}

/// [`term_ascii`] for a value.
pub fn value_ascii(g: &Globals, names: &[Name], value: &Value) -> String {
    match quote(g, names.len(), value) {
        Ok(t) => term_ascii(g, names, &t),
        Err(_) => "…".into(),
    }
}

/// Prints all of `term`, or fails if part of it is nested too deeply to
/// print: for showing a result, where `…` would hide part of it.
pub fn term_in_full(g: &Globals, names: &[Name], term: &Term) -> Result<String> {
    let mut names = names.to_vec();
    let printer = Printer::new(g);
    let text = printer.print(&mut names, term, Prec::Arrow);
    if printer.elided.get() {
        return Err(g.budget.too_deep(PASS));
    }
    Ok(text)
}

/// The name the printer's depth guard reports.
const PASS: &str = "printer";

/// Prints `value`, whose free variables are named by `names` (outermost first).
/// If the value can't be quoted within the resource limits, it's shown as `…`.
pub fn value(g: &Globals, names: &[Name], value: &Value) -> String {
    match quote(g, names.len(), value) {
        Ok(t) => term(g, names, &t),
        Err(_) => "…".into(),
    }
}

/// The longest a term may be in a message before its inner parts are
/// shown as `…`.
const MESSAGE_LIMIT: usize = 240;

/// Prints `value` for an error message: like [`value`], but a result longer
/// than [`MESSAGE_LIMIT`] characters has its inner parts replaced by `…`,
/// keeping the outermost layers. Calls are shown as written
/// (`List.length xs`), not as what they compute to ([`quote_folded`];
/// docs/proposals/folded-calls.md, stage 3). Setting
/// `STITCHWORT_FULL_TERMS` shows everything.
pub fn value_for_message(g: &Globals, names: &[Name], value: &Value) -> String {
    let Ok(t) = quote_folded(g, names.len(), value) else {
        return "…".into();
    };
    term_for_message(g, names, &t)
}

/// [`value_for_message`], showing the arguments the compiler fills in, for
/// two types that print the same without them.
pub fn value_for_message_hidden(g: &Globals, names: &[Name], value: &Value) -> String {
    let Ok(t) = quote_folded(g, names.len(), value) else {
        return "…".into();
    };
    let mut ns = names.to_vec();
    let printer = Printer::new(g);
    printer.show_hidden.set(true);
    let text = printer.print(&mut ns, &t, Prec::Arrow);
    if text.chars().count() <= MESSAGE_LIMIT * 2 {
        return text;
    }
    let mut text: String = text.chars().take(MESSAGE_LIMIT * 2).collect();
    text.push('…');
    text
}

/// [`value_for_message`], for a term.
pub fn term_for_message(g: &Globals, names: &[Name], term_: &Term) -> String {
    term_within(g, names, term_, MESSAGE_LIMIT)
}

/// The longest a term may be in a goal (docs/proposals/lsp-goal-holes.md
/// §3.3): a goal is the one place the whole term matters.
const GOAL_LIMIT: usize = 4000;

/// [`value_for_message`], with the larger limit of a goal's types.
pub fn value_for_goal(g: &Globals, names: &[Name], value: &Value) -> String {
    let Ok(t) = quote_folded(g, names.len(), value) else {
        return "…".into();
    };
    term_within(g, names, &t, GOAL_LIMIT)
}

/// [`term_for_message`], with a result longer than `limit` characters
/// shortened.
fn term_within(g: &Globals, names: &[Name], term_: &Term, limit: usize) -> String {
    note_failed_mention(g, term_);
    let full = term(g, names, term_);
    if full.chars().count() <= limit || std::env::var_os("STITCHWORT_FULL_TERMS").is_some() {
        return full;
    }
    // Reprint with less and less depth until it fits.
    for depth in (1..=10).rev() {
        let mut ns = names.to_vec();
        let printer = Printer::new(g);
        printer.max_depth.set(Some(depth));
        let text = printer.print(&mut ns, term_, Prec::Arrow);
        if text.chars().count() <= limit {
            return text;
        }
    }
    // Still too wide (a long list, say): cut it off.
    let mut text: String = full.chars().take(limit).collect();
    text.push('…');
    text
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
    Arrow,
    /// `p ↔ q`: between `->` and `||`, not associative (D1202).
    Iff,
    /// `p || q`, then `p && q`: looser than comparisons, grouping to the right.
    Or,
    And,
    Eq,
    Add,
    /// `*`, `/`, `%`: tighter than `+`, looser than a prefix minus.
    Mul,
    /// A prefix minus: tighter than `*`, looser than application.
    Neg,
    App,
    Atom,
}

struct Printer<'g> {
    g: &'g Globals,
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
}

impl<'g> Printer<'g> {
    fn new(g: &'g Globals) -> Self {
        Printer {
            g,
            elided: Cell::new(false),
            max_depth: Cell::new(None),
            depth: Cell::new(0),
            show_hidden: Cell::new(false),
            ascii: Cell::new(false),
        }
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
                Term::App(f, e, _) if matches!(f.strip_loc(), Term::Def(id) if self.g.registry.is_def(Builtin::RowOp, *id)) =>
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
        if self.g.budget.stack_exhausted() {
            self.elided.set(true);
            return ("…".into(), Prec::Atom);
        }
        match term {
            Term::Loc(_, t) | Term::Ann(t, _) => self.go(names, t),
            Term::Var(ix) => {
                let name = names
                    .len()
                    .checked_sub(ix + 1)
                    .map_or_else(|| format!("?{ix}"), |l| names[l].to_string());
                (name, Prec::Atom)
            }
            Term::Def(id) => (self.g.def(*id).name.to_string(), Prec::Atom),
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
                let mut text = data.name.to_string();
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
            Term::Data(d, args) => self.applied(
                names,
                self.g.data(*d).name.to_string(),
                args.iter().map(|a| &**a),
            ),
            Term::Ctor(d, 0, _) if is(self.g, Builtin::UnitType, *d) => ("()".into(), Prec::Atom),
            // A double with known bits and the standard witness, as its
            // literal: `1.5`, `-0.0`, `Float.nan`.
            Term::Ctor(d, 0, args)
                if Some(*d) == self.g.builtins.float.data
                    && let [bits, witness] = args.as_slice()
                    && matches!(witness.strip_loc(), Term::Refl)
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
            // A record, as a literal: `{ name = "A", age = 3 }`.
            Term::Ctor(d, 0, args) if self.g.data(*d).record => {
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
                let name = self.g.data(*d).ctors[*c].name.to_string();
                self.applied(names, name, args.iter().map(|a| &**a))
            }
            // `p -> Void` is how `Not p` computes; print it the way it's written.
            Term::Pi(_, Icit::Explicit, a, b)
                if !b.mentions(0)
                    && matches!(b.strip_loc(), Term::Data(d, _) if is(self.g, Builtin::Void, *d)) =>
            {
                self.not(names, a)
            }
            Term::Pi(x, icit, a, b) => {
                let uses = b.mentions(0);
                let dom = if icit.is_implicit() || uses {
                    self.print(names, a, Prec::Arrow)
                } else {
                    self.print(names, a, Prec::Or)
                };
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
            // Nested lambdas are one run: `x y => body`. A lambda is a whole
            // expression only; everywhere else it gets brackets, since it
            // prints at the loosest precedence (docs/proposals/lambda-syntax.md §8.3).
            // Implicit and auto parameters are written as such (§4.3), with
            // their types left to be worked out, since a lambda doesn't
            // record them: `[a: _] x => x`.
            Term::Lam(x, icit, b) => {
                let mut params = vec![lambda_param(x, *icit)];
                names.push(x.clone());
                let mut body = &**b;
                while let Term::Lam(y, icit, inner) = body.strip_loc() {
                    params.push(lambda_param(y, *icit));
                    names.push(y.clone());
                    body = inner;
                }
                let body = self.print(names, body, Prec::Arrow);
                names.truncate(names.len() - params.len());
                (format!("{} => {body}", params.join(" ")), Prec::Arrow)
            }
            // The annotation isn't shown, as for `Ann`.
            Term::Let(x, _, v, b, _) => {
                let value = self.print(names, v, Prec::Arrow);
                names.push(x.clone());
                let body = self.print(names, b, Prec::Arrow);
                names.pop();
                (format!("let {x} := {value}; {body}"), Prec::Arrow)
            }
            Term::Meta(_) if let Some(name) = self.label(names, term) => name,
            Term::Meta(m) => (format!("?{m}"), Prec::Atom),
            Term::App(..) if let Some(shown) = self.label(names, term) => shown,
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
                    if (self.g.registry.is_def(Builtin::CompIn, *id)
                        || self.g.registry.is_def(Builtin::DoneIn, *id))
                        && let [row, value] = &args[..]
                        && let Term::Ctor(d, c, fields) = row.strip_loc()
                        && fields.is_empty()
                        && self.g.registry.ctor(Builtin::RowEmpty) == Some((*d, *c))
                    {
                        return self.go(names, value);
                    }
                    // A computation in a bare row that may be partial
                    // (docs/proposals/partial-stage-3.md): `CompD d e a` is
                    // `{e} a`, as written; at `Total` it's `CompIn e a`, and
                    // at `MayDiverge` `{Partial | e} a`. `doneD Total e v`
                    // is `doneIn e v`.
                    if (self.g.registry.is_def(Builtin::CompD, *id)
                        || self.g.registry.is_def(Builtin::DoneD, *id))
                        && let [div, row, result] = &args[..]
                    {
                        let ctor = match div.strip_loc() {
                            Term::Ctor(d, c, fields) if fields.is_empty() => Some((*d, *c)),
                            _ => None,
                        };
                        let empty = matches!(row.strip_loc(), Term::Ctor(d, c, fields)
                            if fields.is_empty()
                                && self.g.registry.ctor(Builtin::RowEmpty) == Some((*d, *c)));
                        let total =
                            ctor.is_some() && ctor == self.g.registry.ctor(Builtin::DivTotal);
                        let may = ctor.is_some() && ctor == self.g.registry.ctor(Builtin::DivMay);
                        if self.g.registry.is_def(Builtin::DoneD, *id) {
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
                            let row = self.print(names, row, Prec::App);
                            if may {
                                return (format!("{{Partial | {row}}} {shown}"), Prec::App);
                            }
                            return (format!("{{{row}}} {shown}"), Prec::App);
                        }
                    }
                    // A computation in a row variable's row: `{e} a`.
                    if self.g.registry.is_def(Builtin::CompIn, *id)
                        && let [row, result] = &args[..]
                    {
                        let row = self.print(names, row, Prec::App);
                        let result = self.print(names, result, Prec::App);
                        return (format!("{{{row}}} {result}"), Prec::App);
                    }
                    // A projection, as written: `x.name` or `p.fst`.
                    if let Some(field) = self.projection_field(*id)
                        && let [arg] = &args[..]
                    {
                        let arg = self.print(names, arg, Prec::Atom);
                        return (format!("{arg}.{field}"), Prec::Atom);
                    }
                    // `if c then a else b`.
                    if self.g.registry.is_def(Builtin::IfThenElse, *id)
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
                    // A partial computation: `{IO, Partial} a`.
                    if self.g.builtins.primitive(*id) == Some(crate::partial::Primitive::Delay)
                        && let [ops, _, result] = &args[..]
                        && let Some(row) = self.row_with(names, ops, true)
                    {
                        let result = self.print(names, result, Prec::App);
                        return (format!("{row} {result}"), Prec::App);
                    }
                    let infix = match self.g.registry.def_builtin(*id) {
                        Some(Builtin::Add) => Some(("+", Prec::Add)),
                        Some(Builtin::Sub) => Some(("-", Prec::Add)),
                        Some(Builtin::Mul) => Some(("*", Prec::Mul)),
                        Some(Builtin::Div) => Some(("/", Prec::Mul)),
                        Some(Builtin::Mod) => Some(("%", Prec::Mul)),
                        Some(Builtin::IntAdd) => Some(("+", Prec::Add)),
                        Some(Builtin::IntSub) => Some(("-", Prec::Add)),
                        Some(Builtin::IntMul) => Some(("*", Prec::Mul)),
                        Some(Builtin::IntDiv) => Some(("/", Prec::Mul)),
                        Some(Builtin::IntMod) => Some(("%", Prec::Mul)),
                        Some(Builtin::LessEq) => Some((self.sym("≤", "<="), Prec::Eq)),
                        Some(Builtin::LessThan) => Some(("<", Prec::Eq)),
                        _ => None,
                    };
                    if let (Some((op, prec)), [lhs, rhs]) = (infix, &args[..]) {
                        // `+`, `-`, `*`, `/` and `%` associate left;
                        // comparisons don't associate.
                        let (left, right) = match prec {
                            Prec::Add => (Prec::Add, Prec::App),
                            Prec::Mul => (Prec::Mul, Prec::Neg),
                            _ => (Prec::Add, Prec::Add),
                        };
                        let lhs = self.print(names, lhs, left);
                        let rhs = self.print(names, rhs, right);
                        return (format!("{lhs} {op} {rhs}"), prec);
                    }
                    if self.g.registry.is_def(Builtin::Not, *id)
                        && let [prop] = &args[..]
                    {
                        return self.not(names, prop);
                    }
                    // `List.Mem x xs` as `x ∈ xs`.
                    if let Some((x, xs)) = self.membership(term) {
                        let x = self.print(names, x, Prec::Add);
                        let xs = self.print(names, xs, Prec::Add);
                        return (format!("{x} {} {xs}", self.sym("∈", "in")), Prec::Eq);
                    }
                }
                if self.show_hidden.get() {
                    return self.applied_with_hidden(names, term);
                }
                let head = self.print(names, head, Prec::App);
                self.applied(names, head, args.into_iter())
            }
            Term::Case(ix, _, _) | Term::NumCase(ix, _, _) => {
                let scrutinee = self.print(names, &Term::Var(*ix), Prec::Atom);
                (format!("case {scrutinee} of …"), Prec::Arrow)
            }
            Term::Eq(_, a, b) => {
                let lhs = self.print(names, a, Prec::Add);
                let rhs = self.print(names, b, Prec::Add);
                (format!("{lhs} = {rhs}"), Prec::Eq)
            }
            Term::J(m, b, p) => self.applied(names, "J".into(), [&**m, &**b, &**p].into_iter()),
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

    /// `Not p` as the operators that write it, in their Unicode spellings
    /// (D1204): `a ≠ b`, `x ∉ xs`, or `¬p`.
    fn not(&self, names: &mut Vec<Name>, prop: &Term) -> (String, Prec) {
        if let Term::Eq(_, a, b) = prop.strip_loc() {
            let a = self.print(names, a, Prec::Add);
            let b = self.print(names, b, Prec::Add);
            return (format!("{a} {} {b}", self.sym("≠", "!=")), Prec::Eq);
        }
        if !self.show_hidden.get()
            && let Some((x, xs)) = self.membership(prop)
        {
            let x = self.print(names, x, Prec::Add);
            let xs = self.print(names, xs, Prec::Add);
            return (format!("{x} {} {xs}", self.sym("∉", "!in")), Prec::Eq);
        }
        // `!` binds more loosely than application: `¬p x` is `¬(p x)`.
        let p = self.print(names, prop, Prec::App);
        (format!("{}{p}", self.sym("¬", "!")), Prec::Neg)
    }

    /// The element and the list of `List.Mem x xs`.
    fn membership<'t>(&self, term: &'t Term) -> Option<(&'t Term, &'t Term)> {
        let id = self.g.registry.loaded_def(Builtin::ListMem)?;
        let (head, args) = explicit_spine(term.strip_loc());
        match (head, &args[..]) {
            (Term::Def(d), [x, xs]) if *d == id => Some((x, xs)),
            _ => None,
        }
    }

    /// A call of a local definition, by its name (`Globals::print_labels`).
    fn label(&self, names: &mut Vec<Name>, term: &Term) -> Option<(String, Prec)> {
        let labels = self.g.print_labels.borrow();
        if labels.is_empty() {
            return None;
        }
        let mut args = Vec::new();
        let mut head = term.strip_loc();
        while let Term::App(f, a, icit) = head {
            args.push((a.as_ref(), *icit));
            head = f.strip_loc();
        }
        args.reverse();
        let label = labels.iter().find(|l| match (&l.head, head) {
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
        let name = label.name.to_string();
        let rest: Vec<&Term> = args[label.levels.len()..]
            .iter()
            .filter(|(_, icit)| *icit == Icit::Explicit)
            .map(|(a, _)| *a)
            .collect();
        drop(labels);
        Some(self.applied(names, name, rest.into_iter()))
    }

    /// The field name of a projection `R.f`, if `id` is one: a record's
    /// generated projection, a data type's generated accessor for a shared
    /// field (docs/proposals/variant-fields.md §9.3), such as the prelude's
    /// `Pair.fst` or `Pair.snd`.
    fn projection_field(&self, id: DefId) -> Option<String> {
        match self.g.registry.def_builtin(id) {
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
            .datas
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
fn is(g: &Globals, b: Builtin, d: DataId) -> bool {
    g.registry.is_data(b, d)
}

/// Whether `d` is the library built-in `b`, if its file is loaded.
fn is_loaded(g: &Globals, b: Builtin, d: DataId) -> bool {
    g.registry.loaded_data(b) == Some(d)
}

/// `Succ (Succ Zero)` as `2`.
fn nat_literal(g: &Globals, term: &Term) -> Option<BigUint> {
    let mut n = 0u64;
    let mut term = term.strip_loc();
    loop {
        match term {
            Term::Nat(k) => return Some(&**k + n),
            Term::Ctor(d, 0, _) if is(g, Builtin::Nat, *d) => return Some(n.into()),
            Term::Ctor(d, 1, args) if is(g, Builtin::Nat, *d) => {
                n += 1;
                term = args[0].strip_loc();
            }
            _ => return None,
        }
    }
}

/// `OfNat 5` as `5` and `NegSucc 4` as `-5`: whether it's negative, and the
/// magnitude.
fn int_literal(g: &Globals, term: &Term) -> Option<(bool, BigUint)> {
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
fn char_literal(g: &Globals, term: &Term) -> Option<char> {
    match term.strip_loc() {
        Term::Ctor(d, 0, args) if is(g, Builtin::Char, *d) && args.len() == 2 => {
            let code = u32::try_from(nat_literal(g, &args[0])?).ok()?;
            char::from_u32(code)
        }
        _ => None,
    }
}

/// `MkText ['h', 'i']` as `"hi"`.
fn text_literal(g: &Globals, term: &Term) -> Option<Vec<char>> {
    match term.strip_loc() {
        Term::Ctor(d, 0, args) if is(g, Builtin::Text, *d) && args.len() == 1 => {
            char_list(g, &args[0])
        }
        _ => None,
    }
}

/// A list of character literals, as cons cells, ending in `Nil` or in a
/// compact list (whose characters are literals).
fn char_list(g: &Globals, term: &Term) -> Option<Vec<char>> {
    let mut chars = Vec::new();
    let mut term = term.strip_loc();
    loop {
        match term {
            Term::Chars(rest) => {
                chars.extend_from_slice(rest.as_slice());
                return Some(chars);
            }
            Term::Ctor(d, 0, _) if is(g, Builtin::List, *d) => return Some(chars),
            Term::Ctor(d, 1, args) if is(g, Builtin::List, *d) => {
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
fn list_literal<'t>(g: &Globals, term: &'t Term) -> Option<Vec<&'t Term>> {
    let mut items = Vec::new();
    let mut term = term.strip_loc();
    loop {
        match term {
            Term::Ctor(d, 0, _) if is(g, Builtin::List, *d) => return Some(items),
            Term::Ctor(d, 1, args) if is(g, Builtin::List, *d) => {
                items.push(&args[0]);
                term = args[1].strip_loc();
            }
            _ => return None,
        }
    }
}

/// Records on `g` that a message showed a term that uses a definition that
/// failed: whatever went wrong then is fallout of that failure (see
/// `Globals::failed_mentioned`). Looks at the whole term, whatever the
/// message elides.
fn note_failed_mention(g: &Globals, term: &Term) {
    if g.failed_mentioned.get() || g.budget.stack_exhausted() {
        return;
    }
    if let Term::Def(d) = term
        && g.def(*d).state() == crate::globals::State::Failed
    {
        g.failed_mentioned.set(true);
        return;
    }
    term.for_each_child(|c, _| note_failed_mention(g, c));
}
