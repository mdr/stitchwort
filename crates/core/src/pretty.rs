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
use crate::term::{DataId, Icit, Name, Sort, Term};
use crate::value::{Value, quote};

/// Prints `term`, whose free variables are named by `names` (outermost first).
pub fn term(g: &Globals, names: &[Name], term: &Term) -> String {
    let mut names = names.to_vec();
    Printer::new(g).print(&mut names, term, Prec::Arrow)
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

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
    Arrow,
    /// `p || q`, then `p && q`: looser than comparisons, grouping to the right.
    Or,
    And,
    Eq,
    Add,
    /// A prefix minus: tighter than `*`, looser than application.
    Neg,
    App,
    Atom,
}

struct Printer<'g> {
    g: &'g Globals,
    /// Whether something was too deeply nested to print, and shown as `…`.
    elided: Cell<bool>,
}

impl<'g> Printer<'g> {
    fn new(g: &'g Globals) -> Self {
        Printer {
            g,
            elided: Cell::new(false),
        }
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
    /// `Plus` ending in `NoOp` or `sigOp e`.
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
                Term::App(f, e, _) if matches!(f.strip_loc(), Term::Def(id) if self.g.registry.is_def(Builtin::SigOp, *id)) =>
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
                match self.row(names, &args[0]) {
                    Some(row) => {
                        let result = self.print(names, &args[2], Prec::App);
                        (format!("{row} {result}"), Prec::App)
                    }
                    None => self.applied(names, "Comp".into(), args.iter().map(|a| &**a)),
                }
            }
            // `And p q` and `Or p q` as they're written: `p && q`, `p || q`.
            Term::Data(d, args)
                if args.len() == 2
                    && (is(self.g, Builtin::And, *d) || is(self.g, Builtin::Or, *d)) =>
            {
                let (op, prec, left) = if is(self.g, Builtin::And, *d) {
                    ("&&", Prec::And, Prec::Eq)
                } else {
                    ("||", Prec::Or, Prec::And)
                };
                let lhs = self.print(names, &args[0], left);
                let rhs = self.print(names, &args[1], prec);
                (format!("{lhs} {op} {rhs}"), prec)
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
            Term::Data(d, args) => self.applied(
                names,
                self.g.data(*d).name.to_string(),
                args.iter().map(|a| &**a),
            ),
            Term::Ctor(d, 0, _) if is(self.g, Builtin::UnitType, *d) => ("()".into(), Prec::Atom),
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
                if let Term::Eq(_, lhs, rhs) = a.strip_loc() {
                    let lhs = self.print(names, lhs, Prec::Add);
                    let rhs = self.print(names, rhs, Prec::Add);
                    return (format!("{lhs} != {rhs}"), Prec::Eq);
                }
                self.applied(names, "Not".into(), [&**a].into_iter())
            }
            Term::Pi(x, icit, a, b) => {
                let dom = self.print(names, a, Prec::Or);
                let uses = b.mentions(0);
                names.push(x.clone());
                let cod = self.print(names, b, Prec::Arrow);
                names.pop();
                if icit.is_implicit() {
                    let dom = self.print(names, a, Prec::Arrow);
                    let auto = if *icit == Icit::Auto { "auto " } else { "" };
                    (format!("[{auto}{x} : {dom}] -> {cod}"), Prec::Arrow)
                } else if uses {
                    let dom = self.print(names, a, Prec::Arrow);
                    (format!("({x} : {dom}) -> {cod}"), Prec::Arrow)
                } else {
                    (format!("{dom} -> {cod}"), Prec::Arrow)
                }
            }
            Term::Lam(x, _, b) => {
                names.push(x.clone());
                let body = self.print(names, b, Prec::Arrow);
                names.pop();
                (format!("\\{x} => {body}"), Prec::Arrow)
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
            Term::App(..) => {
                // Implicit arguments are filled in by the compiler, so they
                // aren't shown.
                let (head, args) = explicit_spine(term);
                if let Term::Def(id) = head {
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
                        Some(Builtin::LessEq) => Some(("<=", Prec::Eq)),
                        Some(Builtin::LessThan) => Some(("<", Prec::Eq)),
                        _ => None,
                    };
                    if let (Some((op, prec)), [lhs, rhs]) = (infix, &args[..]) {
                        // `+` and `-` associate left; comparisons don't associate.
                        let right = if prec == Prec::Add {
                            Prec::App
                        } else {
                            Prec::Add
                        };
                        let lhs = self.print(names, lhs, Prec::Add);
                        let rhs = self.print(names, rhs, right);
                        return (format!("{lhs} {op} {rhs}"), prec);
                    }
                    if self.g.registry.is_def(Builtin::Not, *id)
                        && let [prop] = &args[..]
                        && let Term::Eq(_, a, b) = prop.strip_loc()
                    {
                        let a = self.print(names, a, Prec::Add);
                        let b = self.print(names, b, Prec::Add);
                        return (format!("{a} != {b}"), Prec::Eq);
                    }
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

    fn tuple(&self, names: &mut Vec<Name>, items: &[&Term]) -> String {
        let items: Vec<String> = items
            .iter()
            .map(|t| self.print(names, t, Prec::Arrow))
            .collect();
        format!("({})", items.join(", "))
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
