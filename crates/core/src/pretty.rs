//! Printing core terms in surface-like syntax, for error messages and the REPL.

use num_bigint::BigUint;

use crate::globals::Globals;
use crate::term::{DataId, Icit, Name, Sort, Term};
use crate::value::{Value, quote};

/// Prints `term`, whose free variables are named by `names` (outermost first).
pub fn term(g: &Globals, names: &[Name], term: &Term) -> String {
    let mut names = names.to_vec();
    Printer { g }.print(&mut names, term, Prec::Arrow)
}

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
    Eq,
    Add,
    App,
    Atom,
}

struct Printer<'g> {
    g: &'g Globals,
}

impl Printer<'_> {
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
        let mut labels = Vec::new();
        let mut ops = ops.strip_loc();
        let tail = loop {
            match ops {
                Term::Data(d, args) if data_named(self.g, *d, "Plus") && args.len() == 2 => {
                    labels.push(self.print(names, &args[0], Prec::Arrow));
                    ops = args[1].strip_loc();
                }
                Term::Data(d, _) if data_named(self.g, *d, "NoOp") => break None,
                Term::App(f, e, _) if matches!(f.strip_loc(), Term::Def(id) if &*self.g.def(*id).name == "sigOp") =>
                {
                    break Some(self.print(names, e, Prec::App));
                }
                _ => return None,
            }
        };
        Some(match (labels.is_empty(), tail) {
            (true, Some(t)) => format!("{{{t}}}"),
            (_, Some(t)) => format!("{{{} | {t}}}", labels.join(", ")),
            (_, None) => format!("{{{}}}", labels.join(", ")),
        })
    }

    fn go(&self, names: &mut Vec<Name>, term: &Term) -> (String, Prec) {
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
            Term::Data(d, _) if data_named(self.g, *d, "UnitType") => ("()".into(), Prec::Atom),
            // A computation over a row of abilities: `{State Nat | e} a`.
            Term::Data(d, args) if data_named(self.g, *d, "Comp") && args.len() == 3 => {
                match self.row(names, &args[0]) {
                    Some(row) => {
                        let result = self.print(names, &args[2], Prec::App);
                        (format!("{row} {result}"), Prec::App)
                    }
                    None => self.applied(names, "Comp".into(), args.iter().map(|a| &**a)),
                }
            }
            Term::Data(d, args) => self.applied(
                names,
                self.g.data(*d).name.to_string(),
                args.iter().map(|a| &**a),
            ),
            Term::Ctor(d, 0, _) if data_named(self.g, *d, "UnitType") => ("()".into(), Prec::Atom),
            Term::Ctor(d, c, args) => {
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
                let name = self.g.data(*d).ctors[*c].name.to_string();
                self.applied(names, name, args.iter().map(|a| &**a))
            }
            // `p -> Void` is how `Not p` computes; print it the way it's written.
            Term::Pi(_, Icit::Explicit, a, b)
                if !b.mentions(0)
                    && matches!(b.strip_loc(), Term::Data(d, _) if data_named(self.g, *d, "Void")) =>
            {
                if let Term::Eq(_, lhs, rhs) = a.strip_loc() {
                    let lhs = self.print(names, lhs, Prec::Add);
                    let rhs = self.print(names, rhs, Prec::Add);
                    return (format!("{lhs} != {rhs}"), Prec::Eq);
                }
                self.applied(names, "Not".into(), [&**a].into_iter())
            }
            Term::Pi(x, icit, a, b) => {
                let dom = self.print(names, a, Prec::Eq);
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
                (format!("\\{x} -> {body}"), Prec::Arrow)
            }
            Term::Meta(m) => (format!("?{m}"), Prec::Atom),
            Term::App(..) => {
                // Implicit arguments are filled in by the compiler, so they
                // aren't shown.
                let (head, args) = explicit_spine(term);
                if let Term::Def(id) = head {
                    let name = &*self.g.def(*id).name;
                    let infix = match name {
                        "add" => Some(("+", Prec::Add)),
                        "sub" => Some(("-", Prec::Add)),
                        "LessEq" => Some(("<=", Prec::Eq)),
                        "LessThan" => Some(("<", Prec::Eq)),
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
                    if let ("Not", [prop]) = (name, &args[..])
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
            Term::Case(ix, _, _) => {
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

fn data_named(g: &Globals, d: DataId, name: &str) -> bool {
    &*g.data(d).name == name
}

/// `Succ (Succ Zero)` as `2`.
fn nat_literal(g: &Globals, term: &Term) -> Option<BigUint> {
    let mut n = 0u64;
    let mut term = term.strip_loc();
    loop {
        match term {
            Term::Nat(k) => return Some(&**k + n),
            Term::Ctor(d, 0, _) if data_named(g, *d, "Nat") => return Some(n.into()),
            Term::Ctor(d, 1, args) if data_named(g, *d, "Nat") => {
                n += 1;
                term = args[0].strip_loc();
            }
            _ => return None,
        }
    }
}

/// `MkChar 97 _` as `'a'`.
fn char_literal(g: &Globals, term: &Term) -> Option<char> {
    match term.strip_loc() {
        Term::Ctor(d, 0, args) if data_named(g, *d, "Char") && args.len() == 2 => {
            let code = u32::try_from(nat_literal(g, &args[0])?).ok()?;
            char::from_u32(code)
        }
        _ => None,
    }
}

/// `MkText ['h', 'i']` as `"hi"`.
fn text_literal(g: &Globals, term: &Term) -> Option<Vec<char>> {
    match term.strip_loc() {
        Term::Ctor(d, 0, args) if data_named(g, *d, "Text") && args.len() == 1 => {
            list_literal(g, &args[0])?
                .into_iter()
                .map(|c| char_literal(g, c))
                .collect()
        }
        _ => None,
    }
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
            Term::Ctor(d, 0, _) if data_named(g, *d, "List") => return Some(items),
            Term::Ctor(d, 1, args) if data_named(g, *d, "List") => {
                items.push(&args[0]);
                term = args[1].strip_loc();
            }
            _ => return None,
        }
    }
}
