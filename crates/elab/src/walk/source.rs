//! Code and statements about code, read back as source a program can write,
//! for the implicits `check --expand-walk` writes out where unification
//! can't find them ([`nested_bind`]). Only the forms the elaborator makes of
//! a block are read: a value, an operation performed, a `let` and a call.
//! Anything else gives None, and the expansion leaves the implicit to be
//! found.

use super::*;

/// The source of a term in `cx`'s scope with the binders `names` pushed
/// (outermost first): None where it would name something a program can't
/// (`%x`, a shadowed `x✝`), is cut short, or has an unknown or code in it
/// (`Done x` and `bind` aren't written as such in a block).
fn plain(cx: &Ctx, names: &[stitchwort_core::Name], term: &Term) -> Option<String> {
    let reg = cx.g().env.registry();
    let code = [Builtin::Done, Builtin::Call].map(|b| reg.ctor(b));
    let binds = [
        Builtin::Bind,
        Builtin::BindIn,
        Builtin::BindD,
        Builtin::BindDv,
    ]
    .map(|b| reg.def(b));
    if term.subterms().any(|(t, _)| match t {
        Term::Meta(_) => true,
        Term::Ctor(d, c, _) => code.contains(&Some((*d, *c))),
        Term::Def(id) => binds.contains(&Some(*id)),
        _ => false,
    }) {
        return None;
    }
    let text = stitchwort_core::pretty::term_in(&cx.g(), cx.e, names, term);
    (!text.contains(['%', '✝', '…'])).then_some(text)
}

/// Code (`Done x`, `Call o k`, `Effect.bind c k`, a call) as the lines of a
/// block, the last its result.
pub(super) fn code_lines(
    cx: &Ctx,
    names: &mut Vec<stitchwort_core::Name>,
    term: &Term,
) -> Option<Vec<String>> {
    let g = cx.g();
    let reg = g.env.registry();
    let term = bare(term);
    if let Term::Ctor(d, c, fields) = term {
        if reg.ctor(Builtin::Done) == Some((*d, *c)) && fields.len() == 1 {
            return Some(vec![plain(cx, names, &fields[0])?]);
        }
        if reg.ctor(Builtin::Call) == Some((*d, *c)) && fields.len() == 2 {
            let performed = operation(cx, names, &fields[0])?;
            return then_lines(cx, names, performed, &fields[1]);
        }
        return None;
    }
    let (head, args) = term.spine();
    if let Term::Def(id) = bare(head)
        && reg.def(Builtin::Bind) == Some(*id)
    {
        let [.., c, k] = &args[..] else {
            return None;
        };
        if args.len() != 6 {
            return None;
        }
        let mut first = code_lines(cx, names, c)?;
        let last = first.pop()?;
        // `let v := (let y := o; f y)` is written `let y := o; let v := f y`:
        // the same code where it starts with an operation, which `bind`
        // computes on. A bound computation that is a call stays one.
        if !first.is_empty() && !performs(cx, c) {
            return None;
        }
        // The names the lines before bind are in scope in the rest.
        let mut scoped = names.clone();
        for line in &first {
            let name = line.strip_prefix("let ")?.split(" := ").next()?;
            scoped.push(name.into());
        }
        let rest = then_lines(cx, &mut scoped, last, k)?;
        first.extend(rest);
        return Some(first);
    }
    Some(vec![plain(cx, names, term)?])
}

/// Whether code starts with an operation performed: a `Call`, or a bind
/// of code that does.
fn performs(cx: &Ctx, term: &Term) -> bool {
    let g = cx.g();
    let reg = g.env.registry();
    match bare(term) {
        Term::Ctor(d, c, _) => reg.ctor(Builtin::Call) == Some((*d, *c)),
        t => {
            let (head, args) = t.spine();
            matches!(bare(head), Term::Def(id) if reg.def(Builtin::Bind) == Some(*id))
                && args.len() == 6
                && performs(cx, args[4])
        }
    }
}

/// `name`, or a variant of it no name in `names` is.
fn unclashing(names: &[stitchwort_core::Name], name: &str) -> stitchwort_core::Name {
    let taken = |n: &str| names.iter().any(|m| &**m == n);
    if !taken(name) {
        return name.into();
    }
    (1..)
        .map(|i| format!("{name}{i}"))
        .find(|n| !taken(n))
        .expect("some number is free")
        .into()
}

/// `let v := performed` and the lines of `k`'s body; just `performed` where
/// `k` only returns the value.
fn then_lines(
    cx: &Ctx,
    names: &mut Vec<stitchwort_core::Name>,
    performed: String,
    k: &Term,
) -> Option<Vec<String>> {
    let Term::Lam(name, _, body, _) = bare(k) else {
        return None;
    };
    let done = cx.g().env.registry().ctor(Builtin::Done);
    if matches!(bare(body), Term::Ctor(d, c, fields)
        if Some((*d, *c)) == done && matches!(&fields[..], [f] if matches!(bare(f), Term::Var(0))))
    {
        return Some(vec![performed]);
    }
    let name = unclashing(names, if generated(name) { "value" } else { name });
    names.push(name.clone());
    let rest = code_lines(cx, names, body);
    names.pop();
    let mut lines = vec![format!("let {name} := {performed}")];
    lines.extend(rest?);
    Some(lines)
}

/// An operation as performed, `Parse.mark()` or `Parse.next (n => True)`:
/// its constructor inside the row's injections, written as a call.
fn operation(cx: &Ctx, names: &[stitchwort_core::Name], o: &Term) -> Option<String> {
    let plus = cx.g().env.registry().data(Builtin::Plus);
    let mut o = bare(o);
    while let Term::Ctor(d, _, fields) = o
        && Some(*d) == plus
        && fields.len() == 1
    {
        o = bare(&fields[0]);
    }
    if !matches!(o, Term::Ctor(..)) {
        return None;
    }
    let text = plain(cx, names, o)?;
    Some(match text.strip_suffix(" ()") {
        Some(name) if !name.contains(' ') => format!("{name}()"),
        _ => text,
    })
}

/// A thunk of code, `() => …`: on one line, or as a block on the lines
/// after.
pub(super) fn thunk(
    cx: &Ctx,
    names: &mut Vec<stitchwort_core::Name>,
    code: &Term,
) -> Option<String> {
    let lines = code_lines(cx, names, code)?;
    Some(match &lines[..] {
        [one] => format!("() => {one}"),
        _ => format!("() =>\n{MORE}{}", lines.join(&format!("\n{MORE}"))),
    })
}

/// The goal a statement is written for: its relation's arguments, in the
/// scope of the first `base` names.
pub(super) struct Outer {
    pub(super) base: usize,
    pub(super) args: Vec<Term>,
}

/// A statement of the family's relation about code, or a function to one
/// (a post, `v => R … (() => k v) holds`), with its thunks as code: the
/// relation's thunk arguments are `arg => code`. An argument still unknown
/// (the invariant, solved later in the walk) is the outer goal's there.
pub(super) fn statement_source(
    cx: &Ctx,
    family: &Family,
    names: &mut Vec<stitchwort_core::Name>,
    term: &Term,
    outer: &Outer,
) -> Option<String> {
    let term = bare(term);
    if let Term::Lam(name, _, body, _) = term {
        let name = unclashing(names, if generated(name) { "value" } else { name });
        names.push(name.clone());
        let body = statement_source(cx, family, names, body, outer);
        names.pop();
        return Some(format!("{name} => {}", body?));
    }
    let (head, args) = term.spine();
    let Term::Def(id) = bare(head) else {
        return plain(cx, names, term);
    };
    if *id != family.relation {
        return plain(cx, names, term);
    }
    let icits = app_icits(term);
    let mut out = written_name(cx, *id);
    for (i, a) in args.iter().enumerate() {
        if icits.get(i) != Some(&Icit::Explicit) {
            continue;
        }
        let text = if matches!(bare(a), Term::Meta(_)) {
            let known = (outer.args.get(i)).and_then(|a| plain(cx, &names[..outer.base], a));
            match known {
                Some(text) if expand::atomic(&[Piece::Text(text.clone())]) => text,
                Some(text) => format!("({text})"),
                None => "_".to_string(),
            }
        } else if family.thunks.contains(&i) {
            let Term::Lam(_, _, code, _) = bare(a) else {
                return None;
            };
            // The thunk's own argument, `()`, is never used by the code.
            names.push("%unit".into());
            let text = thunk(cx, names, code);
            names.pop();
            format!("({})", text?)
        } else {
            let text = statement_source(cx, family, names, a, outer)?;
            if expand::atomic(&[Piece::Text(text.clone())]) {
                text
            } else {
                format!("({text})")
            }
        };
        out.push(' ');
        out.push_str(&text);
    }
    Some(out)
}

/// How each argument of an application is passed, in order.
fn app_icits(term: &Term) -> Vec<Icit> {
    let mut out = Vec::new();
    let mut t = bare(term);
    while let Term::App(f, _, icit) = t {
        out.push(*icit);
        t = bare(f);
    }
    out.reverse();
    out
}
