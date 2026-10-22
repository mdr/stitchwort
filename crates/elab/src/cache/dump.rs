//! A canonical text of everything an elaborator holds that later code
//! reads, for the check cache's differential test
//! (docs/proposals/check-cache.md §5.4): a session loaded from the cache
//! must give the same text as one that elaborated everything.
//!
//! It is written independently of the entry encoding, so a field the
//! encoder forgets shows up as a difference. A session's load order is the
//! same with and without the cache, so ids are printed as they are.

use std::fmt::Write;

use stitchwort_core::{Icit, Term};
use stitchwort_syntax::Span;

use crate::Elaborator;

fn span(out: &mut String, s: Span) {
    let _ = write!(out, "@{}:{}-{}", s.file.index(), s.start, s.end);
}

fn icit(i: Icit) -> &'static str {
    match i {
        Icit::Explicit => "e",
        Icit::Implicit => "i",
        Icit::Auto => "a",
    }
}

/// Every node of `t`, names, spans and flags included, without recursing.
fn term(out: &mut String, t: &Term) {
    enum Item<'t> {
        Term(&'t Term),
        Text(&'static str),
    }
    let mut stack = vec![Item::Term(t)];
    while let Some(item) = stack.pop() {
        let t = match item {
            Item::Text(s) => {
                out.push_str(s);
                continue;
            }
            Item::Term(t) => t,
        };
        let mut children: Vec<&Term> = Vec::new();
        match t {
            Term::Var(i) => {
                let _ = write!(out, "v{i}");
            }
            Term::Def(id) => {
                let _ = write!(out, "d{}", id.0);
            }
            Term::Data(d, args) => {
                let _ = write!(out, "(D{}", d.0);
                children.extend(args.iter().map(|a| &**a));
            }
            Term::Ctor(d, c, args) => {
                let _ = write!(out, "(C{}.{c}", d.0);
                children.extend(args.iter().map(|a| &**a));
            }
            Term::Nat(n) => {
                let _ = write!(out, "n{n}");
            }
            Term::Chars(c) => {
                let s: String = c.as_slice().iter().collect();
                let _ = write!(out, "{s:?}");
            }
            Term::Sort(s) => {
                let _ = write!(out, "{s:?}");
            }
            Term::Pi(x, i, a, b) => {
                let _ = write!(out, "(Pi {x} {}", icit(*i));
                children.extend([&**a, &**b]);
            }
            Term::Lam(x, i, b) => {
                let _ = write!(out, "(Lam {x} {}", icit(*i));
                children.push(b);
            }
            Term::App(f, a, i) => {
                let _ = write!(out, "(App {}", icit(*i));
                children.extend([&**f, &**a]);
            }
            Term::Ann(a, b) => {
                out.push_str("(Ann");
                children.extend([&**a, &**b]);
            }
            Term::Let(x, ty, v, b, erased) => {
                let _ = write!(out, "(Let {x} {erased}");
                children.extend([&**ty, &**v, &**b]);
            }
            Term::Case(x, d, branches) => {
                let _ = write!(out, "(Case v{x} D{}", d.0);
                for b in branches.iter() {
                    let _ = write!(out, " [{}]", b.names.join(" "));
                    match &b.body {
                        Some(body) => children.push(body),
                        None => out.push_str(" impossible"),
                    }
                }
            }
            Term::NumCase(x, arms, default) => {
                let _ = write!(out, "(NumCase v{x}");
                for arm in arms.iter() {
                    let _ = write!(out, " {}", arm.value);
                    children.push(&arm.body);
                }
                children.push(default);
            }
            Term::Eq(ty, a, b) => {
                let _ = write!(out, "(Eq {}", ty.is_some());
                if let Some(ty) = ty {
                    children.push(ty);
                }
                children.extend([&**a, &**b]);
            }
            Term::Refl => out.push_str("refl"),
            Term::J(m, b, p) => {
                out.push_str("(J");
                children.extend([&**m, &**b, &**p]);
            }
            Term::Loc(s, b) => {
                out.push_str("(Loc ");
                span(out, *s);
                children.push(b);
            }
            Term::Meta(m) => {
                let _ = write!(out, "?{m}");
            }
        }
        let opened = matches!(
            t,
            Term::Data(..)
                | Term::Ctor(..)
                | Term::Pi(..)
                | Term::Lam(..)
                | Term::App(..)
                | Term::Ann(..)
                | Term::Let(..)
                | Term::Case(..)
                | Term::NumCase(..)
                | Term::Eq(..)
                | Term::J(..)
                | Term::Loc(..)
        );
        if opened {
            stack.push(Item::Text(")"));
        }
        for c in children.into_iter().rev() {
            stack.push(Item::Term(c));
            stack.push(Item::Text(" "));
        }
    }
}

/// The canonical dump of `e` (see the module's comment).
pub fn canonical_dump(e: &Elaborator) -> String {
    let mut out = String::new();
    let g = &e.globals;
    for (i, def) in g.defs.iter().enumerate() {
        let _ = write!(
            out,
            "def {i} {} {} {:?} arity {} group {:?} theorem {} instance {} fold {} export {} ",
            def.name,
            def.path,
            def.state(),
            def.arity,
            def.group
                .as_ref()
                .map(|m| m.iter().map(|d| d.0).collect::<Vec<_>>()),
            def.theorem,
            def.instance,
            def.fold,
            def.export,
        );
        span(&mut out, def.span);
        out.push_str("\n  ty ");
        term(&mut out, &def.ty);
        out.push_str("\n  body ");
        match def.body() {
            Some(b) => term(&mut out, b),
            None => out.push('-'),
        }
        for v in &def.validators {
            let _ = write!(out, "\n  validator {} ", v.param);
            term(&mut out, &v.decision);
        }
        out.push('\n');
    }
    for (i, data) in g.datas.iter().enumerate() {
        let _ = write!(
            out,
            "data {i} {} {} {:?} {:?} record {} auto {:?} group {:?} before {} {} ",
            data.name,
            data.path,
            data.state(),
            data.sort,
            data.record,
            data.auto_params,
            data.group.iter().map(|d| d.0).collect::<Vec<_>>(),
            data.defs_before,
            data.datas_before,
        );
        span(&mut out, data.span);
        for (x, t) in data.params.iter() {
            let _ = write!(out, "\n  param {x} ");
            term(&mut out, t);
        }
        for (x, t) in data.indices.iter() {
            let _ = write!(out, "\n  index {x} ");
            term(&mut out, t);
        }
        for ctor in &data.ctors {
            let _ = write!(
                out,
                "\n  ctor {} sorts {:?} erased {:?} implicit {:?}",
                ctor.name, ctor.field_sorts, ctor.field_erased, ctor.implicit
            );
            for (x, t) in &ctor.fields {
                let _ = write!(out, "\n    field {x} ");
                term(&mut out, t);
            }
            for r in &ctor.result {
                out.push_str("\n    result ");
                term(&mut out, r);
            }
        }
        for v in &data.validators {
            let _ = write!(out, "\n  validator {} {} ", v.ctor, v.field);
            term(&mut out, &v.decision);
        }
        out.push('\n');
    }
    let _ = writeln!(out, "registry missing {:?}", g.registry.missing());
    for id in 0..g.defs.len() {
        let id = stitchwort_core::DefId(id);
        if let Some(b) = g.registry.def_builtin(id) {
            let _ = writeln!(out, "builtin {b:?} = def {}", id.0);
        }
        if let Some(n) = g.builtins.native(id) {
            let _ = writeln!(out, "native {} = def {}", n.name(), id.0);
        }
    }
    // (A library built-in whose file hasn't loaded is missing, and may not
    // be asked for.)
    let missing = g.registry.missing();
    for b in stitchwort_core::registry::Builtin::ALL {
        if missing.contains(b) {
            continue;
        }
        if let Some(d) = g.registry.data(*b) {
            let _ = writeln!(out, "builtin {b:?} = data {}", d.0);
        }
    }

    e.scope.dump(&mut out);

    let mut sorted: Vec<String> = e
        .records
        .iter()
        .map(|(d, r)| {
            format!(
                "record {} {:?}",
                d.0,
                r.projections
                    .iter()
                    .map(|p| p.map(|p| p.0))
                    .collect::<Vec<_>>()
            )
        })
        .collect();
    sorted.extend(e.interfaces.iter().map(|(d, i)| {
        format!(
            "interface {} {} supers {:?} projections {:?} methods {:?} relations {:?}",
            d.0,
            i.dict,
            i.supers.iter().map(|(k, s)| (k, s.0)).collect::<Vec<_>>(),
            i.projections.iter().map(|p| p.0).collect::<Vec<_>>(),
            i.methods.iter().map(|p| p.0).collect::<Vec<_>>(),
            i.relations,
        )
    }));
    sorted.extend(e.instances.iter().map(|((i, h), info)| {
        let mut s = format!(
            "instance {} {} def {} {} {:?} valid {} ",
            i.0, h.0, info.def.0, info.name, info.params, info.valid
        );
        span(&mut s, info.span);
        s
    }));
    for (what, table) in [
        ("owner", &e.data_owners),
        ("no_eq", &e.no_eq),
        ("no_show", &e.no_show),
        ("no_ord", &e.no_ord),
    ] {
        sorted.extend(table.iter().map(|(d, s)| format!("{what} {} {s}", d.0)));
    }
    sorted.extend(e.helper_keys.iter().map(|k| format!("helper {k}")));
    sorted.extend(
        e.namespace_defs
            .iter()
            .map(|(n, r)| format!("namespace {n} {r:?}")),
    );
    sorted.sort();
    for line in sorted {
        out.push_str(&line);
        out.push('\n');
    }
    for (i, a) in e.abilities.iter().enumerate() {
        let _ = writeln!(
            out,
            "ability {i} {} op_data {} res {} elim {} ops {:?} order {:?}",
            a.name, a.op_data.0, a.res.0, a.elim.0, a.ops, a.order
        );
    }
    for (id, s) in &e.lifted {
        let _ = write!(out, "lifted {} ", id.0);
        span(&mut out, *s);
        out.push('\n');
    }
    for t in &e.tests {
        let _ = write!(
            out,
            "test {} {} {} def {} ",
            t.library, t.namespace, t.name, t.def.0
        );
        span(&mut out, t.span);
        if let Some(sides) = &t.sides {
            let _ = write!(out, " sides {} ", sides.op);
            term(&mut out, &sides.left);
            out.push(' ');
            term(&mut out, &sides.right);
        }
        out.push('\n');
    }
    let _ = writeln!(out, "module {:?}", g.module);
    let _ = writeln!(
        out,
        "prelude_defs {} library {:?}",
        e.prelude_defs,
        e.loaded_library_files()
    );
    // What navigation recorded, which its index is made from.
    if let Some(nav) = &e.nav {
        nav.borrow()
            .dump(&mut out, &|key| e.scope.get(key).map(|(g, _)| g));
    }
    out
}
