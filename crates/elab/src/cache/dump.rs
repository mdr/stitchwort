//! A canonical text of everything an elaborator holds that later code
//! reads, for the check cache's differential test
//! (docs/proposals/check-cache.md §5.4): a session loaded from the cache
//! must give the same text as one that elaborated everything.
//!
//! It is written independently of the entry encoding, so a field the
//! encoder forgets shows up as a difference: `state::Tables::dump` prints
//! each table whole through its kind, and each row's text is written here
//! ([`Dump`]), apart from its bytes (`rows.rs`). A session's load order is the
//! same with and without the cache, so ids are printed as they are.

use std::fmt::Write;

use stitchwort_core::globals::{FieldDefaults, ParamDefaults, UpdateShown};
use stitchwort_core::js_repr::JsRepr;
use stitchwort_core::{Icit, Term};
use stitchwort_syntax::Span;

use crate::Elaborator;
use crate::TestDecl;
use crate::effects::AbilityInfo;
use crate::interfaces::{InstanceInfo, InterfaceInfo};
use crate::lift::MatchColumns;
use crate::records::RecordInfo;
use crate::state::Dump;
use std::rc::Rc;
use stitchwort_core::{DataId, DefId};

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
/// A test's probe, as text.
fn dump_probe(out: &mut String, p: &crate::Probe) {
    let _ = write!(out, "(whole {} ", p.whole);
    if let Some(truth) = &p.truth {
        out.push_str("truth ");
        term(out, truth);
        out.push(' ');
    }
    match &p.kind {
        crate::ProbeKind::Other => out.push_str("other"),
        crate::ProbeKind::Compare { op, left, right } => {
            let _ = write!(out, "compare {op} ");
            term(out, left);
            out.push(' ');
            term(out, right);
        }
        crate::ProbeKind::And(a, b) => {
            out.push_str("and ");
            dump_probe(out, a);
            out.push(' ');
            dump_probe(out, b);
        }
    }
    out.push(')');
}

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
            Term::Quot(form, args, erased) => {
                let _ = write!(out, "({} {erased}", form.name());
                children.extend(args.iter().map(|a| &**a));
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
                | Term::Quot(..)
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
    let g = &e.ev();
    for (i, def) in g.env.defs().iter().enumerate() {
        let _ = write!(
            out,
            "def {i} {} {} {:?} arity {} group {:?} theorem {} instance {} fold {} export {} opaque {} tailrec {} unfolding {:?} ",
            def.name(),
            def.path(),
            def.state(),
            def.arity(),
            def.group()
                .as_ref()
                .map(|m| m.iter().map(|d| d.0).collect::<Vec<_>>()),
            def.theorem(),
            def.instance(),
            def.fold(),
            def.export(),
            def.opaque(),
            def.tailrec(),
            def.unfolding().iter().map(|d| d.0).collect::<Vec<_>>(),
        );
        span(&mut out, def.span());
        out.push_str("\n  ty ");
        term(&mut out, def.ty());
        out.push_str("\n  body ");
        match def.body() {
            Some(b) => term(&mut out, b),
            None => out.push('-'),
        }
        // What admission works out besides the body, so that a trusted
        // replay (stage 3) is compared with a full check on it too.
        let (transparent, lift_leaf, recursive, inert) = def.admitted_metadata();
        let _ = write!(
            out,
            "\n  transparent {:?} lift_leaf {lift_leaf} recursive {recursive} inert {inert:?} \
             param_default {}",
            transparent.iter().map(|d| d.0).collect::<Vec<_>>(),
            def.param_default(),
        );
        if let Some(run) = def.own_run_body() {
            out.push_str("\n  run ");
            term(&mut out, run);
        }
        for v in def.validators() {
            let _ = write!(out, "\n  validator {} ", v.param);
            term(&mut out, &v.decision);
        }
        out.push('\n');
    }
    for (i, data) in g.env.datas().iter().enumerate() {
        let _ = write!(
            out,
            "data {i} {} {} {:?} {:?} record {} auto {:?} proofs {:?} group {:?} before {} {} ",
            data.name(),
            data.path(),
            data.state(),
            data.sort(),
            data.record(),
            data.auto_params(),
            data.proof_params(),
            data.group().iter().map(|d| d.0).collect::<Vec<_>>(),
            data.defs_before(),
            data.datas_before(),
        );
        span(&mut out, data.span());
        for (x, t) in data.params().iter() {
            let _ = write!(out, "\n  param {x} ");
            term(&mut out, t);
        }
        for (x, t) in data.indices().iter() {
            let _ = write!(out, "\n  index {x} ");
            term(&mut out, t);
        }
        for ctor in data.ctors() {
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
        for v in data.validators() {
            let _ = write!(out, "\n  validator {} {} ", v.ctor, v.field);
            term(&mut out, &v.decision);
        }
        out.push('\n');
    }
    let _ = writeln!(out, "registry missing {:?}", g.env.registry().missing());
    for id in 0..g.env.defs().len() {
        let id = stitchwort_core::DefId(id);
        if let Some(b) = g.env.registry().def_builtin(id) {
            let _ = writeln!(out, "builtin {b:?} = def {}", id.0);
        }
        if let Some(n) = g.env.builtins().native(id) {
            let _ = writeln!(out, "native {} = def {}", n.name(), id.0);
        }
    }
    // (A library built-in whose file hasn't loaded is missing, and may not
    // be asked for.)
    let missing = g.env.registry().missing();
    for b in stitchwort_core::registry::Builtin::ALL {
        if missing.contains(b) {
            continue;
        }
        if let Some(d) = g.env.registry().data(*b) {
            let _ = writeln!(out, "builtin {b:?} = data {}", d.0);
        }
    }

    e.scope.dump(&mut out);

    e.tables.dump(&mut out);
    let _ = writeln!(out, "module {:?}", e.unit.module_path);
    let _ = writeln!(out, "library {:?}", e.loaded_library_files());
    // What navigation recorded, which its index is made from.
    e.present
        .dump(&mut out, &|key| e.scope.get(key).map(|(g, _)| g));
    out
}

impl Dump for DefId {
    fn dump(&self, out: &mut String) {
        let _ = write!(out, "{}", self.0);
    }
}

impl Dump for DataId {
    fn dump(&self, out: &mut String) {
        let _ = write!(out, "{}", self.0);
    }
}

impl Dump for Span {
    fn dump(&self, out: &mut String) {
        span(out, *self);
    }
}

impl Dump for String {
    fn dump(&self, out: &mut String) {
        out.push_str(self);
    }
}

impl<A: Dump, B: Dump> Dump for (A, B) {
    fn dump(&self, out: &mut String) {
        self.0.dump(out);
        out.push(' ');
        self.1.dump(out);
    }
}

impl<A: Dump, B: Dump, C: Dump> Dump for (A, B, C) {
    fn dump(&self, out: &mut String) {
        self.0.dump(out);
        out.push(' ');
        self.1.dump(out);
        out.push(' ');
        self.2.dump(out);
    }
}

impl Dump for RecordInfo {
    fn dump(&self, out: &mut String) {
        let projections: Vec<Option<usize>> =
            self.projections.iter().map(|p| p.map(|p| p.0)).collect();
        let _ = write!(out, "{projections:?}");
    }
}

impl Dump for InterfaceInfo {
    fn dump(&self, out: &mut String) {
        let _ = write!(
            out,
            "{} supers {:?} projections {:?} methods {:?} relations {:?}",
            self.dict,
            self.supers
                .iter()
                .map(|(k, s)| (k, s.0))
                .collect::<Vec<_>>(),
            self.projections.iter().map(|p| p.0).collect::<Vec<_>>(),
            self.methods.iter().map(|p| p.0).collect::<Vec<_>>(),
            self.relations,
        );
    }
}

impl Dump for InstanceInfo {
    fn dump(&self, out: &mut String) {
        let _ = write!(
            out,
            "def {} {} {:?} valid {} ",
            self.def.0, self.name, self.params, self.valid
        );
        span(out, self.span);
    }
}

impl Dump for () {
    fn dump(&self, _: &mut String) {}
}

impl Dump for Rc<FieldDefaults> {
    fn dump(&self, out: &mut String) {
        let _ = write!(out, "{:?}", **self);
    }
}

impl Dump for Rc<ParamDefaults> {
    fn dump(&self, out: &mut String) {
        let _ = write!(out, "{:?}", **self);
    }
}

impl Dump for Rc<UpdateShown> {
    fn dump(&self, out: &mut String) {
        let _ = write!(out, "{} ", self.params);
        term(out, &self.base);
        for (field, value) in &self.fields {
            let _ = write!(out, " {field} = ");
            term(out, value);
        }
    }
}

impl Dump for Rc<JsRepr> {
    fn dump(&self, out: &mut String) {
        let _ = write!(out, "{:?}", **self);
    }
}

impl Dump for Rc<MatchColumns> {
    fn dump(&self, out: &mut String) {
        let _ = write!(out, "{:?} {:?}", self.cols, self.eqs);
    }
}

impl Dump for AbilityInfo {
    fn dump(&self, out: &mut String) {
        let _ = write!(
            out,
            "{} op_data {} res {} elim {} ops {:?} order {:?}",
            self.name, self.op_data.0, self.res.0, self.elim.0, self.ops, self.order
        );
    }
}

impl Dump for TestDecl {
    fn dump(&self, out: &mut String) {
        let _ = write!(
            out,
            "{} {} {} def {} ",
            self.library, self.namespace, self.name, self.def.0
        );
        span(out, self.span);
        if let Some(probe) = &self.probe {
            out.push_str(" probe ");
            dump_probe(out, probe);
        }
    }
}
