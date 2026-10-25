//! Tests of the library index and loader, and the report of what the core
//! must keep (docs/proposals/std-library.md §5, §7).

use std::collections::{BTreeMap, BTreeSet};

use stitchwort_core::collections::HashMap;
use stitchwort_core::registry::{Builtin, Kind};
use stitchwort_syntax::ast::{Decl, Module};

use crate::library::{IndexedFile, LibraryIndex, file_names};
use crate::module::{Ref, decl_refs, result_head};
use crate::project::grouped;
use crate::scope::{self, Resolved};
use crate::{Elaborator, Global, prelude};

/// One declaration of the core (a signature with its equations, a data
/// type, an ability), for the closure report.
struct Unit {
    name: String,
    keys: Vec<String>,
    /// Non-blank, non-comment lines.
    lines: usize,
    first_line: usize,
    deps: BTreeSet<usize>,
}

/// Every declaration of file `f` of the index, with what it refers to: by
/// the resolver (dot notation: every function of that name).
fn units(index: &LibraryIndex, f: usize) -> Vec<Unit> {
    let mut scratch = Elaborator::new();
    scratch.loading_prelude = true;
    for (g, file) in index.files.iter().enumerate() {
        for name in &file.names {
            scratch.scope.insert(
                &name.key,
                Global::Pending(g, name.kind),
                name.span,
                name.follower,
            );
        }
    }
    let file = &index.files[f];
    let groups = grouped(&file.module.decls);
    let mut owner_unit: HashMap<String, usize> = HashMap::default();
    let mut out: Vec<Unit> = Vec::new();
    for (i, (decl, _)) in groups.iter().enumerate() {
        let alone = IndexedFile {
            path: String::new(),
            id: file.id,
            text: String::new(),
            module: Module {
                namespace: None,
                imports: Vec::new(),
                decls: vec![(*decl).clone()],
                failed: Vec::new(),
            },
            names: Vec::new(),
            edges: Vec::new(),
        };
        let keys: Vec<String> = file_names(&scratch, &alone)
            .expect("names")
            .into_iter()
            .map(|n| n.key)
            .collect();
        for k in &keys {
            owner_unit.insert(k.clone(), i);
        }
        let start = decl.span().start as usize;
        let end = groups
            .get(i + 1)
            .map_or(file.text.len(), |(d, _)| d.span().start as usize);
        let text = &file.text[start..end.max(start)];
        let lines = text
            .lines()
            .filter(|l| !l.trim().is_empty() && !l.trim_start().starts_with("--"))
            .count();
        out.push(Unit {
            name: keys.first().cloned().unwrap_or_default(),
            keys,
            lines,
            first_line: file.text[..start].matches('\n').count() + 1,
            deps: BTreeSet::new(),
        });
    }
    // Dot notation: any function with that last component.
    let mut by_short: HashMap<&str, Vec<usize>> = HashMap::default();
    for (key, &i) in &owner_unit {
        by_short.entry(scope::short(key)).or_default().push(i);
    }
    for (i, (decl, equations)) in groups.iter().enumerate() {
        let mut deps = BTreeSet::new();
        for (r, _) in decl_refs(decl, equations) {
            let (n, mut fields) = match &r {
                Ref::Name(n) => (n, Vec::new()),
                Ref::Dot(n, field) => (n, vec![field.clone()]),
            };
            if fields.is_empty()
                && let Resolved::Found { key, rest, .. } = scratch.resolve(&n.text)
            {
                if let Some(&u) = owner_unit.get(key) {
                    deps.insert(u);
                }
                fields = rest;
            }
            for field in &fields {
                deps.extend(by_short.get(field.as_str()).into_iter().flatten().copied());
            }
        }
        deps.remove(&i);
        out[i].deps = deps;
    }
    out
}

/// The units that declare a function whose result is `Decidable …`.
fn decidable_procedures(index: &LibraryIndex, f: usize, units: &[Unit]) -> BTreeSet<usize> {
    let file = &index.files[f];
    let by_first: HashMap<&str, usize> = units
        .iter()
        .enumerate()
        .filter_map(|(i, u)| u.keys.first().map(|k| (k.as_str(), i)))
        .collect();
    let mut out = BTreeSet::new();
    for (decl, _) in grouped(&file.module.decls) {
        if let Decl::Signature { name, ty, .. } = decl
            && result_head(ty).is_some_and(|h| h.text == "Decidable")
            && let Some(&u) = by_first.get(format!("Std.{}", name.text).as_str())
        {
            out.insert(u);
        }
    }
    out
}

/// The units that must stay in the core: what the compiler names (the
/// registry), and every `Decidable` procedure (D58), with everything they
/// need.
fn core_closure(index: &LibraryIndex, units: &[Unit]) -> BTreeSet<usize> {
    let by_key: HashMap<&str, usize> = units
        .iter()
        .enumerate()
        .flat_map(|(i, u)| u.keys.iter().map(move |k| (k.as_str(), i)))
        .collect();
    let mut roots: BTreeSet<usize> = BTreeSet::new();
    for b in Builtin::ALL {
        if b.home() == stitchwort_core::registry::Home::Library {
            continue;
        }
        let name = match b.kind() {
            Kind::Ctor(parent) => parent.name(),
            _ => b.name(),
        };
        let key = format!("Std.{name}");
        let unit = by_key
            .get(key.as_str())
            .unwrap_or_else(|| panic!("the registry names `{key}`, which isn't declared"));
        roots.insert(*unit);
    }
    roots.extend(decidable_procedures(index, 0, units));
    // Every instance stays with its laws (D170), and so does each name
    // generated code writes in full (`PRELUDE_ROOTS`: a file of keys, one
    // per line).
    for (decl, _) in grouped(&index.files[0].module.decls) {
        if let Decl::Signature {
            name,
            instance: true,
            ..
        } = decl
            && let Some(&u) = by_key.get(format!("Std.{}", name.text).as_str())
        {
            roots.insert(u);
        }
    }
    if let Ok(path) = std::env::var("PRELUDE_ROOTS") {
        for key in std::fs::read_to_string(path)
            .expect("the roots file")
            .lines()
        {
            if let Some(&u) = by_key.get(key.trim()) {
                roots.insert(u);
            }
        }
    }
    let mut closure = BTreeSet::new();
    let mut stack: Vec<usize> = roots.into_iter().collect();
    while let Some(u) = stack.pop() {
        if closure.insert(u) {
            stack.extend(units[u].deps.iter().copied());
        }
    }
    closure
}

/// What each declaration of the monolithic prelude needs, and the size of
/// the core closure D58 implies. Run on the prelude as it was before any
/// move (its text is the only input):
/// `PRELUDE_REPORT=path cargo test -p stitchwort-elab --release closure_report -- --ignored --nocapture`.
#[test]
#[ignore = "a report, not a check"]
fn closure_report() {
    let text = match std::env::var("PRELUDE_REPORT") {
        Ok(path) => std::fs::read_to_string(path).expect("the prelude to report on"),
        Err(_) => prelude().to_string(),
    };
    let index = LibraryIndex::build(&text, &[], 8 << 20).expect("index");
    let units = units(&index, 0);
    let closure = core_closure(&index, &units);
    let decidable = decidable_procedures(&index, 0, &units);
    let total_lines: usize = units.iter().map(|u| u.lines).sum();
    let closure_lines: usize = closure.iter().map(|&u| units[u].lines).sum();
    println!(
        "core closure: {} of {} declarations, {closure_lines} of {total_lines} lines \
         ({} decidable procedures)",
        closure.len(),
        units.len(),
        decidable.len()
    );
    let mut by_block: BTreeMap<usize, (usize, usize, usize, usize)> = BTreeMap::new();
    for (i, u) in units.iter().enumerate() {
        let e = by_block.entry(u.first_line / 250 * 250).or_default();
        e.0 += 1;
        if closure.contains(&i) {
            e.1 += 1;
            e.3 += u.lines;
        }
        e.2 += u.lines;
    }
    for (block, (n, kept, lines, kept_lines)) in by_block {
        println!(
            "lines {block:>4}+: {kept:>3} of {n:>3} declarations, {kept_lines:>3} of {lines:>3} lines in the closure"
        );
    }
    println!("--- every declaration, with the declarations it needs (* = in the closure)");
    for (i, u) in units.iter().enumerate() {
        let mark = if closure.contains(&i) { '*' } else { ' ' };
        let needs: Vec<String> = u
            .deps
            .iter()
            .map(|&d| {
                format!(
                    "{}{}",
                    if closure.contains(&d) { "*" } else { "" },
                    scope::display(&units[d].name)
                )
            })
            .collect();
        println!(
            "{mark} {:>4} {:>3}  {}  <- {}",
            u.first_line,
            u.lines,
            scope::display(&u.name),
            needs.join(" ")
        );
    }
}
