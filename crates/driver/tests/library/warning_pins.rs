//! No Stitchwort code gives warnings (Matt, 16 Nov 2026), and the standard
//! library's are never shown to programs, so nothing else would notice a new
//! one. `warning_pins.tsv` pins what is still there, per project, file and
//! code: every count is a ceiling, and the table only ever goes down. A
//! project's rows are added when its warnings are counted the same way
//! (`std` is the only one so far).

use std::collections::BTreeMap;

use stitchwort_driver::driver::{Session, with_stack};

const STACK: usize = 16 * 1024 * 1024;

/// The pinned ceilings: (project, file, code) to count.
fn pins() -> BTreeMap<(String, String, String), usize> {
    include_str!("warning_pins.tsv")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|l| {
            let c: Vec<&str> = l.split('\t').collect();
            let [project, file, code, n] = c[..] else {
                panic!("a pin line has four tab-separated columns: {l:?}")
            };
            (
                (project.into(), file.into(), code.into()),
                n.parse().expect("a count"),
            )
        })
        .collect()
}

#[test]
fn the_library_warnings_stay_within_their_pins() {
    with_stack(STACK, || {
        let session = Session::eager_from_source_for_stack(STACK);
        let all = session.library_warning_report(&|name| name.starts_with("std/"));
        let mut counts: BTreeMap<(String, String, String), usize> = BTreeMap::new();
        for d in &all {
            let file = d.primary_span().map_or("?".to_string(), |s| {
                session.sources.get(s.file).name.clone()
            });
            let file = match file.strip_prefix("std/") {
                Some(path) => path.to_string(),
                None => "core".to_string(),
            };
            *counts
                .entry(("std".into(), file, d.code.to_string()))
                .or_default() += 1;
        }
        let pins = pins();
        let over: Vec<String> = counts
            .iter()
            .filter(|(key, n)| **n > pins.get(*key).copied().unwrap_or(0))
            .map(|((p, f, c), n)| {
                format!(
                    "{p} {f} {c}: {n} (pinned {})",
                    pins.get(&(p.clone(), f.clone(), c.clone())).unwrap_or(&0)
                )
            })
            .collect();
        assert!(
            over.is_empty(),
            "warnings above their pins in warning_pins.tsv (fix the code, \
             or the warning if it is wrong; never raise a pin):\n{}",
            over.join("\n")
        );
    });
}
