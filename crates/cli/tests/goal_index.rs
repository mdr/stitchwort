//! Goals as data in `stitchwort check --index` (docs/proposals/code-navigation.md,
//! "Goals"; docs/research/agentic-proving.md T3), end to end with the built
//! command: each goal's hypotheses and target, its lemma, and a
//! counterexample as data; and long goals cut in the human output.

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

use serde_json::Value;

/// `examples/goals/`.
fn goals_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/goals")
}

/// The examples of `examples/goals/`: name (less `.sw`) and text.
fn examples() -> Vec<(String, String)> {
    let mut all: Vec<(String, String)> = std::fs::read_dir(goals_dir())
        .unwrap()
        .filter_map(|entry| {
            let path = entry.unwrap().path();
            let name = path.file_name()?.to_str()?.strip_suffix(".sw")?.to_string();
            Some((name, std::fs::read_to_string(&path).unwrap()))
        })
        .collect();
    all.sort();
    all
}

fn stitchwort(cwd: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(args)
        .arg("--no-cache")
        .current_dir(cwd)
        .stdin(Stdio::null())
        .output()
        .expect("run stitchwort")
}

/// A scratch folder of its own for `test`.
fn scratch(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "stitchwort-goal-index-{}-{test}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// The index `check --index -` writes for the file `name` in `dir`.
fn index_of(dir: &Path, name: &str) -> Value {
    let output = stitchwort(dir, &["check", "--index", "-", name]);
    let json = std::str::from_utf8(&output.stdout).unwrap();
    serde_json::from_str(json).unwrap_or_else(|e| panic!("{name}: {e}\n{json}"))
}

/// The index's diagnostics.
fn diagnostics(index: &Value) -> Vec<Value> {
    index["diagnostics"].as_array().unwrap().clone()
}

fn is_goal(d: &Value) -> bool {
    d["severity"] == "goal"
}

/// Runs `f` on each example, on threads of their own.
fn each_example<T: Send>(f: impl Fn(&str, &str) -> T + Sync) -> Vec<(String, T)> {
    let all = examples();
    assert!(!all.is_empty());
    std::thread::scope(|s| {
        let handles: Vec<_> = all
            .iter()
            .map(|(name, text)| {
                let f = &f;
                s.spawn(move || (name.clone(), f(name, text)))
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    })
}

/// Each goal example's diagnostics in the index, snapshotted: the `goal`
/// member (hypotheses, target, lemma) and, where the search found one, the
/// `counterexample` member. Every goal has a `goal`, its parts agreeing with
/// its label.
#[test]
fn goal_examples_in_the_index() {
    let results = each_example(|name, _| {
        let index = index_of(&goals_dir(), &format!("{name}.sw"));
        assert_eq!(index["version"], 3);
        let diagnostics = diagnostics(&index);
        for d in diagnostics.iter().filter(|d| is_goal(d)) {
            let goal = &d["goal"];
            let mut lines: Vec<String> = goal["hypotheses"]
                .as_array()
                .unwrap()
                .iter()
                .map(|h| match h["value"].as_str() {
                    Some(v) => format!(
                        "{}: {} := {v}",
                        h["name"].as_str().unwrap(),
                        h["type"].as_str().unwrap()
                    ),
                    None => format!(
                        "{}: {}",
                        h["name"].as_str().unwrap(),
                        h["type"].as_str().unwrap()
                    ),
                })
                .collect();
            lines.push(format!("⊢ {}", goal["target"].as_str().unwrap()));
            assert_eq!(
                d["labels"][0]["message"].as_str().unwrap(),
                lines.join("\n"),
                "{name}: the goal's parts disagree with its label"
            );
        }
        serde_json::to_string_pretty(&diagnostics).unwrap()
    });
    for (name, json) in results {
        insta::assert_snapshot!(format!("goal_index__{name}"), json);
    }
}

/// Each lemma the index gives, pasted at the end of its example's file and
/// checked again, is a goal with the same hypotheses and target. A summary
/// of which goals have a lemma is snapshotted.
#[test]
fn lemmas_check_as_the_same_goal() {
    let dir = scratch("lemmas");
    let results = each_example(|name, text| {
        let index = index_of(&goals_dir(), &format!("{name}.sw"));
        let mut summary = Vec::new();
        for (i, d) in diagnostics(&index)
            .iter()
            .filter(|d| is_goal(d))
            .enumerate()
        {
            let goal = &d["goal"];
            let Some(lemma) = goal["lemma"].as_str() else {
                summary.push(format!("{name} goal {}: no lemma", i + 1));
                continue;
            };
            summary.push(format!("{name} goal {}: {lemma}", i + 1));
            let lemma_name = lemma.split([' ', ':']).nth(1).unwrap();
            let file = format!("{name}-{}.sw", i + 1);
            std::fs::write(dir.join(&file), format!("{text}\n{lemma}\n")).unwrap();
            let again = index_of(&dir, &file);
            let found: Vec<Value> = diagnostics(&again)
                .into_iter()
                .filter(|d| d["message"] == format!("in `{lemma_name}`"))
                .collect();
            assert_eq!(
                found.len(),
                1,
                "{name}: `{lemma}` gives no goal (or several):\n{again:#}"
            );
            assert!(is_goal(&found[0]), "{name}: `{lemma}`:\n{:#}", found[0]);
            assert_eq!(
                (&found[0]["goal"]["hypotheses"], &found[0]["goal"]["target"]),
                (&goal["hypotheses"], &goal["target"]),
                "{name}: `{lemma}` is another goal"
            );
            assert_eq!(found[0]["labels"][0]["message"], d["labels"][0]["message"]);
            // Its own lemma is itself, renamed.
            assert_eq!(
                found[0]["goal"]["lemma"].as_str().map(|l| l.replacen(
                    &format!("{lemma_name}Goal1"),
                    lemma_name,
                    1
                )),
                Some(lemma.to_string())
            );
        }
        summary
    });
    let summary: Vec<String> = results.into_iter().flat_map(|(_, s)| s).collect();
    let made = summary.iter().filter(|s| !s.ends_with("no lemma")).count();
    insta::assert_snapshot!(
        "goal_index__lemmas",
        format!(
            "{made} lemmas, {} goals without one\n\n{}",
            summary.len() - made,
            summary.join("\n")
        )
    );
}

/// A line of a goal longer than 400 characters is cut in the middle on the
/// command line, unless `--full-goals`; the index has it all.
#[test]
fn long_goal_lines_are_cut_in_the_middle() {
    let dir = scratch("long");
    let sum = "x + ".repeat(150);
    std::fs::write(
        dir.join("long.sw"),
        format!("theorem long (x: Nat): {sum}x = 1 := ?\n"),
    )
    .unwrap();
    // The index has the whole goal.
    let index = index_of(&dir, "long.sw");
    let goal = &index["diagnostics"][0];
    let target = goal["goal"]["target"].as_str().unwrap();
    assert_eq!(target, format!("{sum}x = 1"));
    let label = goal["labels"][0]["message"].as_str().unwrap();
    assert_eq!(label, format!("x: Nat\n⊢ {target}"));

    // The command line cuts its line in the middle, keeping 200 characters
    // each side; the short line isn't cut.
    let cut = String::from_utf8(stitchwort(&dir, &["check", "long.sw"]).stderr).unwrap();
    let left_out = target.chars().count() + "⊢ ".chars().count() - 400;
    assert!(
        cut.contains(&format!(
            "…[{left_out} characters left out; --full-goals shows them]…"
        )),
        "{cut}"
    );
    assert!(!cut.contains(&format!("⊢ {target}")), "{cut}");
    assert!(cut.contains("⊢ x + x + x"), "{cut}");
    assert!(cut.contains("+ x + x = 1\n"), "{cut}");
    assert!(cut.contains("╰── x: Nat\n"), "{cut}");

    let full =
        String::from_utf8(stitchwort(&dir, &["check", "--full-goals", "long.sw"]).stderr).unwrap();
    assert!(full.contains(&format!("⊢ {target}\n")), "{full}");
    assert!(!full.contains("left out"), "{full}");
}
