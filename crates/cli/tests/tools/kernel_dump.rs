//! `STITCHWORT_DUMP_KERNEL`: the type and value the kernel is given for one
//! declaration (crates/elab/src/kernel.rs). `STITCHWORT_BIG_READBACK`: every
//! read-back over a node count, with a backtrace (crates/core/src/budget.rs).

use std::process::Command;

#[test]
fn dumps_the_named_declarations_type_and_value_once() {
    let dir = std::env::temp_dir().join(format!("stitchwort-kernel-dump-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("dump.sw");
    std::fs::write(&path, "def double (n: Nat): Nat := n\n").expect("write source");

    let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["check", "--no-cache"])
        .arg(&path)
        .env("STITCHWORT_DUMP_KERNEL", "Main.double")
        .output()
        .expect("run stitchwort");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "check failed:\n{stderr}");
    assert!(
        stderr
            .lines()
            .any(|line| line == "kernel dump: Main.double"),
        "{stderr}"
    );
    assert!(stderr.contains("  type: Nat → Nat"), "{stderr}");
    assert!(stderr.contains("  value: "), "{stderr}");
    assert_eq!(
        stderr.matches("kernel dump: ").count(),
        1,
        "printed once:\n{stderr}"
    );
}

#[test]
fn reports_readbacks_over_the_given_node_count() {
    let dir = std::env::temp_dir().join(format!("stitchwort-big-readback-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("readback.sw");
    // Unfolding `big` reads its body back: four nodes a `replicate`, plus
    // the argument.
    let source = "import Std (List, Nat, Eq)\n\n\
         def replicate: Nat -> a -> List a\n  \
         | Zero, x => Nil\n  \
         | Succ n, x => Cons x (replicate n x)\n\n\
         opaque def big (n: Nat): List Nat := replicate 1 n\n\n\
         theorem t (n: Nat): big n = big n unfolding big := \
         rewrite (byComputing: big n = big n)\n";
    std::fs::write(&path, source).expect("write source");

    let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["check", "--no-cache"])
        .arg(&path)
        .env("STITCHWORT_BIG_READBACK", "1")
        .output()
        .expect("run stitchwort");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "check failed:\n{stderr}");
    assert!(
        stderr
            .lines()
            .any(|line| line.starts_with("big readback: ") && line.contains("nodes in Main.t")),
        "no report for Main.t:\n{stderr}"
    );
    // The report names the source line of the proof step (SW-4630): the
    // `theorem` line, 9.
    assert!(
        stderr
            .lines()
            .any(|line| line.starts_with("  at:") && line.contains("readback.sw:9:")),
        "no source position:\n{stderr}"
    );

    let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
        .args(["check", "--no-cache"])
        .arg(&path)
        .env_remove("STITCHWORT_BIG_READBACK")
        .output()
        .expect("run stitchwort");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(out.status.success(), "check failed:\n{stderr}");
    assert!(
        !stderr
            .lines()
            .any(|line| line.starts_with("big readback: ")),
        "reported with the variable unset:\n{stderr}"
    );
}

/// The steps of each declaration in `check --timings`'s "steps by phase"
/// table: the name, then the total and the five phase columns.
fn phase_rows(stderr: &str) -> Vec<(String, Vec<u64>)> {
    let mut lines = stderr
        .lines()
        .skip_while(|l| !l.starts_with("steps by phase"));
    let header = lines.next().expect("the phase table's header");
    for column in ["steps", "walk", "unify", "apply", "read-back", "other"] {
        assert!(header.contains(column), "{column} in {header}");
    }
    lines
        .take_while(|l| !l.is_empty())
        .map(|l| {
            // A label may hold spaces (a component's declarations), so the
            // six counts are taken from the right.
            let words: Vec<&str> = l.split_whitespace().collect();
            let (name, counts) = words.split_at(words.len() - 6);
            (
                name.join(" "),
                counts.iter().map(|w| w.parse().expect("a count")).collect(),
            )
        })
        .collect()
}

#[test]
fn step_phases_add_up_to_each_declarations_steps() {
    let dir = std::env::temp_dir().join(format!("stitchwort-step-phases-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("phases.sw");
    std::fs::write(
        &path,
        "import Std (List, Nat)\n\n\
         def twice (xs: List Nat): List Nat := List.append xs xs\n",
    )
    .expect("write source");
    let run = |phases: bool| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
        command
            .args(["check", "--no-cache", "--timings=all"])
            .arg(&path);
        if phases {
            command.env("STITCHWORT_STEP_PHASES", "1");
        }
        let out = command.output().expect("run stitchwort");
        let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
        assert!(out.status.success(), "check failed:\n{stderr}");
        stderr
    };

    let off = run(false);
    assert!(!off.contains("steps by phase"), "{off}");

    let on = run(true);
    let rows = phase_rows(&on);
    let twice = rows.iter().find(|(name, _)| name == "Main.twice");
    assert!(twice.is_some(), "Main.twice in\n{on}");
    for (name, columns) in &rows {
        assert_eq!(columns.len(), 6, "{name}: {columns:?}");
        assert_eq!(
            columns[1..].iter().sum::<u64>(),
            columns[0],
            "{name}'s phases sum to its steps"
        );
    }
    assert!(
        rows.iter().any(|(_, c)| c[1..5].iter().any(|&n| n > 0)),
        "some step is charged to a named phase:\n{on}"
    );
}

#[test]
fn no_project_cache_checks_the_project_afresh_without_touching_its_entry() {
    let base =
        std::env::temp_dir().join(format!("stitchwort-project-cache-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&base);
    let src = base.join("src");
    std::fs::create_dir_all(&src).expect("create project");
    std::fs::write(base.join("stitchwort.yaml"), "").expect("write config");
    std::fs::write(
        src.join("a.sw"),
        "namespace A\n\ndef x: Nat := 1\n\ntest \"x\" := x == 1\n",
    )
    .expect("write source");
    let check = |extra: &[&str]| {
        let out = Command::new(env!("CARGO_BIN_EXE_stitchwort"))
            .args(["check", "--timings=all"])
            .args(extra)
            .current_dir(&base)
            .output()
            .expect("run stitchwort");
        let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
        assert!(out.status.success(), "check failed:\n{stderr}");
        stderr
    };
    let cold = check(&[]);
    assert!(!cold.contains("A (cached)"), "{cold}");
    let warm = check(&[]);
    assert!(warm.contains("A (cached)"), "{warm}");

    let fresh = check(&["--no-project-cache"]);
    assert!(!fresh.contains("A (cached)"), "A checked afresh:\n{fresh}");
    // The project's entry is untouched: the next plain check still hits it.
    assert!(check(&[]).contains("A (cached)"));
}
