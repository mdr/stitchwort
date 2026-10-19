//! One namespace over several files (docs/proposals/multi-file.md §4.4,
//! §12): what `Session::load_namespace` checks as one module.

use stitchwort_core::DefId;
use stitchwort_core::hash::{ContentHash, def_hash};
use stitchwort_driver::driver::{Cache, Outcome, Session};
use stitchwort_syntax::{Diagnostic, Severity};

fn load(files: &[(&str, &str)]) -> Session {
    let mut session = Session::new();
    if let Err(errors) = session.load_namespace(files) {
        panic!("{errors:#?}");
    }
    session
}

fn errors(files: &[(&str, &str)]) -> (Session, Vec<Diagnostic>) {
    let mut session = Session::new();
    let errors = session
        .load_namespace(files)
        .expect_err("should be refused")
        .into_iter()
        .filter(|d| d.severity == Severity::Error)
        .collect();
    (session, errors)
}

fn file_of<'a>(session: &'a Session, d: &Diagnostic, label: usize) -> &'a str {
    &session.sources.get(d.labels[label].span.file).name
}

fn passes(session: &Session) {
    let results = session.run_tests(&Cache::disabled());
    assert!(!results.is_empty());
    for result in &results {
        assert_eq!(result.outcome, Outcome::Passed, "{}", result.name);
    }
}

fn hash_of_path(session: &Session, path: &str) -> ContentHash {
    let g = &session.elab.globals;
    let id = g
        .defs
        .iter()
        .position(|d| &*d.path == path)
        .unwrap_or_else(|| panic!("no definition `{path}`"));
    def_hash(g, DefId(id)).unwrap().expect("checked")
}

#[test]
fn mutual_recursion_and_dot_notation_across_files() {
    let session = load(&[
        (
            "a.sw",
            "namespace Shapes\n\n\
             type Shape: Type =\n  | Square (side: Nat)\n  | Rect (width: Nat) (height: Nat)\n\n\
             def isEven: Nat -> Bool\n  | Zero => True\n  | Succ n => isOdd n\n",
        ),
        (
            "b.sw",
            "namespace Shapes\n\n\
             def isOdd: Nat -> Bool\n  | Zero => False\n  | Succ n => isEven n\n\n\
             def Shape.area: Shape -> Nat\n  | Square s => s * s\n  | Rect w h => w * h\n",
        ),
        (
            "c.sw",
            "namespace Shapes\n\n\
             test \"area\" := (Rect 2 3).area == 6\n\
             test \"odd\" := isOdd 3 && isEven 4\n",
        ),
    ]);
    passes(&session);
    assert_eq!(session.elab.tests.len(), 2);
}

#[test]
fn an_import_in_one_file_isnt_visible_in_a_sibling() {
    let (session, errors) = errors(&[
        (
            "a.sw",
            "namespace N\n\nimport List (map)\n\ndef f(): List Nat := map (\\x => x) [1]\n",
        ),
        (
            "b.sw",
            "namespace N\n\ndef g(): List Nat := map (\\x => x) [1]\n",
        ),
    ]);
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert_eq!(errors[0].code, "E-UNKNOWN-NAME");
    assert_eq!(file_of(&session, &errors[0], 0), "b.sw");
}

#[test]
fn a_duplicate_across_files_names_both() {
    let (session, errors) = errors(&[
        ("a.sw", "namespace N\n\ndef f(): Nat := 1\n"),
        ("b.sw", "namespace N\n\ndef f(): Nat := 2\n"),
    ]);
    assert_eq!(errors.len(), 1, "{errors:#?}");
    let d = &errors[0];
    assert_eq!(d.code, "E-DUPLICATE");
    let mut files = vec![file_of(&session, d, 0), file_of(&session, d, 1)];
    files.sort_unstable();
    assert_eq!(files, ["a.sw", "b.sw"]);
}

#[test]
fn an_import_clashing_with_a_sibling_declaration() {
    let (session, errors) = errors(&[
        (
            "a.sw",
            "namespace N\n\nimport List (map)\n\ndef f(): Nat := 1\n",
        ),
        ("b.sw", "namespace N\n\ndef map(): Nat := 2\n"),
    ]);
    assert_eq!(errors.len(), 1, "{errors:#?}");
    let d = &errors[0];
    assert_eq!(d.code, "E-IMPORT-CLASH");
    assert!(d.message.contains("another file of namespace N"), "{d:?}");
    assert_eq!(file_of(&session, d, 0), "a.sw");
    assert_eq!(file_of(&session, d, 1), "b.sw");
}

#[test]
fn auto_doesnt_use_a_sibling_files_procedure() {
    let procedure = "namespace N\n\n\
         type Token: Prop =\n  | MkToken\n\n\
         def decToken: Decidable Token := Yes MkToken\n\n\
         def needsToken: [auto t: Token] -> Nat := 1\n";
    let use_it = "def client: Nat := needsToken\n\ntest \"client\" := client == 1\n";
    let (_, errors) = errors(&[
        ("a.sw", procedure),
        ("b.sw", &format!("namespace N\n\n{use_it}")),
    ]);
    assert_eq!(errors.len(), 1, "{errors:#?}");
    let d = &errors[0];
    assert_eq!(d.code, "E-AUTO-NONE");
    assert!(
        d.notes
            .iter()
            .any(|n| n.contains("is in another file of") && n.contains("a.sw")),
        "{d:#?}"
    );
    // The same use below the procedure, in its own file.
    passes(&load(&[("a.sw", &format!("{procedure}\n{use_it}"))]));
}

#[test]
fn tests_run_by_file_then_source_order() {
    let session = load(&[
        (
            "b.sw",
            "namespace N\n\ntest \"b2\" := True\ntest \"b1\" := True\n",
        ),
        ("a.sw", "namespace N\n\ntest \"a1\" := True\n"),
    ]);
    let names: Vec<&str> = session.elab.tests.iter().map(|t| t.name.as_str()).collect();
    assert_eq!(names, ["a1", "b2", "b1"]);
    assert!(session.elab.tests.iter().all(|t| t.namespace == "N"));
}

const PING: &str = "def ping (n: Nat): Nat := match n with
  | Zero => Zero
  | Succ k => pong k
";
const PONG: &str = "def pong (n: Nat): Nat := match n with
  | Zero => Zero
  | Succ k => ping k
";

#[test]
fn file_order_doesnt_change_hashes() {
    let file = |body: &str| format!("namespace Shapes\n\n{body}");
    let (ping, pong) = (file(PING), file(PONG));
    let hashes = |files: &[(&str, &str)]| {
        let session = load(files);
        (
            hash_of_path(&session, "Shapes.ping"),
            hash_of_path(&session, "Shapes.pong"),
        )
    };
    let reference = hashes(&[("x.sw", &ping), ("y.sw", &pong)]);
    assert_eq!(hashes(&[("y.sw", &pong), ("x.sw", &ping)]), reference);
    assert_eq!(hashes(&[("x.sw", &pong), ("y.sw", &ping)]), reference);
    assert_eq!(hashes(&[("y.sw", &ping), ("x.sw", &pong)]), reference);
    assert_ne!(reference.0, reference.1);
}

#[test]
fn abilities_in_two_files_hash_the_same_in_any_order() {
    let ask = "namespace N\n\nability Ask where\n  ask : () -> {Ask} Nat\n";
    let log = "namespace N\n\nability Log where\n  say : Nat -> {Log} ()\n";
    let both = "namespace N\n\ndef both(): {Log, Ask} Nat :=\n  say 1\n  ask()\n";
    let hash = |files: &[(&str, &str)]| hash_of_path(&load(files), "N.both");
    let reference = hash(&[("x.sw", ask), ("y.sw", log), ("z.sw", both)]);
    assert_eq!(
        hash(&[("z.sw", both), ("y.sw", log), ("x.sw", ask)]),
        reference
    );
    assert_eq!(
        hash(&[("x.sw", log), ("y.sw", ask), ("z.sw", both)]),
        reference
    );
}

/// After a single file is loaded, an expression typed in sees the file's
/// imports (file 0's, as before).
#[test]
fn imports_still_work_for_eval_after_a_single_file() {
    let mut session = Session::new();
    session
        .load(
            "test.sw",
            "import List (map)\n\ndef double(n: Nat): Nat := n + n\n",
        )
        .unwrap();
    let expr = session
        .parse_expression("<eval>", "map double [1, 2]")
        .unwrap();
    session.elab.infer_expr(&expr).unwrap();
}
