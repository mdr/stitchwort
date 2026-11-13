//! The differential cases of the machine (docs/proposals/fast-runtime.md,
//! stage 2) against the reference evaluator, which is the oracle: every
//! runnable `main` of the examples and the AoC project prints the same on
//! both, with the same input, and ends the same way; numbers near the
//! machine-word limits, lists and handlers behave the same.
//!
//! The cases are plain functions over a backend (`crate::backend`), shared
//! by two test binaries: `stitchwort-rt`'s (`machine.rs`, on the machine)
//! and `stitchwort-native`'s (`machine_native.rs`, on Cranelift code;
//! `stitchwort-rt` can't dev-depend on `stitchwort-native`, which depends on
//! it). `differential_tests!` lists them as tests in each.

#![allow(dead_code)] // each binary uses some of these

use std::path::{Path, PathBuf};
use std::rc::Rc;

use stitchwort_core::DefId;
use stitchwort_driver::driver::{Cache, Outcome, Session, par_map, tier_sample, with_stack};
use stitchwort_driver::project::{DiskFiles, Target};
use stitchwort_driver::run::Main;
use stitchwort_elab::TestDecl;
use stitchwort_rt::ir::GlobalId;
use stitchwort_rt::value::Value;
use stitchwort_rt::{Limits, Machine, Program, lower_definitions, lower_main};

pub const STACK: usize = 256 * 1024 * 1024;

pub fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// What a run printed, and how it ended: `Ok` or the error's message.
pub type Run = (String, Result<(), String>);

pub fn reference(session: &Session, main: &Main, input: &[u8]) -> Run {
    let mut output = Vec::new();
    let result = session.run_main(main, &mut &input[..], &mut output);
    (
        String::from_utf8_lossy(&output).into_owned(),
        result.map_err(|e| e.to_string()),
    )
}

/// `program`'s `main` on the backend under test (`crate::backend`).
pub fn on_backend(program: &Program, limits: Limits, input: &[u8]) -> Run {
    crate::backend::run(program, limits, input)
}

pub fn lowered(session: &Session, main: &Main, what: &str) -> Program {
    let g = &session.elab.ev();
    lower_main(g, session.elab.options.limits, main.term(), main.row)
        .unwrap_or_else(|e| panic!("{what}: lowering main: {e:?}"))
}

/// Runs `main` both ways with `input`: the same output, and the same end.
pub fn same_both_ways(session: &Session, main: &Main, program: &Program, input: &[u8], what: &str) {
    let expected = reference(session, main, input);
    let got = on_backend(
        program,
        Limits::from_core(session.elab.options.limits),
        input,
    );
    assert_eq!(
        got,
        expected,
        "{what} with input {:?}: the {} disagrees with `stitchwort run`",
        String::from_utf8_lossy(input),
        crate::backend::NAME
    );
}

/// Runs the program's own tests on the machine and compares each outcome
/// with the reference evaluator's (`stitchwort test --reference`). How
/// many ran.
pub fn run_tests(session: &Session, program: &Program, what: &str, library: bool) -> usize {
    run_tests_where(session, program, what, library, |_| true)
}

/// [`run_tests`], for the tests `keep` keeps.
pub fn run_tests_where(
    session: &Session,
    program: &Program,
    what: &str,
    library: bool,
    keep: impl Fn(&TestDecl) -> bool + Copy,
) -> usize {
    let results = if library {
        session.run_library_tests(&Cache::disabled())
    } else {
        session.run_tests_where(&Cache::disabled(), keep)
    };
    let decls = session
        .elab
        .tests()
        .iter()
        .filter(|t| t.library == library && (library || keep(t)));
    let mut m = Machine::new(program, Limits::from_core(session.elab.options.limits));
    let true_ = program.shapes.true_;
    let mut ran = 0;
    for (decl, result) in decls.zip(results) {
        assert_eq!(decl.name, result.name);
        let expected = match result.outcome {
            Outcome::Passed => true,
            Outcome::Failed => false,
            Outcome::OutOfResources(_) => continue,
        };
        // A test that runs partial code (D1183) is a `Delay`, which
        // `stitchwort test` steps as `run` steps a partial `main`; `global`
        // only evaluates it to that `Delay`.
        if session.elab.is_partial(decl.def).unwrap_or(false) {
            continue;
        }
        let Some(g) = program.globals.iter().position(|g| g.def == decl.def) else {
            panic!("{what}: test {:?} wasn't lowered", decl.name);
        };
        let g = GlobalId(u32::try_from(g).unwrap());
        m.reset_steps();
        match m.global(g) {
            Ok(Value::Tag(t)) => assert_eq!(
                t == true_,
                expected,
                "{what}: test {:?} on the machine disagrees with `stitchwort test`",
                decl.name
            ),
            Ok(other) => panic!("{what}: test {:?} gave {other:?}", decl.name),
            Err(e) => panic!("{what}: test {:?} ran out on the machine: {e}", decl.name),
        }
        ran += 1;
    }
    ran
}

/// Every definition with a body (or a primitive), lowered together.
pub fn everything(session: &Session, what: &str) -> Program {
    let g = &session.elab.ev();
    // Not what relies on an open goal: it may reach the goal's assumption,
    // which has nothing to run.
    let ids: Vec<DefId> = (0..g.env.defs().len())
        .map(DefId)
        .filter(|id| !session.elab.is_unfinished(*id))
        .filter(|id| g.def(*id).body().is_some() || g.env.builtins().primitive(*id).is_some())
        .collect();
    lower_definitions(g, session.elab.options.limits, &ids)
        .unwrap_or_else(|e| panic!("{what}: lowering every definition: {e:?}"))
}

pub fn sw_files(dir: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("read examples")
        .map(|e| e.expect("read entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "sw"))
        .collect();
    files.sort();
    files
}

pub fn load_file(path: &Path) -> (Session, String) {
    let text = std::fs::read_to_string(path).expect("read example");
    let name = path.file_name().unwrap().to_string_lossy().to_string();
    let mut session = Session::for_stack(STACK);
    session.include_in_folder(
        Rc::new(DiskFiles {
            root: path.parent().unwrap().to_path_buf(),
        }),
        &name,
    );
    session
        .load(&name, &text)
        .unwrap_or_else(|e| panic!("{} doesn't check: {e:?}", path.display()));
    (session, text)
}

/// A small program's `main`, run both ways with `input`.
pub fn both_ways(source: &str, input: &[u8]) -> Run {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("test.sw", source)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("main");
        let program = lowered(&session, &main, "test.sw");
        let expected = reference(&session, &main, input);
        let got = on_backend(
            &program,
            Limits::from_core(session.elab.options.limits),
            input,
        );
        assert_eq!(
            got,
            expected,
            "the {} disagrees with `stitchwort run`",
            crate::backend::NAME
        );
        got
    })
}

/// Functions that add to a call of themselves (`Succ (f x)`, `x + f xs`,
/// on `Nat` and `Int`, through a `let`, with a branch that is a plain tail
/// call), and two that don't qualify (a product, a sum with two calls).
pub const CALLS_PLUS_A_NUMBER: &str = r#"
import Std (Int, List, Nat, Text)

def size: List Nat -> Nat
  | [] => 0
  | [x, ..rest] => Succ (size rest)

def total: List Nat -> Nat
  | [] => 0
  | [x, ..rest] => x + total rest

def bumped: List Nat -> Nat
  | [] => 5
  | [x, ..rest] =>
    let r := bumped rest
    r + 2 + x

def evens: List Nat -> Nat
  | [] => 0
  | [x, ..rest] => if x % 2 == 0 then Succ (Succ (evens rest)) else evens rest

def signed: List Nat -> Int
  | [] => -7
  | [x, ..rest] => signed rest + (Nat.toInt x - 3)

def product: List Nat -> Nat
  | [] => 1
  | [x, ..rest] => (x % 3 + 1) * product rest

def fib: Nat -> Nat
  | 0 => 0
  | 1 => 1
  | Succ (Succ n) => fib (Succ n) + fib n

def run (n: Nat): Text :=
  let xs := List.range 0 n
  Text.join [Nat.toText (size xs), Nat.toText (total xs), Nat.toText (bumped xs),
    Nat.toText (evens xs), Int.toText (signed xs), Nat.toText (product (xs.take 12)),
    Nat.toText (fib 15)] ' '
"#;

/// The parts of the AoC project that the AoC sweeps check one at a time,
/// side by side on [`par_map`]: `Aoc.Common`, and each day with the
/// namespaces under it (`Aoc.Year2024.Day01` with its `Tests`, `Spec` and
/// `Proofs`). Together they are the whole project. One session for the whole
/// project ran its tests, and each day's `main`, on one thread: 5,953 s for
/// `aoc_agrees` and 5,606 s for `every_aoc_main_lowers` in a loaded full
/// tier (SW-2962), most of it in the reference evaluator.
///
/// `AOC_PARTS=<text>,<text>` keeps only the parts whose names contain one
/// of them, to run a few days of a sweep:
/// `STITCHWORT_TIER=full AOC_PARTS=Year2024.Day01 task test:one -- aoc_agrees`.
pub fn aoc_parts() -> Vec<String> {
    let dir = root().join("aoc/src/Aoc");
    let names = |dir: &Path| -> Vec<String> {
        let mut names: Vec<String> = std::fs::read_dir(dir)
            .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
            .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
            .collect();
        names.sort();
        names
    };
    let mut parts = Vec::new();
    for top in names(&dir) {
        if top == "Common" {
            parts.push("Aoc.Common".to_string());
            continue;
        }
        // A file or folder elsewhere would be in no part.
        assert!(top.starts_with("Year"), "aoc/src/Aoc/{top}: in no part");
        for day in names(&dir.join(&top)) {
            assert!(
                day.starts_with("Day"),
                "aoc/src/Aoc/{top}/{day}: in no part"
            );
            parts.push(format!("Aoc.{top}.{day}"));
        }
    }
    assert!(parts.len() > 40, "{parts:?}");
    if let Ok(only) = std::env::var("AOC_PARTS") {
        parts.retain(|part| only.split(',').any(|o| part.contains(o)));
    }
    parts
}

/// A session with `part` of the AoC project ([`aoc_parts`]) checked, and
/// what it uses.
pub fn aoc_part(part: &str) -> Session {
    let mut session = Session::for_stack(STACK);
    session
        .load_project(
            &DiskFiles {
                root: root().join("aoc"),
            },
            "aoc",
            &Target::Subtrees(vec![part.to_string()]),
        )
        .unwrap_or_else(|e| panic!("{part} doesn't check: {e:?}"));
    session
}

/// Whether `test` is declared in `part` or a namespace under it, rather than
/// in a part it uses.
pub fn in_part(test: &TestDecl, part: &str) -> bool {
    test.namespace == part || test.namespace.starts_with(&format!("{part}."))
}

/// The answers each AoC day prints on its real input, as
/// `crates/cli/tests/running/aoc_answers.rs` checks `stitchwort run` prints them.
pub const AOC_ANSWERS: &[(&str, &str, &str, &str)] = &[
    ("2025", "01", "1076", "6379"),
    ("2025", "02", "16793817782", "27469417404"),
    ("2025", "03", "17263", "170731717900423"),
    ("2025", "04", "1397", "8758"),
    ("2025", "05", "525", "333892124923577"),
    ("2025", "06", "4722948564882", "9581313737063"),
    ("2025", "07", "1594", "15650261281478"),
    ("2024", "01", "2066446", "24931009"),
    ("2024", "02", "534", "577"),
    ("2024", "03", "174960292", "56275602"),
    ("2024", "04", "2524", "1873"),
    ("2024", "05", "4569", "6456"),
    ("2024", "06", "4967", "1789"),
    ("2024", "07", "66343330034722", "637696070419031"),
    ("2024", "08", "344", "1182"),
    ("2024", "09", "6242766523059", "6272188244509"),
    ("2024", "10", "461", "875"),
];

/// Every example's `main` prints the same on the machine as on the
/// reference evaluator, with the inputs `run_js.rs` uses; and every test
/// of every example has the same outcome.
pub fn examples_agree() {
    let mut paths = sw_files(&root().join("examples/accept"));
    paths.extend(sw_files(&root().join("examples/extract")));
    // Each file on the thread pool: (whether it has a `main`, its tests run).
    let per_file = par_map(STACK, &paths, |path| {
        let what = path.display().to_string();
        let (mut session, text) = load_file(path);
        // The tests run on the machine (`Machine::global`); native code has no
        // such entry yet (docs/reviews/SW-2535-native-default-plan.md, §3).
        let tests = if crate::backend::NATIVE {
            0
        } else {
            run_tests(&session, &everything(&session, &what), &what, false)
        };
        // A `(run: random)` example prints a different number each run.
        if (text.contains("def main()") || text.contains("def main ()"))
            && !text.contains("(run: random)")
        {
            let main = session
                .main()
                .unwrap_or_else(|e| panic!("{what}: main: {e:?}"));
            let program = lowered(&session, &main, &what);
            for input in [&b""[..], b"Ada\n3\n4\n\n", b"one\ntwo\r\nthree"] {
                same_both_ways(&session, &main, &program, input, &what);
            }
            return (1, tests);
        }
        (0, tests)
    });
    let mains: usize = per_file.iter().map(|(m, _)| m).sum();
    let tests: usize = per_file.iter().map(|(_, t)| t).sum();
    eprintln!("{mains} mains and {tests} tests agree");
    assert!(mains >= 9, "{mains}");
    assert!(crate::backend::NATIVE || tests >= 500, "{tests}");
}

/// Arithmetic around 2^63 and 2^64, where numbers stop fitting a machine
/// word: each operation's result printed, both ways.
pub fn numbers_near_the_word_limits() {
    let (out, result) = both_ways(
        r#"
import Std (Nat, Text, Int)

def p63: Nat := 9223372036854775808
def p64: Nat := 18446744073709551616
def nats: List Nat := [0, 1, 2, p63 - 1, p63, p63 + 1, p64 - 1, p64, p64 + 1, p64 * p64]

def ints: List Int :=
  [0, 1, -1, Nat.toInt p63 - 1, -(Nat.toInt p63), -(Nat.toInt p63) - 1, Nat.toInt p63,
   Nat.toInt p64 - 1, Nat.toInt p64, -(Nat.toInt p64), Nat.toInt (p64 * p64), 7, -7, 2, -2]

def showNat (n: Nat): Text := Nat.toText n
def showInt (n: Int): Text := Int.toText n

def natPair (a: Nat) (b: Nat): Text :=
  Text.join [showNat (a + b), showNat (a - b), showNat (a * b),
    if a <= b then "le" else "gt", if a == b then "eq" else "ne", if a < b then "lt" else "ge"] ' '

def natOne (a: Nat): Text :=
  Text.join [showNat (a / 3), showNat (a % 3), showNat (a / 9223372036854775808),
    showNat (a % 9223372036854775807), showNat (a / 18446744073709551617),
    showNat (Nat.toInt a |> Int.toNat), matchNat a] ' '

def intPair (a: Int) (b: Int): Text :=
  Text.join [showInt (a + b), showInt (a - b), showInt (a * b),
    if a <= b then "le" else "gt", if a < b then "lt" else "ge", if a == b then "eq" else "ne"] ' '

def intOne (a: Int): Text :=
  Text.join [showInt (-a), showNat (Int.natAbs a), showInt (Int.abs a), showNat (Int.toNat a),
    showInt (Int.sign a), showInt (a / 7), showInt (a % 7), showInt (a / -7), showInt (a % -7),
    showInt (Int.tdiv a 7), showInt (Int.tmod a (-7)), showInt (Int.fdiv a (-7)),
    showInt (Int.fmod a 7), showInt (a / 18446744073709551617), showInt (a % -9223372036854775809),
    showNat (Int.modNat a 9223372036854775809),
    match Int.toNatChecked a with
      | Some n => showNat n
      | None => "none",
    match a with
      | OfNat n => "ofNat " ++ showNat n
      | NegSucc n => "negSucc " ++ showNat n] ' '

def matchNat: Nat -> Text
  | 0 => "zero"
  | Succ n => "succ " ++ showNat n

def printAll: List Text -> {IO} ()
  | [] => ()
  | [t, ..rest] =>
    IO.print t
    printAll rest

def main(): {IO} () :=
  printAll (nats.map (a => Text.join (nats.map (b => natPair a b)) ','))
  printAll (nats.map natOne)
  printAll (ints.map (a => Text.join (ints.map (b => intPair a b)) ','))
  printAll (ints.map intOne)
  IO.print (match Text.toInt "-9223372036854775809" with
    | Some n => showInt (n + 1)
    | None => "none")
  IO.print (match Text.toNat "18446744073709551616" with
    | Some n => showNat (n - 1)
    | None => "none")
"#,
        b"",
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out.lines().count(), 2 * 10 + 2 * 15 + 2, "{out}");
}

/// Dividing by 0 gives 0 and leaves the dividend as the remainder, for
/// `Nat` and every `Int` division, on words and beyond them, the same on
/// the machine as in the definitions.
pub fn dividing_by_zero() {
    let (out, result) = both_ways(
        r#"
import Std (Nat, Text, Int)

def big: Nat := 18446744073709551616 * 3 + 5

def nats: List Nat := [0, 7, big]

def ints: List Int := [0, 7, -7, Nat.toInt big, -(Nat.toInt big)]

def zero (n: Nat): Nat := n - n

def natLine (n: Nat): Text :=
  Text.join [Nat.toText (n / zero n), Nat.toText (n % zero n), Nat.toText (Nat.ceilDiv n (zero n))] ' '

def intLine (a: Int): Text :=
  let d := a - a
  Text.join [Int.toText (a / d), Int.toText (a % d), Int.toText (Int.tdiv a d), Int.toText (Int.tmod a d),
    Int.toText (Int.fdiv a d), Int.toText (Int.fmod a d), Nat.toText (Int.modNat a (Int.natAbs d))] ' '

def main(): {IO} () :=
  IO.print (Text.join (nats.map natLine) ',')
  IO.print (Text.join (ints.map intLine) ',')
"#,
        b"",
    );
    assert_eq!(result, Ok(()));
    let big = "55340232221128654853";
    assert_eq!(
        out,
        format!(
            "0 0 0,0 7 0,0 {big} 0\n0 0 0 0 0 0 0,0 7 0 7 0 7 7,0 -7 0 -7 0 -7 0,\
             0 {big} 0 {big} 0 {big} {big},0 -{big} 0 -{big} 0 -{big} 0\n"
        )
    );
}

/// [`CALLS_PLUS_A_NUMBER`] gives the same numbers on the machine as on the
/// reference evaluator, which doesn't run them as loops; the sums are
/// loops, and the product and `fib` aren't.
pub fn calls_plus_a_number_agree() {
    let source = format!("{CALLS_PLUS_A_NUMBER}\ndef main(): {{IO}} () := IO.print (run 50)\n");
    let (out, result) = both_ways(&source, b"");
    assert_eq!(result, Ok(()));
    assert_eq!(out, "50 1225 1330 50 1068 1296 610\n");
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session.load("test.sw", &source).expect("checks");
        let main = session.main().expect("main");
        let program = lowered(&session, &main, "test.sw");
        let loops: Vec<&str> = program
            .globals
            .iter()
            .filter_map(|g| g.name.strip_suffix("[sum]")?.strip_prefix("Main."))
            .collect();
        assert_eq!(loops, ["size", "total", "bumped", "evens", "signed"]);
    });
}

/// The values a loop of cells builds are immutable to the program: a list
/// from `map` is shared and used as often as any other, and matching on it,
/// taking it apart and building from it behave as before.
pub fn a_list_built_as_a_loop_is_an_ordinary_value() {
    let (out, result) = both_ways(
        r#"
import Std (List, Nat, Text)

def double (xs: List Nat): List Nat := xs.map (x => x * 2)
def evens (xs: List Nat): List Nat := xs.filter (x => x % 4 == 0)
def tree: Nat -> List Nat -> List (List Nat)
  | 0, xs => []
  | Succ n, xs => Cons (double xs) (tree n (evens xs))
def show (xs: List Nat): Text := Text.join (xs.map Nat.toText) ','

def main(): {IO} () :=
  let base := List.range 0 12
  let doubled := double base
  let both := doubled ++ doubled
  IO.print (Text.join [show doubled, show both, show (evens doubled),
    show (List.concat (tree 3 base)), show (List.zip doubled base |> .map (p => p.fst + p.snd))] ' ')
"#,
        b"",
    );
    assert_eq!(result, Ok(()));
    assert!(out.starts_with("0,2,4,6,8,10,12,14,16,18,20,22 "), "{out}");
}

/// `map` with a callback that performs an operation, under a handler that
/// resumes twice, gives each resumption its own list: the effectful `map`
/// is not run as a loop of cells, and the pure one's cells are not shared
/// between the two runs.
pub fn map_under_a_handler_that_resumes_twice() {
    let (out, result) = both_ways(
        r#"
import Std (List, Nat, Text)

ability Choose where
  choose: () → {Choose} Bool

def allResults (prog: () → {Choose | e} a): {e} List a :=
  handle prog() with
    | return x => [x]
    | choose u, k => List.append (k True) (k False)

def pick (x: Nat): {Choose} Nat := if choose() then x else x + 100

def weigh (xs: List Nat): Nat := xs.foldLeft 0 (total x => total * 1000 + x)

def twice (xs: List Nat): List Nat := xs.map (x => x * 2)

def main(): {IO} () :=
  let results := allResults (u => List.range 0 3 |> .map pick)
  let again := allResults (u => twice (List.range 0 3 |> .map pick))
  let shown := (xs: List (List Nat)) => Text.join (xs.map (ys => Nat.toText (weigh ys))) ','
  IO.print (Text.join [shown results, shown again] ' ')
"#,
        b"",
    );
    assert_eq!(result, Ok(()));
    assert_eq!(
        out,
        "1002,1102,101002,101102,100001002,100001102,100101002,100101102 \
         2004,2204,202004,202204,200002004,200002204,200202004,200202204\n"
    );
}

/// `Text.take`, `Text.drop` and `Text.contains` count Unicode scalar values,
/// not bytes, and agree with their definitions on the edge cases: empty
/// texts, astral characters, characters either side of the surrogates,
/// counts of 0, the length, more than the length and beyond a machine word,
/// and the empty needle.
pub fn text_take_drop_and_contains_agree() {
    let (out, result) = both_ways(
        r#"
import Std (Nat, Text, List)

def texts: List Text := ["", "a", "abc", "\u{1F600}", "a\u{1F600}b", "\u{D7FF}\u{E000}\u{10000}\u{10FFFF}", "h\u{E9}llo"]
def counts: List Nat := [0, 1, 2, 3, 4, 18446744073709551616]
def needles: List Text := ["", "a", "b", "bc", "\u{1F600}", "\u{1F600}b", "\u{E000}", "\u{10FFFF}", "\u{E9}l", "abcd"]

def show (t: Text): Text := "[" ++ t ++ "]"

def bool (b: Bool): Text := if b then "T" else "F"

def printAll: List Text -> {IO} ()
  | [] => ()
  | [t, ..rest] =>
    IO.print t
    printAll rest

def main(): {IO} () :=
  printAll (texts.map (t => Text.join (counts.map (n => show (Text.take t n) ++ show (Text.drop t n))) ' '))
  printAll (texts.map (t => Text.join (needles.map (needle => bool (Text.contains t needle))) ' '))
"#,
        b"",
    );
    assert_eq!(result, Ok(()));
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(lines.len(), 14, "{out}");
    assert_eq!(
        lines[4],
        "[][a\u{1F600}b] [a][\u{1F600}b] [a\u{1F600}][b] [a\u{1F600}b][] [a\u{1F600}b][] [a\u{1F600}b][]"
    );
    assert_eq!(lines[7], "T F F F F F F F F F");
}

/// Reuse in place (stage 4) only ever changes a cell nobody else can see: a
/// list that's still used after a `map`, `filter` or sort over it, one a
/// closure captured, one a constant holds, and one bound twice, is
/// unchanged, both ways.
pub fn reuse_leaves_shared_values_alone() {
    let (out, result) = both_ways(
        r#"
import Std (Nat, Text, List)

def show (xs: List Nat): Text := Text.join (xs.map Nat.toText) ','

def kept: List Nat := [5, 3, 9, 1]

def main(): {IO} () :=
  let xs := List.range 0 6
  let ys := xs.map (x => x * 10)
  IO.print (show ys)
  IO.print (show xs)
  let evens := xs.filter (x => x % 2 == 0)
  IO.print (show evens ++ " " ++ show xs)
  let sorted := List.sortBy kept Nat.compare
  IO.print (show sorted ++ " " ++ show kept)
  let f := (n: Nat) => show (xs.map (x => x + n))
  IO.print (f 1 ++ " " ++ f 2 ++ " " ++ show xs)
  let pair := (xs, xs)
  IO.print (show (pair.fst.map (x => x + 100)) ++ " " ++ show pair.snd)
  let fresh := (List.range 0 4).map (x => x + 1)
  IO.print (show (fresh.map (x => x * 2)))
"#,
        b"",
    );
    assert_eq!(result, Ok(()));
    assert_eq!(
        out,
        "0,10,20,30,40,50\n0,1,2,3,4,5\n0,2,4 0,1,2,3,4,5\n1,3,5,9 5,3,9,1\n\
         1,2,3,4,5,6 2,3,4,5,6,7 0,1,2,3,4,5\n100,101,102,103,104,105 0,1,2,3,4,5\n2,4,6,8\n"
    );
}

/// The simplifier treats only a `Bool` as a truth value: `if c then x else
/// y`, with `x` known to be `Some …` and `y` known to be `None` (the same
/// tags as `True` and `False`), is not `c`.
pub fn known_constructors_keep_their_type() {
    let (out, result) = both_ways(
        r#"
import Std (Nat, Text, Option)

def pick (c: Bool) (x: Option Nat) (y: Option Nat): Option Nat :=
  match x with
    | Some n =>
      match y with
        | None => if c then x else y
        | Some m => None
    | None => None

def show (o: Option Nat): Text :=
  match o with
    | Some n => "Some " ++ Nat.toText n
    | None => "None"

def main(): {IO} () :=
  IO.print (show (pick True (Some 3) None))
  IO.print (show (pick False (Some 3) None))
"#,
        b"",
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out, "Some 3\nNone\n");
}

/// A lambda that captures nothing is one shared closure, read by
/// `StaticClosure`, while one that captures a variable is built each time;
/// shared closures stored in data and applied many times give the same
/// answers.
pub fn capture_free_lambdas_are_shared() {
    let source = "import Std (Nat, Text, List)\n\
         def pair (n: Nat): List (Nat -> Nat) := [x => x + 1, x => x + n]\n\
         def apply (fs: List (Nat -> Nat)) (x: Nat): Nat :=\n\
         \x20 match fs with\n\
         \x20   | [] => x\n\
         \x20   | [f, ..rest] => apply rest (f x)\n\
         def loop (i: Nat) (acc: Nat): Nat :=\n\
         \x20 match i with\n\
         \x20   | Zero => acc\n\
         \x20   | Succ k => loop k (apply (pair k) acc)\n\
         def main(): {IO} () := IO.print (Nat.toText (loop 50 0))\n";
    let (out, result) = both_ways(source, b"");
    assert_eq!(result, Ok(()));
    assert_eq!(out, "1275\n");
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("test.sw", source)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("main");
        let program = lowered(&session, &main, "test.sw");
        let image = stitchwort_rt::code::compile(&program);
        let pair = program
            .globals
            .iter()
            .position(|g| &*g.name == "Main.pair")
            .expect("pair is used");
        let code = &image.codes[image.global_code[pair].expect("pair has code") as usize];
        let count = |want: fn(&stitchwort_rt::code::Instr) -> bool| {
            code.instrs.iter().filter(|i| want(i)).count()
        };
        use stitchwort_rt::code::Instr;
        assert_eq!(
            count(|i| matches!(i, Instr::StaticClosure { .. })),
            1,
            "{:?}",
            code.instrs
        );
        assert_eq!(
            count(|i| matches!(i, Instr::Closure { .. })),
            1,
            "{:?}",
            code.instrs
        );
    });
}

/// Partial application, over-application and closures, both ways.
pub fn functions_as_values() {
    let (out, result) = both_ways(
        r#"
import Std (Nat, Text)

def add3 (a: Nat) (b: Nat) (c: Nat): Nat := a + b + c
def twice (f: Nat -> Nat) (x: Nat): Nat := f (f x)
def pick (b: Bool): Nat -> Nat -> Nat := if b then (x y => x) else (x y => y)
def compose (f: Nat -> Nat) (g: Nat -> Nat): Nat -> Nat := x => f (g x)

def main(): {IO} () :=
  let add1 := add3 1
  let add12 := add1 2
  IO.print (Nat.toText (add12 3))
  IO.print (Nat.toText (twice (add3 1 1) 0))
  IO.print (Nat.toText (pick True 7 8 + pick False 7 8))
  IO.print (Nat.toText ((compose add12 (twice add12)) 0))
  IO.print (Text.join ([1, 2, 3].map (x => Nat.toText (add3 x x x))) ',')
  IO.print (Text.fold "abc" "!" (c acc => Text.fromList [c] ++ acc))
"#,
        b"",
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out, "6\n4\n15\n9\n3,6,9\nabc!\n");
}

/// The programs of `crates/bench` that have a `main` (`programs.rs`), run
/// both ways.
pub fn bench_programs_agree() {
    let (out, result) = both_ways(
        "
import Std (Nat)

def printMany : Nat -> {IO} ()
  | Zero   => ()
  | Succ n =>
    IO.print (Nat.toText n)
    printMany n

def main () : {IO} () := printMany 20000
",
        b"",
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out.lines().count(), 20_000);
    let (out, result) = both_ways(
        "
import Std (IO, Int, Nat, Text)

type Pos = { at : Nat, ok : at < 100 }

def wrap (x : Int) : Pos := { at = Int.modNat x 100, ok = Int.modNatLt x 100 }

def walk : List Text -> Pos -> Nat
  | Nil,       p => p.at
  | Cons t ts, p => walk ts (wrap (p.at.toInt + Nat.toInt (Text.length t * 37)))

def main () : {IO} () := IO.print (Nat.toText (walk (IO.readAllLines ()) (wrap 50)))
",
        "L68\n".repeat(200).as_bytes(),
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out, "50\n");
}

/// A program that runs out of resources is reported as `E-RESOURCE` by both
/// runners, after the same output, though not necessarily at the same
/// point or with the same words (the machine counts frames entered, the
/// reference evaluator its own steps).
pub fn running_out_of_resources_is_reported_alike() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load(
                "test.sw",
                r#"
import Std (Nat, Text)

def spin: Nat -> Nat
  | 0 => 0
  | Succ n => spin n

def deep: Nat -> Nat
  | 0 => 0
  | Succ n => 2 * deep n

def main(): {IO} () :=
  IO.print "before"
  let line := IO.readAll ()
  IO.print (Nat.toText (if Text.length line == 1 then spin 5000000 else deep 100000))
"#,
            )
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        session.elab.options.limits.work = 1_000_000;
        session.elab.options.limits.frames = 10_000;
        let main = session.main().expect("main");
        let program = lowered(&session, &main, "test.sw");
        for input in [&b"x"[..], b"xy"] {
            let expected = reference(&session, &main, input);
            let got = on_backend(
                &program,
                Limits::from_core(session.elab.options.limits),
                input,
            );
            assert_eq!(got.0, "before\n");
            assert_eq!(got.0, expected.0);
            for run in [&got, &expected] {
                let message = run.1.as_ref().expect_err("it runs out");
                assert!(message.starts_with("ran out of resources: "), "{message}");
            }
        }
    });
}

/// Every AoC day, on its real input, prints the known answers on the
/// machine (`aoc_answers.rs`), and on its example input prints what the
/// reference evaluator prints. The AoC project's tests agree too. Each part
/// of the project ([`aoc_parts`]) in a session of its own, side by side.
///
/// The real input runs only on the machine: the reference evaluator takes
/// minutes there on the heavy days (2021 day 5: over 120 s against 8.7 s on
/// the machine), and the known answers check that run (D3540).
pub fn aoc_agrees() {
    // Full tier only: with its sample of days it took 38 minutes in the
    // daily tier (31 Oct 2026, docs/testing.md); SW-839's fast lowering
    // check is to take its place there.
    if !stitchwort_driver::driver::full_tier("aoc_agrees") {
        return;
    }
    let parts = aoc_parts();
    // A corpus sweep: every other day below the full tier.
    let answers: Vec<_> = tier_sample(AOC_ANSWERS.iter().collect(), 2);
    if std::env::var_os("AOC_PARTS").is_none() {
        for (year, day, _, _) in &answers {
            let part = format!("Aoc.Year{year}.Day{day}");
            assert!(parts.contains(&part), "{part}: not a part of the project");
        }
    }
    let ran = par_map(STACK, &parts, |part| {
        let mut session = aoc_part(part);
        let mut ran = 0;
        // The real-input tests are left out: on the reference evaluator they
        // take minutes (SW-412), and each day's `main` is compared on the
        // real input below.
        if !crate::backend::NATIVE {
            ran = run_tests_where(&session, &everything(&session, part), part, false, |t| {
                in_part(t, part) && !t.name.starts_with("real input")
            });
        }
        let answered = answers
            .iter()
            .filter(|(year, day, _, _)| *part == format!("Aoc.Year{year}.Day{day}"));
        for (year, day, part1, part2) in answered {
            let name = format!("{part}.main");
            let main = session
                .main_named(&name, "aoc")
                .unwrap_or_else(|e| panic!("{name}: {e:?}"));
            let program = lowered(&session, &main, &name);
            let limits = Limits::from_core(session.elab.options.limits);
            let input = std::fs::read(root().join(format!("aoc/inputs/{year}/day{day}.txt")))
                .expect("the puzzle input");
            let start = std::time::Instant::now();
            let got = on_backend(&program, limits, &input);
            eprintln!(
                "{name}: {:?} on the {}",
                start.elapsed(),
                crate::backend::NAME
            );
            assert_eq!(
                got,
                (format!("Part 1: {part1}\nPart 2: {part2}\n"), Ok(())),
                "{name} on the {}",
                crate::backend::NAME
            );
            // The real input isn't compared with the reference evaluator:
            // it takes minutes there on the heavy days, and the known
            // answers above check the machine's run (D3540). Both
            // evaluators still run the example input.
            let example = std::fs::read(root().join(format!("aoc/examples/{year}/day{day}.txt")))
                .expect("the example input");
            same_both_ways(&session, &main, &program, &example, &name);
        }
        ran
    });
    if !crate::backend::NATIVE {
        eprintln!("{} AoC tests agree", ran.iter().sum::<usize>());
    }
}

/// Lists the differential cases as tests, each with the attributes given
/// (the native copy's are `ignore`d unless asked for).
macro_rules! differential_tests {
    ($($attr:meta),* $(,)?) => {
        differential_tests!(@names [$($attr),*]
            examples_agree
            aoc_agrees
            numbers_near_the_word_limits
            dividing_by_zero
            calls_plus_a_number_agree
            a_list_built_as_a_loop_is_an_ordinary_value
            map_under_a_handler_that_resumes_twice
            text_take_drop_and_contains_agree
            reuse_leaves_shared_values_alone
            known_constructors_keep_their_type
            capture_free_lambdas_are_shared
            functions_as_values
            bench_programs_agree
            running_out_of_resources_is_reported_alike
        );
    };
    (@names $attrs:tt $($name:ident)*) => {
        $(differential_tests!(@one $attrs $name);)*
    };
    (@one [$($attr:meta),*] $name:ident) => {
        #[test]
        $(#[$attr])*
        fn $name() {
            $crate::differential::$name()
        }
    };
}
