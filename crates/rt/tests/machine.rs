//! The machine (docs/proposals/fast-runtime.md, stage 2) against the
//! reference evaluator, which is the oracle: every runnable `main` of the
//! examples and the AoC project prints the same on both, with the same
//! input, and ends the same way; every `test` of those programs and of the
//! library has the same outcome; and numbers near the machine-word limits,
//! deep recursion and long lists work.

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

const STACK: usize = 256 * 1024 * 1024;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// What a run printed, and how it ended: `Ok` or the error's message.
type Run = (String, Result<(), String>);

fn reference(session: &Session, main: &Main, input: &[u8]) -> Run {
    let mut output = Vec::new();
    let result = session.run_main(main, &mut &input[..], &mut output);
    (
        String::from_utf8_lossy(&output).into_owned(),
        result.map_err(|e| e.to_string()),
    )
}

fn machine(program: &Program, limits: Limits, input: &[u8]) -> Run {
    let mut output = Vec::new();
    let result = stitchwort_rt::run_main(program, limits, &mut &input[..], &mut output);
    (
        String::from_utf8_lossy(&output).into_owned(),
        result.map_err(|e| e.to_string()),
    )
}

fn lowered(session: &Session, main: &Main, what: &str) -> Program {
    let g = &session.elab.globals;
    lower_main(g, session.elab.limits, main.term(), main.row)
        .unwrap_or_else(|e| panic!("{what}: lowering main: {e:?}"))
}

/// Runs `main` both ways with `input`: the same output, and the same end.
fn same_both_ways(session: &Session, main: &Main, program: &Program, input: &[u8], what: &str) {
    let expected = reference(session, main, input);
    let got = machine(program, Limits::from_core(session.elab.limits), input);
    assert_eq!(
        got,
        expected,
        "{what} with input {:?}: the machine disagrees with `stitchwort run`",
        String::from_utf8_lossy(input)
    );
}

/// Runs the program's own tests on the machine and compares each outcome
/// with the reference evaluator's (`stitchwort test --reference`). How
/// many ran.
fn run_tests(session: &Session, program: &Program, what: &str, library: bool) -> usize {
    run_tests_where(session, program, what, library, |_| true)
}

/// [`run_tests`], for the tests `keep` keeps.
fn run_tests_where(
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
        .tests
        .iter()
        .filter(|t| t.library == library && (library || keep(t)));
    let mut m = Machine::new(program, Limits::from_core(session.elab.limits));
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
fn everything(session: &Session, what: &str) -> Program {
    let g = &session.elab.globals;
    let ids: Vec<DefId> = (0..g.defs.len())
        .map(DefId)
        .filter(|id| g.def(*id).body().is_some() || g.builtins.primitive(*id).is_some())
        .collect();
    lower_definitions(g, session.elab.limits, &ids)
        .unwrap_or_else(|e| panic!("{what}: lowering every definition: {e:?}"))
}

fn sw_files(dir: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .expect("read examples")
        .map(|e| e.expect("read entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "sw"))
        .collect();
    files.sort();
    files
}

fn load_file(path: &Path) -> (Session, String) {
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

/// Every example's `main` prints the same on the machine as on the
/// reference evaluator, with the inputs `run_js.rs` uses; and every test
/// of every example has the same outcome.
#[test]
fn examples_agree() {
    let mut paths = sw_files(&root().join("examples/accept"));
    paths.extend(sw_files(&root().join("examples/extract")));
    // Each file on the thread pool: (whether it has a `main`, its tests run).
    let per_file = par_map(STACK, &paths, |path| {
        let what = path.display().to_string();
        let (mut session, text) = load_file(path);
        let tests = run_tests(&session, &everything(&session, &what), &what, false);
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
    assert!(tests >= 500, "{tests}");
}

/// The library's own tests (many of them of the text and integer natives)
/// have the same outcomes on the machine.
#[test]
fn library_tests_agree() {
    with_stack(STACK, || {
        let session = Session::with_library_tests();
        let program = everything(&session, "the library");
        let ran = run_tests(&session, &program, "the library", true);
        eprintln!("{ran} library tests agree");
        assert!(ran >= 70, "{ran}");
    });
}

fn aoc() -> Session {
    let dir = root().join("aoc");
    let mut session = Session::for_stack(STACK);
    session
        .load_project(&DiskFiles { root: dir }, "aoc", &Target::Everything)
        .unwrap_or_else(|e| panic!("aoc doesn't check: {e:?}"));
    session
}

/// The answers each AoC day prints on its real input, as
/// `crates/cli/tests/aoc_answers.rs` checks `stitchwort run` prints them.
const AOC_ANSWERS: &[(&str, &str, &str, &str)] = &[
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
];

/// Every AoC day, on its real input, prints the known answers on the
/// machine (`aoc_answers.rs`), and on its real and example inputs prints
/// what `stitchwort run` prints. The AoC project's tests agree too.
#[test]
fn aoc_agrees() {
    with_stack(STACK, || {
        let mut session = aoc();
        let what = "aoc";
        // The real-input tests are left out: on the reference evaluator they
        // take minutes (SW-412), and each day's `main` is compared on the
        // real input below.
        let ran = run_tests_where(&session, &everything(&session, what), what, false, |t| {
            !t.name.starts_with("real input")
        });
        eprintln!("{ran} AoC tests agree");
        // A corpus sweep: every other day below the full tier.
        for (year, day, part1, part2) in tier_sample(AOC_ANSWERS.iter().collect(), 2) {
            let name = format!("Aoc.Year{year}.Day{day}.main");
            let main = session
                .main_named(&name, "aoc")
                .unwrap_or_else(|e| panic!("{name}: {e:?}"));
            let program = lowered(&session, &main, &name);
            let limits = Limits::from_core(session.elab.limits);
            let input = std::fs::read(root().join(format!("aoc/inputs/{year}/day{day}.txt")))
                .expect("the puzzle input");
            let start = std::time::Instant::now();
            let got = machine(&program, limits, &input);
            eprintln!("{name}: {:?} on the machine", start.elapsed());
            assert_eq!(
                got,
                (format!("Part 1: {part1}\nPart 2: {part2}\n"), Ok(())),
                "{name} on the machine"
            );
            same_both_ways(&session, &main, &program, &input, &name);
            let example = std::fs::read(root().join(format!("aoc/examples/{year}/day{day}.txt")))
                .expect("the example input");
            same_both_ways(&session, &main, &program, &example, &name);
        }
    });
}

/// A small program's `main`, run both ways with `input`.
fn both_ways(source: &str, input: &[u8]) -> Run {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("test.sw", source)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("main");
        let program = lowered(&session, &main, "test.sw");
        let expected = reference(&session, &main, input);
        let got = machine(&program, Limits::from_core(session.elab.limits), input);
        assert_eq!(got, expected, "the machine disagrees with `stitchwort run`");
        got
    })
}

/// A small program's `main`, on the machine only (for what the reference
/// evaluator takes too long over).
fn on_the_machine(source: &str, limits: Limits) -> Run {
    on_the_machine_with(source, limits, b"")
}

/// A small program's `main`, on the machine only, with `input`.
fn on_the_machine_with(source: &str, limits: Limits, input: &[u8]) -> Run {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("test.sw", source)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("main");
        let program = lowered(&session, &main, "test.sw");
        machine(&program, limits, input)
    })
}

/// Arithmetic around 2^63 and 2^64, where numbers stop fitting a machine
/// word: each operation's result printed, both ways.
#[test]
fn numbers_near_the_word_limits() {
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

/// A list of a million numbers, built and summed by non-tail recursion:
/// a million frames deep, on the machine's own stack, then freed.
#[test]
fn deep_recursion_over_a_long_list() {
    let (out, result) = on_the_machine(
        r#"
import Std (Nat, Text)

def build: Nat -> List Nat
  | 0 => []
  | Succ n => Cons (n + 1) (build n)

def total: List Nat -> Nat
  | [] => 0
  | [x, ..rest] => x + total rest

def main(): {IO} () := IO.print (Nat.toText (total (build 1000000)))
"#,
        Limits::default(),
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out, "500000500000\n");
}

/// Recursing more deeply than the frame limit allows is `E-RESOURCE`, not a
/// crash.
#[test]
fn recursing_too_deeply_runs_out() {
    let (out, result) = on_the_machine(
        r#"
import Std (Nat, Text)

def count: Nat -> Nat
  | 0 => 0
  | Succ n => 1 + count n

def main(): {IO} () :=
  IO.print "before"
  IO.print (Nat.toText (count 100000))
"#,
        Limits {
            steps: u64::MAX,
            frames: 10_000,
        },
    );
    assert_eq!(out, "before\n");
    assert_eq!(
        result,
        Err("ran out of resources: it recursed more deeply than allowed".into())
    );
}

/// A loop in tail position runs in constant space, however long.
#[test]
fn tail_calls_dont_grow_the_stack() {
    let (out, result) = on_the_machine(
        r#"
import Std (Nat, Text)

def loop: Nat -> Nat -> Nat
  | 0, acc => acc
  | Succ n, acc => loop n (acc + 2)

def main(): {IO} () := IO.print (Nat.toText (loop 3000000 0))
"#,
        Limits {
            steps: u64::MAX,
            frames: 100,
        },
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out, "6000000\n");
}

/// `Text.take`, `Text.drop` and `Text.contains` count Unicode scalar values,
/// not bytes, and agree with their definitions on the edge cases: empty
/// texts, astral characters, characters either side of the surrogates,
/// counts of 0, the length, more than the length and beyond a machine word,
/// and the empty needle.
#[test]
fn text_take_drop_and_contains_agree() {
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

/// On a million characters, each of `Text.take`, `Text.drop` and
/// `Text.contains` is one native step, not one step per character as its
/// definition would be.
#[test]
fn text_take_drop_and_contains_are_native() {
    let input = "\u{1F600}".repeat(999_999) + "b";
    let (out, result) = on_the_machine_with(
        r#"
import Std (Nat, Text, IO)

def main(): {IO} () :=
  let input := IO.readAll()
  let rest := Text.drop input 500000
  IO.print (Nat.toText (Text.length (Text.take rest 250000)))
  IO.print (Nat.toText (Text.length rest))
  IO.print (if Text.contains input "\u{1F600}b" then "found" else "missing")
  IO.print (if Text.contains input "ba" then "found" else "missing")
"#,
        Limits {
            steps: 10_000,
            frames: 100,
        },
        input.as_bytes(),
    );
    assert_eq!(result, Ok(()));
    assert_eq!(out, "250000\n500000\nfound\nmissing\n");
}

/// Reuse in place (stage 4) only ever changes a cell nobody else can see: a
/// list that's still used after a `map`, `filter` or sort over it, one a
/// closure captured, one a constant holds, and one bound twice, is
/// unchanged, both ways.
#[test]
fn reuse_leaves_shared_values_alone() {
    let (out, result) = both_ways(
        r#"
import Std (Nat, Text, List)

def show (xs: List Nat): Text := Text.join (xs.map Nat.toText) ','

def kept: List Nat := [5, 3, 9, 1]

def main(): {IO} () :=
  let xs := List.range 6
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
  let fresh := (List.range 4).map (x => x + 1)
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
#[test]
fn known_constructors_keep_their_type() {
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

/// `map` builds each new cell in the one it takes apart, when that one is
/// uniquely owned: its code (the empty-row variant, for a pure callback)
/// reuses the cell.
#[test]
fn map_reuses_its_cells() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load(
                "test.sw",
                "import Std (Nat, Text, List)\n\
                 def main(): {IO} () := IO.print (Text.join ((List.range 3).map Nat.toText) ',')\n",
            )
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("main");
        let program = lowered(&session, &main, "test.sw");
        let image = stitchwort_rt::code::compile(&program);
        let map = program
            .globals
            .iter()
            .position(|g| &*g.name == "Std.List.map[empty]")
            .expect("map is used");
        let code = &image.codes[image.global_code[map].expect("map has code") as usize];
        assert!(
            code.instrs
                .iter()
                .any(|i| matches!(i, stitchwort_rt::code::Instr::CtorReuse { .. })),
            "{:?}",
            code.instrs
        );
    });
}

/// Partial application, over-application and closures, both ways.
#[test]
fn functions_as_values() {
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
#[test]
fn bench_programs_agree() {
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
#[test]
fn running_out_of_resources_is_reported_alike() {
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
  | Succ n => 1 + deep n

def main(): {IO} () :=
  IO.print "before"
  let line := IO.readAll ()
  IO.print (Nat.toText (if Text.length line == 1 then spin 5000000 else deep 100000))
"#,
            )
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        session.elab.limits.work = 1_000_000;
        session.elab.limits.frames = 10_000;
        let main = session.main().expect("main");
        let program = lowered(&session, &main, "test.sw");
        for input in [&b"x"[..], b"xy"] {
            let expected = reference(&session, &main, input);
            let got = machine(&program, Limits::from_core(session.elab.limits), input);
            assert_eq!(got.0, "before\n");
            assert_eq!(got.0, expected.0);
            for run in [&got, &expected] {
                let message = run.1.as_ref().expect_err("it runs out");
                assert!(message.starts_with("ran out of resources: "), "{message}");
            }
        }
    });
}
