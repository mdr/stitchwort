//! Lowering to the erased IR (docs/proposals/fast-runtime.md, stage 1):
//! every `main` and every definition of the examples, the example projects
//! and the AoC project lowers without error, and a few small programs lower
//! to the IR in the snapshots.

use std::path::{Path, PathBuf};
use std::rc::Rc;

use stitchwort_core::DefId;
use stitchwort_driver::driver::{Cache, Outcome, Session, with_stack};
use stitchwort_driver::project::{DiskFiles, Target};
use stitchwort_rt::{Program, lower_definitions, lower_main};

mod interp;

const STACK: usize = 256 * 1024 * 1024;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn well_formed(program: &Program, what: &str) {
    if let Err(e) = program.validate() {
        panic!("{what}: the IR isn't well formed: {e}\n{program}");
    }
    let _ = program.to_string();
}

/// Every definition with a body (or a primitive), lowered together.
fn lower_everything(session: &Session, what: &str) -> usize {
    let g = &session.elab.globals;
    let ids: Vec<DefId> = (0..g.defs.len())
        .map(DefId)
        .filter(|id| g.def(*id).body().is_some() || g.builtins.primitive(*id).is_some())
        .collect();
    let program = lower_definitions(g, session.elab.limits, &ids)
        .unwrap_or_else(|e| panic!("{what}: lowering every definition: {e:?}"));
    // Well formed, and printable.
    well_formed(&program, what);
    run_tests(session, &program, what, false)
}

/// Runs the program's own tests on the IR, with the reference interpreter
/// in `interp/`, and compares each outcome with the reference evaluator's
/// (`stitchwort test`). A test that uses partial computations, which the
/// interpreter doesn't run, is skipped. How many tests ran.
fn run_tests(session: &Session, program: &Program, what: &str, library: bool) -> usize {
    let results = if library {
        session.run_library_tests(&Cache::disabled())
    } else {
        session.run_tests(&Cache::disabled())
    };
    let decls = session.elab.tests.iter().filter(|t| t.library == library);
    let interp = interp::Interp::new(program);
    let mut ran = 0;
    for (decl, result) in decls.zip(results) {
        assert_eq!(decl.name, result.name);
        let expected = match result.outcome {
            Outcome::Passed => true,
            Outcome::Failed => false,
            Outcome::OutOfResources(_) => continue,
        };
        let Some(g) = program.globals.iter().position(|g| g.def == decl.def) else {
            panic!("{what}: test {:?} wasn't lowered", decl.name);
        };
        let g = stitchwort_rt::ir::GlobalId(u32::try_from(g).unwrap());
        match interp.global(g) {
            Ok(interp::V::Ctor(c, _)) => assert_eq!(
                c == 1,
                expected,
                "{what}: test {:?} on the IR disagrees with `stitchwort test`",
                decl.name
            ),
            Ok(other) => panic!("{what}: test {:?} gave {other:?}", decl.name),
            Err(e) if e.starts_with("unsupported") => continue,
            Err(e) => panic!("{what}: test {:?} failed on the IR: {e}", decl.name),
        }
        ran += 1;
    }
    ran
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

/// Examples with quotients, which the runtime doesn't lower until stage 1.3
/// of docs/proposals/map-equality.md (§14.1): lowering them is refused
/// (`E-RUNTIME`) rather than guessed at. Empty again once it does.
const NOT_LOWERED_YET: &[&str] = &["quot-forms.sw"];

fn is_main(name: &str) -> bool {
    name == "main" || name.ends_with(".main")
}

/// Each example file on its own: its `main`, if it has one, and every
/// definition.
#[test]
fn every_example_lowers() {
    with_stack(STACK, || {
        let mut mains = 0;
        let mut files = 0;
        let mut tests = 0;
        for folder in ["examples/accept", "examples/extract"] {
            for path in sw_files(&root().join(folder)) {
                let what = path.display().to_string();
                let text = std::fs::read_to_string(&path).expect("read example");
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
                    .unwrap_or_else(|e| panic!("{what} doesn't check: {e:?}"));
                if NOT_LOWERED_YET.contains(&name.as_str()) {
                    let g = &session.elab.globals;
                    let ids: Vec<DefId> = (0..g.defs.len())
                        .map(DefId)
                        .filter(|id| g.def(*id).body().is_some())
                        .collect();
                    match lower_definitions(g, session.elab.limits, &ids) {
                        Err(e) if e.code == "E-RUNTIME" && e.message.contains("yet") => {}
                        Err(e) => panic!("{what}: refused for another reason: {e:?}"),
                        Ok(_) => panic!("{what}: lowered; take it off `NOT_LOWERED_YET`"),
                    }
                    continue;
                }
                files += 1;
                tests += lower_everything(&session, &what);
                // A runnable `main`, as `run_js.rs` finds them (some
                // examples have a `main` that's a value).
                if text.contains("def main()") || text.contains("def main ()") {
                    let main = session
                        .main()
                        .unwrap_or_else(|e| panic!("{what}: main: {e:?}"));
                    let g = &session.elab.globals;
                    let program = lower_main(g, session.elab.limits, main.term())
                        .unwrap_or_else(|e| panic!("{what}: lowering main: {e:?}"));
                    well_formed(&program, &what);
                    mains += 1;
                }
            }
        }
        eprintln!(
            "lowered {mains} mains and everything in {files} files; ran {tests} tests on the IR"
        );
        assert!(files > 100, "{files}");
        assert!(mains >= 9, "{mains}");
    });
}

/// Loads the project in `dir`, then lowers every `main` it has (each as
/// `stitchwort run` would run it) and every definition. How many mains.
fn lower_project(dir: &Path) -> usize {
    let name = dir.file_name().unwrap().to_string_lossy().to_string();
    let mut session = Session::for_stack(STACK);
    let files = DiskFiles {
        root: dir.to_path_buf(),
    };
    session
        .load_project(&files, &name, &Target::Everything)
        .unwrap_or_else(|e| panic!("{name} doesn't check: {e:?}"));
    let tests = lower_everything(&session, &name);
    eprintln!("{name}: ran {tests} tests on the IR");
    let g = &session.elab.globals;
    let mains: Vec<String> = g
        .defs
        .iter()
        .filter(|d| is_main(&d.name) && !d.path.starts_with("Std."))
        .map(|d| d.name.to_string())
        .collect();
    for main_name in &mains {
        let main = session
            .main_named(main_name, &name)
            .unwrap_or_else(|e| panic!("{name}: {main_name}: {e:?}"));
        let g = &session.elab.globals;
        let program = lower_main(g, session.elab.limits, main.term())
            .unwrap_or_else(|e| panic!("{name}: lowering {main_name}: {e:?}"));
        well_formed(&program, main_name);
    }
    mains.len()
}

#[test]
fn every_example_project_lowers() {
    with_stack(STACK, || {
        let dir = root().join("examples/projects/accept");
        let mut dirs: Vec<PathBuf> = std::fs::read_dir(&dir)
            .unwrap()
            .map(|e| e.unwrap().path())
            .filter(|p| p.is_dir())
            .collect();
        dirs.sort();
        let mains: usize = dirs.iter().map(|d| lower_project(d)).sum();
        eprintln!("lowered {mains} mains in {} projects", dirs.len());
        assert!(!dirs.is_empty());
    });
}

#[test]
fn every_aoc_main_lowers() {
    with_stack(STACK, || {
        let mains = lower_project(&root().join("aoc"));
        eprintln!("lowered {mains} AoC mains");
        assert!(mains >= 7, "{mains}");
    });
}

/// The whole library lowers, and its own tests (many of them of the text
/// and integer natives) give the same outcomes on the IR.
#[test]
fn the_library_lowers_and_its_tests_agree() {
    with_stack(STACK, || {
        let session = Session::with_library_tests();
        let g = &session.elab.globals;
        let ids: Vec<DefId> = (0..g.defs.len())
            .map(DefId)
            .filter(|id| g.def(*id).body().is_some() || g.builtins.primitive(*id).is_some())
            .collect();
        let program = lower_definitions(g, session.elab.limits, &ids).expect("lowers");
        well_formed(&program, "the library");
        let ran = run_tests(&session, &program, "the library", true);
        eprintln!("ran {ran} library tests on the IR");
        assert!(ran >= 70, "{ran}");
    });
}

/// The IR of a small program's `main`.
fn ir(source: &str) -> String {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("test.sw", source)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("main");
        let g = &session.elab.globals;
        let program = lower_main(g, session.elab.limits, main.term())
            .unwrap_or_else(|e| panic!("lowering: {e:?}"));
        well_formed(&program, "main");
        program.to_string()
    })
}

#[test]
fn recursion_on_lists() {
    insta::assert_snapshot!(ir(r#"
import Std (Nat, Text, Int)
def total: List Nat -> Nat
  | [] => 0
  | [x, ..rest] => x + total rest

def double: List Nat -> List Nat
  | [] => []
  | [x, ..rest] => Cons (x * 2) (double rest)

def main(): {IO} () := IO.print (Nat.toText (total (double [1, 2, 3])))
"#));
}

#[test]
fn a_record() {
    insta::assert_snapshot!(ir(r#"
import Std (Nat, Text, Int)
type Point = { x: Nat, y: Nat }

def swap (p: Point): Point := { x = p.y, y = p.x }

def main(): {IO} () :=
  let p := swap { x = 1, y = 2 }
  IO.print (Nat.toText p.x)
"#));
}

#[test]
fn an_effectful_main_with_io() {
    insta::assert_snapshot!(ir(r#"
import Std (Nat, Text, Int)
def greet (name: Text): {IO} () := IO.print ("hello " ++ name)

def main(): {IO} () :=
  match IO.readLine() with
    | Some name => greet name
    | None => IO.print "nobody"
"#));
}

#[test]
fn text_and_int_natives() {
    insta::assert_snapshot!(ir(r#"
import Std (Nat, Text, Int)
def signed (t: Text): Int :=
  match Text.toInt t with
    | Some n => n * -3 + 7
    | None => 0

def main(): {IO} () :=
  let parts := Text.split ',' "12,-5,x"
  IO.print (Text.join ' ' (parts.map (t => Int.toText (signed t))))
  IO.print (if Text.length "abc" == 3 && "a" < "b" then "yes" else "no")
"#));
}

/// `==` and `<` on each type with native values.
#[test]
fn comparisons() {
    insta::assert_snapshot!(ir(r#"
import Std (Nat, Text, Int)
def nats (a: Nat) (b: Nat): Bool := a == b || a < b
def ints (a: Int) (b: Int): Bool := a == b || a < b
def chars (a: Char) (b: Char): Bool := a == b
def texts (a: Text) (b: Text): Bool := a == b

def main(): {IO} () :=
  if nats 1 2 && ints 3 (-4) && chars 'a' 'b' && texts "x" "y" then IO.print "yes" else ()
"#));
}

#[test]
fn a_local_def() {
    insta::assert_snapshot!(ir(r#"
import Std (Nat, Text, Int)
def sumTo (n: Nat): Nat :=
  def go: Nat -> Nat -> Nat
    | 0, acc => acc
    | Succ k, acc => go k (acc + k + 1)
  go n 0

def main(): {IO} () := IO.print (Nat.toText (sumTo 10))
"#));
}

#[test]
fn a_lambda_capturing_variables() {
    insta::assert_snapshot!(ir(r#"
import Std (Nat, Text, Int)
def scale (a: Nat) (b: Nat) (xs: List Nat): List Nat := xs.map (x => a * x + b)

def main(): {IO} () :=
  let k := 3
  IO.print (Nat.toText ((scale k 1 [1, 2]).foldLeft (acc x => acc + x + k) 0))
"#));
}

/// A definition with `decreasing` runs the recursion as written: its fuel,
/// the fuelled `%go` and the measure aren't part of the program
/// (docs/proposals/well-founded-recursion.md §6.5).
#[test]
fn decreasing_drops_the_fuel() {
    let ir = ir(r#"
import Std (Nat)
def gcd (a: Nat) (b: Nat): Nat
  decreasing b
:=
  if h: b = 0 then a else gcd b (a % b) [decreasing := Nat.modLess a b h]

def main(): {IO} () := IO.print (Nat.toText (gcd 12 18))
"#);
    assert!(ir.contains("gcd.%step"), "{ir}");
    assert!(!ir.contains("%go"), "the fuelled helper is lowered:\n{ir}");
}

/// The proof of a measure's decrease can be a parameter (`shrinks`): the
/// `[decreasing := shrinks x h]` at the recursive call applies an erased
/// variable, which is erased, not applied.
#[test]
fn decreasing_proof_parameter_is_not_applied() {
    let ir = ir(r#"
import Std (IO, Nat, Void)
def until (x: Nat) (step: Nat -> Nat) (measure: Nat -> Nat)
    (shrinks: (y: Nat) -> Not (step y = y) -> measure (step y) < measure y): Nat
  decreasing measure x
:=
  if h: step x = x then x else until (step x) step measure shrinks [decreasing := shrinks x h]

def main(): {IO} () := IO.print (Nat.toText (until 3 (n => n) (n => n) (y h => Void.exfalso (h rfl))))
"#);
    assert!(!ir.contains("apply erased"), "{ir}");
}

/// A function that recurses only inside a closure (accessibility as data,
/// `AccIntro (m => accFuel k m ..)`) isn't inlined at a call with a literal:
/// that unrolled it once per unit of the literal, so a 13-digit number took
/// minutes to lower and run (SW-253). Here an 8-digit one would take 12 s.
#[test]
fn recursion_inside_a_closure_is_not_unrolled() {
    let ir = ir(r#"
import Std (Void, Bool, List, Nat)

type AccLt: Nat -> Type =
  | AccIntro [n: Nat] (below: (m: Nat) -> m < n -> AccLt m): AccLt n

def accFuel: (k: Nat) -> (n: Nat) -> n < k -> AccLt n
  | Zero,   n, h => Void.absurd (Bool.falseNotTrue h)
  | Succ k, n, h => AccIntro (m hm => accFuel k m (Nat.leTrans (Succ m) n k hm h))

def digitsGo (n: Nat) (acc: List Nat) (a: AccLt n): List Nat :=
  match a with
    | AccIntro below =>
      if e: Nat.leq n 9 = False
      then digitsGo (n / 10) (Cons (n % 10) acc) (below (n / 10) (Nat.divTenLess n e))
      else Cons n acc

def digits (n: Nat): List Nat := digitsGo n Nil (accFuel (Succ n) n (Nat.leRefl n))

def main(): {IO} () := IO.print "${(digits 12345678).length}"
"#);
    let unrolled = ir.matches("AccIntro").count();
    assert!(unrolled < 10, "{unrolled} AccIntro in the IR of main");
}
