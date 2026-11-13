//! Lowering to the erased IR (docs/proposals/fast-runtime.md, stage 1):
//! every `main` and every definition of the examples, the example projects
//! and the AoC project lowers without error, and a few small programs lower
//! to the IR in the snapshots.

use std::path::{Path, PathBuf};
use std::rc::Rc;

use stitchwort_core::{DataId, DefId, Term};
use stitchwort_driver::driver::{Cache, Outcome, Session, par_map, with_stack};
use stitchwort_driver::project::{DiskFiles, Target};
use stitchwort_rt::{Program, lower_definitions, lower_main};

use crate::interp;

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

/// Every definition with a body (or a primitive), lowered together, and
/// the program's tests run on the IR.
fn lower_everything(session: &Session, what: &str) -> usize {
    lower_everything_where(session, what, |_| true)
}

/// [`lower_everything`], running only the tests `keep` keeps.
fn lower_everything_where(
    session: &Session,
    what: &str,
    keep: impl Fn(&stitchwort_elab::TestDecl) -> bool + Copy,
) -> usize {
    let g = &session.elab.ev();
    // Not what relies on an open goal: it may reach the goal's assumption,
    // which has nothing to run.
    let ids: Vec<DefId> = (0..g.env.defs().len())
        .map(DefId)
        .filter(|id| !session.elab.is_unfinished(*id))
        .filter(|id| g.def(*id).body().is_some() || g.env.builtins().primitive(*id).is_some())
        .collect();
    let program = lower_definitions(g, session.elab.options.limits, &ids)
        .unwrap_or_else(|e| panic!("{what}: lowering every definition: {e:?}"));
    // Well formed, and printable.
    well_formed(&program, what);
    run_tests(session, &program, what, false, keep)
}

/// Runs the program's own tests on the IR, with the reference interpreter
/// in `interp/`, and compares each outcome with the reference evaluator's
/// (`stitchwort test`). A test that uses partial computations, which the
/// interpreter doesn't run, is skipped. How many tests ran.
fn run_tests(
    session: &Session,
    program: &Program,
    what: &str,
    library: bool,
    keep: impl Fn(&stitchwort_elab::TestDecl) -> bool + Copy,
) -> usize {
    // The real-input tests are left out, as in `machine.rs`'s `aoc_agrees`:
    // on the reference evaluator they take minutes (SW-412), and the
    // machine checks the answers (`aoc_answers`).
    let keep = |t: &stitchwort_elab::TestDecl| !t.name.starts_with("real input") && keep(t);
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

fn is_main(name: &str) -> bool {
    name == "main" || name.ends_with(".main")
}

/// Each example file on its own: its `main`, if it has one, and every
/// definition.
#[test]
fn every_example_lowers() {
    let mut paths = sw_files(&root().join("examples/accept"));
    paths.extend(sw_files(&root().join("examples/extract")));
    // Each file on the thread pool: (whether it has a `main`, its tests run).
    let per_file = par_map(STACK, &paths, |path| {
        let what = path.display().to_string();
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
            .unwrap_or_else(|e| panic!("{what} doesn't check: {e:?}"));
        let tests = lower_everything(&session, &what);
        // A runnable `main`, as `run_js.rs` finds them (some
        // examples have a `main` that's a value).
        if text.contains("def main()") || text.contains("def main ()") {
            let main = session
                .main()
                .unwrap_or_else(|e| panic!("{what}: main: {e:?}"));
            let g = &session.elab.ev();
            let program = lower_main(g, session.elab.options.limits, main.term(), main.row)
                .unwrap_or_else(|e| panic!("{what}: lowering main: {e:?}"));
            well_formed(&program, &what);
            return (1, tests);
        }
        (0, tests)
    });
    let files = per_file.len();
    let mains: usize = per_file.iter().map(|(m, _)| m).sum();
    let tests: usize = per_file.iter().map(|(_, t)| t).sum();
    eprintln!("lowered {mains} mains and everything in {files} files; ran {tests} tests on the IR");
    assert!(files > 100, "{files}");
    assert!(mains >= 9, "{mains}");
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
    let g = &session.elab.ev();
    let mains: Vec<String> = g
        .env
        .defs()
        .iter()
        .filter(|d| is_main(d.name()) && !d.path().starts_with("Std."))
        .map(|d| d.name().to_string())
        .collect();
    for main_name in &mains {
        let main = session
            .main_named(main_name, &name)
            .unwrap_or_else(|e| panic!("{name}: {main_name}: {e:?}"));
        let g = &session.elab.ev();
        let program = lower_main(g, session.elab.options.limits, main.term(), main.row)
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
    // All tier only: it took 36 minutes in the broad tier (31 Oct 2026,
    // docs/testing.md); SW-839's fast lowering check is to take its place.
    if !stitchwort_driver::driver::all_tier("every_aoc_main_lowers") {
        return;
    }
    // Each part of the project in a session of its own, side by side
    // (`differential::aoc_parts`).
    let parts = crate::differential::aoc_parts();
    let lowered = par_map(STACK, &parts, |part| {
        let mut session = crate::differential::aoc_part(part);
        let tests =
            lower_everything_where(&session, part, |t| crate::differential::in_part(t, part));
        let within = format!("{part}.");
        let mains: Vec<String> = session
            .elab
            .ev()
            .env
            .defs()
            .iter()
            .filter(|d| is_main(d.name()) && d.path().starts_with(&within))
            .map(|d| d.name().to_string())
            .collect();
        for main_name in &mains {
            let main = session
                .main_named(main_name, "aoc")
                .unwrap_or_else(|e| panic!("{main_name}: {e:?}"));
            let g = &session.elab.ev();
            let program = lower_main(g, session.elab.options.limits, main.term(), main.row)
                .unwrap_or_else(|e| panic!("lowering {main_name}: {e:?}"));
            well_formed(&program, main_name);
        }
        (tests, mains.len())
    });
    let tests: usize = lowered.iter().map(|(t, _)| t).sum();
    let mains: usize = lowered.iter().map(|(_, m)| m).sum();
    eprintln!("lowered {mains} AoC mains; ran {tests} AoC tests on the IR");
    if std::env::var_os("AOC_PARTS").is_none() {
        assert!(mains >= 7, "{mains}");
    }
}

/// The whole library lowers, and its own tests (many of them of the text
/// and integer natives) give the same outcomes on the IR.
#[test]
fn the_library_lowers_and_its_tests_agree() {
    with_stack(STACK, || {
        let session = Session::with_library_tests();
        let g = &session.elab.ev();
        let ids: Vec<DefId> = (0..g.env.defs().len())
            .map(DefId)
            .filter(|id| g.def(*id).body().is_some() || g.env.builtins().primitive(*id).is_some())
            .collect();
        let program = lower_definitions(g, session.elab.options.limits, &ids).expect("lowers");
        well_formed(&program, "the library");
        let ran = run_tests(&session, &program, "the library", true, |_| true);
        eprintln!("ran {ran} library tests on the IR");
        assert!(ran >= 70, "{ran}");
    });
}

/// The same, with every determined field stored as well and each match
/// checking its rebuild of every one against the stored field
/// (`checking_rebuilds`): every branch of the library's matches on such a
/// type has its rebuilds found, and those its tests reach are compared.
#[test]
fn the_library_rebuilds_its_determined_fields() {
    with_stack(STACK, || {
        let _check = stitchwort_rt::erasure::checking_rebuilds();
        let session = Session::with_library_tests();
        let g = &session.elab.ev();
        let ids: Vec<DefId> = (0..g.env.defs().len())
            .map(DefId)
            .filter(|id| g.def(*id).body().is_some() || g.env.builtins().primitive(*id).is_some())
            .collect();
        let program = lower_definitions(g, session.elab.options.limits, &ids).expect("lowers");
        well_formed(&program, "the library");
        let ran = run_tests(&session, &program, "the library", true, |_| true);
        assert!(ran >= 70, "{ran}");
    });
}

/// Which fields of the library's data types the fast runtime doesn't
/// store, since the constructor's indices determine them
/// (docs/proposals/erase-determined-fields.md), and the census of their
/// rebuilds that cost a call where reading a stored field didn't (none):
/// a change to either shows up in review.
#[test]
fn the_library_s_determined_fields() {
    with_stack(STACK, || {
        let session = Session::with_library_tests();
        let g = &session.elab.ev();
        let ids: Vec<DefId> = (0..g.env.defs().len())
            .map(DefId)
            .filter(|id| g.def(*id).body().is_some() || g.env.builtins().primitive(*id).is_some())
            .collect();
        stitchwort_rt::erasure::census_rebuilds();
        lower_definitions(g, session.elab.options.limits, &ids).expect("lowers");
        let census = stitchwort_rt::erasure::take_census();
        let mut out = String::new();
        for d in (0..g.env.datas().len()).map(DataId) {
            for (c, ctor) in g.data(d).ctors().iter().enumerate() {
                let determined = stitchwort_core::determined::ctor_determined(g, d, c);
                for (i, (name, _)) in ctor.fields.iter().enumerate() {
                    if determined[i] {
                        out.push_str(&format!("{}.{} {name}\n", g.data(d).name(), ctor.name));
                    }
                }
            }
        }
        out.push_str(&format!("rebuilds that call: {census:#?}\n"));
        insta::assert_snapshot!(out);
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
        let g = &session.elab.ev();
        let program = lower_main(g, session.elab.options.limits, main.term(), main.row)
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
  let parts := Text.split "12,-5,x" ','
  IO.print (Text.join (parts.map (t => Int.toText (signed t))) ' ')
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

-- The fold is in a pure function: an unannotated lambda inside `main`'s
-- `{IO}` takes the ambient row, so `foldLeft` there would be called at `{IO}`.
def total (k: Nat) (xs: List Nat): Nat := xs.foldLeft 0 (acc x => acc + x + k)

def main(): {IO} () :=
  let k := 3
  IO.print (Nat.toText (total k (scale k 1 [1, 2])))
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

/// A pure use of an effect-polymorphic function calls its empty-row variant
/// (docs/proposals/effect-polymorphism.md, design E): `List.map` at the
/// empty row is a plain map's code, with no row passed and no test of one.
#[test]
fn a_pure_use_of_map_has_no_row_dispatch() {
    let ir = ir(r#"
import Std (List, Nat)

def step (n: Nat): Nat := n + 1

def main(): {IO} () := IO.print (Nat.toText (List.sum (List.map [1, 2, 3] step)))
"#);
    assert!(!ir.contains("Empty"), "a row in the IR:\n{ir}");
    assert!(
        !ir.contains("bindIn") && !ir.contains("doneIn"),
        "a row eliminator in the IR:\n{ir}"
    );
    insta::assert_snapshot!(ir);
}

/// Loops built around a call whose arguments bind variables of their own
/// (`examples/accept/trmc-argument-binders.sw`) are well formed, and no two
/// globals share a name.
#[test]
fn loops_over_arguments_that_bind_are_well_formed() {
    with_stack(STACK, || {
        let path = root().join("examples/accept/trmc-argument-binders.sw");
        let text = std::fs::read_to_string(&path).expect("read example");
        let mut session = Session::for_stack(STACK);
        session
            .load("trmc-argument-binders.sw", &text)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("main");
        let g = &session.elab.ev();
        let program = lower_main(g, session.elab.options.limits, main.term(), main.row)
            .unwrap_or_else(|e| panic!("lowering main: {e:?}"));
        well_formed(&program, "trmc-argument-binders.sw");
        let mut names: Vec<&str> = program.globals.iter().map(|g| &*g.name).collect();
        assert!(names.iter().any(|n| n.contains("[cells]")), "{names:?}");
        let count = names.len();
        names.sort();
        names.dedup();
        assert_eq!(names.len(), count, "two globals share a name");
    });
}

/// A one-field record is stored as its field (D866), so the match a
/// projection lowers to binds the field to the record's own variable. Read
/// inside a closure that captures the record, the field must be captured as
/// the record is: it was captured at its own level, which the frame making
/// the closure doesn't have (SW-1997). The projection, `Term::Proj`, comes
/// from record eta, which nothing in a program's source makes, so it's put
/// in place of the accessor's calls.
#[test]
fn a_closure_reads_a_projection_of_a_captured_one_field_record() {
    let source = r#"
import Std (Nat, Text, Int)
type Cave = { rows: Nat }

-- The record comes from the input, so that specialisation doesn't fold it
-- into the closure.
def main(): {IO} () :=
  let rows := match IO.readLine() with
    | Some line => line.length
    | None => 0
  IO.print (Nat.toText ((cave => ([1, 2].map (x => x + cave.rows)).sum) { rows = rows }))
"#;
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("test.sw", source)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let main = session.main().expect("main");
        let g = &session.elab.ev();
        let rows = (0..g.env.defs().len())
            .map(DefId)
            .rfind(|id| &**g.def(*id).name() == "Cave.rows")
            .expect("the accessor");
        let cave = (0..g.env.datas().len())
            .map(DataId)
            .rfind(|d| &**g.data(*d).name() == "Cave")
            .expect("the record");
        assert!(g.data(cave).unboxed_field().is_some());
        // `main`'s body, with the projection, in place of `main` in the
        // term that runs it.
        let main_def = (0..g.env.defs().len())
            .map(DefId)
            .rfind(|id| &**g.def(*id).name() == "main")
            .expect("main");
        let mut projections = 0;
        let body = g
            .def(main_def)
            .body()
            .expect("main has a body")
            .rewrite_up(g, &mut |t| {
                let (head, args) = t.spine();
                Ok(match (head, &args[..]) {
                    (Term::Def(id), [record]) if *id == rows => {
                        projections += 1;
                        Some(Term::Proj(cave, 0, Rc::new((*record).clone())))
                    }
                    _ => None,
                })
            })
            .expect("within limits");
        let term = main
            .term()
            .rewrite_up(g, &mut |t| {
                Ok(matches!(t, Term::Def(id) if *id == main_def).then(|| body.clone()))
            })
            .expect("within limits");
        assert_eq!(projections, 1, "{body:?}");
        let program = lower_main(g, session.elab.options.limits, &term, main.row)
            .unwrap_or_else(|e| panic!("lowering: {e:?}"));
        well_formed(&program, "main");
    });
}

/// Fields the result indices determine aren't stored
/// (docs/proposals/erase-determined-fields.md): `Fin`'s successor stores
/// only the predecessor, which makes `Fin` a number
/// (docs/proposals/nat-shaped-types.md), `Vec`'s cells store no length, and
/// a match that reads one rebuilds it from the matched value's index:
/// `height` computes `Succ (n - 1)`. (`Fin.toNat` is the identity, bound by
/// hash in `stitchwort_rt::natives`, so its call is the number itself.)
#[test]
fn determined_fields_are_rebuilt() {
    insta::assert_snapshot!(ir(r#"
import Std (Fin, Nat, Text, Vec)

type Tower: Nat → Type =
  | Ground: Tower 0
  | Floor (label: Nat) (below: Tower n): Tower (Succ n)

def height: Tower n → Nat
  | Ground => 0
  | Floor [n := k] _ _ => Succ k

def main(): {IO} () :=
  let v: Vec Nat 2 := Vec.map (VCons 1 (VCons 2 VNil)) (x => x + 1)
  IO.print "${Fin.toNat (FSucc FZero: Fin 3)} ${height (Floor 1 Ground)} ${Vec.toList v}"
"#));
}

/// Types shaped like `Nat` (docs/proposals/nat-shaped-types.md) are
/// numbers: successors around the zero are a literal, around anything else
/// an addition, and a match is a `Nat` match with the zero's arm first,
/// whichever order the type declares them in. `Fin.toNat` is the identity
/// on them, inlined at its calls.
#[test]
fn nat_shaped_types_are_numbers() {
    insta::assert_snapshot!(ir(r#"
import Std (Nat, Text, Fin)
type Count =
  | More (rest: Count) (ok: 1 = 1)
  | Stop

def Count.size: Count → Nat
  | Stop => 0
  | More rest _ => Succ (Count.size rest)

def Count.grow (c: Count): Count := More (More c rfl) rfl

def last: Fin 5 → Nat
  | FSucc (FSucc i) => Fin.toNat i
  | _ => 7

def main(): {IO} () :=
  IO.print (Nat.toText (Count.size (Count.grow (More Stop rfl)) + last (FSucc (FSucc FZero))))
"#));
}

/// Which types the runtime stores as numbers
/// ([`stitchwort_rt::erasure::nat_shape`]), in the library and in a
/// program: two constructors, one storing no fields and one storing a
/// single field of the type itself, alone in its group and not a
/// proposition. `Fin` is one, since its index fields are determined by its
/// result index and not stored.
#[test]
fn which_types_are_nat_shaped() {
    let source = r#"
import Std (Fin, Nat)
-- Loads `Fin`, which is shaped like `Nat` (its index is determined).
def first: Fin 3 := FZero
-- Shaped like `Nat`: a parameter, an index, either order.
type Count (a: Type) =
  | More (rest: Count a)
  | Stop
type Depth: Type → Type 1 =
  | Flat: Depth Nat
  | Deeper (inner: Depth b): Depth (List b)
-- Not: two run-time fields, a field of another type, a proposition, a
-- mutual pair, an implicit field (D141) the result index doesn't
-- determine, since it isn't a `Nat`.
type Two =
  | Leaf
  | Node (left: Two) (right: Two)
type Wrap =
  | Nothing
  | Just (n: Nat)
type Small: Nat → Prop =
  | SmallZero: Small 0
  | SmallSucc (s: Small n): Small (Succ n)
type Even =
  | EvenZero
  | EvenSucc (odd: Odd)
type Odd =
  | OddZero
  | OddSucc (even: Even)
type Rank: Bool → Type =
  | Low: Rank False
  | Up (below: Rank b): Rank True
"#;
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("test.sw", source)
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let g = &session.elab.ev();
        let shaped: Vec<String> = (0..g.env.datas().len())
            .map(DataId)
            .filter(|d| stitchwort_rt::erasure::nat_shape(g, *d).is_some())
            .map(|d| g.data(d).name().to_string())
            .collect();
        assert_eq!(shaped, ["Nat", "Fin", "Count", "Depth"]);
        let count = (0..g.env.datas().len())
            .map(DataId)
            .find(|d| &**g.data(*d).name() == "Count")
            .expect("Count");
        let shape = stitchwort_rt::erasure::nat_shape(g, count).expect("shaped");
        assert_eq!((shape.zero, shape.succ, shape.field), (1, 0, 0));
    });
}

/// `Fin.toNat` and `Fin.ofNatLt` run as the identity only while `Fin` is
/// stored as a number: not while rebuilds are checked, when its cells keep
/// their index and an identity would hand back a cell.
#[test]
fn fin_natives_need_fin_as_a_number() {
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load(
                "test.sw",
                "import Std (Fin, Nat)\ndef two: Nat := Fin.toNat (Fin.ofNatLt 3 2 rfl)\n",
            )
            .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
        let g = &session.elab.ev();
        let names = |g: &stitchwort_core::Ev| {
            let mut names: Vec<String> = stitchwort_rt::natives::fin_natives(g)
                .expect("hashes")
                .keys()
                .map(|id| g.def(*id).name().to_string())
                .collect();
            names.sort();
            names
        };
        assert_eq!(names(g), ["Fin.ofNatLt", "Fin.toNat"]);
        let _checking = stitchwort_rt::erasure::checking_rebuilds();
        assert!(names(g).is_empty());
    });
}
