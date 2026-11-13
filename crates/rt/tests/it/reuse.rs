//! Reuse across calls (crates/rt/src/reuse.rs): the copies taking a reuse
//! token are checked by `Program::validate`, survive the codec, stay within
//! their caps on real programs, and change no answer, against the
//! reference evaluator too.

use std::path::{Path, PathBuf};

use stitchwort_driver::driver::{Session, tier_sample, with_stack};
use stitchwort_driver::project::{DiskFiles, Target};
use stitchwort_rt::code::{self, Instr};
use stitchwort_rt::ir::{Expr, GlobalId, GlobalKind, Program, Reuse};
use stitchwort_rt::reuse::{MAX_COPIES, MAX_GROWTH, MIN_GROWTH};
use stitchwort_rt::{Limits, decode, encode, lower_main, run_main};

const STACK: usize = 256 * 1024 * 1024;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

const MAP_PROGRAM: &str = r#"import Std (IO, List, Map, Nat, Option)

def build (keys: List Nat): Map Nat Nat :=
  List.foldLeft keys Map.empty (m i => Map.insert m i i)

def drain: Nat → Map Nat Nat → Nat
  | Zero, m => 0
  | Succ fuel, m => match Map.popMin m with
    | None => 0
    | Some found => found.fst.snd + drain fuel found.snd

def main(): {IO} () :=
  IO.print "${drain 100 (build ((List.range 0 60).map (i => (i * 7) % 61)))}"
"#;

fn lowered(source: &str) -> (Session, Program, Limits) {
    let mut session = Session::for_stack(STACK);
    session.use_test_std_cache();
    session
        .load("test.sw", source)
        .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
    let main = session.main().expect("main");
    let program = lower_main(
        &session.elab.ev(),
        session.elab.options.limits,
        main.term(),
        main.row,
    )
    .expect("lowers");
    let limits = Limits::from_core(session.elab.options.limits);
    (session, program, limits)
}

fn run(program: &Program, limits: Limits) -> (String, Result<(), String>) {
    let mut output = Vec::new();
    let result = run_main(program, limits, &mut "".as_bytes(), &mut output);
    (
        String::from_utf8_lossy(&output).into_owned(),
        result.map_err(|e| e.to_string()),
    )
}

/// The first copy, and the global it copies.
fn a_copy(program: &Program) -> (usize, GlobalId) {
    program
        .globals
        .iter()
        .enumerate()
        .find_map(|(g, global)| match global.reuse {
            Reuse::Copy { of, .. } => Some((g, of)),
            _ => None,
        })
        .expect("a copy")
}

/// A copy's body may neither read nor bind its token's slot, and nothing
/// may name a copy: as a call, a function value or a partial application.
#[test]
fn validation_keeps_tokens_out_of_the_ir() {
    with_stack(STACK, || {
        let (_, program, _) = lowered(MAP_PROGRAM);
        assert_eq!(program.validate(), Ok(()));
        let (copy, of) = a_copy(&program);
        let token = match &program.globals[copy].kind {
            GlobalKind::Function { params, .. } => params - 1,
            _ => unreachable!(),
        };
        let with_body = |f: &dyn Fn(&Expr) -> Expr| {
            let (_, mut program, _) = lowered(MAP_PROGRAM);
            if let GlobalKind::Function { body, .. } = &mut program.globals[copy].kind {
                body.expr = f(&body.expr);
            }
            program.validate()
        };
        let read = with_body(&|e| Expr::Let(0, Box::new(Expr::Local(token)), Box::new(e.clone())));
        assert!(read.is_err(), "{read:?}");
        let bound = with_body(&|e| Expr::Let(token, Box::new(Expr::Erased), Box::new(e.clone())));
        assert!(
            bound.as_ref().is_err_and(|e| e.contains("token")),
            "{bound:?}"
        );
        let named = with_body(&|_| Expr::Global(GlobalId(copy as u32)));
        assert!(
            named.as_ref().is_err_and(|e| e.contains("a copy")),
            "{named:?}"
        );
        let pap = with_body(&|_| Expr::PartialApp(GlobalId(copy as u32), vec![Expr::Erased]));
        assert!(pap.as_ref().is_err_and(|e| e.contains("a copy")), "{pap:?}");
        // The two sides must agree.
        let (_, mut program, _) = lowered(MAP_PROGRAM);
        program.globals[of.0 as usize].reuse = Reuse::None;
        assert!(program.validate().is_err());
        let (_, mut program, _) = lowered(MAP_PROGRAM);
        program.globals[copy].reuse = Reuse::None;
        assert!(program.validate().is_err());
    });
}

/// The copies survive the codec, which `stitchwort build` embeds: the
/// decoded program has them, compiles to the same bytecode, calls them,
/// and prints the same.
#[test]
fn copies_survive_the_codec() {
    with_stack(STACK, || {
        let (_, program, limits) = lowered(MAP_PROGRAM);
        let (decoded, _) = decode(&encode(&program, &limits)).expect("decodes");
        let reuse = |p: &Program| {
            p.globals
                .iter()
                .map(|g| g.reuse.clone())
                .collect::<Vec<_>>()
        };
        assert_eq!(reuse(&decoded), reuse(&program));
        let (a, b) = (code::compile(&program), code::compile(&decoded));
        assert_eq!(format!("{:?}", a.codes), format!("{:?}", b.codes));
        assert_eq!(a.folds, b.folds);
        let (copy, _) = a_copy(&decoded);
        let copy = copy as u32;
        let called = b.codes.iter().any(|c| {
            c.instrs.iter().any(
                |i| matches!(i, Instr::Call { g, .. } | Instr::TailCall { g, .. } if *g == copy),
            )
        });
        assert!(called, "no call of the copy");
        assert_eq!(run(&decoded, limits), run(&program, limits));
        assert_eq!(run(&program, limits).0, "1776\n");
    });
}

/// `Map.Tree.balance` is `rebuild (shape l r) l key value r`: `shape`
/// picks one of five constants and `rebuild` takes it apart at once. Both
/// are inlined, so balance builds the unrotated node itself, with no
/// `Shape` made or tested, and takes a token for it (crates/rt/src/opt.rs,
/// `Context`).
#[test]
fn balance_builds_its_node_itself() {
    fn walk(e: &Expr, calls: &mut Vec<u32>, nodes: &mut usize) {
        match e {
            Expr::Call(g, a) => {
                calls.push(g.0);
                a.iter().for_each(|x| walk(x, calls, nodes));
            }
            Expr::Ctor(_, _, a) => {
                *nodes += usize::from(a.len() == 5);
                a.iter().for_each(|x| walk(x, calls, nodes));
            }
            Expr::Prim(_, a) | Expr::PartialApp(_, a) | Expr::Closure(_, a) => {
                a.iter().for_each(|x| walk(x, calls, nodes));
            }
            Expr::Apply(f, a) => {
                walk(f, calls, nodes);
                a.iter().for_each(|x| walk(x, calls, nodes));
            }
            Expr::Let(_, v, b) => {
                walk(v, calls, nodes);
                walk(b, calls, nodes);
            }
            Expr::Match(x, _, arms) => {
                walk(x, calls, nodes);
                arms.iter().for_each(|a| walk(&a.body, calls, nodes));
            }
            Expr::NumSwitch(x, arms, d) => {
                walk(x, calls, nodes);
                arms.iter().for_each(|(_, b)| walk(b, calls, nodes));
                walk(d, calls, nodes);
            }
            Expr::If(c, t, f) => {
                walk(c, calls, nodes);
                walk(t, calls, nodes);
                walk(f, calls, nodes);
            }
            _ => {}
        }
    }
    with_stack(STACK, || {
        let (_, program, _) = lowered(MAP_PROGRAM);
        let named = |name: &str| {
            program
                .globals
                .iter()
                .position(|g| &*g.name == name)
                .unwrap_or_else(|| panic!("no {name}"))
        };
        let balance = named("Std.Map.Tree.balance");
        let GlobalKind::Function { body, .. } = &program.globals[balance].kind else {
            panic!("balance is a function");
        };
        let (mut calls, mut nodes) = (Vec::new(), 0);
        walk(&body.expr, &mut calls, &mut nodes);
        for callee in ["Std.Map.Tree.shape", "Std.Map.Tree.rebuild"] {
            assert!(
                !calls.contains(&(named(callee) as u32)),
                "balance calls {callee}:\n{:#?}",
                body.expr
            );
        }
        assert!(nodes > 0, "balance builds no node:\n{:#?}", body.expr);
        assert!(
            matches!(&program.globals[balance].reuse, Reuse::Copies(c) if c.iter().any(|(n, _)| *n == 5)),
            "balance takes no token: {:?}",
            program.globals[balance].reuse
        );
    });
}

/// Tokens held around an effect operation whose handler resumes twice: each
/// resumption gets its own result, as the reference evaluator says.
#[test]
fn a_handler_resuming_twice_sees_its_own_cells() {
    let source = r#"import Std (IO, List, Nat, Text)

ability Choice where
  fork: () → {Choice} Bool

type Box =
  | MkBox (a: Nat) (b: Nat)

def fill: Nat → Nat → Box
  | Zero, x => MkBox x (x * 2)
  | Succ n, x => fill n (x + 1)

def twist (b: Box): {Choice} Box :=
  match b with
    | MkBox x y =>
      let c := fork ()
      let next := fill 2 (if c then x else y)
      match next with
        | MkBox p q => fill 1 (p + q)

def collect (prog: () → {Choice} Box): List Box :=
  handle prog() with
    | return x => [x]
    | fork (), k => List.append (k True) (k False)

def show: List Box → Text
  | [] => ""
  | [MkBox a b, ..rest] => "${a}/${b} " ++ show rest

def main(): {IO} () :=
  IO.print (show (collect (() => twist (MkBox 3 10))))
"#;
    with_stack(STACK, || {
        let (mut session, program, limits) = lowered(source);
        let main = session.main().expect("main");
        let mut output = Vec::new();
        session
            .run_main(&main, &mut &b""[..], &mut output)
            .expect("runs");
        let expected = String::from_utf8(output).expect("text");
        assert_eq!(expected, "16/32 37/74 \n");
        assert_eq!(run(&program, limits), (expected, Ok(())));
    });
}

/// The copies made for AoC days' `main`s (a sample, always with 2021 day
/// 15, the dijkstra benchmark; every day in the all tier) stay within the
/// caps: at most `MAX_COPIES`, adding at most `MAX_GROWTH`% of the IR's
/// nodes (or `MIN_GROWTH`). The counts are printed for the report.
#[test]
fn copies_stay_within_their_caps_on_aoc() {
    with_stack(STACK, || {
        let mut days: Vec<String> = Vec::new();
        for year in std::fs::read_dir(root().join("aoc/src/Aoc")).expect("aoc") {
            let year = year
                .expect("a year")
                .file_name()
                .into_string()
                .expect("a name");
            if !year.starts_with("Year") {
                continue;
            }
            for day in std::fs::read_dir(root().join("aoc/src/Aoc").join(&year)).expect("days") {
                let day = day
                    .expect("a day")
                    .file_name()
                    .into_string()
                    .expect("a name");
                days.push(format!("Aoc.{year}.{day}"));
            }
        }
        days.sort();
        assert!(days.len() > 40, "{days:?}");
        let mut days = tier_sample(days, 4);
        if !days.iter().any(|d| d == "Aoc.Year2021.Day15") {
            days.push("Aoc.Year2021.Day15".to_string());
        }
        let mut session = Session::for_stack(STACK);
        session
            .load_project(
                &DiskFiles {
                    root: root().join("aoc"),
                },
                "aoc",
                &Target::Namespaces(days.clone()),
            )
            .unwrap_or_else(|e| panic!("aoc doesn't check: {e:?}"));
        let (mut copies, mut nodes, mut added) = (0, 0, 0);
        for day in &days {
            let name = format!("{day}.main");
            let Ok(main) = session.main_named(&name, "aoc") else {
                continue;
            };
            let program = session.lower_fast(&main).expect("lowers");
            let (c, n, a) = sizes(&program);
            eprintln!("{name}: {c} copies, {a} of {n} nodes");
            assert!(c <= MAX_COPIES, "{name}: {c} copies");
            assert!(
                a <= (n * MAX_GROWTH / 100).max(MIN_GROWTH),
                "{name}: {a} of {n} nodes"
            );
            copies += c;
            nodes += n;
            added += a;
        }
        eprintln!(
            "{} days: {copies} copies, {added} nodes added to {nodes} ({:.1}%)",
            days.len(),
            100.0 * added as f64 / nodes as f64
        );
    });
}

/// The copies in `program`, and its IR nodes without and in them.
fn sizes(program: &Program) -> (usize, usize, usize) {
    fn size(e: &Expr) -> usize {
        let mut n = 0;
        let mut work = vec![e];
        while let Some(e) = work.pop() {
            n += 1;
            match e {
                Expr::Call(_, a)
                | Expr::Prim(_, a)
                | Expr::PartialApp(_, a)
                | Expr::Closure(_, a)
                | Expr::Ctor(_, _, a) => work.extend(a),
                Expr::Apply(f, a) => {
                    work.push(f);
                    work.extend(a);
                }
                Expr::Let(_, v, b) => {
                    work.push(v);
                    work.push(b);
                }
                Expr::Match(s, _, arms) => {
                    work.push(s);
                    work.extend(arms.iter().map(|a| &a.body));
                }
                Expr::NumSwitch(s, arms, d) => {
                    work.push(s);
                    work.extend(arms.iter().map(|(_, b)| b));
                    work.push(d);
                }
                Expr::If(c, t, f) => {
                    work.push(c);
                    work.push(t);
                    work.push(f);
                }
                _ => {}
            }
        }
        n
    }
    let (mut copies, mut nodes, mut added) = (0, 0, 0);
    for global in &program.globals {
        let n = match &global.kind {
            GlobalKind::Function { body, .. } | GlobalKind::Constant { body } => size(&body.expr),
            GlobalKind::Native(_) => 0,
        };
        if let Reuse::Copy { .. } = global.reuse {
            copies += 1;
            added += n;
        } else {
            nodes += n;
        }
    }
    nodes += program
        .lambdas
        .iter()
        .map(|l| size(&l.body.expr))
        .sum::<usize>();
    nodes += size(&program.entry.expr);
    (copies, nodes, added)
}
