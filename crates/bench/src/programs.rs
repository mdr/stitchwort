//! The benchmarks. Each one checks its own result, so a benchmark can't get
//! faster by quietly doing something else.

use std::io::{self, Write};
use std::path::{Path, PathBuf};

use stitchwort_driver::driver::{Cache, Outcome, Session};
use stitchwort_driver::render::render;
use stitchwort_syntax::Diagnostic;

use crate::{Benchmark, Prepared, STACK, Work};

pub const ALL: &[Benchmark] = &[
    Benchmark {
        name: "examples",
        about: "checks every example under examples/ and runs their tests, as the example suite does",
        prepare: examples,
    },
    Benchmark {
        name: "extract-js",
        about: "generates JS and .d.ts for each examples/extract/ program (already checked)",
        prepare: extract_js,
    },
    Benchmark {
        name: "eval-lengths",
        about: "evaluates `lengths 400 3000`: 400 lists of 3,000 elements, built and measured",
        prepare: || eval(LENGTHS, "lengths 400 3000", "1200000"),
    },
    Benchmark {
        name: "text-append",
        about: "a loop of `++` building a text of 100,000 characters",
        prepare: || eval(TEXT, "Text.length (repText 20000 \"abcd,\")", "100000"),
    },
    Benchmark {
        name: "text-split-join",
        about: "`Text.split` then `Text.join` on a text of 10,000 characters",
        prepare: || {
            let program = format!("{TEXT}\ndef big : Text := \"{}\"\n", "abcd,".repeat(2000));
            eval(
                program,
                "Text.length (Text.join ',' (Text.split ',' big))",
                "10000",
            )
        },
    },
    // A long literal is one compact list in the checked term (compact text,
    // stage 2): checking it, and walking it.
    Benchmark {
        name: "check-text-literal",
        about: "checks a definition whose body is a text literal of 50,000 characters",
        prepare: || check(format!("def big : Text := \"{}\"\n", "abcd,".repeat(10000))),
    },
    Benchmark {
        name: "text-literal-walk",
        about: "counts the characters of a text literal of 100,000 characters, with an accumulator",
        prepare: || {
            let program = format!(
                "{TEXT}\ndef big : Text := \"{}\"\n",
                "abcd,\\u{1F600}".repeat(16667)
            );
            eval(program, "lengthFrom 0 (Text.toList big)", "100002")
        },
    },
    Benchmark {
        name: "text-nat-to-text",
        about: "`Nat.toText` on 10,000 numbers of up to 11 digits",
        prepare: || eval(TEXT, "natTexts 10000 0", "98884"),
    },
    Benchmark {
        name: "run-prints",
        about: "runs a `main` that prints 20,000 lines, as `stitchwort run` does",
        prepare: run_prints,
    },
    Benchmark {
        name: "run-proof-fields",
        about: "runs a `main` that threads a record with a proof field through 200 lines of input",
        prepare: run_proof_fields,
    },
    Benchmark {
        name: "check-number-pattern",
        about: "checks `f 200 = True; f _ = False`",
        prepare: || check("def f : Nat -> Bool\n  | 200 => True\n  | _ => False\n".into()),
    },
    Benchmark {
        name: "check-number-table",
        about: "checks a table `t 0 = 0 … t 255 = 255`",
        prepare: || {
            let rows: String = (0..256).map(|i| format!("  | {i} => {i}\n")).collect();
            check(format!("def t : Nat -> Nat\n{rows}  | _ => 0\n"))
        },
    },
    // Number patterns compile to number cases, so these measure literal
    // magnitude, table width and context separately
    // (docs/proposals/number-patterns.md).
    Benchmark {
        name: "check-number-huge",
        about: "checks `f 10^30 = True; f _ = False`",
        prepare: || {
            check(format!(
                "def f : Nat -> Bool\n  | {} => True\n  | _ => False\n",
                "1".to_string() + &"0".repeat(30)
            ))
        },
    },
    Benchmark {
        name: "check-number-wide",
        about: "checks a table `t 0 = 0 … t 999 = 999`",
        prepare: || {
            let rows: String = (0..1000).map(|i| format!("  | {i} => {i}\n")).collect();
            check(format!("def t : Nat -> Nat\n{rows}  | _ => 0\n"))
        },
    },
    Benchmark {
        name: "check-number-dependent",
        about: "checks 50 number equations whose other arguments' types depend on the number",
        prepare: || {
            let rows: String = (0..50)
                .map(|i| format!("  | {}, a, b, c => a\n", 2 * i + 1))
                .collect();
            check(format!(
                "def Shape : Nat -> Type\n  | 0 => Nat\n  | _ => Bool\n\n\
                 def dep : (n : Nat) -> Shape n -> Shape n -> Shape n -> Shape n\n\
                 {rows}  | n, a, b, c => c\n"
            ))
        },
    },
    Benchmark {
        name: "check-number-columns",
        about: "checks 60 equations on three number columns, each with `_` in the other two",
        prepare: || {
            let mut rows = String::new();
            for c in 0..3 {
                for i in 0..20 {
                    let mut pats = ["_".to_string(), "_".to_string(), "_".to_string()];
                    pats[c] = (10 * i + 7).to_string();
                    rows += &format!("  | {} => {}\n", pats.join(", "), c * 100 + i);
                }
            }
            check(format!(
                "def m : Nat -> Nat -> Nat -> Nat\n{rows}  | _, _, _ => 0\n"
            ))
        },
    },
    Benchmark {
        name: "check-list-rfl",
        about: "checks `theorem a : [1, …, 20000] = [1, …, 20000]` by `rfl`",
        prepare: || check(list_theorem(20_000, "rfl")),
    },
    Benchmark {
        name: "check-list-sym-rfl",
        about: "the same by `Eq.sym rfl`, whose hidden arguments are solved to the list",
        prepare: || check(list_theorem(20_000, "Eq.sym rfl")),
    },
    // The next three are near the command line's limits, measured on
    // 2026-10-15: a sum of 9,500 ones checks and 10,000 doesn't; 12,740
    // nested parentheses are too many to parse. Nested applications check at
    // 6,000 and not at 10,000, but cost grows with the square of the depth
    // (6,000 takes 5.6 s), so this one is well inside.
    Benchmark {
        name: "check-long-sum",
        about: "checks `1 + 1 + … + 1` with 9,000 ones",
        prepare: || check(format!("def x : Nat := {}\n", vec!["1"; 9000].join(" + "))),
    },
    Benchmark {
        name: "check-nested-parens",
        about: "checks `((…(0)…))`, 12,000 deep",
        prepare: || check(format!("def x : Nat := {}\n", nested(12_000, "(", "0"))),
    },
    Benchmark {
        name: "check-nested-apps",
        about: "checks `f (f (… 0))`, 2,000 deep",
        prepare: || {
            check(format!(
                "def f (n : Nat) : Nat := n\n\ndef x : Nat := {}\n",
                nested(2000, "f (", "0")
            ))
        },
    },
    // The checker computes only what types need
    // (docs/proposals/checker-evaluation.md): `cost` takes about 5.8 million
    // steps to compute, and none of these next few needs it.
    Benchmark {
        name: "check-closed-print",
        about: "checks `IO.print (Nat.toText cost)`, for a closed `cost` over 200,000 elements",
        prepare: || {
            check(closed(
                "def main () : {IO} () := IO.print (Nat.toText cost)",
            ))
        },
    },
    Benchmark {
        name: "check-closed-dot",
        about: "checks `cost.toText`, for a closed `cost` over 200,000 elements",
        prepare: || check(closed("def x : Text := cost.toText")),
    },
    Benchmark {
        name: "check-closed-eqeq",
        about: "checks `cost == 5`, for a closed `cost` over 200,000 elements",
        prepare: || check(closed("def b : Bool := cost == 5")),
    },
    Benchmark {
        name: "check-closed-list-eqeq",
        about: "checks `List.range 100000 == List.range 100000`",
        prepare: || {
            check("def big (u : ()) : Bool := List.range 100000 == List.range 100000\n".into())
        },
    },
    // These still compute `cost` while checking, since a type needs its
    // value and the evaluator is strict: recorded to measure option (b)
    // against.
    Benchmark {
        name: "check-closed-if-less",
        about: "checks `if cost < 5 then 1 else 2` (the branches assume `cost < 5`)",
        prepare: || check(closed("def y : Nat := if cost < 5 then 1 else 2")),
    },
    Benchmark {
        name: "check-closed-indexed",
        about: "checks `mk cost : V cost`, for a type `V` indexed by a `Nat`",
        prepare: || {
            check(closed(
                "type V (n : Nat) = { xs : List Nat }\n\ndef mk (n : Nat) : V n := { xs = [] }\n\n\
                 def big (u : ()) : V cost := mk cost",
            ))
        },
    },
    Benchmark {
        name: "check-closed-rfl",
        about: "checks `rfl : cost = cost`",
        prepare: || check(closed("def big (u : ()) : cost = cost := rfl")),
    },
];

/// `body`, after a closed definition `cost` that's expensive to compute.
fn closed(body: &str) -> String {
    format!("def cost : Nat := List.length (List.range 200000)\n{body}\n")
}

/// From TODO.md's measurements: `length (replicate n 1)`, `k` times.
const LENGTHS: &str = "
def replicate : Nat -> a -> List a
  | Zero,   x => Nil
  | Succ n, x => Cons x (replicate n x)

def lengths : Nat -> Nat -> Nat
  | Zero,   n => 0
  | Succ k, n => List.length (replicate n 1) + lengths k n
";

const TEXT: &str = "
def repText : Nat -> Text -> Text
  | Zero,   t => \"\"
  | Succ n, t => t ++ repText n t

def lengthFrom (k : Nat) : List Char -> Nat
  | Nil       => k
  | Cons c cs => lengthFrom (Succ k) cs

-- The total length of `Nat.toText` of `k` numbers spread over 0 to about 10^10.
def natTexts : Nat -> Nat -> Nat
  | Zero,   acc => acc
  | Succ k, acc => natTexts k (acc + Text.length (Nat.toText (k * 1000003)))
";

const PRINTS: &str = "
def printMany : Nat -> {IO} ()
  | Zero   => ()
  | Succ n =>
    IO.print (Nat.toText n)
    printMany n

def main () : {IO} () := printMany 20000
";

fn nested(n: usize, around: &str, inner: &str) -> String {
    format!("{}{inner}{}", around.repeat(n), ")".repeat(n))
}

fn list_theorem(n: usize, proof: &str) -> String {
    let list = (1..=n)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    format!("theorem a : [{list}] = [{list}] := {proof}\n")
}

/// What `session`'s budget has counted so far.
fn work(session: &Session) -> Work {
    let budget = &session.elab.globals.budget;
    Work {
        steps: budget.total_work(),
        visits: budget.total_visits(),
    }
}

fn rendered(session: &Session, diagnostics: &[Diagnostic]) -> String {
    diagnostics
        .iter()
        .map(|d| render(&session.sources, d, false))
        .collect()
}

fn loaded(program: &str) -> Result<Session, String> {
    let mut session = Session::for_stack(STACK);
    match session.load("bench.sw", program) {
        Ok(_) => Ok(session),
        Err(ds) => Err(rendered(&session, &ds)),
    }
}

/// Evaluates `expr` with `program` loaded, which must give `expected`.
fn eval(
    program: impl AsRef<str>,
    expr: &'static str,
    expected: &'static str,
) -> Result<Prepared, String> {
    let mut session = loaded(program.as_ref())?;
    Ok(Prepared::new(move || {
        let before = work(&session);
        let result = session
            .parse_expression("<bench>", expr)
            .and_then(|e| session.elab.eval_expr(&e));
        match result {
            Ok((value, _)) if value == expected => Ok(work(&session) - before),
            Ok((value, _)) => Err(format!("`{expr}` gave {value}, not {expected}")),
            Err(d) => Err(rendered(&session, &[d])),
        }
    }))
}

/// Checks `program`, which must check.
fn check(program: String) -> Result<Prepared, String> {
    let mut session = Session::for_stack(STACK);
    Ok(Prepared::new(move || {
        let before = work(&session);
        match session.load("bench.sw", &program) {
            Ok(_) => Ok(work(&session) - before),
            Err(ds) => Err(rendered(&session, &ds)),
        }
    }))
}

/// Counts the lines written to it.
struct Lines(usize);

impl Write for Lines {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0 += buf.iter().filter(|&&b| b == b'\n').count();
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn run_prints() -> Result<Prepared, String> {
    let mut session = loaded(PRINTS)?;
    let main = session.main().map_err(|d| rendered(&session, &[d]))?;
    Ok(Prepared::new(move || {
        let before = work(&session);
        let mut output = Lines(0);
        session
            .run_main(&main, &mut io::empty(), &mut output)
            .map_err(|e| rendered(&session, &[e.diagnostic(&main)]))?;
        match output.0 {
            20_000 => Ok(work(&session) - before),
            n => Err(format!("printed {n} lines, not 20,000")),
        }
    }))
}

/// A record with a proof field, rebuilt for each of 200 input lines: erasure
/// skips the proof (`erase.rs`).
const PROOF_FIELDS: &str = "
type Pos = { at : Nat, ok : at < 100 }

def wrap (x : Int) : Pos := { at = Int.modNat x 100, ok = Int.modNatLt x 100 }

def walk : List Text -> Pos -> Nat
  | Nil,       p => p.at
  | Cons t ts, p => walk ts (wrap (p.at.toInt + Nat.toInt (Text.length t * 37)))

def main () : {IO} () := IO.print (Nat.toText (walk (IO.readAllLines ()) (wrap 50)))
";

fn run_proof_fields() -> Result<Prepared, String> {
    let mut session = loaded(PROOF_FIELDS)?;
    let main = session.main().map_err(|d| rendered(&session, &[d]))?;
    let input = "L68\n".repeat(200);
    Ok(Prepared::new(move || {
        let before = work(&session);
        let mut output = Vec::new();
        session
            .run_main(&main, &mut input.as_bytes(), &mut output)
            .map_err(|e| rendered(&session, &[e.diagnostic(&main)]))?;
        // Each line moves the dial by 3 * 37 = 111, so 11 mod 100: after 200
        // lines, 50 + 2,200 lands back on 50.
        let printed = String::from_utf8_lossy(&output).into_owned();
        match printed.as_str() {
            "50\n" => Ok(work(&session) - before),
            other => Err(format!("printed {other:?}, not \"50\\n\"")),
        }
    }))
}

/// Example programs under `examples/<dir>`, sorted, as (name, text).
fn example_files(dir: &str) -> Result<Vec<(String, String)>, String> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let entries = std::fs::read_dir(root.join(dir)).map_err(|e| format!("examples/{dir}: {e}"))?;
    let mut paths: Vec<PathBuf> = entries
        .filter_map(|entry| Some(entry.ok()?.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "sw"))
        .collect();
    paths.sort();
    paths
        .into_iter()
        .map(|path| {
            let name = format!("{dir}/{}", path.file_name().unwrap().to_string_lossy());
            let text = std::fs::read_to_string(&path).map_err(|e| format!("{name}: {e}"))?;
            Ok((name, text))
        })
        .collect()
}

/// A short fingerprint of some files: a count for other files isn't
/// comparable.
fn fingerprint(files: &[(String, String)]) -> String {
    let mut hasher = blake3::Hasher::new();
    for (name, text) in files {
        for part in [name, text] {
            hasher.update(&(part.len() as u64).to_le_bytes());
            hasher.update(part.as_bytes());
        }
    }
    format!(
        "{} files, {}",
        files.len(),
        &hasher.finalize().to_hex()[..16]
    )
}

/// What `crates/cli/tests/examples.rs` does, without comparing snapshots:
/// accepted examples are checked and their tests run; rejected ones are
/// checked and their errors rendered. Each example has its own session.
fn examples() -> Result<Prepared, String> {
    let accepted = [example_files("accept")?, example_files("extract")?].concat();
    let rejected = [example_files("reject")?, example_files("soundness")?].concat();
    let inputs = fingerprint(&[accepted.as_slice(), rejected.as_slice()].concat());
    Ok(Prepared {
        inputs: Some(inputs),
        run: Box::new(move || {
            let mut total = Work::default();
            for (name, text) in &accepted {
                let mut session = Session::for_stack(16 * 1024 * 1024);
                if let Err(ds) = session.load(name, text) {
                    return Err(format!("{name}:\n{}", rendered(&session, &ds)));
                }
                for result in session.run_tests(&Cache::disabled()) {
                    if result.outcome != Outcome::Passed {
                        return Err(format!("{name}: test \"{}\" failed", result.name));
                    }
                }
                total = total + work(&session);
            }
            for (name, text) in &rejected {
                let mut session = Session::new();
                if let Err(ds) = session.load(name, text) {
                    std::hint::black_box(rendered(&session, &ds));
                }
                total = total + work(&session);
            }
            Ok(total)
        }),
    })
}

/// Generating JS for each extraction example, already loaded.
fn extract_js() -> Result<Prepared, String> {
    let files = example_files("extract")?;
    let inputs = fingerprint(&files);
    let sessions = files
        .iter()
        .map(|(name, text)| {
            let mut session = Session::for_stack(STACK);
            match session.load(name, text) {
                Ok(_) => Ok(session),
                Err(ds) => Err(format!("{name}:\n{}", rendered(&session, &ds))),
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Prepared {
        inputs: Some(inputs),
        run: Box::new(move || {
            let mut total = Work::default();
            for session in &sessions {
                let before = work(session);
                let output = session.extract().map_err(|d| rendered(session, &[d]))?;
                std::hint::black_box(output);
                total = total + (work(session) - before);
            }
            Ok(total)
        }),
    })
}
