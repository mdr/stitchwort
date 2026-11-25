//! The four execution paths of `Float` (docs/proposals/float.md §3.3, §7.4):
//! the native kernel, the WebAssembly kernel, the Rust runtime and Node
//! compute the same canonical bits for every operation the kernel computes
//! (the rounding operations `+ - * / %`, `floor`, `ceil`, `trunc`, `round`,
//! `ofInt` and `ofNat`; `neg`, `abs`, `isNaN`, `isFinite`, `toInt`, `==`, `<`, `<=`
//! (in an `if`, as a `Bool`, and against literals), `Float.compare`,
//! `Ord.compare`, `Float.less`, `Float.leq`, `Float.ieeeEq`, `ieeeLt`,
//! `ieeeLe`; the record's constructor and `.bits`), on every pair from an
//! edge set and some random patterns, on literal expressions, and in sorting
//! them (`sort`, `sortOn`, `sortWith` by `<=` and `<`, each checked against
//! `f64::total_cmp` too). Results are compared as canonical
//! bit patterns, shown in hex, never as JSON numbers (which would hide `-0`
//! and lose `NaN`). `toText`, which only the runtimes compute, has a test of
//! its own: the Rust runtime against Node's `String(x)`, and `toSource`
//! read back by the kernel.
//!
//! The kernels compute every rounding operation through its definition
//! (std/Float/Model.sw), the float natives being off while checking and
//! evaluating outside a run, so these tests compare those definitions with
//! the hardware and Node; [`add_and_sub_round_like_the_hardware`],
//! [`mul_rounds_like_the_hardware`], [`div_rounds_like_the_hardware`] and
//! [`rem_and_whole_numbers_match_the_hardware`] add operands built to land
//! on rounding boundaries, with slices of Berkeley TestFloat's cases.
//!
//! The WebAssembly kernel is the playground's bundle in `web/pkg`, run by
//! `web/tests/float-wasm.mjs` under Node. Build it first (`web/build.sh`, or
//! its `cargo build --target wasm32-unknown-unknown` and `wasm-bindgen`
//! steps). Without it, or if it was built from other sources (its source
//! fingerprint differs), that path is left out, and the test says so.

use std::fmt::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use stitchwort_cli::driver::Session;

/// The edge set (§7.4 item 1): zeros, the NaN, the infinities, the
/// smallest subnormals, the largest finite, 2^53 and its neighbours, halves,
/// `0.49999999999999994`, 2^52 + 1, and ordinary values.
const EDGES: &[u64] = &[
    0,
    1 << 63,
    0x7FF8_0000_0000_0000,
    0x7FF0_0000_0000_0000,
    0xFFF0_0000_0000_0000,
    1,
    (1 << 63) | 1,
    0x000F_FFFF_FFFF_FFFF,
    0x7FEF_FFFF_FFFF_FFFF,
    0xFFEF_FFFF_FFFF_FFFF,
    0x4340_0000_0000_0000,
    0x4340_0000_0000_0001,
    0x433F_FFFF_FFFF_FFFF,
    0x3FE0_0000_0000_0000,
    0xBFE0_0000_0000_0000,
    0x4004_0000_0000_0000,
    0xC004_0000_0000_0000,
    0x3FDF_FFFF_FFFF_FFFF,
    0x4330_0000_0000_0001,
    0x3FF8_0000_0000_0000,
    0x3FB9_9999_9999_999A,
    4680253341308362424,
    // -1.5 (a negative half), and 1e100 (whole, far beyond 2^64).
    0xBFF8_0000_0000_0000,
    0x54B2_49AD_2594_C37D,
];

/// Random valid patterns (xorshift, so the same ones every run).
fn random_patterns(n: usize) -> Vec<u64> {
    let mut seed = 0x2545_F491_4F6C_DD1Du64;
    let mut out = Vec::new();
    while out.len() < n {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        if stitchwort_core::float::is_valid(seed) {
            out.push(seed);
        }
    }
    out
}

/// Literal expressions, elaborated to bits once, written into the JS from
/// the bits.
const LITERALS: &[&str] = &[
    "0.1 + 0.2",
    "80281.87 - 80000",
    "0.0 + -0.0",
    "-0.0 - 0.0",
    "1e308 + 1e308",
    "5e-324 - 5e-324",
    "-0",
    "9007199254740992 + 1",
    "0.49999999999999994 + 0.5",
    "Float.infinity - Float.infinity",
    // Stage 1b: the other rounding operations, and an `a * b - c` whose
    // fused multiply-add would differ (C5).
    "0.1 * 3.0",
    "0.1 * 0.1 - 0.01",
    "1.0 / 0.0",
    "1.0 / -0.0",
    "0.0 / 0.0",
    "-5.5 % 2.0",
    "1e308 * 10.0",
    "5e-324 / 2.0",
    "Float.round 0.49999999999999994",
    "Float.round (-0.5)",
    "Float.round (-0.0)",
    "Float.round 4503599627370497",
    "Float.round (-2.5)",
    "Float.ofNat 9007199254740993",
    "Float.ofNat 9007199254740995",
    "Float.ofInt (-9007199254740993)",
    "Float.ofNat (Nat.pow 2 64 + 1)",
    "Float.ofNat (Nat.pow 10 100)",
    "Float.ofInt (Int.neg (Nat.toInt (Nat.pow 10 100)))",
    "Float.ofNat (Nat.pow 2 1024)",
    "Float.ofNat (Nat.pow 2 1024 - Nat.pow 2 970)",
    "Float.ofNat (Nat.pow 2 1024 - Nat.pow 2 970 - 1)",
    "Float.ofInt (Int.neg (Nat.toInt (Nat.pow 2 1024 - Nat.pow 2 970 - 1)))",
];

/// The program: `results`, a list of numbers (bits; 1 and 0 for a `Bool`;
/// 0, 1, 2 for an `Ordering`; an `Option Int` as 0 for `None`, `2n + 1` for
/// `Some n` with `n >= 0` and `2m` for `Some (-m)`), and a `main` printing
/// them one per line. Its values are made with the record's constructor
/// from bits known only at run time, so the operations on them aren't
/// folded.
fn program(values: &[u64]) -> (String, usize) {
    let mut src = String::from(
        "import Std (Float, Int, List, Nat, Ord, Text)\n\n\
         type Timed = { startTime: Float, tag: Nat }\n\n\
         def build (b: Nat) (h: Float.isValid b = True): Float := { bits = b, valid = h }\n\n\
         def ofBits (b: Nat): Float := if h: Float.isValid b = True then build b h else Float.nan\n\n\
         def flag (b: Bool): Nat := if b then 1 else 0\n\n\
         def less (x: Float) (y: Float): Nat := if x < y then 1 else 0\n\n\
         def lessEq (x: Float) (y: Float): Nat := if x <= y then 1 else 0\n\n\
         def order: Ordering -> Nat\n  | Less => 0\n  | Equal => 1\n  | Greater => 2\n\n\
         def code: Option Int -> Nat\n  | None => 0\n  | Some (OfNat n) => 2 * n + 1\n  | Some (NegSucc n) => 2 * n + 2\n\n\
         def backAgain (x: Float): Float := match Float.toInt x with\n  | Some n => Float.ofInt n\n  | None => Float.nan\n\n",
    );
    for (i, bits) in values.iter().enumerate() {
        let _ = writeln!(src, "def v{i}: Float := ofBits {bits}\n");
    }
    let mut items = Vec::new();
    for i in 0..values.len() {
        items.push(format!("(v{i}).bits"));
        items.push(format!("(Float.neg v{i}).bits"));
        items.push(format!("(Float.abs v{i}).bits"));
        items.push(format!("flag (Float.isNaN v{i})"));
        items.push(format!("flag (Float.isFinite v{i})"));
        items.push(format!("(Float.floor v{i}).bits"));
        items.push(format!("(Float.ceil v{i}).bits"));
        items.push(format!("(Float.trunc v{i}).bits"));
        items.push(format!("(Float.round v{i}).bits"));
        items.push(format!("(Float.sqrt v{i}).bits"));
        items.push(format!("code (Float.toInt v{i})"));
        items.push(format!("(backAgain v{i}).bits"));
        // Against literals and a named constant: the operand isn't bound.
        items.push(format!("flag (v{i} < 1.5)"));
        items.push(format!("flag (0.0 <= v{i})"));
        items.push(format!("flag (Float.nan <= v{i})"));
        for j in 0..values.len() {
            items.push(format!("(Float.add v{i} v{j}).bits"));
            items.push(format!("(Float.sub v{i} v{j}).bits"));
            items.push(format!("(Float.mul v{i} v{j}).bits"));
            items.push(format!("(Float.div v{i} v{j}).bits"));
            items.push(format!("(Float.rem v{i} v{j}).bits"));
            items.push(format!("flag (v{i} == v{j})"));
            items.push(format!("flag (Float.ieeeEq v{i} v{j})"));
            items.push(format!("flag (Float.ieeeLt v{i} v{j})"));
            items.push(format!("flag (Float.ieeeLe v{i} v{j})"));
            items.push(format!("order (Float.compare v{i} v{j})"));
            items.push(format!("less v{i} v{j}"));
            items.push(format!("lessEq v{i} v{j}"));
            items.push(format!("flag (v{i} < v{j})"));
            items.push(format!("flag (v{i} <= v{j})"));
            items.push(format!("flag (Float.less v{i} v{j})"));
            items.push(format!("flag (Float.leq v{i} v{j})"));
            items.push(format!("order (Ord.compare v{i} v{j})"));
        }
    }
    for literal in LITERALS {
        items.push(format!("(({literal}): Float).bits"));
    }
    let all: Vec<String> = (0..values.len()).map(|i| format!("v{i}")).collect();
    let _ = writeln!(src, "def values: List Float := [{}]\n", all.join(", "));
    src.push_str(
        "def timed: List Timed := values.map (t => { startTime = t, tag = t.bits })\n\n\
         def bitsOf (xs: List Float): List Nat := xs.map (x => x.bits)\n\n",
    );
    let _ = writeln!(src, "def results: List Nat := [{}]\n", items.join(", "));
    let _ = writeln!(
        src,
        "def sorted: List Nat := List.concat [{}]\n",
        SORTED.join(", ")
    );
    src.push_str(
        "def main(): {IO} () := IO.print (List.append results sorted |> List.map (n => n.toText) |> Text.join '\\n')\n",
    );
    (src, items.len() + SORTED.len() * values.len())
}

/// The values sorted by the total order, as bits, after the program's
/// `results`: through the dictionary (`sort`, and `sortOn` a record's field,
/// which carries the bits as its `tag`) and by `<=` and `<` directly,
/// forwards and backwards.
const SORTED: [&str; 6] = [
    "bitsOf values.sort",
    "bitsOf values.reverse.sort",
    "List.sortOn timed .startTime |> List.map (e => e.tag)",
    "List.sortOn timed.reverse .startTime |> List.map (e => e.tag)",
    "bitsOf (List.sortWith values (a b => a <= b))",
    "bitsOf (List.sortWith values.reverse (a b => a < b))",
];

/// Per value: its bits and the 13 unary results; per pair, 17 results.
const PER_VALUE: usize = 15;
const PER_PAIR: usize = 17;

/// What each path computed, as numbers (in decimal: an `Option Int` from
/// `toInt` can be beyond 128 bits).
fn numbers(what: &str, text: &str, expected: usize) -> Vec<String> {
    let text = text.trim().trim_start_matches('[').trim_end_matches(']');
    let out: Vec<String> = text
        .split([',', '\n'])
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(|s| {
            assert!(
                s.bytes().all(|b| b.is_ascii_digit()),
                "{what}: not a number: {s:?}"
            );
            s.to_string()
        })
        .collect();
    assert_eq!(out.len(), expected, "{what}: {} results", out.len());
    out
}

/// A result as the test reports it: a bit pattern in hex.
fn shown(n: &str) -> String {
    match n.parse::<u128>() {
        Ok(k) => format!("{k:#018x}"),
        Err(_) => n.to_string(),
    }
}

fn stitchwort_run(path: &Path, js: bool) -> String {
    let mut command = crate::common::cli_with("run", if js { &["--js"] } else { &[] });
    command.arg("--no-cache");
    let out = command.arg(path).output().expect("start stitchwort");
    assert!(
        out.status.success(),
        "run (js: {js}): {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn web_pkg() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../web/pkg")
}

fn wasm_script() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../web/tests/float-wasm.mjs")
}

/// Whether `web/pkg` holds a bundle built from these sources. If it's absent,
/// or built from other sources (a stale bundle from before a change), the
/// WebAssembly kernel's path is left out, saying why and how to rebuild; with
/// STITCHWORT_REQUIRE_WASM=1 the test fails instead of skipping.
fn wasm_bundle_current() -> bool {
    let why = if !web_pkg().join("stitchwort_web_bg.wasm").exists() {
        "isn't built".to_string()
    } else {
        let out = Command::new("node")
            .arg(wasm_script())
            .arg("fingerprint")
            .output()
            .expect("run node");
        let theirs = String::from_utf8_lossy(&out.stdout).trim().to_string();
        let ours = stitchwort_cli::driver::SOURCE_FINGERPRINT;
        if out.status.success() && theirs == ours {
            return true;
        }
        format!(
            "was built from other sources (its fingerprint is {theirs:?}, these sources' {ours:?})"
        )
    };
    let rebuild = "Rebuild it with web/build.sh (or `cargo build -p stitchwort-web \
         --target wasm32-unknown-unknown --release` and `wasm-bindgen --target web \
         --no-typescript --out-dir web/pkg \
         target/wasm32-unknown-unknown/release/stitchwort_web.wasm`)";
    if stitchwort_core::env_flag::env_flag("STITCHWORT_REQUIRE_WASM") {
        panic!(
            "web/pkg {why}, and STITCHWORT_REQUIRE_WASM=1 requires the WebAssembly kernel. {rebuild}"
        );
    }
    eprintln!("web/pkg {why}: the WebAssembly kernel's path is left out. {rebuild}");
    false
}

#[test]
fn the_four_paths_agree_on_canonical_bits() {
    let mut values: Vec<u64> = EDGES.to_vec();
    values.extend(random_patterns(10));
    let (source, count) = program(&values);
    let dir = std::env::temp_dir().join(format!("stitchwort-float-paths-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("paths.sw");
    std::fs::write(&path, &source).expect("write source");

    // The native kernel: the playground's Evaluate path, in this process.
    let mut session = Session::new();
    session
        .load("paths.sw", &source)
        .unwrap_or_else(|e| panic!("{e:?}"));
    let expr = session
        .parse_expression("expression", "List.append results sorted")
        .expect("parses");
    let (kernel, _) = session.elab.eval_expr(&expr).expect("evaluates");
    let mut paths = vec![("native kernel", numbers("native kernel", &kernel, count))];

    // The WebAssembly kernel, if the bundle is built.
    if wasm_bundle_current() {
        let out = Command::new("node")
            .arg(wasm_script())
            .args(["evaluate"])
            .arg(&path)
            .arg("List.append results sorted")
            .output()
            .expect("run node");
        assert!(
            out.status.success(),
            "WebAssembly kernel: {}",
            String::from_utf8_lossy(&out.stderr)
        );
        let text = String::from_utf8_lossy(&out.stdout).into_owned();
        paths.push((
            "WebAssembly kernel",
            numbers("WebAssembly kernel", &text, count),
        ));
    }

    paths.push((
        "Rust runtime",
        numbers("Rust runtime", &stitchwort_run(&path, false), count),
    ));
    paths.push(("Node", numbers("Node", &stitchwort_run(&path, true), count)));
    let _ = std::fs::remove_dir_all(&dir);

    let (base_name, base) = &paths[0];
    let mut wrong = Vec::new();
    for (name, results) in &paths[1..] {
        for (i, (a, b)) in base.iter().zip(results).enumerate() {
            if a != b {
                wrong.push(format!(
                    "result {i}: {base_name} {}, {name} {}",
                    shown(a),
                    shown(b)
                ));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "{} disagreements:\n{}",
        wrong.len(),
        wrong[..wrong.len().min(20)].join("\n")
    );
    // Every value made from its bits gives them back, through every path.
    for (k, bits) in values.iter().enumerate() {
        let stride = PER_VALUE + PER_PAIR * values.len();
        assert_eq!(base[k * stride], bits.to_string(), "value {k}");
    }
    // And every sort is IEEE 754's totalOrder, by Rust's `f64::total_cmp`
    // (one NaN, so no payloads to tell apart).
    let mut expected = values.clone();
    expected.sort_by(|a, b| f64::from_bits(*a).total_cmp(&f64::from_bits(*b)));
    let expected: Vec<String> = expected.iter().map(u64::to_string).collect();
    let sorts = &base[count - SORTED.len() * values.len()..];
    for (sort, got) in SORTED.iter().zip(sorts.chunks(values.len())) {
        assert_eq!(got, &expected[..], "{sort}");
    }
    eprintln!(
        "{count} results agree on {} paths: {}",
        paths.len(),
        paths.iter().map(|(n, _)| *n).collect::<Vec<_>>().join(", ")
    );
}

/// Doubles whose `String(x)` exercises each of `Number::toString`'s layouts:
/// whole numbers up to 10^21, decimals down to 10^-6, and exponents beyond.
const PRINTED: &[f64] = &[
    1e21,
    1e20,
    123456789012345680000.0,
    1e-6,
    1e-7,
    0.000001234,
    123.0,
    100.0,
    0.1,
    0.30000000000000004,
    80281.87,
    1.5e-7,
    2.5e300,
    -1234.5678,
    9007199254740993.0,
];

/// `toText` (§2.6, D688): the Rust runtime's is Node's `String(x)` on every
/// edge value, the doubles above and 5,000 random patterns (a test of the two
/// interpretations shipped, not a promise across engines); `toSource` is the
/// same on both, and reads back, as Stitchwort source the kernel elaborates,
/// as the same bits.
#[test]
fn to_text_is_string_and_to_source_reads_back() {
    let mut values: Vec<u64> = EDGES.to_vec();
    values.extend(PRINTED.iter().map(|x| x.to_bits()));
    values.extend(random_patterns(5000));
    let mut src = String::from(
        "import Std (Float, List, Text)\n\n\
         def build (b: Nat) (h: Float.isValid b = True): Float := { bits = b, valid = h }\n\n\
         def ofBits (b: Nat): Float := if h: Float.isValid b = True then build b h else Float.nan\n\n",
    );
    let list = |f: &str| {
        (0..values.len())
            .map(|i| format!("{f} (ofBits {})", values[i]))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let _ = writeln!(src, "def texts: List Text := [{}]\n", list("Float.toText"));
    let _ = writeln!(
        src,
        "def sources: List Text := [{}]\n",
        list("Float.toSource")
    );
    src.push_str(
        "def main(): {IO} () := IO.print (List.append texts sources |> Text.join '\\n')\n",
    );
    let dir = std::env::temp_dir().join(format!("stitchwort-float-text-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("text.sw");
    std::fs::write(&path, &src).expect("write source");
    let rust = stitchwort_run(&path, false);
    let node = stitchwort_run(&path, true);
    let _ = std::fs::remove_dir_all(&dir);
    let rust: Vec<&str> = rust.lines().collect();
    let node: Vec<&str> = node.lines().collect();
    assert_eq!(rust.len(), 2 * values.len(), "{rust:?}");
    let wrong: Vec<String> = rust
        .iter()
        .zip(&node)
        .enumerate()
        .filter(|(_, (a, b))| a != b)
        .map(|(i, (a, b))| {
            format!(
                "{:#018x}: Rust runtime {a:?}, Node {b:?}",
                values[i % values.len()]
            )
        })
        .collect();
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    // Spot checks of `String`'s layouts.
    for (x, text) in [
        (1e21, "1e+21"),
        (1e-7, "1e-7"),
        (1e-6, "0.000001"),
        (123.0, "123"),
        (-0.0, "0"),
        (f64::NEG_INFINITY, "-Infinity"),
        (0.30000000000000004, "0.30000000000000004"),
    ] {
        let i = values
            .iter()
            .position(|b| *b == x.to_bits())
            .expect("printed");
        assert_eq!(rust[i], text, "{x}");
    }

    // `toSource` reads back as the same double.
    let sources = &rust[values.len()..];
    let mut back = String::from("import Std (Float, List)\n\n");
    let items: Vec<String> = sources
        .iter()
        .map(|s| format!("(({s}): Float).bits"))
        .collect();
    let _ = writeln!(back, "def back: List Nat := [{}]", items.join(", "));
    let mut session = Session::new();
    session
        .load("back.sw", &back)
        .unwrap_or_else(|e| panic!("{e:?}"));
    let expr = session
        .parse_expression("expression", "back")
        .expect("parses");
    let (kernel, _) = session.elab.eval_expr(&expr).expect("evaluates");
    let got = numbers("toSource read back", &kernel, values.len());
    for (k, bits) in values.iter().enumerate() {
        assert_eq!(got[k], bits.to_string(), "{:?} read back", sources[k]);
    }
}

/// The kernel gate (§3.4, crates/driver/src/float_gate.rs) on the
/// WebAssembly kernel, if the bundle is built: every check passes there too.
#[test]
fn the_gate_passes_on_the_webassembly_kernel() {
    if !wasm_bundle_current() {
        return;
    }
    let out = Command::new("node")
        .arg(wasm_script())
        .arg("gate")
        .output()
        .expect("run node");
    let report = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{report}");
    assert!(report.contains("3483 passed, 0 failed"), "{report}");
}

/// Pairs whose sum or difference lands on a rounding boundary
/// (docs/proposals/float-laws.md §8): ties either way, results just under
/// and over a power of two, overflow at exactly the halfway point past the
/// largest double, subnormal results, and the sign of a zero result.
fn boundary_pairs() -> Vec<(f64, f64)> {
    let two = |k: i32| 2f64.powi(k);
    let max = f64::MAX;
    let tiny = f64::from_bits(1);
    let min_normal = f64::MIN_POSITIVE;
    let mut pairs = vec![
        // Ties: to even, down and up.
        (1.0, two(-53)),
        (1.0, 3.0 * two(-53)),
        (1.0 + two(-52), two(-53)),
        (9007199254740992.0, 1.0),
        (9007199254740992.0, 3.0),
        (-1.0, -two(-53)),
        // Just under and over powers of two.
        (2.0 - two(-52), two(-53)),
        (2.0 - two(-52), two(-54)),
        (2.0, -two(-53)),
        (2.0, -two(-52)),
        (1.0, -two(-54)),
        (1.0, -two(-53)),
        (1.0, -(two(-53) + two(-105))),
        (two(1023), two(1023) - two(970)),
        // Overflow: halfway past the largest double goes to infinity, just
        // below it stays.
        (max, two(970)),
        (max, two(969)),
        (max, two(970) - two(917)),
        (max, max),
        (-max, -two(970)),
        (-max, -two(969)),
        // Subnormal results.
        (tiny, tiny),
        (min_normal, -tiny),
        (min_normal, -min_normal),
        (3.0 * tiny, -2.0 * tiny),
        (1e-300, tiny),
        (min_normal + tiny, -min_normal),
        // The sign of a zero.
        (0.0, 0.0),
        (-0.0, -0.0),
        (-0.0, 0.0),
        (0.0, -0.0),
        (1.5, -1.5),
        (-1.5, 1.5),
        (tiny, -tiny),
        (-tiny, tiny),
        (-0.0, tiny),
        // Infinities and the NaN.
        (f64::INFINITY, f64::NEG_INFINITY),
        (f64::INFINITY, f64::INFINITY),
        (f64::NEG_INFINITY, max),
        (f64::NAN, 1.0),
        // Cancellation, and operands far apart.
        (1e16, 1.0),
        (0.1, 0.2),
        (1e308, -1e292),
        (two(-1000), two(1000)),
    ];
    // Random operands of close magnitude, where rounding decides the most.
    let mut seed = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    while pairs.len() < 200 {
        let a = next();
        let shift = (next() % 60) << 52;
        let b = (a & !(0x7FF << 52)) | ((a & (0x7FF << 52)).saturating_sub(shift) & (0x7FF << 52));
        let b = if next() % 2 == 0 { b ^ (1 << 63) } else { b };
        let (x, y) = (f64::from_bits(a), f64::from_bits(b));
        if x.is_finite() && y.is_finite() {
            pairs.push((x, y));
        }
    }
    pairs
}

/// `Float.add` and `Float.sub`, computed by the kernel through their
/// definitions, give the machine's bits on [`boundary_pairs`], as do the
/// Rust runtime and Node.
#[test]
fn add_and_sub_round_like_the_hardware() {
    let pairs = boundary_pairs();
    let bits = |x: f64| stitchwort_core::float::canonical_bits(x);
    let mut src = String::from(
        "import Std (Float, List, Nat, Text)\n\n\
         def build (b: Nat) (h: Float.isValid b = True): Float := { bits = b, valid = h }\n\n\
         def ofBits (b: Nat): Float := if h: Float.isValid b = True then build b h else Float.nan\n\n",
    );
    let mut items = Vec::new();
    let mut expected = Vec::new();
    for &(x, y) in &pairs {
        let (a, b) = (bits(x), bits(y));
        items.push(format!("(Float.add (ofBits {a}) (ofBits {b})).bits"));
        items.push(format!("(Float.sub (ofBits {a}) (ofBits {b})).bits"));
        expected.push(bits(x + y).to_string());
        expected.push(bits(x - y).to_string());
    }
    let _ = writeln!(src, "def results: List Nat := [{}]\n", items.join(", "));
    src.push_str(
        "def main(): {IO} () := IO.print (results |> List.map (n => n.toText) |> Text.join '\\n')\n",
    );
    let dir = std::env::temp_dir().join(format!("stitchwort-float-round-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("round.sw");
    std::fs::write(&path, &src).expect("write source");

    let mut session = Session::new();
    session
        .load("round.sw", &src)
        .unwrap_or_else(|e| panic!("{e:?}"));
    let expr = session
        .parse_expression("expression", "results")
        .expect("parses");
    let (kernel, _) = session.elab.eval_expr(&expr).expect("evaluates");
    let count = expected.len();
    let paths = [
        ("kernel", numbers("kernel", &kernel, count)),
        (
            "Rust runtime",
            numbers("Rust runtime", &stitchwort_run(&path, false), count),
        ),
        ("Node", numbers("Node", &stitchwort_run(&path, true), count)),
    ];
    let _ = std::fs::remove_dir_all(&dir);
    let mut wrong = Vec::new();
    for (name, results) in &paths {
        for (i, (got, want)) in results.iter().zip(&expected).enumerate() {
            if got != want {
                let (x, y) = pairs[i / 2];
                let op = if i % 2 == 0 { '+' } else { '-' };
                wrong.push(format!(
                    "{name}: {x:e} {op} {y:e} gave {}, the machine {}",
                    shown(got),
                    shown(want)
                ));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "{} disagreements:\n{}",
        wrong.len(),
        wrong[..wrong.len().min(20)].join("\n")
    );
}

/// Products that land on rounding boundaries: ties either way, results just
/// under and over a power of two, overflow at and just below the halfway
/// point past the largest double, subnormal results and underflow to a
/// zero, signed zeros, and the special cases.
fn mul_boundary_pairs() -> Vec<(f64, f64)> {
    let two = |k: i32| 2f64.powi(k);
    let max = f64::MAX;
    let tiny = f64::from_bits(1);
    let min_normal = f64::MIN_POSITIVE;
    // 1 + 2^-52: its square is 1 + 2^-51 + 2^-104, just above a pattern.
    let next = 1.0 + two(-52);
    vec![
        // Exact ties: (2^26 + 1)^2 = 2^52 + 2^27 + 1 is exact; times 2 and
        // 3 it needs 54 bits, a tie, to even down and up.
        (67108865.0, 67108865.0 * 2.0),
        (67108865.0 * 3.0, 67108865.0),
        (1.5, 1.0 + two(-52)),
        (1.5, 1.0 + 3.0 * two(-52)),
        (3.0, 1.0 + two(-52)),
        (next, next),
        (next, 1.0 - two(-53)),
        (1.0 - two(-53), 1.0 - two(-53)),
        (-1.5, 1.0 + two(-52)),
        // Just under and over powers of two.
        (2.0 - two(-52), 1.0 + two(-52)),
        (2.0 - two(-52), 2.0 - two(-52)),
        (1.0 + two(-52), 1.0 - two(-53)),
        // Overflow: 2^1023 * (2 - 2^-53) is halfway past the largest double.
        (two(1023), 2.0 - two(-53)),
        (two(1023), 2.0 - two(-52)),
        (two(1023), 2.0),
        (max, 1.0 + two(-52)),
        (max, 1.0),
        (-max, 2.0),
        (1e308, 10.0),
        // Subnormal results, ties among them, and underflow to a zero.
        (tiny, 0.5),
        (tiny, 1.5),
        (3.0 * tiny, 0.5),
        (tiny, -0.5),
        (min_normal, 0.5),
        (min_normal, 1.0 - two(-53)),
        (min_normal, two(-52)),
        (min_normal, two(-53)),
        (min_normal, 1.5 * two(-53)),
        (1e-200, 1e-200),
        (-1e-200, 1e-200),
        (two(-537), two(-537)),
        (two(-538), two(-537)),
        // Signed zeros.
        (0.0, 0.0),
        (-0.0, 0.0),
        (-0.0, -0.0),
        (0.0, -1.5),
        (-0.0, max),
        (tiny, -tiny),
        // Infinities and the NaN.
        (f64::INFINITY, 0.0),
        (f64::NEG_INFINITY, -0.0),
        (f64::INFINITY, -tiny),
        (f64::NEG_INFINITY, f64::NEG_INFINITY),
        (f64::NAN, 0.0),
        (1.0, f64::NAN),
        // Ordinary values, and by 10, as decimal code does.
        (0.1, 3.0),
        (0.1, 10.0),
        (123456789.0, 10.0),
        (9007199254740991.0, 10.0),
        (0.1, 0.1),
    ]
}

/// The f64_mul slice of Berkeley TestFloat (testfloat_f64_mul.txt): its
/// operands and the result it gives, NaNs made canonical.
fn testfloat_mul_cases() -> Vec<(u64, u64, u64)> {
    let canonical = |h: &str| {
        let bits = u64::from_str_radix(h, 16).expect("hex");
        stitchwort_core::float::canonical_bits(f64::from_bits(bits))
    };
    include_str!("testfloat_f64_mul.txt")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|l| {
            let f: Vec<&str> = l.split_whitespace().collect();
            (canonical(f[0]), canonical(f[1]), canonical(f[2]))
        })
        .collect()
}

/// `Float.mul`, computed by the kernel through its definition, gives the
/// machine's bits on [`mul_boundary_pairs`] and on TestFloat's cases, as do
/// the Rust runtime and Node; and the machine gives TestFloat's results.
#[test]
fn mul_rounds_like_the_hardware() {
    let bits = |x: f64| stitchwort_core::float::canonical_bits(x);
    let mut pairs: Vec<(u64, u64)> = mul_boundary_pairs()
        .into_iter()
        .map(|(x, y)| (bits(x), bits(y)))
        .collect();
    for (a, b, r) in testfloat_mul_cases() {
        assert_eq!(
            bits(f64::from_bits(a) * f64::from_bits(b)),
            r,
            "the machine and TestFloat on {a:#018x} * {b:#018x}"
        );
        pairs.push((a, b));
    }
    let items = pairs
        .iter()
        .map(|(a, b)| format!("(Float.mul (ofBits {a}) (ofBits {b})).bits"))
        .collect();
    let expected = pairs
        .iter()
        .map(|&(a, b)| bits(f64::from_bits(a) * f64::from_bits(b)))
        .collect();
    agree_with_the_machine("mul", items, expected, |i| {
        let (a, b) = pairs[i];
        format!("{a:#018x} * {b:#018x}")
    });
}

/// `Float.sqrt` on the edges (the zeros, the infinities, the NaN, negative
/// numbers, the subnormals, the largest double), perfect squares, `2`, `0.1`
/// and random patterns. The kernel through `Float.Model.sqrtBits`, the Rust
/// runtime and Node (`Math.sqrt`) all give the machine's correctly rounded
/// bits.
#[test]
fn sqrt_rounds_like_the_hardware() {
    let mut values = vec![
        0.0,
        -0.0,
        1.0,
        2.0,
        4.0,
        0.25,
        9.0,
        1e300,
        0.1,
        -1.0,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        f64::MAX,
        f64::MIN_POSITIVE,
        f64::from_bits(1),
        f64::from_bits(3),
        f64::from_bits(0x000F_FFFF_FFFF_FFFF),
        (1u64 << 52) as f64 * 3.0,
    ];
    values.extend(random_patterns(60).into_iter().map(f64::from_bits));
    let bits = |x: f64| stitchwort_core::float::canonical_bits(x);
    let items = values
        .iter()
        .map(|&x| format!("(Float.sqrt (ofBits {})).bits", bits(x)))
        .collect();
    let expected = values.iter().map(|&x| bits(x.sqrt())).collect();
    agree_with_the_machine("sqrt", items, expected, |i| {
        format!("sqrt {:#018x}", bits(values[i]))
    });
}

/// Checks that the kernel (through the definitions), the Rust runtime and
/// Node each compute `expected` (canonical bits) for `items`, expressions of
/// `ofBits n` whose `.bits` they are; `describe` names item `i` in a
/// failure.
fn agree_with_the_machine(
    tag: &str,
    items: Vec<String>,
    expected: Vec<u64>,
    describe: impl Fn(usize) -> String,
) {
    let mut src = String::from(
        "import Std (Float, List, Nat, Text)\n\n\
         def build (b: Nat) (h: Float.isValid b = True): Float := { bits = b, valid = h }\n\n\
         def ofBits (b: Nat): Float := if h: Float.isValid b = True then build b h else Float.nan\n\n",
    );
    let expected: Vec<String> = expected.iter().map(u64::to_string).collect();
    let _ = writeln!(src, "def results: List Nat := [{}]\n", items.join(", "));
    src.push_str(
        "def main(): {IO} () := IO.print (results |> List.map (n => n.toText) |> Text.join '\\n')\n",
    );
    let dir = std::env::temp_dir().join(format!("stitchwort-float-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join(format!("{tag}.sw"));
    std::fs::write(&path, &src).expect("write source");

    let mut session = Session::new();
    session
        .load("machine.sw", &src)
        .unwrap_or_else(|e| panic!("{e:?}"));
    let expr = session
        .parse_expression("expression", "results")
        .expect("parses");
    let (kernel, _) = session.elab.eval_expr(&expr).expect("evaluates");
    let count = expected.len();
    let paths = [
        ("kernel", numbers("kernel", &kernel, count)),
        (
            "Rust runtime",
            numbers("Rust runtime", &stitchwort_run(&path, false), count),
        ),
        ("Node", numbers("Node", &stitchwort_run(&path, true), count)),
    ];
    let _ = std::fs::remove_dir_all(&dir);
    let mut wrong = Vec::new();
    for (name, results) in &paths {
        for (i, (got, want)) in results.iter().zip(&expected).enumerate() {
            if got != want {
                wrong.push(format!(
                    "{name}: {} gave {}, the machine {}",
                    describe(i),
                    shown(got),
                    shown(want)
                ));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "{} disagreements:\n{}",
        wrong.len(),
        wrong[..wrong.len().min(20)].join("\n")
    );
}

/// Quotients on rounding boundaries. In the normal range a quotient is
/// never exactly halfway between two doubles, so the ties are subnormal
/// results (an odd number of half units, to even); beside them, quotients
/// just either side of a tie, results just under and over a power of two,
/// overflow and underflow, and the special cases.
fn div_boundary_pairs() -> Vec<(f64, f64)> {
    let two = |k: i32| 2f64.powi(k);
    let max = f64::MAX;
    let tiny = f64::from_bits(1);
    let min_normal = f64::MIN_POSITIVE;
    let largest_subnormal = f64::from_bits(0x000F_FFFF_FFFF_FFFF);
    vec![
        // Exact ties, all subnormal: 0.5, 1.5, 2.5 and 3.5 units, to even.
        (tiny, 2.0),
        (3.0 * tiny, 2.0),
        (5.0 * tiny, 2.0),
        (7.0 * tiny, 2.0),
        (-tiny, 2.0),
        (3.0 * tiny, -2.0),
        (3.0 * tiny, 6.0),
        (min_normal, two(53)),
        (3.0 * min_normal, two(53)),
        (largest_subnormal, 2.0),
        // Just either side of those ties.
        (min_normal * (1.0 + two(-52)), two(53)),
        (min_normal * (1.0 - two(-53)), two(53)),
        (3.0 * min_normal, two(53) + 2.0),
        (3.0 * min_normal, two(53) - 1.0),
        (tiny, 2.0 - two(-52)),
        (tiny, 2.0 + two(-51)),
        // Normal quotients near halfway, either way.
        (1.0, 3.0),
        (2.0, 3.0),
        (1.0, 1.0 + two(-52)),
        (1.0 + two(-52), 1.0 + two(-51)),
        (1.0, 1.0 - two(-53)),
        (2.0 - two(-52), 1.0 + two(-52)),
        (1.0 + two(-51), 1.0 + two(-52)),
        (9007199254740991.0, 9007199254740990.0),
        (0.3, 0.1),
        (1.0, 10.0),
        (123456789.0, 10.0),
        (9007199254740991.0, 10.0),
        (-7.0, 0.1),
        // Just under and over powers of two.
        (two(1023), two(1023) + two(971)),
        (two(1023) - two(970), two(1023)),
        (1.0, 1.0 - two(-52)),
        // Overflow, and just below it.
        (max, 0.5),
        (max, 1.0 - two(-53)),
        (max, 1.0 - two(-52) * 0.5 - two(-53)),
        (max, 1.0 + two(-52)),
        (two(1000), two(-30)),
        (-max, two(-1)),
        // Underflow to a zero and to the smallest subnormal.
        (tiny, 3.0),
        (tiny, 1.5),
        (tiny, max),
        (-tiny, max),
        (min_normal, max),
        (1e-300, 1e300),
        // Division by a zero, the infinities and the NaN, with their signs.
        (1.0, 0.0),
        (1.0, -0.0),
        (-1.0, 0.0),
        (0.0, 0.0),
        (-0.0, 0.0),
        (0.0, -1.0),
        (-0.0, -1.0),
        (f64::INFINITY, f64::INFINITY),
        (f64::INFINITY, -2.0),
        (f64::NEG_INFINITY, 0.0),
        (1.0, f64::INFINITY),
        (-1.0, f64::INFINITY),
        (1.0, f64::NEG_INFINITY),
        (f64::NAN, 1.0),
        (1.0, f64::NAN),
        (0.0, f64::NAN),
    ]
}

/// The f64_div slice of Berkeley TestFloat (testfloat_f64_div.txt): its
/// operands and the result it gives, NaNs made canonical.
fn testfloat_div_cases() -> Vec<(u64, u64, u64)> {
    let canonical = |h: &str| {
        let bits = u64::from_str_radix(h, 16).expect("hex");
        stitchwort_core::float::canonical_bits(f64::from_bits(bits))
    };
    include_str!("testfloat_f64_div.txt")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|l| {
            let f: Vec<&str> = l.split_whitespace().collect();
            (canonical(f[0]), canonical(f[1]), canonical(f[2]))
        })
        .collect()
}

/// `Float.div`, computed by the kernel through its definition, gives the
/// machine's bits on [`div_boundary_pairs`] and on TestFloat's cases, as do
/// the Rust runtime and Node; and the machine gives TestFloat's results.
#[test]
fn div_rounds_like_the_hardware() {
    let bits = |x: f64| stitchwort_core::float::canonical_bits(x);
    let mut pairs: Vec<(u64, u64)> = div_boundary_pairs()
        .into_iter()
        .map(|(x, y)| (bits(x), bits(y)))
        .collect();
    for (a, b, r) in testfloat_div_cases() {
        assert_eq!(
            bits(f64::from_bits(a) / f64::from_bits(b)),
            r,
            "the machine and TestFloat on {a:#018x} / {b:#018x}"
        );
        pairs.push((a, b));
    }
    let items = pairs
        .iter()
        .map(|(a, b)| format!("(Float.div (ofBits {a}) (ofBits {b})).bits"))
        .collect();
    let expected = pairs
        .iter()
        .map(|&(a, b)| bits(f64::from_bits(a) / f64::from_bits(b)))
        .collect();
    agree_with_the_machine("div", items, expected, |i| {
        let (a, b) = pairs[i];
        format!("{a:#018x} / {b:#018x}")
    });
}

/// Values where `floor`, `ceil`, `trunc` and `round` decide the most: the
/// zeros, the infinities, the NaN, halves and the doubles beside them, the
/// neighbourhoods of 2^52 (above which every double is whole) and 2^53,
/// subnormals and the largest doubles.
fn whole_number_edges() -> Vec<f64> {
    let two = |k: i32| 2f64.powi(k);
    let mut out = vec![
        0.0,
        -0.0,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        f64::from_bits(1),
        -f64::from_bits(1),
        f64::from_bits(0x000F_FFFF_FFFF_FFFF),
        f64::MIN_POSITIVE,
        f64::MAX,
        -f64::MAX,
        1e300,
        0.1,
        -0.1,
        1.0 - two(-53),
        -(1.0 - two(-53)),
        1.0,
        -1.0,
        1.0 + two(-52),
        -(1.0 + two(-52)),
    ];
    // Halves, and the doubles just below and above them.
    for k in [0.5, 1.5, 2.5, 3.5, 1e6 + 0.5, two(51) + 0.5, two(52) - 0.5] {
        for x in [k, -k] {
            out.push(x);
            out.push(f64::from_bits(x.to_bits() - 1));
            out.push(f64::from_bits(x.to_bits() + 1));
        }
    }
    for x in [
        two(52),
        two(52) + 1.0,
        two(52) - 1.0,
        two(53),
        two(53) - 1.0,
        two(53) + 2.0,
    ] {
        out.push(x);
        out.push(-x);
    }
    out
}

/// The f64_roundToInt slice of Berkeley TestFloat
/// (testfloat_f64_round_to_int.txt): the operation, its operand and the
/// result TestFloat gives, NaNs made canonical.
fn testfloat_round_to_int_cases() -> Vec<(String, u64, u64)> {
    let canonical = |h: &str| {
        let bits = u64::from_str_radix(h, 16).expect("hex");
        stitchwort_core::float::canonical_bits(f64::from_bits(bits))
    };
    include_str!("testfloat_f64_round_to_int.txt")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.trim().is_empty())
        .map(|l| {
            let f: Vec<&str> = l.split_whitespace().collect();
            (f[0].to_string(), canonical(f[1]), canonical(f[2]))
        })
        .collect()
}

/// `floor`, `ceil`, `trunc` and `round` (JS's `Math.round`, ties towards
/// +infinity) on [`whole_number_edges`], and the first three on TestFloat's
/// cases; `%` (JS's, truncating) on pairs of edges and on pairs where the
/// quotient is huge or tiny. The kernel through the definitions, the Rust
/// runtime and Node all give the machine's bits, and the machine gives
/// TestFloat's.
#[test]
fn rem_and_whole_numbers_match_the_hardware() {
    let bits = |x: f64| stitchwort_core::float::canonical_bits(x);
    let mut cases: Vec<(&str, u64, u64)> = Vec::new();
    let unary = |name: &str, x: f64| -> f64 {
        match name {
            "floor" => x.floor(),
            "ceil" => x.ceil(),
            "trunc" => x.trunc(),
            _ => stitchwort_core::float::js_round(x),
        }
    };
    for x in whole_number_edges() {
        for name in ["floor", "ceil", "trunc", "round"] {
            cases.push((name, bits(x), 0));
        }
    }
    let testfloat = testfloat_round_to_int_cases();
    for (name, a, r) in &testfloat {
        assert_eq!(
            bits(unary(name, f64::from_bits(*a))),
            *r,
            "the machine and TestFloat on {name} {a:#018x}"
        );
    }
    for (name, a, _) in &testfloat {
        let name = match name.as_str() {
            "floor" => "floor",
            "ceil" => "ceil",
            _ => "trunc",
        };
        cases.push((name, *a, 0));
    }
    let two = |k: i32| 2f64.powi(k);
    let edges = [
        0.0,
        -0.0,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        f64::from_bits(1),
        f64::MAX,
        -5.5,
        2.0,
        0.1,
        -3.0,
        two(53) + 2.0,
    ];
    for &x in &edges {
        for &y in &edges {
            cases.push(("rem", bits(x), bits(y)));
        }
    }
    for (x, y) in [
        (f64::MAX, f64::from_bits(1)),
        (f64::MAX, 3.0),
        (-f64::MAX, 0.1),
        (1e300, 1e-300),
        (f64::from_bits(1), f64::MAX),
        (two(53) + 2.0, 3.0),
        (-two(53), 0.1),
        (5.5, -2.0),
        (1.0, 0.1),
        (-1.0, 0.1),
        (6.0, 3.0),
        (-6.0, 3.0),
        (0.30000000000000004, 0.1),
    ] {
        cases.push(("rem", bits(x), bits(y)));
    }
    let items = cases
        .iter()
        .map(|&(name, a, b)| match name {
            "rem" => format!("(Float.rem (ofBits {a}) (ofBits {b})).bits"),
            _ => format!("(Float.{name} (ofBits {a})).bits"),
        })
        .collect();
    let expected = cases
        .iter()
        .map(|&(name, a, b)| {
            let x = f64::from_bits(a);
            bits(match name {
                "rem" => x % f64::from_bits(b),
                _ => unary(name, x),
            })
        })
        .collect();
    agree_with_the_machine("whole", items, expected, |i| {
        let (name, a, b) = cases[i];
        match name {
            "rem" => format!("{a:#018x} % {b:#018x}"),
            _ => format!("{name} {a:#018x}"),
        }
    });
}
