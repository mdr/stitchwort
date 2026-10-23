//! The four execution paths of `Float` (docs/proposals/float.md §3.3, §7.4):
//! the native kernel, the WebAssembly kernel, the Rust runtime and Node
//! compute the same canonical bits for stage 1a's operations (`add`, `sub`,
//! `neg`, `abs`, `isNaN`, `==`, `Float.ieeeEq`, the record's constructor and
//! `.bits`), on every pair from an edge set and some random patterns, and on
//! literals. Results are compared as canonical bit patterns, shown in hex,
//! never as JSON numbers (which would hide `-0` and lose `NaN`).
//!
//! The WebAssembly kernel is the playground's bundle in `web/pkg`, run by
//! `web/tests/float-wasm.mjs` under Node. Build it first (`web/build.sh`, or
//! its `cargo build --target wasm32-unknown-unknown` and `wasm-bindgen`
//! steps); without it that path is left out, and the test says so.

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
];

/// The program: `results`, a list of numbers (bits, or 1 and 0 for a
/// `Bool`), and a `main` printing them one per line. Its values are made
/// with the record's constructor from bits known only at run time.
fn program(values: &[u64]) -> (String, usize) {
    let mut src = String::from(
        "import Std (Float, List, Text)\n\n\
         def build (b: Nat) (h: Float.isValid b = True): Float := { bits = b, valid = h }\n\n\
         def ofBits (b: Nat): Float := if h: Float.isValid b = True then build b h else Float.nan\n\n\
         def flag (b: Bool): Nat := if b then 1 else 0\n\n",
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
        for j in 0..values.len() {
            items.push(format!("(Float.add v{i} v{j}).bits"));
            items.push(format!("(Float.sub v{i} v{j}).bits"));
            items.push(format!("flag (v{i} == v{j})"));
            items.push(format!("flag (Float.ieeeEq v{i} v{j})"));
        }
    }
    for literal in LITERALS {
        items.push(format!("(({literal}): Float).bits"));
    }
    let _ = writeln!(src, "def results: List Nat := [{}]\n", items.join(", "));
    src.push_str("def main(): {IO} () := IO.print (results |> List.map (n => n.toText) |> Text.join '\\n')\n");
    (src, items.len())
}

/// What each path computed, as numbers.
fn numbers(what: &str, text: &str, expected: usize) -> Vec<u128> {
    let text = text.trim().trim_start_matches('[').trim_end_matches(']');
    let out: Vec<u128> = text
        .split([',', '\n'])
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(|s| {
            s.parse()
                .unwrap_or_else(|_| panic!("{what}: not a number: {s:?}"))
        })
        .collect();
    assert_eq!(out.len(), expected, "{what}: {} results", out.len());
    out
}

fn stitchwort_run(path: &Path, js: bool) -> String {
    let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
    command.args(["run", "--no-cache"]);
    if js {
        command.arg("--js");
    }
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
        .parse_expression("expression", "results")
        .expect("parses");
    let (kernel, _) = session.elab.eval_expr(&expr).expect("evaluates");
    let mut paths = vec![("native kernel", numbers("native kernel", &kernel, count))];

    // The WebAssembly kernel, if the bundle is built.
    if web_pkg().join("stitchwort_web_bg.wasm").exists() {
        let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../web/tests/float-wasm.mjs");
        let out = Command::new("node")
            .arg(&script)
            .args(["evaluate"])
            .arg(&path)
            .arg("results")
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
    } else {
        eprintln!("web/pkg isn't built: the WebAssembly kernel's path is left out");
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
                    "result {i}: {base_name} {a:#018x}, {name} {b:#018x}"
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
        let stride = 4 + 4 * values.len();
        assert_eq!(base[k * stride], u128::from(*bits), "value {k}");
    }
}

/// The kernel gate (§3.4, crates/driver/src/float_gate.rs) on the
/// WebAssembly kernel, if the bundle is built: every check passes there too.
#[test]
fn the_gate_passes_on_the_webassembly_kernel() {
    if !web_pkg().join("stitchwort_web_bg.wasm").exists() {
        eprintln!("web/pkg isn't built: the gate on the WebAssembly kernel is left out");
        return;
    }
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../web/tests/float-wasm.mjs");
    let out = Command::new("node")
        .arg(&script)
        .arg("gate")
        .output()
        .expect("run node");
    let report = String::from_utf8_lossy(&out.stdout);
    assert!(out.status.success(), "{report}");
    assert!(report.contains("107 passed, 0 failed"), "{report}");
}
