//! `Float` at run time (docs/proposals/float.md §3.5, §7.4): the generated
//! JS's canonical-bits module and its two laws, and a program using the
//! record's constructor and `.bits` printing the same under the Rust runtime
//! and Node. Requires `node` on the PATH (the Nix dev shell provides it).

use std::path::PathBuf;
use std::process::Command;

fn temp_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("stitchwort-float-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

/// Runs `script` (an ES module) under Node: its standard output.
fn node(name: &str, script: &str) -> String {
    let dir = temp_dir(name);
    std::fs::write(dir.join("test.mjs"), script).expect("write script");
    let out = Command::new("node")
        .arg("test.mjs")
        .current_dir(&dir)
        .output()
        .expect("run `node` (is it on the PATH? `nix develop` provides it)");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        out.status.success(),
        "node failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// `toCanonicalBits(fromCanonicalBits(b)) === b` for every valid canonical
/// pattern `b`, and `Object.is(fromCanonicalBits(toCanonicalBits(x)), x)`
/// for every number `x`, on the edge set, random patterns and NaNs of several
/// signs and payloads (made with a typed array, as external code could).
#[test]
fn the_canonical_bits_module_keeps_its_two_laws() {
    let script = format!(
        r#"{module}
const edges = [0n, 0x8000000000000000n, 1n, 0x8000000000000001n, 0x3ff0000000000000n,
  0xbff0000000000000n, 0x3fe0000000000000n, 0xbfe0000000000000n, 0x4004000000000000n,
  0xc004000000000000n, 0x7fefffffffffffffn, 0xffefffffffffffffn, 0x7ff0000000000000n,
  0xfff0000000000000n, 0x7ff8000000000000n, 0x4340000000000000n, 0x4340000000000001n,
  0x433fffffffffffffn, 0x3fdfffffffffffffn, 0x4330000000000001n, 0x000fffffffffffffn];
const valid = (b) => b <= 0x7ff0000000000000n || b === 0x7ff8000000000000n
  || (b >= 0x8000000000000000n && b <= 0xfff0000000000000n);
let seed = 0x2545f4914f6cdd1dn;
const next = () => {{
  seed ^= (seed << 13n) & 0xffffffffffffffffn;
  seed ^= seed >> 7n;
  seed ^= (seed << 17n) & 0xffffffffffffffffn;
  return seed;
}};
const patterns = [...edges];
for (let i = 0; i < 10000; i++) patterns.push(next());
let first = 0, second = 0, failures = [];
const view = new DataView(new ArrayBuffer(8));
for (const b of patterns) {{
  view.setBigUint64(0, b);
  const x = view.getFloat64(0);
  if (!Object.is(fromCanonicalBits(toCanonicalBits(x)), x)) failures.push(`second law ${{b.toString(16)}}`);
  second++;
  if (x !== x && toCanonicalBits(x) !== 0x7ff8000000000000n) failures.push(`NaN ${{b.toString(16)}}`);
  if (valid(b)) {{
    if (toCanonicalBits(fromCanonicalBits(b)) !== b) failures.push(`first law ${{b.toString(16)}}`);
    first++;
  }}
}}
for (const b of [0x7ff0000000000001n, 0xfff8000000000000n, 0xffffffffffffffffn, 0x7ff4000000000000n]) {{
  view.setBigUint64(0, b);
  const nan = view.getFloat64(0);
  if (toCanonicalBits(nan) !== 0x7ff8000000000000n || toCanonicalBits(nan * 1) !== 0x7ff8000000000000n)
    failures.push(`payload ${{b.toString(16)}}`);
}}
console.log(JSON.stringify({{ first, second, failures }}));
"#,
        module = stitchwort_js::FLOAT_BITS
    );
    let out = node("laws", &script);
    assert!(out.contains(r#""failures":[]"#), "{out}");
    // Every valid edge and some of the random patterns were checked both ways.
    assert!(out.contains(r#""second":10021"#), "{out}");
}

const PROGRAM: &str = r#"import Std (Float, Text)

-- The record's constructor with bits known only at run time.
def build (b: Nat) (h: Float.isValid b = True): Float := { bits = b, valid = h }

def ofBits (b: Nat): Float := if h: Float.isValid b = True then build b h else Float.nan

def show (x: Float): Text := x.bits.toText

def yes (b: Bool): Text := if b then "yes" else "no"

def same (x: Float) (y: Float): Text := yes (x == y)

def main(): {IO} () :=
  IO.print ([
    show (0.1 + 0.2), show (1.0 - 2.0), show (Float.neg Float.nan), show (Float.abs (-2.5)),
    show (Float.infinity - Float.infinity), show (ofBits 4607182418800017408 + 0.5), show (-0),
    show (ofBits 18444492273895866368), show (Float.neg (ofBits 0)),
    same 0.0 (-0.0), yes (Float.ieeeEq 0.0 (-0.0)), same Float.nan Float.nan,
    yes (Float.ieeeEq Float.nan Float.nan), yes (Float.isNaN (ofBits 9221120237041090560)),
    same (ofBits 4609434218613702656) 1.5
  ] |> Text.join ' ')
"#;

/// The record's constructor (with bits known only at run time) and `.bits`,
/// and the 1a operations, print the same with the Rust runtime and Node.
#[test]
fn floats_print_the_same_both_ways() {
    let dir = temp_dir("run");
    let path = dir.join("floats.sw");
    std::fs::write(&path, PROGRAM).expect("write source");
    let run = |js: bool| {
        let mut command = Command::new(env!("CARGO_BIN_EXE_stitchwort"));
        command.args(["run", "--no-cache"]);
        if js {
            command.arg("--js");
        }
        let out = command.arg(&path).output().expect("start stitchwort");
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        String::from_utf8_lossy(&out.stdout).into_owned()
    };
    let (rust, js) = (run(false), run(true));
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(rust, js);
    assert_eq!(
        rust.trim(),
        "4599075939470750516 13830554455654793216 9221120237041090560 4612811918334230528 \
         9221120237041090560 4609434218613702656 9223372036854775808 9221120237041090560 \
         9223372036854775808 no yes yes no yes yes"
    );
}

const BOUNDARY: &str = r#"import Std (Float, Option)

export def identity (x: Float): Float := x

export def makeInfinity (unused: Bool): Float := Float.infinity

export def bits (x: Float): Nat := x.bits

export def magnitude (x: Float): Option Float := if Float.isNaN x then None else Some (Float.abs x)
"#;

fn extracted(source: &str) -> stitchwort_js::Output {
    let mut session = stitchwort_cli::driver::Session::new();
    session
        .load("boundary.sw", source)
        .unwrap_or_else(|e| panic!("{e:?}"));
    stitchwort_js::generate(&session.elab.globals, session.elab.limits)
        .expect("extraction succeeds")
}

/// The JS boundary (docs/proposals/float.md §5, D685): every `number`
/// crosses in and back out as the same value under `Object.is`, `NaN`, the
/// infinities and `-0` included; a NaN with another payload is `Float.nan`
/// (its bits are the canonical ones); a `bigint`, a string and other values
/// are refused; an exported infinity can be passed back; `Option Float` is
/// `number | undefined`, and `Float` is `number` in the declarations.
#[test]
fn every_number_crosses_the_boundary() {
    let output = extracted(BOUNDARY);
    assert!(
        output.dts.contains("identity(x: number): number")
            && output
                .dts
                .contains("magnitude(x: number): number | undefined"),
        "{}",
        output.dts
    );
    let script = format!(
        "{}\n{}",
        "import * as m from \"./module.mjs\";",
        r#"const out = [];
for (const x of [-0, 0, 80281.87, NaN, Infinity, -Infinity, 5e-324, Number.MAX_VALUE])
  out.push(Object.is(m.identity(x), x));
out.push(Object.is(m.identity(m.makeInfinity(true)), Infinity));
const view = new DataView(new ArrayBuffer(8));
view.setBigUint64(0, 0xfff8000000000001n);
out.push(m.bits(view.getFloat64(0)) === 0x7ff8000000000000n);
out.push(m.bits(-0) === 0x8000000000000000n);
out.push(m.magnitude(NaN) === undefined, m.magnitude(-2.5) === 2.5);
for (const bad of [1n, "1", undefined, null, {}]) {
  try { m.identity(bad); out.push(false); }
  catch (e) { out.push(e instanceof m.StitchwortInputError); }
}
console.log(JSON.stringify(out));
"#
    );
    let dir = temp_dir("boundary");
    std::fs::write(dir.join("module.mjs"), &output.js).expect("write module");
    std::fs::write(dir.join("test.mjs"), script).expect("write script");
    let result = Command::new("node")
        .arg("test.mjs")
        .current_dir(&dir)
        .output()
        .expect("run node");
    let _ = std::fs::remove_dir_all(&dir);
    let stdout = String::from_utf8_lossy(&result.stdout);
    assert!(
        result.status.success() && !stdout.contains("false"),
        "{stdout}\n{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(stdout.matches("true").count(), 18, "{stdout}");
}

/// All `Float` bit reinterpretation is in the one module (D701): no typed
/// array or `DataView` anywhere else in generated code, extracted or run.
/// (The runner's `Int32Array` over a `SharedArrayBuffer`, which only sleeps,
/// is no reinterpretation.)
#[test]
fn typed_arrays_appear_only_in_the_canonical_bits_module() {
    let mut session = stitchwort_cli::driver::Session::new();
    session
        .load("floats.sw", PROGRAM)
        .unwrap_or_else(|e| panic!("{e:?}"));
    let main = session.main().expect("a main");
    let run = session.extract_program(&main).expect("generates").module;
    for (what, js) in [("extracted", extracted(BOUNDARY).js), ("run", run)] {
        let module = stitchwort_js::FLOAT_BITS;
        assert!(js.contains(module), "{what}: no canonical-bits module");
        let rest = js.replacen(module, "", 1);
        for word in [
            "DataView",
            "new ArrayBuffer",
            "Float64Array",
            "Float32Array",
            "BigUint64Array",
            "BigInt64Array",
        ] {
            assert!(!rest.contains(word), "{what}: `{word}` outside the module");
        }
    }
}
