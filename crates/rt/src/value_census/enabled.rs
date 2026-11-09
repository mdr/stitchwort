//! The counters and the report (see the parent module).

use std::fmt::Write as _;
use std::mem::size_of;
use std::sync::Once;
use std::sync::atomic::{AtomicI64, AtomicU64, Ordering::Relaxed};

use crate::effect::{Handler, Resume, StateRun};
use crate::value::{Delay, Fun, Value};

/// The Rc header: strong and weak counts.
const RC: u64 = 16;
/// Cells with this many fields or more share the last arity bucket.
const ARITIES: usize = 17;

/// The kinds of values a field holds.
const KINDS: [&str; 15] = [
    "erased",
    "tag",
    "nat_lt_2^61",
    "nat_2^61_to_2^63",
    "nat_2^63_to_2^64",
    "bignat",
    "int_in_61_bits",
    "int_wider_than_61_bits",
    "bigint",
    "float",
    "cell",
    "fun",
    "text",
    "array",
    "delay",
];
/// The kinds a one-word value of option A cannot hold inline (with 61-bit
/// scalars): they are boxed.
const BOXED_IN_A: [usize; 4] = [3, 4, 7, 9];

const MODELS: [&str; 4] = ["today", "C", "E", "A"];

#[allow(clippy::declare_interior_mutable_const)] // only to repeat into arrays
const ZERO: AtomicU64 = AtomicU64::new(0);
#[allow(clippy::declare_interior_mutable_const)]
const ZERO_I: AtomicI64 = AtomicI64::new(0);

static CELLS: [AtomicU64; ARITIES] = [ZERO; ARITIES];
/// Fields summed over the cells in the last bucket (the rest are exact).
static LAST_BUCKET_FIELDS: AtomicU64 = AtomicU64::new(0);
/// Cells native code allocated (`sw_cell_new`): counted by arity and size,
/// but not by what they hold, since native code fills them afterwards.
static NATIVE_CELLS: AtomicU64 = AtomicU64::new(0);
static REUSES: AtomicU64 = AtomicU64::new(0);
static CELL_KINDS: [AtomicU64; 15] = [ZERO; 15];
static REUSE_KINDS: [AtomicU64; 15] = [ZERO; 15];
static CAPTURE_KINDS: [AtomicU64; 15] = [ZERO; 15];

/// `Fun` variants by name.
const FUNS: [&str; 11] = [
    "global",
    "closure",
    "pap",
    "done_k",
    "resume",
    "state_run",
    "state_k",
    "jump_k",
    "jumped",
    "delay_k",
    "translate_k",
];
static FUN_COUNT: [AtomicU64; 11] = [ZERO; 11];
/// Captured values (closure captures, pap arguments) over all of a variant.
static FUN_CAPTURED: [AtomicU64; 11] = [ZERO; 11];
static DELAYS: AtomicU64 = AtomicU64::new(0);
static STATE_RUNS: AtomicU64 = AtomicU64::new(0);
static HANDLERS: AtomicU64 = AtomicU64::new(0);
static ARRAYS: AtomicU64 = AtomicU64::new(0);
static ARRAY_ELEMENTS: AtomicU64 = AtomicU64::new(0);
static ARRAY_PUSHES: AtomicU64 = AtomicU64::new(0);
static TEXTS: AtomicU64 = AtomicU64::new(0);
static TEXT_BYTES: AtomicU64 = AtomicU64::new(0);
static BIGS: AtomicU64 = AtomicU64::new(0);
static BIG_LIMBS: AtomicU64 = AtomicU64::new(0);

/// Bytes allocated so far, by model, by object class.
static CELL_BYTES: [AtomicU64; 4] = [ZERO; 4];
static FUN_BYTES: [AtomicU64; 4] = [ZERO; 4];
static DELAY_BYTES: [AtomicU64; 4] = [ZERO; 4];
static OTHER_BYTES: [AtomicU64; 4] = [ZERO; 4];
/// A's boxes for scalars that do not fit (in cell fields and captures).
static A_BOXES: AtomicU64 = AtomicU64::new(0);
/// What cells, closures and delays hold now and the most they held, by model.
static LIVE: [AtomicI64; 4] = [ZERO_I; 4];
static PEAK: [AtomicU64; 4] = [ZERO; 4];
static LIVE_CELLS: AtomicI64 = ZERO_I;
static PEAK_CELLS: AtomicU64 = ZERO;

static REGISTERED: Once = Once::new();

fn register() {
    REGISTERED.call_once(|| {
        extern "C" fn at_exit() {
            if let Ok(path) = std::env::var("STITCHWORT_VALUE_CENSUS") {
                let _ = std::fs::write(path, report());
            }
        }
        #[allow(unsafe_code)]
        // SAFETY: `at_exit` is a plain C function that takes nothing.
        unsafe {
            libc::atexit(at_exit)
        };
    });
}

fn kind(v: &Value) -> usize {
    match v {
        Value::Erased => 0,
        Value::Tag(_) => 1,
        Value::Nat(n) if *n < 1 << 61 => 2,
        Value::Nat(n) if *n < 1 << 63 => 3,
        Value::Nat(_) => 4,
        Value::BigNat(_) => 5,
        Value::Int(i) if (-(1i64 << 60)..1i64 << 60).contains(i) => 6,
        Value::Int(_) => 7,
        Value::BigInt(_) => 8,
        Value::Float(_) => 9,
        Value::Data(..) => 10,
        Value::Fun(_) => 11,
        Value::Text(_) => 12,
        Value::Array(_) => 13,
        Value::Delay(_) => 14,
    }
}

/// Cells (and in-place refills) by field count and by how many of their
/// fields are of an enum type and hold its value: `ENUM_CELLS[refill][n][k]`.
static ENUM_CELLS: [[[AtomicU64; ARITIES]; ARITIES]; 2] =
    [const { [const { [ZERO; ARITIES] }; ARITIES] }; 2];

pub(super) fn stored_cell(enum_mask: u8, fields: &[Value], refill: bool) {
    let k = (fields.iter().take(8).enumerate())
        .filter(|(i, v)| enum_mask >> i & 1 == 1 && matches!(v, Value::Tag(_)))
        .count();
    ENUM_CELLS[refill as usize][fields.len().min(ARITIES - 1)][k].fetch_add(1, Relaxed);
}

fn count_kinds(table: &[AtomicU64; 15], values: &[Value]) -> u64 {
    let mut boxes = 0;
    for v in values {
        let k = kind(v);
        table[k].fetch_add(1, Relaxed);
        if BOXED_IN_A.contains(&k) {
            boxes += 1;
        }
    }
    boxes
}

fn add(table: &[AtomicU64; 4], sizes: [u64; 4]) {
    for (t, s) in table.iter().zip(sizes) {
        t.fetch_add(s, Relaxed);
    }
}

fn live(delta: [i64; 4]) {
    for (i, d) in delta.into_iter().enumerate() {
        let now = LIVE[i].fetch_add(d, Relaxed) + d;
        if d > 0 {
            PEAK[i].fetch_max(now as u64, Relaxed);
        }
    }
}

fn cell_sizes(n: u64) -> [u64; 4] {
    [RC + 24 * n, 8 + 24 * n, 8 + 16 * n, 8 + 8 * n]
}

/// The counts of a cell of `n` fields that do not depend on what it holds.
fn cell_of_arity(n: usize) {
    CELLS[n.min(ARITIES - 1)].fetch_add(1, Relaxed);
    if n >= ARITIES - 1 {
        LAST_BUCKET_FIELDS.fetch_add(n as u64, Relaxed);
    }
    let sizes = cell_sizes(n as u64);
    add(&CELL_BYTES, sizes);
    live(sizes.map(|s| s as i64));
    let now = LIVE_CELLS.fetch_add(1, Relaxed) + 1;
    PEAK_CELLS.fetch_max(now as u64, Relaxed);
}

pub(super) fn cell(fields: &[Value]) {
    register();
    cell_of_arity(fields.len());
    let boxes = count_kinds(&CELL_KINDS, fields);
    A_BOXES.fetch_add(boxes, Relaxed);
}

pub(super) fn cell_native(n: usize) {
    register();
    NATIVE_CELLS.fetch_add(1, Relaxed);
    cell_of_arity(n);
}

pub(super) fn cell_reuse(fields: &[Value]) {
    register();
    REUSES.fetch_add(1, Relaxed);
    count_kinds(&REUSE_KINDS, fields);
}

pub(super) fn cell_freed(len: usize) {
    live(cell_sizes(len as u64).map(|s| -(s as i64)));
    LIVE_CELLS.fetch_sub(1, Relaxed);
}

/// The Value slots in the largest variant of each enum, and so how much E
/// and A save per object over today's layout.
const FUN_V: u64 = 2;
const DELAY_V: u64 = 3;

fn enum_sizes(s: usize, v: u64) -> [u64; 4] {
    let s = s as u64;
    [RC + s, RC + s, RC + s - 8 * v, 8 + s - 16 * v]
}

fn fun_index(f: &Fun) -> (usize, u64) {
    match f {
        Fun::Global(_) => (0, 0),
        Fun::Closure { captures, .. } => (1, captures.len() as u64),
        Fun::Pap { args, .. } => (2, args.len() as u64),
        Fun::DoneK => (3, 0),
        Fun::Resume(..) => (4, 0),
        Fun::StateRun(_) => (5, 0),
        Fun::StateK(_) => (6, 0),
        Fun::JumpK => (7, 0),
        Fun::Jumped(..) => (8, 0),
        Fun::DelayK(_) => (9, 0),
        Fun::TranslateK(_) => (10, 0),
    }
}

fn fun_sizes(f: &Fun) -> [u64; 4] {
    let (i, k) = fun_index(f);
    let mut s = enum_sizes(size_of::<Fun>(), FUN_V);
    // Captures are a second allocation today; A has them in the closure.
    let boxed = |per| if k > 0 { per * k } else { 0 };
    s[0] += boxed(24);
    s[1] += boxed(24);
    s[2] += boxed(16);
    s[3] = match i {
        1 => 16 + 8 * k,
        2 => 24 + 8 * k,
        8 => 24,
        _ => 16,
    };
    s
}

pub(super) fn fun(f: &Fun, made: bool) {
    let sizes = fun_sizes(f);
    if !made {
        live(sizes.map(|s| -(s as i64)));
        return;
    }
    register();
    let (i, k) = fun_index(f);
    FUN_COUNT[i].fetch_add(1, Relaxed);
    FUN_CAPTURED[i].fetch_add(k, Relaxed);
    let held: &[Value] = match f {
        Fun::Closure { captures, .. } => captures,
        Fun::Pap { args, .. } => args,
        _ => &[],
    };
    let boxes = count_kinds(&CAPTURE_KINDS, held);
    if let Fun::Pap { head, .. } = f {
        count_kinds(&CAPTURE_KINDS, std::slice::from_ref(head));
    }
    A_BOXES.fetch_add(boxes, Relaxed);
    add(&FUN_BYTES, sizes);
    live(sizes.map(|s| s as i64));
}

fn delay_sizes() -> [u64; 4] {
    enum_sizes(size_of::<Delay>(), DELAY_V)
}

pub(super) fn delay(_: &Delay, made: bool) {
    let sizes = delay_sizes();
    if !made {
        live(sizes.map(|s| -(s as i64)));
        return;
    }
    register();
    DELAYS.fetch_add(1, Relaxed);
    add(&DELAY_BYTES, sizes);
    live(sizes.map(|s| s as i64));
}

pub(super) fn state_run() {
    register();
    STATE_RUNS.fetch_add(1, Relaxed);
    add(&OTHER_BYTES, enum_sizes(size_of::<StateRun>(), 3));
}

pub(super) fn handler() {
    register();
    HANDLERS.fetch_add(1, Relaxed);
    add(&OTHER_BYTES, enum_sizes(size_of::<Handler>(), 2));
}

pub(super) fn array(len: usize) {
    register();
    ARRAYS.fetch_add(1, Relaxed);
    ARRAY_ELEMENTS.fetch_add(len as u64, Relaxed);
    let m = len as u64;
    add(
        &OTHER_BYTES,
        [40 + 24 * m, 40 + 24 * m, 40 + 16 * m, 24 + 8 * m],
    );
}

pub(super) fn array_push() {
    ARRAY_PUSHES.fetch_add(1, Relaxed);
}

pub(super) fn text(len: usize) {
    register();
    TEXTS.fetch_add(1, Relaxed);
    TEXT_BYTES.fetch_add(len as u64, Relaxed);
    let s = RC + len as u64;
    add(&OTHER_BYTES, [s; 4]);
}

pub(super) fn big(limbs: usize) {
    register();
    BIGS.fetch_add(1, Relaxed);
    BIG_LIMBS.fetch_add(limbs as u64, Relaxed);
    let s = RC + 24 + 8 * limbs as u64;
    add(&OTHER_BYTES, [s; 4]);
}

fn get(a: &AtomicU64) -> u64 {
    a.load(Relaxed)
}

/// The report: `key value` lines.
fn report() -> String {
    let mut out = String::new();
    let mut line = |k: String, v: u64| {
        let _ = writeln!(out, "{k} {v}");
    };
    line("size_of.Value".into(), size_of::<Value>() as u64);
    line("size_of.Fun".into(), size_of::<Fun>() as u64);
    line("size_of.Delay".into(), size_of::<Delay>() as u64);
    line("size_of.Handler".into(), size_of::<Handler>() as u64);
    line("size_of.Resume".into(), size_of::<Resume>() as u64);
    line("size_of.StateRun".into(), size_of::<StateRun>() as u64);
    line("size_of.RcHeader".into(), RC);
    let mut cells = 0;
    let mut fields = 0;
    for (n, c) in CELLS.iter().enumerate() {
        let c = get(c);
        cells += c;
        if n < ARITIES - 1 {
            fields += c * n as u64;
        }
        line(format!("cells.arity.{n}"), c);
    }
    fields += get(&LAST_BUCKET_FIELDS);
    line("cells.total".into(), cells);
    line("cells.fields".into(), fields);
    line("cells.native".into(), get(&NATIVE_CELLS));
    line("cells.reused_in_place".into(), get(&REUSES));
    for (i, name) in KINDS.iter().enumerate() {
        line(format!("cell_field.{name}"), get(&CELL_KINDS[i]));
    }
    for (i, name) in KINDS.iter().enumerate() {
        line(format!("reuse_field.{name}"), get(&REUSE_KINDS[i]));
    }
    for (i, name) in KINDS.iter().enumerate() {
        line(format!("capture.{name}"), get(&CAPTURE_KINDS[i]));
    }
    for (i, name) in FUNS.iter().enumerate() {
        line(format!("fun.{name}"), get(&FUN_COUNT[i]));
        line(format!("fun.{name}.captured"), get(&FUN_CAPTURED[i]));
    }
    line("delay".into(), get(&DELAYS));
    line("state_run".into(), get(&STATE_RUNS));
    line("handler".into(), get(&HANDLERS));
    line("array".into(), get(&ARRAYS));
    line("array.elements_at_creation".into(), get(&ARRAY_ELEMENTS));
    line("array.pushes".into(), get(&ARRAY_PUSHES));
    line("text".into(), get(&TEXTS));
    line("text.bytes".into(), get(&TEXT_BYTES));
    line("big".into(), get(&BIGS));
    line("big.limbs".into(), get(&BIG_LIMBS));
    line("a_boxes".into(), get(&A_BOXES));
    for (i, m) in MODELS.iter().enumerate() {
        line(format!("bytes.cells.{m}"), get(&CELL_BYTES[i]));
        line(format!("bytes.funs.{m}"), get(&FUN_BYTES[i]));
        line(format!("bytes.delays.{m}"), get(&DELAY_BYTES[i]));
        line(format!("bytes.other.{m}"), get(&OTHER_BYTES[i]));
        line(format!("peak.{m}"), get(&PEAK[i]));
    }
    line("peak.cells".into(), get(&PEAK_CELLS));
    // What is still live at exit; a negative figure would mean an object
    // freed that was never counted as made.
    for (i, m) in MODELS.iter().enumerate() {
        line(format!("end_live.{m}"), LIVE[i].load(Relaxed).max(0) as u64);
        line(
            format!("end_live_negative.{m}"),
            (-LIVE[i].load(Relaxed)).max(0) as u64,
        );
    }
    line(
        "end_live.cells".into(),
        LIVE_CELLS.load(Relaxed).max(0) as u64,
    );
    line(
        "end_live_negative.cells".into(),
        (-LIVE_CELLS.load(Relaxed)).max(0) as u64,
    );
    // `enum.<fields>.<enum fields>` and `enum_refill.…`: cells, and in-place
    // refills, by how many fields are enums (declared so, among the first eight).
    for (refill, name) in ["enum", "enum_refill"].into_iter().enumerate() {
        for (n, row) in ENUM_CELLS[refill].iter().enumerate() {
            for (k, c) in row.iter().enumerate() {
                if c.load(Relaxed) > 0 {
                    line(format!("{name}.{n}.{k}"), c.load(Relaxed));
                }
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn line(report: &str, key: &str) -> u64 {
        report
            .lines()
            .find_map(|l| l.strip_prefix(key)?.strip_prefix(' ')?.parse().ok())
            .unwrap_or_else(|| panic!("no line {key}"))
    }

    /// Run with `--features value-census` and `-- value_census`: the counters
    /// are the process's, so this must be the only test in it.
    #[test]
    fn a_cell_and_a_closure_are_counted_and_freed() {
        let before = report();
        let list = Value::data(1, [Value::Nat(1 << 62), Value::Tag(0)]);
        let closure = Value::Fun(crate::value_census::new_fun(Fun::Closure {
            lambda: 0,
            captures: vec![Value::Float(1.5), list.clone()].into(),
        }));
        let after = report();
        let d = |k: &str| line(&after, k) - line(&before, k);
        assert_eq!(d("cells.arity.2"), 1);
        assert_eq!(d("cell_field.nat_2^61_to_2^63"), 1);
        assert_eq!(d("cell_field.tag"), 1);
        assert_eq!(d("capture.float"), 1);
        assert_eq!(d("capture.cell"), 1);
        assert_eq!(d("fun.closure"), 1);
        // 16 + 24 * 2 for the cell; 16 + 56 for the `Fun` and 48 for its captures.
        assert_eq!(d("bytes.cells.today"), 64);
        assert_eq!(d("bytes.cells.E"), 40);
        assert_eq!(d("bytes.funs.today"), 16 + size_of::<Fun>() as u64 + 48);
        drop(closure);
        drop(list);
        let end = report();
        assert!(line(&end, "peak.today") >= line(&after, "peak.today"));
        assert_eq!(LIVE_CELLS.load(Relaxed), 0);
    }
}
