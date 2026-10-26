//! The interface between the machine and native code (stage N1 of
//! docs/proposals/native-compilation.md): what `stitchwort-native`'s
//! compiled code reads and calls, and where the machine hands a call to it.
//!
//! **Values.** Native code works on the machine's own [`Value`]s, in its
//! own layout: `Value` is `repr(u8)`, so its tag is the first byte and each
//! variant's fields follow in order (a number at byte 8, a constructor's tag
//! at byte 4 and its cell at bytes 8–23). Native code also reads the
//! reference count of an `Rc`'s allocation, which `std` lays out as the
//! strong count, the weak count, then the value (`RcInner` is `repr(C)`),
//! and a slice's fat pointer as the address then the length. Those are facts
//! about `std` rather than guarantees, so [`probe_layout`] checks every one
//! at run time before any native code runs, and native code isn't used if
//! one fails.
//!
//! **The crossing** ([`NativeIslands`]). Native code runs the bodies it has
//! compiled (since stage N4, every body `main` reaches but the entry), and
//! the machine hands a call over wherever it would push a frame for one: a
//! `Call`, an exact `Apply` or `enter` (from the effect loop, the runner,
//! eval/apply), and in tail positions a `TailCall` or exact `TailApply`
//! (after `replace`'s step and release):
//!
//! - **Counting.** The machine counts the step and checks the frame limit
//!   for the body, exactly as for a frame it pushes, then passes its
//!   counters in: the steps so far, and the frames pending including the
//!   body's. Native code counts on from there by the
//!   machine's rules (a step and a frame for a call, a step for a tail
//!   call) and hands the steps back, so a run counts the same whichever
//!   runner did the work.
//! - **Ownership.** The arguments are taken from the entry's registers as
//!   `Call` takes them (`MOVE` operands moved, the rest cloned) and moved
//!   into native code, which owns them from then on. The result is moved
//!   back and written to the call's register, as a returning frame's would
//!   be.
//! - **Errors.** Running out of steps or frames sets an error in the
//!   [`Context`]; every native frame then drops its registers and returns,
//!   and the crossing gives the machine the [`ResourceError`], which ends
//!   its run as any other does. Nothing is leaked and nothing panics through
//!   native frames.
//! - **Constants** are the machine's: native code reads and fills the
//!   machine's cache of global values, so a constant is computed once per
//!   run whichever runner needs it first.
//! - **Function values** (stage N3) cross both ways as they are: a `Fun`
//!   is `repr(u8)` too (its variant byte first, a global's or lambda's
//!   index at byte 4, a closure's captures at bytes 8–23), so native code
//!   reads a closure's captures and keys its apply caches on the first word
//!   (`fun_key`). Native code applies a function value through the code
//!   [`Context`] lists for each global and lambda, or through
//!   [`sw_apply_prepare`], which does what the machine's `apply` does, and
//!   has the machine enter what has no native code. A function value native
//!   code returns is the machine's to apply.
//! - **Back into the machine** (stage N4). What native code doesn't compile
//!   the machine runs for it, nested on top of whatever is pending
//!   (`machine::nested`), counting on from native code's counters. Since
//!   stage NO3 of docs/proposals/native-only.md the whole effect runtime is
//!   compiled (runtime bodies and the leaves below), so that is only a
//!   function value whose body isn't compiled, which `census::n1_blocker`
//!   makes none today; even in a tail position it's a nested run, not the
//!   tail request N4 had.

use std::mem::MaybeUninit;
use std::rc::Rc;

use stitchwort_core::ResourceError;

use crate::code::{Image, Instr, NO_REG, NumTable};
use crate::effect::{EffectOp, Handler, Resume};
use crate::ir::{GlobalKind, PrimOp, Program, Shapes};
use crate::machine::{Limits, State, Work, nested};
use crate::value::{Fields, Fun, Value};

// ------------------------------------------------------------ the layout

/// `Value`'s tags (its first byte), in declaration order.
pub const TAG_ERASED: u8 = 0;
pub const TAG_NAT: u8 = 1;
pub const TAG_BIG_NAT: u8 = 2;
pub const TAG_INT: u8 = 3;
pub const TAG_BIG_INT: u8 = 4;
pub const TAG_TEXT: u8 = 5;
pub const TAG_FLOAT: u8 = 6;
pub const TAG_TAG: u8 = 7;
pub const TAG_DATA: u8 = 8;
pub const TAG_FUN: u8 = 9;
pub const TAG_DELAY: u8 = 10;

/// The tags of the values that hold a reference ([`Value::owns`]): bit `t`
/// is set for tag `t`. Each of them keeps an `Rc`'s address at byte 8.
pub const OWNING_TAGS: u64 = (1 << TAG_BIG_NAT)
    | (1 << TAG_BIG_INT)
    | (1 << TAG_TEXT)
    | (1 << TAG_DATA)
    | (1 << TAG_FUN)
    | (1 << TAG_DELAY);

/// A value is three words: the tag (byte 0) and a constructor's tag (bytes
/// 4–7) in the first, then the payload.
pub const VALUE_SIZE: usize = 24;
/// Where a constructor's tag is (`Value::Tag`, `Value::Data`).
pub const CTOR_TAG_AT: i32 = 4;
/// Where a number, or an `Rc`'s address, is.
pub const PAYLOAD_AT: i32 = 8;
/// Where a slice's length is (`Value::Data`'s cell, `Value::Text`).
pub const LEN_AT: i32 = 16;
/// In an `Rc`'s allocation: the strong and weak counts, then the value.
pub const STRONG_AT: i32 = 0;
pub const WEAK_AT: i32 = 8;
pub const RC_VALUE_AT: i32 = 16;

/// A function value's variant ([`Fun`] is `repr(u8)`): its first byte.
pub const FUN_GLOBAL: u8 = 0;
pub const FUN_CLOSURE: u8 = 1;
/// In a [`Fun`]: where a `Closure`'s captures are (a slice's address, then
/// its length). A `Global`'s index and a `Closure`'s lambda are at byte 4.
pub const FUN_CAPTURES_AT: i32 = 8;
/// What [`ApplyCache`] keys on: a function value's first word (its variant
/// and its index or lambda), without the padding bytes between them.
pub const FUN_KEY_MASK: u64 = 0xffff_ffff_0000_00ff;

/// The words of a value, as native code holds it.
#[allow(unsafe_code)]
fn words(v: &Value) -> [u64; 3] {
    let p = (v as *const Value).cast::<u8>();
    // SAFETY: reads within the 24 bytes of `v`. The tag byte is always
    // initialised; the other two words are read as raw bytes into
    // `MaybeUninit`, so padding is never read as an integer (callers only
    // look at the words a variant initialises).
    unsafe {
        let mut out = [0u64; 3];
        out[0] = u64::from(*p);
        let tag = *p;
        if matches!(tag, TAG_TAG | TAG_DATA) {
            out[0] |= u64::from(*(p.add(4).cast::<u32>())) << 32;
        }
        if tag != TAG_ERASED && tag != TAG_TAG {
            out[1] = *(p.add(8).cast::<u64>());
        }
        if matches!(tag, TAG_DATA | TAG_TEXT) {
            out[2] = *(p.add(16).cast::<u64>());
        }
        out
    }
}

/// The strong and weak counts of the `Rc` whose allocation is at `at`.
#[allow(unsafe_code)]
fn counts_at(at: u64) -> (u64, u64) {
    // SAFETY: called only on the address word of a live owning value, which
    // [`probe_layout`] is checking points at an `RcInner`.
    unsafe {
        let p = at as *const u64;
        (*p, *p.add(1))
    }
}

/// Checks every fact about the layout of values that native code relies on
/// (the module comment), on real values: `Err` says which one failed, and
/// then no native code may run. Probed once per process: the probe's own
/// values appear in an allocation trace running then, so a host that traces
/// probes first.
pub fn probe_layout() -> Result<(), String> {
    static PROBED: std::sync::OnceLock<Result<(), String>> = std::sync::OnceLock::new();
    PROBED.get_or_init(probe).clone()
}

fn probe() -> Result<(), String> {
    let check = |ok: bool, what: &str| {
        if ok {
            Ok(())
        } else {
            Err(format!(
                "the layout of values isn't as native code expects: {what}"
            ))
        }
    };
    check(
        std::mem::size_of::<Value>() == VALUE_SIZE,
        "a value isn't 24 bytes",
    )?;
    let tags = [
        (Value::Erased, TAG_ERASED),
        (Value::Nat(7), TAG_NAT),
        (
            Value::nat(num_bigint::BigUint::from(u64::MAX) + 1u32),
            TAG_BIG_NAT,
        ),
        (Value::Int(-7), TAG_INT),
        (
            Value::int(num_bigint::BigInt::from(i64::MIN) - 1),
            TAG_BIG_INT,
        ),
        (Value::Text("abc".into()), TAG_TEXT),
        (Value::float(1.5), TAG_FLOAT),
        (Value::Tag(3), TAG_TAG),
        (Value::data(5, [Value::Nat(1), Value::Nat(2)]), TAG_DATA),
        (Value::Fun(Rc::new(Fun::Global(9))), TAG_FUN),
        (
            Value::Delay(Rc::new(crate::value::Delay::Now(Value::Erased))),
            TAG_DELAY,
        ),
    ];
    for (v, tag) in &tags {
        check(words(v)[0] as u8 == *tag, &format!("{v:?}'s tag"))?;
        check(
            v.owns() == ((OWNING_TAGS >> tag) & 1 == 1),
            &format!("whether {v:?} owns"),
        )?;
    }
    check(
        words(&Value::Nat(0x1234_5678_9abc))[1] == 0x1234_5678_9abc,
        "a `Nat`'s number",
    )?;
    check(
        words(&Value::Tag(0xabcd))[0] >> 32 == 0xabcd,
        "a `Tag`'s tag",
    )?;
    let data = Value::data_vec(0x77, vec![Value::Nat(1), Value::Nat(2), Value::Nat(3)]);
    let Value::Data(_, fields) = &data else {
        unreachable!("a constructor")
    };
    let w = words(&data);
    check(w[0] >> 32 == 0x77, "a constructor's tag")?;
    check(w[2] == 3, "a cell's length")?;
    check(
        w[1] + RC_VALUE_AT as u64 == Rc::as_ptr(&fields.0).cast::<u8>() as u64,
        "where a cell's fields are",
    )?;
    let copy = fields.clone();
    check(counts_at(w[1]) == (2, 1), "a cell's counts")?;
    drop(copy);
    check(counts_at(w[1]) == (1, 1), "a cell's counts after a drop")?;
    let text: Rc<str> = "hello".into();
    let tv = Value::Text(text.clone());
    let tw = words(&tv);
    check(
        tw[1] + RC_VALUE_AT as u64 == Rc::as_ptr(&text).cast::<u8>() as u64 && tw[2] == 5,
        "a text's address and length",
    )?;
    check(counts_at(tw[1]).0 == 2, "a text's count")?;
    probe_functions()?;
    for v in [&tags[2].0, &tags[4].0, &tags[9].0, &tags[10].0] {
        let copy = v.clone();
        let ok = counts_at(words(v)[1]).0 == 2;
        drop(copy);
        check(
            ok && counts_at(words(v)[1]).0 == 1,
            &format!("{v:?}'s count"),
        )?;
    }
    Ok(())
}

/// The facts about [`Fun`]'s layout that native code relies on: the
/// variant byte, a `Global`'s index, a `Closure`'s lambda and captures, as
/// [`ApplyCache`]'s key and `Captured` read them.
#[allow(unsafe_code)]
fn probe_functions() -> Result<(), String> {
    let check = |ok: bool, what: &str| {
        if ok {
            Ok(())
        } else {
            Err(format!(
                "the layout of function values isn't as native code expects: {what}"
            ))
        }
    };
    let closure = Value::Fun(Rc::new(Fun::Closure {
        lambda: 0x1234_5678,
        captures: vec![Value::Nat(5), Value::Nat(6), Value::Nat(7)].into(),
    }));
    let global = Value::Fun(Rc::new(Fun::Global(0x0abc_def0)));
    let pap = Value::Fun(Rc::new(Fun::Pap {
        head: global.clone(),
        args: vec![Value::Nat(1)].into(),
    }));
    // The address of a function value's `Fun`.
    let at = |v: &Value| words(v)[1] + RC_VALUE_AT as u64;
    // SAFETY: each address is a live `Rc<Fun>`'s value (`probe` checked
    // that an owning value keeps its allocation's address at byte 8), and a
    // `Fun` is at least 24 bytes.
    let (first, captures, len) = unsafe {
        let base = at(&closure) as *const u8;
        (
            base.cast::<u64>().read(),
            base.add(FUN_CAPTURES_AT as usize).cast::<u64>().read(),
            base.add(FUN_CAPTURES_AT as usize + 8).cast::<u64>().read(),
        )
    };
    check(first as u8 == FUN_CLOSURE, "a closure's variant")?;
    check(
        first & FUN_KEY_MASK == fun_key(FUN_CLOSURE, 0x1234_5678),
        "a closure's lambda",
    )?;
    let Value::Fun(f) = &closure else {
        unreachable!("a function")
    };
    let Fun::Closure { captures: c, .. } = &**f else {
        unreachable!("a closure")
    };
    check(
        captures == c.as_ptr() as u64 && len == 3,
        "a closure's captures",
    )?;
    // SAFETY: as above.
    let first = unsafe { (at(&global) as *const u64).read() };
    check(
        first & FUN_KEY_MASK == fun_key(FUN_GLOBAL, 0x0abc_def0),
        "a global function's index",
    )?;
    // SAFETY: as above.
    let first = unsafe { (at(&pap) as *const u8).read() };
    check(
        first != FUN_GLOBAL && first != FUN_CLOSURE,
        "a partial application's variant",
    )
}

/// [`ApplyCache`]'s key for a function value of `variant` and `index`.
const fn fun_key(variant: u8, index: u32) -> u64 {
    variant as u64 | (index as u64) << 32
}

// ------------------------------------------------------------ the context

/// No error.
pub const OK: u64 = 0;
/// More steps than the limit: [`ResourceError::Work`].
pub const OUT_OF_STEPS: u64 = 1;
/// More frames than the limit, or the native stack's safety margin reached:
/// [`ResourceError::Depth`].
pub const OUT_OF_FRAMES: u64 = 2;

/// What native code shares with the runtime, by pointer, as every
/// function's first argument. `repr(C)`: compiled code reads and writes the
/// fields at the offsets [`Context`]'s `*_AT` constants give.
#[repr(C)]
pub struct Context {
    /// The machine's step counter: frames entered since the stretch began.
    /// Read when native code starts and written when it returns; in
    /// between, compiled code keeps the steps left in a register.
    pub steps: u64,
    pub step_limit: u64,
    /// Frames pending when native code starts, the machine's and the island
    /// root's; compiled code passes the count on from frame to frame.
    pub frames: u64,
    pub frame_limit: u64,
    /// [`OK`], or why the run stopped. Once set, every native frame drops
    /// its registers and returns.
    pub error: u64,
    /// The lowest stack address native code may call from: a safety margin
    /// behind the frame limit, never the limit itself (§4.3). 0 for none.
    pub stack_limit: u64,
    /// For `Apply`: each global function's compiled code as a function
    /// value's (the entry that takes the function value last, and drops
    /// it), or null.
    pub functions: *const *const u8,
    /// For `Apply`: each lambda's compiled code (taking its closure last),
    /// or null.
    pub lambdas: *const *const u8,
    /// The run this is part of.
    pub run: *mut NativeRun<'static>,
    /// What compiled code refers to by number ([`Tables`]): it holds no
    /// address of the host's, so the same code can go into an object file.
    pub tables: *const Tables,
    /// 1 if the code has the effect runtime's bodies (stage NO2 of
    /// docs/proposals/native-only.md): [`sw_apply_prepare`] then has an
    /// eager resumption run by them ([`RESUME_CODE`]) rather than by the
    /// machine.
    pub resumes: u64,
}

impl Context {
    pub const STEPS_AT: i32 = std::mem::offset_of!(Context, steps) as i32;
    pub const STEP_LIMIT_AT: i32 = std::mem::offset_of!(Context, step_limit) as i32;
    pub const FRAMES_AT: i32 = std::mem::offset_of!(Context, frames) as i32;
    pub const FRAME_LIMIT_AT: i32 = std::mem::offset_of!(Context, frame_limit) as i32;
    pub const ERROR_AT: i32 = std::mem::offset_of!(Context, error) as i32;
    pub const STACK_LIMIT_AT: i32 = std::mem::offset_of!(Context, stack_limit) as i32;
    pub const TABLES_AT: i32 = std::mem::offset_of!(Context, tables) as i32;

    /// The error native code stopped with, if any.
    pub fn result(&self) -> Result<(), ResourceError> {
        match self.error {
            OK => Ok(()),
            OUT_OF_STEPS => Err(ResourceError::Work),
            _ => Err(ResourceError::Depth),
        }
    }
}

// ------------------------------------------------------------- the tables

/// The things compiled code uses that live in the host's memory, which it
/// reaches through [`Context::tables`] by number rather than by an address
/// baked into the code (stage S4 of docs/proposals/standalone-executables.md:
/// the same code then works in an object file, linked into another process).
/// `repr(C)`: compiled code reads `pool` and `caches` at
/// [`Tables::POOL_AT`] and [`Tables::CACHES_AT`]; the helpers read the rest.
///
/// The numbering is [`Numbering`]'s, a function of the image alone, so a
/// runtime that rebuilds the image can rebuild the tables.
#[repr(C)]
pub struct Tables {
    /// The image's constant pool: constant `k` at `pool + 24·k`.
    pub pool: *const Value,
    /// The program's shapes, for the native operations.
    pub shapes: *const Shapes,
    /// Every body's number tables, numbered by [`Numbering::num_table`].
    pub num_tables: *const *const NumTable,
    /// The operations of the image's `Prim`s and `Test`s, numbered by
    /// [`Numbering::op`].
    pub ops: *const PrimOp,
    /// One cache per `Apply` site of the compiled code, numbered by the
    /// compiler.
    pub caches: *mut ApplyCache,
    pub n_caches: u64,
}

impl Tables {
    pub const POOL_AT: i32 = std::mem::offset_of!(Tables, pool) as i32;
    pub const CACHES_AT: i32 = std::mem::offset_of!(Tables, caches) as i32;
}

/// How compiled code numbers an image's operations and number tables: in
/// the order the image's bodies, then their instructions, first use them.
/// Deterministic, so the compiler and a runtime that rebuilt the image from
/// the same program agree.
pub struct Numbering {
    /// Each distinct operation of a `Prim` or `Test`, in order of first use.
    pub ops: Vec<PrimOp>,
    /// For each body, the number of its first number table.
    num_table_base: Vec<u32>,
    /// How many number tables the image has.
    num_tables: u32,
}

impl Numbering {
    pub fn of(image: &Image) -> Numbering {
        let mut ops = Vec::new();
        let mut num_table_base = Vec::with_capacity(image.codes.len());
        let mut num_tables = 0u32;
        for code in &image.codes {
            num_table_base.push(num_tables);
            num_tables += code.num_tables.len() as u32;
            for instr in &code.instrs {
                if let Instr::Prim { op, .. } | Instr::Test { op, .. } = instr
                    && !ops.contains(op)
                {
                    ops.push(*op);
                }
            }
        }
        Numbering {
            ops,
            num_table_base,
            num_tables,
        }
    }

    /// The number of `op`, which the image uses in a `Prim` or `Test`.
    pub fn op(&self, op: PrimOp) -> u32 {
        self.ops
            .iter()
            .position(|o| *o == op)
            .expect("the image uses the operation") as u32
    }

    /// The number of body `code`'s number table `table`.
    pub fn num_table(&self, code: u32, table: u32) -> u32 {
        self.num_table_base[code as usize] + table
    }
}

/// The memory a [`Tables`] points into that it owns (the number tables'
/// addresses, the operations, the caches); the pool and the shapes are the
/// image's and the program's, which must outlive it.
pub struct TableStore {
    tables: *mut Tables,
    num_tables: *mut [*const NumTable],
    ops: *mut [PrimOp],
    caches: *mut [ApplyCache],
}

impl TableStore {
    /// The tables for compiled code of `image` (of `program`) with
    /// `n_caches` `Apply` sites.
    pub fn new(program: &Program, image: &Image, n_caches: usize) -> TableStore {
        let numbering = Numbering::of(image);
        let num_tables: Box<[*const NumTable]> = image
            .codes
            .iter()
            .flat_map(|code| code.num_tables.iter().map(|t| t as *const NumTable))
            .collect();
        debug_assert_eq!(num_tables.len(), numbering.num_tables as usize);
        let ops: Box<[PrimOp]> = numbering.ops.into_boxed_slice();
        let caches: Box<[ApplyCache]> = (0..n_caches).map(|_| ApplyCache::new()).collect();
        // Raw from here on: compiled code reads and writes through them.
        let num_tables = Box::into_raw(num_tables);
        let ops = Box::into_raw(ops);
        let caches = Box::into_raw(caches);
        let tables = Box::into_raw(Box::new(Tables {
            pool: image.pool.as_ptr(),
            shapes: &program.shapes,
            num_tables: num_tables.cast::<*const NumTable>(),
            ops: ops.cast::<PrimOp>(),
            caches: caches.cast::<ApplyCache>(),
            n_caches: n_caches as u64,
        }));
        TableStore {
            tables,
            num_tables,
            ops,
            caches,
        }
    }

    /// For [`Context::tables`].
    pub fn tables(&self) -> *const Tables {
        self.tables
    }
}

impl Drop for TableStore {
    #[allow(unsafe_code)]
    fn drop(&mut self) {
        // SAFETY: each came from `Box::into_raw` in `new` and is freed once;
        // no compiled code runs once the store is dropped.
        unsafe {
            drop(Box::from_raw(self.tables));
            drop(Box::from_raw(self.num_tables));
            drop(Box::from_raw(self.ops));
            drop(Box::from_raw(self.caches));
        }
    }
}

/// The machine's side of a crossing: what native code counts on from and
/// reads, for the length of one call.
pub struct NativeRun<'a> {
    pub program: &'a Program,
    pub(crate) image: &'a Image,
    /// The machine, waiting for the call: native code reads and fills its
    /// cache of global values, adds to its effect counts, and runs it nested
    /// (`machine::nested`) for what it doesn't compile.
    pub(crate) state: *mut State,
    /// Steps so far in this stretch; native code's steps are added.
    pub steps: u64,
    /// Frames pending, the called body's included.
    pub frames: u64,
    pub limits: Limits,
    /// Values frames gave up on leaving with an error ([`sw_unwind`]), in
    /// the order they left.
    pub unwound: Vec<Vec<Value>>,
    /// A tail call's arguments, dropped after the rest.
    pub tail: Vec<Value>,
    /// Each native frame's closure and pending arguments, as it left: the
    /// machine keeps them in its frames, which it clears before registers.
    pub held: Vec<Vec<Value>>,
    /// How many times native code had the machine run something for it in
    /// this crossing (`machine::nested`): what the native-only stages
    /// (docs/proposals/native-only.md) bring to zero. Added to the thread's
    /// total ([`nested_runs`]) when the crossing ends. In every build, not
    /// only debug ones, since the test tiers run release binaries; an
    /// increment per nested run is nothing next to the run.
    pub nested_runs: u64,
}

thread_local! {
    static NESTED_RUNS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// How many nested runs of the machine native code has asked for on this
/// thread so far ([`NativeRun::nested_runs`], summed as each crossing ends).
pub fn nested_runs() -> u64 {
    NESTED_RUNS.with(std::cell::Cell::get)
}

/// Adds a crossing's nested runs to the thread's total.
pub(crate) fn count_nested_runs(n: u64) {
    NESTED_RUNS.with(|total| total.set(total.get() + n));
}

impl NativeRun<'_> {
    /// The machine's state.
    #[allow(unsafe_code)]
    fn state(&mut self) -> &mut State {
        // SAFETY: the machine waits in the crossing while native code runs,
        // so nothing else uses its state; each use here is brief and never
        // overlaps a nested run's.
        unsafe { &mut *self.state }
    }
}

/// Native code for some of a program's bodies: the machine calls it
/// wherever it would push a frame for one (the module comment).
pub trait NativeIslands {
    /// Whether body `code` (an index into the image's codes) has native
    /// code: a global function's or a lambda's.
    fn compiled(&self, code: u32) -> bool;
    /// Whether native code may run under this frame limit: `false` (with a
    /// note why) if the native stack might not hold that many frames, and
    /// the run stays on the machine.
    fn fits(&self, frame_limit: u64) -> bool;
    /// Runs body `code` on `args`, with `env` the closure, for a lambda's
    /// body; the steps it takes are added to `run.steps`. What native
    /// frames gave up on leaving with an error is in `run`'s `unwound`,
    /// `tail` and `held` afterwards, for the machine to drop in its order.
    fn call(
        &self,
        code: u32,
        env: Option<Rc<Fun>>,
        args: Vec<Value>,
        run: &mut NativeRun<'_>,
    ) -> Result<Value, ResourceError>;
}

// ------------------------------------------------------------ the crossing

/// A crossing's trampoline, one per number of arguments: `(context, code,
/// arguments, closure, result)`, in the host's C calling convention. It
/// calls `code` (a function value's entry: a lambda's body, or a global
/// function's adapter) with the arguments moved in and the closure's
/// address word (0 for none) last, and writes the result.
pub type Trampoline = extern "C" fn(*mut Context, *const u8, *mut Value, u64, *mut Value);

/// What the host (the driver, the machine, the CLI) may have used above
/// the crossing into native code.
pub const HOST_ROOM: usize = 8 * 1024 * 1024;
/// What a runtime helper may use at the bottom of the stack (freeing a
/// value, a big number's arithmetic, a native operation).
pub const HELPER_ROOM: usize = 8 * 1024 * 1024;

/// What nesting through the machine may add to each counted frame on the
/// native stack (stage N4): a helper that runs the machine
/// (`sw_apply_prepare`; `sw_perform` and `sw_effect` until NO3, `sw_fold`
/// until NO1), the machine's `nested`
/// and `run`, its way back (`State::cross`, [`Crossing::call`]) and a
/// trampoline. Measured on the release build (aarch64, 26 October 2026),
/// as the stack address at each nested run: a recursion through
/// `Text.fold` used 4,208 bytes per level, two counted frames each (2,104
/// per frame, native frames of at most 792 bytes included); a handler whose
/// clause resumes in a non-tail position (`k 1 + 1`) nests twice per
/// counted frame, 3,904 bytes per frame (native frames of at most 1,384
/// bytes included). Handlers in other positions don't nest: the depth stays
/// in the machine's frames. 4 KiB is more than either whole measurement,
/// native frames included, so with the widest body's bound added
/// ([`level_bound`]) the margin is that bound (5,480 bytes allowed against
/// 3,904 used in the second case). Larger would keep the roguelike's
/// 2,000,000 frames (bodies up to 2,760 bytes) off the 16 GiB stack
/// (`stitchwort_host::NATIVE_STACK`).
///
/// Since stage NO3 of docs/proposals/native-only.md nothing the effect
/// runtime does nests, so only code with a body that isn't compiled (none
/// today) is given this room.
pub const NEST_ROOM: usize = 4 * 1024;

/// A bound on the stack one counted frame uses: a body (`max_frame`) and
/// the nesting through the machine that can come with it ([`NEST_ROOM`]).
pub fn level_bound(max_frame: usize) -> usize {
    max_frame + NEST_ROOM
}

/// The bound on one counted frame of code whose frames are at most
/// `max_frame` and which may nest inside runs of the machine (`nests`) or
/// not: what [`Crossing::fits`] checks, for a `--verbose` note made before
/// any run (`build --native`).
pub fn level(max_frame: usize, nests: bool) -> usize {
    if nests {
        level_bound(max_frame)
    } else {
        max_frame
    }
}

/// How far below the crossing the stack-pointer check puts its floor, for
/// a stack of `stack_size` bytes and bodies of at most `max_frame`: the
/// whole stack less the host's and helpers' room and one more frame (the
/// check runs before a call pushes its frame). `None` if the stack is too
/// small for that.
pub fn floor_depth(stack_size: usize, max_frame: usize) -> Option<usize> {
    stack_size.checked_sub(HOST_ROOM + HELPER_ROOM + max_frame)
}

/// Whether the frame counter always fires before the stack-pointer check:
/// `frame_limit` frames of at most `max_frame` fit above the floor.
pub fn counter_fires_first(frame_limit: u64, stack_size: usize, max_frame: usize) -> bool {
    floor_depth(stack_size, max_frame)
        .is_some_and(|depth| frame_limit.saturating_mul(max_frame as u64) <= depth as u64)
}

/// Compiled bodies, wherever their code is (JIT-compiled memory, or linked
/// into a standalone executable): the tables the code is given in the
/// [`Context`], and the crossing itself (the module comment). Shared by
/// `run --native`'s JIT and a standalone executable's linked code, so the
/// two can't drift.
pub struct Crossing {
    /// For each global: its code as a function value's, or null
    /// ([`Context::functions`]).
    functions: Box<[*const u8]>,
    /// For each lambda: its code, or null ([`Context::lambdas`]).
    lambdas: Box<[*const u8]>,
    /// For each body (by code index): its entry as a function value's (a
    /// lambda's body, or a global function's adapter), or null: what the
    /// machine calls instead of pushing a frame for it.
    entries: Box<[*const u8]>,
    /// The trampolines, by number of arguments.
    trampolines: Box<[Option<Trampoline>]>,
    /// What the code refers to by number ([`Context::tables`]).
    tables: TableStore,
    /// The stack the code runs on, if known: native code then stops with
    /// `E-RESOURCE` rather than run off its end (a safety margin, never the
    /// limit).
    pub stack_size: Option<usize>,
    /// A bound on the stack one counted frame uses: the widest body, and
    /// nesting through the machine if the code can nest ([`level_bound`]).
    pub level: usize,
    /// The lowest stack address native code may call from, fixed at the
    /// first crossing (whose stack is the host's, near the top): nested
    /// crossings are deeper, and mustn't move it.
    stack_floor: std::cell::Cell<Option<u64>>,
    /// [`Context::resumes`].
    resumes: bool,
}

/// Where a [`Crossing`]'s code is and what it's like: its tables, its
/// trampolines as `(number of arguments, trampoline)`, a bound on its
/// frames (`max_frame` bytes), and whether they may nest inside runs of
/// the machine (`nests`), and whether it has the effect runtime's bodies
/// that run resumptions (`resumes`, [`Context::resumes`]).
pub struct CrossingCode<'a> {
    pub functions: Box<[*const u8]>,
    pub lambdas: Box<[*const u8]>,
    pub trampolines: &'a [(u32, Trampoline)],
    pub max_frame: usize,
    pub nests: bool,
    pub resumes: bool,
}

impl Crossing {
    /// The crossing for `code`, compiled for `image`, with `tables`, on a
    /// stack of `stack_size` bytes if known.
    pub fn new(
        image: &Image,
        code: CrossingCode<'_>,
        tables: TableStore,
        stack_size: Option<usize>,
    ) -> Crossing {
        let CrossingCode {
            functions,
            lambdas,
            trampolines,
            max_frame,
            nests,
            resumes,
        } = code;
        let mut entries = vec![std::ptr::null::<u8>(); image.codes.len()].into_boxed_slice();
        for (g, entry) in functions.iter().enumerate() {
            if !entry.is_null()
                && let Some(Some(code)) = image.global_code.get(g)
            {
                entries[*code as usize] = *entry;
            }
        }
        for (l, entry) in lambdas.iter().enumerate() {
            if !entry.is_null()
                && let Some(code) = image.lambda_code.get(l)
            {
                entries[*code as usize] = *entry;
            }
        }
        let arities = trampolines.iter().map(|&(n, _)| n as usize + 1).max();
        let mut by_arity = vec![None; arities.unwrap_or(0)].into_boxed_slice();
        for &(n, trampoline) in trampolines {
            by_arity[n as usize] = Some(trampoline);
        }
        Crossing {
            functions,
            lambdas,
            entries,
            trampolines: by_arity,
            tables,
            stack_size,
            level: level(max_frame, nests),
            stack_floor: std::cell::Cell::new(None),
            resumes,
        }
    }

    /// [`NativeIslands::compiled`].
    pub fn compiled(&self, code: u32) -> bool {
        self.entries
            .get(code as usize)
            .is_some_and(|entry| !entry.is_null())
    }

    /// [`NativeIslands::fits`], without the note: whether the frame counter
    /// fires before the stack check could.
    pub fn fits(&self, frame_limit: u64) -> bool {
        self.stack_size
            .is_none_or(|size| counter_fires_first(frame_limit, size, self.level))
    }

    /// [`NativeIslands::call`]: runs body `code` on `args` (and the closure
    /// `env`), as the machine hands it over (the module comment): the
    /// counters go in and the steps come back in `run`, the arguments are
    /// moved in and the result moved out.
    ///
    /// # Safety
    /// The tables and trampolines are those of finished code for this
    /// image, which stays mapped; `code` is [`Crossing::compiled`].
    #[allow(unsafe_code)]
    pub unsafe fn call(
        &self,
        code: u32,
        env: Option<Rc<Fun>>,
        args: Vec<Value>,
        run: &mut NativeRun<'_>,
    ) -> Result<Value, ResourceError> {
        let entry = self.entries[code as usize];
        let trampoline =
            self.trampolines[args.len()].expect("a trampoline for this many arguments");
        let stack_limit = match self.stack_floor.get() {
            Some(floor) => floor,
            None => {
                let here = {
                    let marker = 0u8;
                    std::hint::black_box(&marker) as *const u8 as u64
                };
                let floor = match self.stack_size {
                    Some(size) => match floor_depth(size, self.level) {
                        Some(depth) => here.saturating_sub(depth as u64),
                        None => u64::MAX,
                    },
                    None => 0,
                };
                self.stack_floor.set(Some(floor));
                floor
            }
        };
        let mut context = Context {
            steps: run.steps,
            step_limit: run.limits.steps,
            frames: run.frames,
            frame_limit: run.limits.frames as u64,
            error: OK,
            stack_limit,
            functions: self.functions.as_ptr(),
            lambdas: self.lambdas.as_ptr(),
            run: (run as *mut NativeRun<'_>).cast::<NativeRun<'static>>(),
            tables: self.tables.tables(),
            resumes: u64::from(self.resumes),
        };
        let env = env.map_or(0, into_word);
        let mut args = std::mem::ManuallyDrop::new(args);
        let mut out = MaybeUninit::<Value>::uninit();
        trampoline(
            &mut context,
            entry,
            args.as_mut_ptr(),
            env,
            out.as_mut_ptr(),
        );
        // SAFETY: native code took the arguments and the closure (moved, as
        // a frame takes them), so the vector gives back only its buffer; it
        // wrote a whole value to `out` (`Erased` after an error), which is
        // now ours. `context.run` isn't used after the
        // call.
        let result = unsafe {
            args.set_len(0);
            std::mem::ManuallyDrop::drop(&mut args);
            out.assume_init()
        };
        run.steps = context.steps;
        context.result().map(|()| result)
    }
}

// ------------------------------------------------------------ the helpers
//
// The runtime functions compiled code calls. Each takes raw pointers, which
// compiled code makes only from: its own registers and temporaries (stack
// slots of whole values, initialised), the machine's image (constants,
// operand lists, tables), which outlives every run, and the context it was
// given. Each does exactly what the machine's instruction does, in the same
// order, so the allocation trace is the same.

/// Reads a value from the three words native code holds it in.
#[allow(unsafe_code)]
unsafe fn from_words(w0: u64, w1: u64, w2: u64) -> Value {
    let mut out = MaybeUninit::<Value>::uninit();
    let p = out.as_mut_ptr().cast::<u64>();
    // SAFETY: the words are a valid value's (the caller's contract): its
    // tag byte, the variant's fields at their offsets, and padding, which
    // may be anything.
    unsafe {
        p.write(w0);
        p.add(1).write(w1);
        p.add(2).write(w2);
        out.assume_init()
    }
}

/// Drops the value held in three words (an owning one whose count may go
/// to zero, or any value under the trace).
///
/// # Safety
/// The words are a value native code owns, and no longer uses.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_drop_words(w0: u64, w1: u64, w2: u64) {
    // SAFETY: the caller's contract.
    drop(unsafe { from_words(w0, w1, w2) });
}

/// Takes a reference to the value held in three words, as `clone` does
/// (for the trace: native code copies the words).
///
/// # Safety
/// The words are a live value native code holds.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_inc(w0: u64, w1: u64, w2: u64) {
    // SAFETY: the caller's contract; the value read from the words isn't
    // dropped, so only the clone's count remains.
    let v = std::mem::ManuallyDrop::new(unsafe { from_words(w0, w1, w2) });
    std::mem::forget(Value::clone(&v));
}

/// Takes the `n` values at `regs` off a frame that is leaving on an error,
/// to be dropped as the machine drops them after a failed run: it clears
/// its frames (each frame's closure and pending arguments, outermost first)
/// and then its registers (one vector for every frame: outermost frame first,
/// each from its lowest register up), then a tail call's fetched arguments.
/// Frames leave innermost first, so the machine (`State::release_failed`)
/// drops what is kept here last first.
/// `mode`: 0, a frame's registers (a segment); 1, a tail call's arguments;
/// 2, a frame's closure (a group, even of no values: every leaving frame
/// pushes one); 3, more for the last group (what the machine keeps in the
/// `Ret` of the frame that just left: an over-application's rest, a
/// `Text.fold`'s function), or, if no frame has left yet (the call failed
/// before its frame was pushed, or in a nested run of the machine, which
/// keeps its own), dropped now, as the machine drops a `Ret` it never
/// pushed.
///
/// # Safety
/// As [`sw_global`]; `regs` points at `n` initialised values, which native
/// code doesn't use again.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_unwind(context: *mut Context, regs: *mut Value, n: u64, mode: u64) {
    // SAFETY: the caller's contract.
    let run = unsafe { &mut *(*context).run };
    let values: Vec<Value> = (0..n as usize)
        .map(|i| unsafe { std::mem::take(&mut *regs.add(i)) })
        .collect();
    match mode {
        0 => run.unwound.push(values),
        1 => run.tail.extend(values),
        2 => run.held.push(values),
        _ => match run.held.last_mut() {
            Some(group) => group.extend(values),
            None => drop(values),
        },
    }
}

/// Drops the `n` values at `regs`, lowest first (as a vector of them is
/// dropped).
///
/// # Safety
/// `regs` points at `n` initialised values, which native code doesn't use
/// again.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_release_up(regs: *mut Value, n: u64) {
    for i in 0..n as usize {
        // SAFETY: within the values.
        drop(unsafe { std::mem::take(&mut *regs.add(i)) });
    }
}

/// `Ctor`: a new cell of `tag` with the `n` values at `fields` (moved), put
/// in `out` (uninitialised).
///
/// # Safety
/// `fields` points at `n` values native code owns; `out` at space for one.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_ctor(tag: u32, fields: *mut Value, n: u64, out: *mut Value) {
    // SAFETY: the caller's contract; the values are moved out (copied
    // bitwise into the new cell, which is then the only owner), and the
    // caller doesn't use them again.
    let n = n as usize;
    let mut cell = Rc::<[Value]>::new_uninit_slice(n);
    let to = Rc::get_mut(&mut cell)
        .expect("a new cell is unique")
        .as_mut_ptr()
        .cast::<Value>();
    unsafe { std::ptr::copy_nonoverlapping(fields, to, n) };
    let cell = unsafe { cell.assume_init() };
    crate::alloc_trace::alloc(tag, &cell);
    unsafe { out.write(Value::Data(tag, Fields(cell))) };
}

/// Frees a unique cell whose fields `Unpack` has all moved out, held in
/// three words: what dropping it does, without the walk over its fields
/// for values to free. The fields are left as they were (native code
/// doesn't erase them), so they're never read: the cell is freed as one of
/// `MaybeUninit` values, which have no drop.
///
/// # Safety
/// The words are a `Value::Data` native code owns, whose cell is unique and
/// whose every field has been moved out (and may still hold the moved
/// value's words).
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_free_emptied(w0: u64, w1: u64, w2: u64) {
    // SAFETY: the caller's contract.
    let Value::Data(_, fields) = (unsafe { from_words(w0, w1, w2) }) else {
        unreachable!("an emptied cell is a constructor's")
    };
    let fields = std::mem::ManuallyDrop::new(fields);
    // SAFETY: `fields` is never used or dropped again; its cell is taken.
    let cell: Rc<[Value]> = unsafe { std::ptr::read(&fields.0) };
    crate::alloc_trace::dec(&cell, true);
    // SAFETY: `MaybeUninit<Value>` has `Value`'s layout, so this is the
    // same allocation with the same layout; dropping it frees the cell
    // without dropping its (moved-out) fields.
    let cell: Rc<[MaybeUninit<Value>]> =
        unsafe { Rc::from_raw(Rc::into_raw(cell) as *const [MaybeUninit<Value>]) };
    drop(cell);
}

/// `CtorReuse`, with the `n` field values at `fields` (moved): the cell
/// held by `token` refilled, if it's unique and has `n` fields, otherwise a
/// new one; the token is used up. Put in `out` (uninitialised).
///
/// # Safety
/// As [`sw_ctor`], and `token` points at a register.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_ctor_reuse(
    tag: u32,
    fields: *mut Value,
    n: u64,
    token: *mut Value,
    out: *mut Value,
) {
    let n = n as usize;
    // SAFETY: the caller's contract.
    let v = match std::mem::take(unsafe { &mut *token }) {
        Value::Data(_, mut cell) if cell.len() == n && unique(&cell.0) => {
            for i in 0..n {
                let v = unsafe { fields.add(i).read() };
                Rc::get_mut(&mut cell.0).expect("unique")[i] = v;
            }
            crate::alloc_trace::reuse(tag, &cell.0);
            Value::Data(tag, cell)
        }
        _ => {
            let cell: Rc<[Value]> = (0..n).map(|i| unsafe { fields.add(i).read() }).collect();
            crate::alloc_trace::alloc(tag, &cell);
            Value::Data(tag, Fields(cell))
        }
    };
    unsafe { out.write(v) };
}

fn unique(cell: &Rc<[Value]>) -> bool {
    Rc::strong_count(cell) == 1 && Rc::weak_count(cell) == 0
}

/// `Unpack`, on a frame's registers `regs`: takes the constructor out of
/// register `src` and puts its fields in registers, as `pairs` (`n` pairs of
/// a field's index and a register) say, keeping the emptied cell in
/// register `token` if it's unique and `token` isn't `NO_REG`.
///
/// # Safety
/// `regs` points at the frame's registers, which every index is within;
/// `pairs` at `2 * n` indices.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_unpack(
    regs: *mut Value,
    src: u32,
    pairs: *const u32,
    n: u64,
    token: u32,
) {
    // SAFETY: the caller's contract.
    let reg = |r: u32| unsafe { &mut *regs.add(r as usize) };
    let pairs = unsafe { std::slice::from_raw_parts(pairs, 2 * n as usize) };
    let Value::Data(tag, mut cell) = std::mem::take(reg(src)) else {
        panic!("internal error: unpacking a value that isn't a constructor")
    };
    if let Some(slice) = Rc::get_mut(&mut cell.0) {
        for p in pairs.as_chunks::<2>().0 {
            *reg(p[1]) = std::mem::take(&mut slice[p[0] as usize]);
        }
        if token != NO_REG {
            for v in slice.iter_mut() {
                *v = Value::Erased;
            }
            *reg(token) = Value::Data(tag, cell);
        }
    } else {
        for p in pairs.as_chunks::<2>().0 {
            *reg(p[1]) = cell[p[0] as usize].clone();
        }
        if token != NO_REG {
            *reg(token) = Value::Erased;
        }
    }
}

/// Empties a unique cell's fields (an `Unpack` that keeps it as a token
/// and doesn't use every field): what the arm doesn't use is freed now.
///
/// # Safety
/// `cell` is the address word of a unique cell of `n` fields.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_empty_cell(cell: u64, n: u64) {
    let fields = (cell + RC_VALUE_AT as u64) as *mut Value;
    for i in 0..n as usize {
        // SAFETY: within the cell, which nothing else refers to.
        unsafe { *fields.add(i) = Value::Erased };
    }
}

/// `DropReuse` on registers `src` and `token`.
///
/// # Safety
/// Both point at registers.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_drop_reuse(src: *mut Value, token: *mut Value) {
    // SAFETY: the caller's contract.
    let v = match std::mem::take(unsafe { &mut *src }) {
        Value::Data(tag, mut cell) if unique(&cell.0) => {
            for v in Rc::get_mut(&mut cell.0).expect("unique").iter_mut() {
                *v = Value::Erased;
            }
            Value::Data(tag, cell)
        }
        _ => Value::Erased,
    };
    unsafe { *token = v };
}

/// A native operation on the values at `args` (`n` pointers to registers),
/// written to register `dst` as the machine's `Prim` writes it.
///
/// # Safety
/// `context` is the running context and `op` an operation's number in its
/// tables; `args` points at `n` pointers to live values, `dst` at a
/// register.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_prim(
    context: *const Context,
    op: u32,
    args: *const *const Value,
    n: u64,
    dst: *mut Value,
) {
    // SAFETY: the caller's contract.
    unsafe {
        let (shapes, op) = shapes_and_op(context, op);
        let refs: Vec<&Value> = (0..n as usize).map(|i| &**args.add(i)).collect();
        let v = crate::prims::eval(shapes, op, &refs);
        *dst = v;
    }
}

/// The program's shapes and operation `op`, from the context's tables.
///
/// # Safety
/// As [`sw_prim`].
#[allow(unsafe_code)]
unsafe fn shapes_and_op<'a>(context: *const Context, op: u32) -> (&'a Shapes, PrimOp) {
    // SAFETY: the caller's contract: the tables outlive the native call,
    // and `op` is within them.
    unsafe {
        let tables = &*(*context).tables;
        (&*tables.shapes, *tables.ops.add(op as usize))
    }
}

/// A native test ([`crate::code::is_test`]) on the values at `args`: 1 if
/// it holds.
///
/// # Safety
/// As [`sw_prim`], without `dst`.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_test(
    context: *const Context,
    op: u32,
    args: *const *const Value,
    n: u64,
) -> u64 {
    // SAFETY: the caller's contract.
    unsafe {
        let (s, op) = shapes_and_op(context, op);
        let refs: Vec<&Value> = (0..n as usize).map(|i| &**args.add(i)).collect();
        match crate::prims::eval(s, op, &refs).tag() {
            Some(t) if t == s.true_ => 1,
            Some(t) if t == s.false_ => 0,
            other => panic!("internal error: a test made {other:?}"),
        }
    }
}

/// `NatPred` of a big number, written to register `dst`.
///
/// # Safety
/// Both point at registers.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_nat_pred(src: *const Value, dst: *mut Value) {
    // SAFETY: the caller's contract.
    unsafe {
        let v = match &*src {
            Value::Nat(n) => Value::Nat(n - 1),
            other => Value::nat(other.to_biguint() - 1u32),
        };
        *dst = v;
    }
}

/// Where a `NumSwitch` on the value at `v` jumps.
///
/// # Safety
/// `context` is the running context and `table` a number table's number in
/// its tables; `v` points at a register.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_num_switch(
    context: *const Context,
    table: u32,
    v: *const Value,
) -> u64 {
    // SAFETY: the caller's contract: the tables outlive the native call,
    // and `table` is within them.
    let table = unsafe { &**(*(*context).tables).num_tables.add(table as usize) };
    u64::from(crate::prims::num_switch(table, unsafe { &*v }))
}

/// `Global g`: if its value is known (a constant computed, or a function
/// value), writes it to `out` (uninitialised) and returns 1; for a constant
/// not yet computed, returns 0 and native code computes it.
///
/// # Safety
/// `context` is the running context; `out` points at space for a value.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_global(context: *mut Context, g: u32, out: *mut Value) -> u64 {
    // SAFETY: the context's run outlives the native call.
    let run = unsafe { &mut *(*context).run };
    if run.state().globals[g as usize].is_none()
        && let GlobalKind::Constant { .. } = run.program.globals[g as usize].kind
    {
        return 0;
    }
    unsafe { out.write(function_value(run, g)) };
    1
}

/// Keeps constant `g`'s value, computed by native code, in the cache.
///
/// # Safety
/// As [`sw_global`]; `v` points at a live value.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_global_set(context: *mut Context, g: u32, v: *const Value) {
    // SAFETY: as for `sw_global`.
    let run = unsafe { &mut *(*context).run };
    run.state().globals[g as usize] = Some(unsafe { (*v).clone() });
}

/// Whether a native operation can be applied by native code (through
/// [`sw_apply_prepare`]): it computes a value from its arguments (not an
/// effect runtime native, which the machine runs on its frames, or
/// `Text.fold`, which calls its function: [`FOLD_CODE`]).
pub fn applicable_native(op: PrimOp) -> bool {
    !matches!(
        op,
        PrimOp::Effect(_) | PrimOp::Text(crate::natives::TextNative::TextFold)
    )
}

/// Stops the process on a broken invariant of native code (a helper can't
/// unwind into compiled code).
fn internal(what: std::fmt::Arguments<'_>) -> ! {
    eprintln!("internal error: native code {what}");
    std::process::abort();
}

/// Global `g`'s value, if it's known: the cached value, or for a function
/// or a native a new function value, kept (the machine's `function_value`).
fn function_value(run: &mut NativeRun<'_>, g: u32) -> Value {
    if let Some(v) = &run.state().globals[g as usize] {
        return v.clone();
    }
    let v = match &run.program.globals[g as usize].kind {
        GlobalKind::Native(op) if op.arity() == 0 => Value::Erased,
        _ => Value::Fun(Rc::new(Fun::Global(g))),
    };
    run.state().globals[g as usize] = Some(v.clone());
    v
}

/// One `Apply`'s cache of its last target (the native crate's module
/// comment): the key of the function value last applied there whose code
/// takes exactly the arguments the site passes (a global function's index,
/// or a closure's lambda, with the variant: [`FUN_KEY_MASK`]), and that
/// code. Compiled code compares a function value's first word with `key`
/// and, if they're the same, calls `code` without asking the runtime.
/// Keyed by code rather than by the value, so it keeps nothing alive.
/// `repr(C)`: compiled code reads `key` and `code` at
/// [`ApplyCache::KEY_AT`] and [`ApplyCache::CODE_AT`].
#[repr(C)]
pub struct ApplyCache {
    pub key: u64,
    pub code: u64,
}

impl ApplyCache {
    pub const KEY_AT: i32 = std::mem::offset_of!(ApplyCache, key) as i32;
    pub const CODE_AT: i32 = std::mem::offset_of!(ApplyCache, code) as i32;

    /// Empty: no function value's key is all ones.
    pub fn new() -> ApplyCache {
        ApplyCache {
            key: u64::MAX,
            code: 0,
        }
    }
}

impl Default for ApplyCache {
    fn default() -> ApplyCache {
        ApplyCache::new()
    }
}

/// What `Apply` of the function value at `f` to `n` arguments calls
/// directly, as the machine's `exact` decides: for a closure or a global
/// function taking exactly `n`, its compiled code (the entry taking the
/// function value last), kept in `cache`. 0 for anything else (a partial
/// application, a native, another number of arguments), which goes through
/// [`sw_apply_prepare`].
///
/// # Safety
/// `context` is the running context; `f` points at a live value; `cache`
/// at a live cache.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_apply_cached(
    context: *mut Context,
    f: *const Value,
    n: u64,
    cache: *mut ApplyCache,
) -> u64 {
    // SAFETY: the caller's contract; the tables have an entry for every
    // global and every lambda.
    let (program, functions, lambdas) = unsafe {
        (
            (*(*context).run).program,
            (*context).functions,
            (*context).lambdas,
        )
    };
    let Value::Fun(fun) = (unsafe { &*f }) else {
        return 0;
    };
    let (key, code) = match &**fun {
        Fun::Global(g) => match program.globals[*g as usize].kind {
            GlobalKind::Function { params, .. } if u64::from(params) == n => {
                (fun_key(FUN_GLOBAL, *g), unsafe {
                    *functions.add(*g as usize)
                })
            }
            _ => return 0,
        },
        Fun::Closure { lambda, .. } if u64::from(program.lambdas[*lambda as usize].params) == n => {
            (fun_key(FUN_CLOSURE, *lambda), unsafe {
                *lambdas.add(*lambda as usize)
            })
        }
        _ => return 0,
    };
    if code.is_null() {
        return 0;
    }
    let cache = unsafe { &mut *cache };
    cache.key = key;
    cache.code = code as u64;
    code as u64
}

/// The machine's eval/apply step for native code ([`sw_apply_prepare`]),
/// written to a stack slot of compiled code: either a value now (`code` 0,
/// the value in `value`), or compiled code to call with the first `arity`
/// values after the header and the word `env` last. Either way, the `rest`
/// values after those are an over-application's, for the result to be
/// applied to next. `cap` is how many values there is room for after the
/// header (set by compiled code).
#[repr(C)]
pub struct ApplyPlan {
    pub code: u64,
    pub env: u64,
    pub arity: u64,
    pub rest: u64,
    pub cap: u64,
    pub value: MaybeUninit<Value>,
}

impl ApplyPlan {
    pub const CODE_AT: i32 = std::mem::offset_of!(ApplyPlan, code) as i32;
    pub const ENV_AT: i32 = std::mem::offset_of!(ApplyPlan, env) as i32;
    pub const ARITY_AT: i32 = std::mem::offset_of!(ApplyPlan, arity) as i32;
    pub const REST_AT: i32 = std::mem::offset_of!(ApplyPlan, rest) as i32;
    pub const CAP_AT: i32 = std::mem::offset_of!(ApplyPlan, cap) as i32;
    pub const VALUE_AT: i32 = std::mem::offset_of!(ApplyPlan, value) as i32;
    /// Where the values start.
    pub const ARGS_AT: i32 = std::mem::size_of::<ApplyPlan>() as i32;
}

/// An [`ApplyPlan`]'s `code` for `Text.fold` applied as a function value:
/// the apply stub calls the compiled `Text.fold` (`rt_text_fold`) on the
/// plan's three values, with no step or frame of its own, as the machine's
/// `enter` runs `fold_start` (stage NO1 of docs/proposals/native-only.md).
/// No code is at address 1.
pub const FOLD_CODE: u64 = 1;

/// An [`ApplyPlan`]'s `code` for an eager resumption (`Fun::Resume`, not
/// lazy) applied to the plan's one value: the apply stub calls the
/// effect runtime's `rt_resume` (stage NO2 of docs/proposals/native-only.md)
/// with the value and the resumption, whose reference the plan's `env`
/// holds, with no step or frame of its own, as the machine's `enter` runs
/// `resume`. Only if the code has the runtime's bodies
/// ([`Context::resumes`]). No code is at address 2. Since stage NO3, also a
/// state-passing handler's function of the state (`Fun::StateRun`)
/// applied to the state.
pub const RESUME_CODE: u64 = 2;

/// An [`ApplyPlan`]'s `code` for an effect native that runs a loop (a
/// fold, `translate` or `runPure`) applied as a function value (stage NO3
/// of docs/proposals/native-only.md): the apply stub calls `rt_loop` on the
/// plan's one value (the computation) and the handler, whose word the
/// plan's `env` holds, with no step or frame of its own, as the machine's
/// `enter` runs `effect`. No code is at address 3.
pub const LOOP_CODE: u64 = 3;

/// `Apply` of the function value at `f` (taken) to the `n` values at
/// `args` (moved), as the machine's `apply` and `enter` do it up to the
/// frame: a partial application's arguments joined to the new ones (copies
/// of its own), then a new partial application if they're too few;
/// otherwise the head's arguments split from the rest, and the head
/// entered: a native's value computed (or `Done` made), or the code to call
/// (a global function's, or a closure's with a new reference to the closure
/// as `env`). The function value is dropped last, as `apply` drops it.
/// Writes an [`ApplyPlan`] at `plan`; `args` may point into it (every
/// argument is read before anything is written).
///
/// The effect runtime's function values are planned as the machine's
/// `enter` runs them: its leaves make a value; an eager resumption or a
/// state-passing handler's function of the state is [`RESUME_CODE`]; an
/// effect native's function value is run as the machine's `effect` runs it
/// (stage NO3), [`LOOP_CODE`] for one that runs a loop.
///
/// A head native code has no code for (a body that isn't compiled: none
/// today) is the machine's to enter, run nested on `frames` frames pending
/// (the caller's), its value the plan's. Native code has written its steps
/// to the context first. A failure there sets the context's error, and the
/// plan then holds only the over-application's values.
///
/// # Safety
/// `context` is the running context; `f` and `args` point at values native
/// code owns; `plan` at an `ApplyPlan` header followed by room for its
/// `cap` values.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_apply_prepare(
    context: *mut Context,
    frames: u64,
    f: *mut Value,
    args: *mut Value,
    n: u64,
    plan: *mut ApplyPlan,
) {
    // SAFETY: the caller's contract; the values are moved out and not used
    // again by the caller.
    let (run, functions, lambdas) = unsafe {
        (
            &mut *(*context).run,
            (*context).functions,
            (*context).lambdas,
        )
    };
    let program = run.program;
    let f = unsafe { f.read() };
    // A partial application given exactly the rest of its arguments, whose
    // head is a compiled global function or a closure: the common case of
    // `List.map xs (add offset)`. Built in the plan directly, with no
    // vectors: the new arguments moved up (they may lie in the plan), the
    // held ones cloned in front, the function value dropped last, as below.
    if let Value::Fun(fun) = &f
        && let Fun::Pap { head, args: held } = &**fun
        && let Value::Fun(h) = head
    {
        let total = held.len() + n as usize;
        let target = match &**h {
            Fun::Global(g)
                if matches!(
                    program.globals[*g as usize].kind,
                    GlobalKind::Function { .. }
                ) =>
            {
                // SAFETY: the table has an entry for every global.
                Some((unsafe { *functions.add(*g as usize) }, false))
            }
            Fun::Closure { lambda, .. } => {
                // SAFETY: the table has an entry for every lambda.
                Some((unsafe { *lambdas.add(*lambda as usize) }, true))
            }
            _ => None,
        };
        if let Some((code, closure)) = target
            && !code.is_null()
            && total == crate::machine::arity(program, head)
            && total <= unsafe { (*plan).cap } as usize
        {
            // A closure head's reference becomes the callee's `env`, as below.
            let env = if closure {
                let held_ref = std::mem::ManuallyDrop::new(Value::Fun(h.clone()));
                words(&held_ref)[1]
            } else {
                0
            };
            // SAFETY: the caller's contract: `args` holds `n` values to
            // move, `plan` room for `cap >= total` values after its header.
            unsafe {
                let to = plan
                    .cast::<u8>()
                    .add(ApplyPlan::ARGS_AT as usize)
                    .cast::<Value>();
                std::ptr::copy(args, to.add(held.len()), n as usize);
                for (i, v) in held.iter().enumerate() {
                    to.add(i).write(v.clone());
                }
                (*plan).code = code as u64;
                (*plan).env = env;
                (*plan).arity = total as u64;
                (*plan).rest = 0;
            }
            drop(f);
            return;
        }
    }
    let args: Vec<Value> = (0..n as usize)
        .map(|i| unsafe { args.add(i).read() })
        .collect();
    // SAFETY: the running context.
    let resumes = unsafe { (*context).resumes } != 0;
    let mut f = f;
    let mut args = args;
    // The function values applied before `f`: `bind (Done x) k` is `k x`,
    // applied as the machine's `effect` applies it, so `bind`'s function
    // value is dropped after `k`, as the outer `apply` drops it.
    let mut applied: Vec<Value> = Vec::new();
    let mut code: *const u8 = std::ptr::null();
    let mut env = 0u64;
    let mut value = None;
    let mut rest = Vec::new();
    let mut machine = false;
    let mut all = loop {
        let Value::Fun(fun) = &f else {
            internal(format_args!("applied {f:?}, which isn't a function"))
        };
        let (head, held): (&Value, &[Value]) = match &**fun {
            Fun::Pap { head, args } => (head, args),
            _ => (&f, &[]),
        };
        let arity = crate::machine::arity(program, head);
        let total = held.len() + args.len();
        let mut all = if held.is_empty() {
            std::mem::take(&mut args)
        } else {
            let mut all = held.to_vec();
            all.append(&mut args);
            all
        };
        if total < arity {
            value = Some(Value::Fun(Rc::new(Fun::Pap {
                head: head.clone(),
                args: std::mem::take(&mut all).into(),
            })));
            break all;
        }
        if total > arity {
            // Only the first function value can be over-applied: `k` is
            // given one value.
            rest = all.split_off(arity);
        }
        let Value::Fun(h) = head else {
            unreachable!("a function")
        };
        // `bind (Done x) k`'s `k` and `x`, to go round again with.
        let mut bound = None;
        match &**h {
            Fun::Global(g) => match program.globals[*g as usize].kind {
                GlobalKind::Native(op) if applicable_native(op) => {
                    let v = {
                        let refs: Vec<&Value> = all.iter().collect();
                        crate::prims::eval(&program.shapes, op, &refs)
                    };
                    drop(std::mem::take(&mut all));
                    value = Some(v);
                }
                GlobalKind::Native(PrimOp::Text(crate::natives::TextNative::TextFold)) => {
                    // The compiled `Text.fold` (stage NO1 of
                    // native-only.md), called with no frame of its own, as
                    // the machine's `enter` runs it.
                    code = FOLD_CODE as *const u8;
                }
                // The effect runtime's natives as function values (stage
                // NO3 of native-only.md), as the machine's `effect` runs
                // them: `bind` and a state-passing handler's fold make a
                // value here (or `k x` goes round again); a fold,
                // `translate` or `runPure` is the runtime's `rt_loop` on
                // the handler and computation made here ([`LOOP_CODE`]).
                GlobalKind::Native(PrimOp::Effect(op)) => {
                    let mut taken = std::mem::take(&mut all).into_iter();
                    let mut arg = || taken.next().expect("an effect native's arguments");
                    let s = &program.shapes;
                    match op {
                        EffectOp::Bind => match (arg(), arg()) {
                            (Value::Data(tag, fields), k) if tag == s.done => {
                                bound = Some((k, crate::machine::field(fields, 0)));
                            }
                            (c, k) => {
                                run.state().counts.binds += 1;
                                value = Some(Value::data(s.bind_node, [c, k]));
                            }
                        },
                        EffectOp::FoldState | EffectOp::FoldStateComp => {
                            value = Some(crate::machine::state_handler(s, op, arg));
                        }
                        // The code has the runtime's bodies: anything that
                        // uses an effect native does (`Context::resumes`).
                        _ => {
                            let (handler, c) = crate::machine::handler_for(s, op, arg);
                            code = LOOP_CODE as *const u8;
                            env = Rc::into_raw(handler) as u64;
                            all = vec![c];
                        }
                    }
                }
                GlobalKind::Function { .. } => {
                    // SAFETY: the table has an entry for every global.
                    code = unsafe { *functions.add(*g as usize) };
                }
                _ => {}
            },
            Fun::Closure { lambda, .. } => {
                // SAFETY: the table has an entry for every lambda.
                code = unsafe { *lambdas.add(*lambda as usize) };
                if !code.is_null() {
                    let closure = std::mem::ManuallyDrop::new(Value::Fun(h.clone()));
                    env = words(&closure)[1];
                }
            }
            // The effect runtime's leaves: a value now, as `enter` makes it.
            Fun::DoneK => {
                let y = all.pop().expect("one argument");
                value = Some(crate::machine::done_k(&program.shapes, y));
            }
            Fun::StateK(resume) => {
                let y = all.pop().expect("one argument");
                value = Some(crate::machine::state_k(&program.shapes, resume, y));
            }
            Fun::JumpK => {
                let s = all.pop().expect("two arguments");
                let v = all.pop().expect("two arguments");
                value = Some(crate::machine::jump_k(v, s));
            }
            Fun::DelayK(capture) => {
                let y = all.pop().expect("one argument");
                value = Some(crate::machine::delay_k(capture, y));
            }
            // A lazy resumption suspends (a value now); an eager one, and a
            // state-passing handler's function of the state, are the
            // effect runtime's `rt_resume` to run (stages NO2 and NO3 of
            // native-only.md), which takes this reference to it.
            Fun::Resume(resume, true) => {
                let y = all.pop().expect("one argument");
                let counts = &mut run.state().counts;
                value = Some(crate::machine::resume_lazily(
                    &program.shapes,
                    counts,
                    resume,
                    y,
                ));
            }
            Fun::Resume(_, false) | Fun::StateRun(_) if resumes => {
                code = RESUME_CODE as *const u8;
                env = into_word(h.clone());
            }
            _ => {}
        }
        if let Some((k, x)) = bound {
            applied.push(std::mem::replace(&mut f, k));
            args = vec![x];
            continue;
        }
        machine = value.is_none() && code.is_null();
        break all;
    };
    if machine {
        // Only a body that isn't compiled (none today), run nested even in
        // a tail position: N4's tail requests went in stage NO3.
        let f = std::mem::replace(&mut f, Value::Erased);
        let all = std::mem::take(&mut all);
        // SAFETY: the running context.
        let steps = unsafe { &mut (*context).steps };
        match nested(run, frames, steps, Work::Enter(f, all)) {
            Ok(v) => value = Some(v),
            Err(e) => {
                // SAFETY: the running context.
                unsafe { (*context).error = error_code(e) };
                value = Some(Value::Erased);
            }
        }
    }
    let exact = all.len();
    let after = rest.len();
    // SAFETY: the caller's contract: room for `cap` values after the
    // header, checked.
    unsafe {
        if exact + after > (*plan).cap as usize {
            internal(format_args!(
                "applied a function value to more arguments than it made room for"
            ));
        }
        let to = plan
            .cast::<u8>()
            .add(ApplyPlan::ARGS_AT as usize)
            .cast::<Value>();
        for (i, v) in all.into_iter().chain(rest).enumerate() {
            to.add(i).write(v);
        }
        (*plan).code = code as u64;
        (*plan).env = env;
        (*plan).arity = if code.is_null() { 0 } else { exact as u64 };
        (*plan).rest = after as u64;
        if let Some(v) = value {
            (*plan).value.write(v);
        }
    }
    drop(f);
    while let Some(f) = applied.pop() {
        drop(f);
    }
}

/// A closure's address word (its `Rc`'s allocation, as a function value
/// holds it at byte 8), for native code, which owns the reference from then
/// on.
pub fn into_word(f: Rc<Fun>) -> u64 {
    Rc::into_raw(f) as u64 - RC_VALUE_AT as u64
}

/// The context's error for `e`.
fn error_code(e: ResourceError) -> u64 {
    match e {
        ResourceError::Work => OUT_OF_STEPS,
        _ => OUT_OF_FRAMES,
    }
}

/// `Closure`: a closure of `lambda` capturing the `n` values at `args`
/// (moved), put in `out` (uninitialised).
///
/// # Safety
/// As [`sw_ctor`].
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_closure(lambda: u32, args: *mut Value, n: u64, out: *mut Value) {
    // SAFETY: the caller's contract.
    let captures: Box<[Value]> = (0..n as usize)
        .map(|i| unsafe { args.add(i).read() })
        .collect();
    unsafe { out.write(Value::Fun(Rc::new(Fun::Closure { lambda, captures }))) };
}

/// `Pap`: global `g` (a function or a native) with the `n` values at `args`
/// (moved), put in `out` (uninitialised).
///
/// # Safety
/// As [`sw_global`] and [`sw_ctor`].
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_pap(
    context: *mut Context,
    g: u32,
    args: *mut Value,
    n: u64,
    out: *mut Value,
) {
    // SAFETY: the caller's contract.
    let held: Box<[Value]> = (0..n as usize)
        .map(|i| unsafe { args.add(i).read() })
        .collect();
    let run = unsafe { &mut *(*context).run };
    let head = function_value(run, g);
    unsafe { out.write(Value::Fun(Rc::new(Fun::Pap { head, args: held }))) };
}

/// `IntCase` of a value that isn't a small `Int`: 1 if it's negative.
///
/// # Safety
/// `v` points at a live value.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_int_negative(v: *const Value) -> u64 {
    // SAFETY: the caller's contract.
    match unsafe { &*v } {
        Value::Int(i) => u64::from(*i < 0),
        Value::BigInt(i) => u64::from(i.sign() == num_bigint::Sign::Minus),
        other => internal(format_args!("matched {other:?} as an `Int`")),
    }
}

/// [`sw_unary`]'s operations: the machine's `IntOfNat`, `IntNegSucc` and
/// `TextChars`.
pub const UNARY_INT_OF_NAT: u32 = 0;
pub const UNARY_INT_NEG_SUCC: u32 = 1;
pub const UNARY_TEXT_CHARS: u32 = 2;

/// One of the machine's one-operand instructions ([`UNARY_INT_OF_NAT`] and
/// so on) on the value at `src`, written to register `dst`.
///
/// # Safety
/// `context` is the running context; both point at registers.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_unary(
    context: *mut Context,
    op: u32,
    src: *const Value,
    dst: *mut Value,
) {
    // SAFETY: the caller's contract.
    unsafe {
        let shapes = &(*(*context).run).program.shapes;
        let src = &*src;
        let v = match op {
            UNARY_INT_OF_NAT => crate::prims::int_to_nat(src),
            UNARY_INT_NEG_SUCC => crate::prims::int_neg_succ(src),
            _ => crate::prims::chars(shapes, crate::prims::text_of(src)),
        };
        *dst = v;
    }
}

// ------------------------------------------------- the effect runtime (N4)
//
// `bind` inline (stage N4), and `Text.fold`'s leaf (stage NO1 of
// docs/proposals/native-only.md). Until stage NO3 the other effect natives
// were run by the machine, nested (`sw_effect`, and `sw_tail_effect` and
// `sw_perform` for a tail position); since NO3 they are all the runtime
// bodies' and the leaves' below.

/// `bind c k`, up to the call: for `c` = `Done x` (the cell taken apart as
/// the machine's `field` does), writes `x` to `out` and returns 1, and
/// native code then applies `k` (which it still owns) to it; otherwise
/// writes the node `Bind c k` (both moved in) and returns 0.
///
/// # Safety
/// `context` is the running context; `c` and `k` point at values native
/// code owns (`c` is taken; `k` only if it returns 0); `out` at space for
/// one.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_bind(
    context: *mut Context,
    c: *mut Value,
    k: *mut Value,
    out: *mut Value,
) -> u64 {
    // SAFETY: the caller's contract.
    let run = unsafe { &mut *(*context).run };
    let s = run.program.shapes;
    match unsafe { c.read() } {
        Value::Data(tag, fields) if tag == s.done => {
            unsafe { out.write(crate::machine::field(fields, 0)) };
            1
        }
        c => {
            let k = unsafe { k.read() };
            run.state().counts.binds += 1;
            unsafe { out.write(Value::data(s.bind_node, [c, k])) };
            0
        }
    }
}

/// A state-passing handler's fold (`op`, its place in [`EffectOp::ALL`]:
/// `FoldState` or `FoldStateComp`) on the three values at `args` (moved):
/// its function of the state to `out`, as the machine's `effect` makes it
/// (`machine::state_handler`; stage NO3 of docs/proposals/native-only.md).
/// A leaf: it runs nothing.
///
/// # Safety
/// `context` is the running context; `args` points at three values native
/// code owns; `out` at space for one.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_eff_state(
    context: *mut Context,
    op: u32,
    args: *mut Value,
    out: *mut Value,
) {
    let op = EffectOp::ALL[op as usize];
    // SAFETY: the caller's contract.
    let shapes = unsafe { &(*(*context).run).program.shapes };
    let mut i = 0;
    let v = crate::machine::state_handler(shapes, op, || {
        // SAFETY: the caller's contract: the op's values, each read once.
        let v = unsafe { args.add(i).read() };
        i += 1;
        v
    });
    // SAFETY: the caller's contract.
    unsafe { out.write(v) };
}

/// For the compiled `Text.fold` (stage NO1 of docs/proposals/native-only.md),
/// a leaf: the last character of the text at `t` (borrowed) before byte
/// `end` (`u64::MAX` for the whole text), as the machine's `fold_step`
/// takes it, written to `out` as a `Char` (`prims::char_value`); returns
/// where it starts, the next call's `end`. `u64::MAX`, with nothing
/// written, if there is none left.
///
/// # Safety
/// `context` is the running context; `t` points at a `Text`; `out` at space
/// for a value.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_text_last(
    context: *mut Context,
    t: *const Value,
    end: u64,
    out: *mut Value,
) -> u64 {
    // SAFETY: the caller's contract.
    let (shapes, text) = unsafe {
        (
            &(*(*context).run).program.shapes,
            crate::prims::text_of(&*t),
        )
    };
    let end = if end == u64::MAX {
        text.len()
    } else {
        end as usize
    };
    match text[..end].chars().next_back() {
        None => u64::MAX,
        Some(c) => {
            // SAFETY: the caller's contract.
            unsafe { out.write(crate::prims::char_value(shapes, c)) };
            (end - c.len_utf8()) as u64
        }
    }
}

// ------------------------------------- the effect runtime's leaves (NO2)
//
// Stage NO2 of docs/proposals/native-only.md: the run loop (`rt_loop`) and
// an eager resumption (`rt_resume`) are native code, emitted by the compiler
// (`stitchwort_native::n1`), and these are their leaves: they take values
// apart and build them exactly as the machine's `eff_run`, `eff_call` and
// `resume` do, in the same order, and never call program code. A handler is
// held by native code as its `Rc`'s pointer word ([`Rc::into_raw`]), which
// it owns; so is a state-passing handler's resumption while its clause runs
// (stage NO3).

/// What [`sw_eff_step`] found, for `rt_loop` to do next.
/// A `Bind` node: its continuation pushed, the loop goes on with its inner
/// computation.
pub const STEP_AGAIN: u64 = 0;
/// `Done x` with a continuation pending: apply it (the first value) to `x`
/// (the second), and go on with the result; the handler is still the loop's.
pub const STEP_APPLY: u64 = 1;
/// The loop's value (the first), the handler dropped.
pub const STEP_RETURN: u64 = 2;
/// A fold's `done x`: the first value applied to the second in a tail
/// position, the handler dropped.
pub const STEP_DONE: u64 = 3;
/// A fold's `call o k`: the first value applied to the next two in a tail
/// position, the handler gone into `k`.
pub const STEP_CALL: u64 = 4;
/// A `translate`'s operation: the first value (`inject`) applied to the
/// second (`o`), then `Call` of the result and the third (`k`, which has
/// the handler) is the loop's value.
pub const STEP_INJECT: u64 = 5;
/// A state-passing handler's `done x s` (stage NO3): the first value
/// applied to the second, then its result to the loop's state in a tail
/// position (the machine's `Ret::Apply`), the handler dropped.
pub const STEP_STATE_DONE: u64 = 6;
/// A state-passing handler's `call o k jump s` (stage NO3): the first value
/// applied to the next four (the state moved out of the loop's), its result
/// then given to [`sw_state_step`] with the resumption (whose word is
/// written for the loop to hold: the machine's `Ret::Step`), which has the
/// handler.
pub const STEP_STATE_CALL: u64 = 7;

/// The handler a native code word holds, taken.
///
/// # Safety
/// `word` came from [`Rc::into_raw`] of a live handler, and native code
/// gives the reference up.
#[allow(unsafe_code)]
unsafe fn handler_taken(word: u64) -> Rc<Handler> {
    // SAFETY: the caller's contract.
    unsafe { Rc::from_raw(word as *const Handler) }
}

/// The resumption a native code word holds, taken.
///
/// # Safety
/// `word` came from [`Rc::into_raw`] of a live resumption, and native code
/// gives the reference up.
#[allow(unsafe_code)]
unsafe fn resume_taken(word: u64) -> Rc<Resume> {
    // SAFETY: the caller's contract.
    unsafe { Rc::from_raw(word as *const Resume) }
}

/// One of the effect runtime's natives that runs a loop (`op`, its place
/// in [`EffectOp::ALL`]: a fold, `translate` or `runPure`) on the values
/// at `args` (moved): the computation to `c` (uninitialised), and the
/// handler's word (owned by native code), as the machine's `effect` makes
/// them.
///
/// # Safety
/// `context` is the running context; `args` points at the op's values,
/// which native code owns; `c` at space for one.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_eff_begin(
    context: *mut Context,
    op: u32,
    args: *mut Value,
    c: *mut Value,
) -> u64 {
    let op = EffectOp::ALL[op as usize];
    // SAFETY: the caller's contract.
    let shapes = unsafe { &(*(*context).run).program.shapes };
    let mut i = 0;
    let (handler, comp) = crate::machine::handler_for(shapes, op, || {
        // SAFETY: the caller's contract: the op's values, each read once.
        let v = unsafe { args.add(i).read() };
        i += 1;
        v
    });
    // SAFETY: the caller's contract.
    unsafe { c.write(comp) };
    Rc::into_raw(handler) as u64
}

/// One step of the run loop (the machine's `eff_run`, and `eff_call` at an
/// operation), on the computation at `c` (taken), with the pending list at
/// `pending` and the state at `state` (native code's; replaced) and the
/// handler `handler` (native code's word): what to do next ([`STEP_AGAIN`]
/// and the others), with the values for it written to `out` (room for
/// five, uninitialised), and `c` the next computation for [`STEP_AGAIN`].
/// Where the handler is done with (every outcome but [`STEP_AGAIN`] and
/// [`STEP_APPLY`]) it's taken, and the pending list is then `Erased`; for
/// [`STEP_STATE_CALL`] so is the state, and the resumption's word is
/// written to `resume`. The step itself is native code's to count; the
/// effect counts are counted here.
///
/// # Safety
/// `context` is the running context; `c`, `pending` and `state` point at
/// values native code owns; `handler` is a handler's word native code owns;
/// `out` at space for five values, `resume` for a word.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_eff_step(
    context: *mut Context,
    c: *mut Value,
    pending: *mut Value,
    state: *mut Value,
    handler: u64,
    out: *mut Value,
    resume_out: *mut u64,
) -> u64 {
    // SAFETY: the caller's contract.
    let run = unsafe { &mut *(*context).run };
    let s = &run.program.shapes;
    let counts = &mut run.state().counts;
    counts.steps += 1;
    let write = |i: usize, v: Value| {
        // SAFETY: the caller's contract: room for five values.
        unsafe { out.add(i).write(v) }
    };
    // SAFETY: the caller's contract.
    let Value::Data(tag, fields) = (unsafe { c.read() }) else {
        internal(format_args!("ran a value that isn't a computation"))
    };
    if tag == s.bind_node {
        counts.pushes += 1;
        let (inner, k) = crate::machine::pair(fields);
        // SAFETY: the caller's contract: `pending` is taken and replaced.
        unsafe {
            let rest = pending.read();
            pending.write(Value::data(0, [k, rest]));
            c.write(inner);
        }
        return STEP_AGAIN;
    }
    // SAFETY: the caller's contract: taken, and replaced below.
    let list = unsafe { pending.read() };
    if tag == s.done {
        if let Value::Data(_, cell) = list {
            counts.pops += 1;
            let (k, next) = crate::machine::pair(cell);
            let x = crate::machine::field(fields, 0);
            // SAFETY: as above.
            unsafe { pending.write(next) };
            write(0, k);
            write(1, x);
            return STEP_APPLY;
        }
        // SAFETY: as above (`Erased`).
        unsafe { pending.write(list) };
        // SAFETY: the caller's contract; the loop is done with it.
        let handler = unsafe { handler_taken(handler) };
        return match &*handler {
            Handler::Fold { done, .. } => {
                let done = done.clone();
                write(0, done);
                write(1, crate::machine::field(fields, 0));
                STEP_DONE
            }
            // `done v s`, the state still the loop's.
            Handler::State { done, .. } => {
                let done = done.clone();
                write(0, done);
                write(1, crate::machine::field(fields, 0));
                STEP_STATE_DONE
            }
            Handler::RunPure => {
                write(0, crate::machine::field(fields, 0));
                STEP_RETURN
            }
            Handler::Translate { .. } | Handler::Step => {
                write(0, Value::Data(tag, fields));
                STEP_RETURN
            }
        };
    }
    debug_assert_eq!(tag, s.call);
    // SAFETY: the caller's contract; the loop is done with it.
    let handler = unsafe { handler_taken(handler) };
    // SAFETY: as above.
    unsafe { pending.write(Value::Erased) };
    if let Handler::Step = &*handler
        && matches!(list, Value::Erased)
    {
        // Nothing pending: the operation as it is (the machine's
        // `eff_call`).
        write(0, Value::Data(s.call, fields));
        return STEP_RETURN;
    }
    let (o, rest) = crate::machine::pair(fields);
    let resume = |handler, op| {
        Rc::new(Resume {
            handler,
            rest,
            pending: list,
            op,
        })
    };
    match &*handler {
        Handler::Fold { call, lazy, .. } => {
            counts.routes += 1;
            let (call, lazy) = (call.clone(), *lazy);
            let k = Value::Fun(Rc::new(Fun::Resume(resume(handler, Value::Erased), lazy)));
            write(0, call);
            write(1, o);
            write(2, k);
            STEP_CALL
        }
        // `call o k jump s` (the machine's `eff_call`), its result for
        // `sw_state_step` with the resumption.
        Handler::State { call, .. } => {
            counts.routes += 1;
            let call = call.clone();
            let resume = resume(handler, Value::Erased);
            let k = Value::Fun(Rc::new(Fun::StateK(resume.clone())));
            let jump = Value::Fun(Rc::new(Fun::JumpK));
            // SAFETY: the caller's contract: the state is taken.
            let st = unsafe { std::mem::take(&mut *state) };
            write(0, call);
            write(1, o);
            write(2, k);
            write(3, jump);
            write(4, st);
            // SAFETY: the caller's contract.
            unsafe { resume_out.write(Rc::into_raw(resume) as u64) };
            STEP_STATE_CALL
        }
        Handler::Translate { inject, .. } => {
            counts.routes += 1;
            let inject = inject.clone();
            let k = Value::Fun(Rc::new(Fun::Resume(resume(handler, o.clone()), false)));
            write(0, inject);
            write(1, o);
            write(2, k);
            STEP_INJECT
        }
        Handler::Step => {
            let k = Value::Fun(Rc::new(Fun::Resume(resume(handler, Value::Erased), false)));
            write(0, Value::data(s.call, [o, k]));
            STEP_RETURN
        }
        Handler::RunPure => internal(format_args!("an operation reached `runPure`")),
    }
}

/// A state-passing handler's clause returned the value at `v` (taken) for
/// the operation whose resumption's word is `resume` (taken): the
/// machine's `state_step` (`machine::state_step`, shared; stage NO3 of
/// docs/proposals/native-only.md). A jump returns 1, with the loop's new
/// handler word written to `handler`, its pending list to `pending` and its
/// state to `state` (both uninitialised: the loop's were moved out), `rest`
/// and the value to go on with to `out`, and the jump's own word to
/// `jumped`, for native code to drop once `rest` is taken apart (the
/// machine drops it after `apply`). Anything else returns 0, with the value
/// as it is at `out`: the handler's result.
///
/// # Safety
/// `context` is the running context; `v` points at a value native code
/// owns; `resume` is a resumption's word native code owns; `out` points at
/// space for two values, `state` and `pending` for one each, `handler` and
/// `jumped` for a word each.
#[allow(unsafe_code, clippy::too_many_arguments)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_state_step(
    context: *mut Context,
    v: *mut Value,
    resume: u64,
    out: *mut Value,
    state: *mut Value,
    pending: *mut Value,
    handler: *mut u64,
    jumped: *mut u64,
) -> u64 {
    // SAFETY: the caller's contract.
    let (run, v, resume) = unsafe { (&mut *(*context).run, v.read(), resume_taken(resume)) };
    let counts = &mut run.state().counts;
    match crate::machine::state_step(counts, v, resume) {
        crate::machine::StateStep::Value(v) => {
            // SAFETY: the caller's contract.
            unsafe { out.write(v) };
            0
        }
        crate::machine::StateStep::Jump {
            handler: h,
            rest,
            pending: p,
            y,
            state: st,
            jumped: f,
        } => {
            // SAFETY: the caller's contract.
            unsafe {
                handler.write(Rc::into_raw(h) as u64);
                pending.write(p);
                state.write(st);
                out.write(rest);
                out.add(1).write(y);
                jumped.write(into_word(f));
            }
            1
        }
    }
}

/// For `rt_resume`: an eager resumption, or (stage NO3) a state-passing
/// handler's function of the state (the function value whose `Rc`'s word
/// is `k`, borrowed), called with the value at `y` (taken), taken apart as
/// the machine's `resume` (or `enter` of a `StateRun`) does: the handler's
/// word (a new reference) to `handler`, and to `out` the pending list and
/// `rest` (`Erased` for a function of the state without one), then:
/// - for an eager resumption (returning 0), `y`;
/// - for a `translate`'s (returning 1), `reply`, the operation and `y`;
/// - for a function of the state (returning 2), the computation to run, or
///   to give `rest`, and the state (`y`).
///
/// Copies, made in the machine's order.
///
/// # Safety
/// `k` is the word of a live `Fun::Resume` or `Fun::StateRun`; `y` points
/// at a value native code owns; `out` at space for five values, `handler`
/// for a word.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_resume_begin(
    k: u64,
    y: *mut Value,
    out: *mut Value,
    handler: *mut u64,
) -> u64 {
    // SAFETY: the caller's contract: borrowed, so not dropped.
    let k = std::mem::ManuallyDrop::new(unsafe { from_words(u64::from(TAG_FUN), k, 0) });
    let Value::Fun(fun) = &*k else {
        internal(format_args!("resumed a value that isn't a function"))
    };
    let write = |i: usize, v: Value| {
        // SAFETY: the caller's contract: room for five values.
        unsafe { out.add(i).write(v) }
    };
    // SAFETY: the caller's contract.
    let y = unsafe { y.read() };
    let resume = match &**fun {
        Fun::Resume(resume, _) => resume,
        // The machine's `enter` of a `StateRun`: the handler, then the
        // pending list, `rest` and the computation, or (with no `rest`) the
        // computation and the pending list.
        Fun::StateRun(run) => {
            // SAFETY: the caller's contract.
            unsafe { handler.write(Rc::into_raw(run.handler.clone()) as u64) };
            if matches!(run.rest, Value::Erased) {
                write(2, run.arg.clone());
                write(0, run.pending.clone());
                write(1, Value::Erased);
            } else {
                write(0, run.pending.clone());
                write(1, run.rest.clone());
                write(2, run.arg.clone());
            }
            write(3, y);
            return 2;
        }
        _ => internal(format_args!("resumed a function that isn't a resumption")),
    };
    // SAFETY: the caller's contract.
    unsafe { handler.write(Rc::into_raw(resume.handler.clone()) as u64) };
    write(0, resume.pending.clone());
    match &*resume.handler {
        Handler::Translate { reply, .. } => {
            write(1, resume.rest.clone());
            write(2, reply.clone());
            write(3, resume.op.clone());
            write(4, y);
            1
        }
        _ => {
            write(1, resume.rest.clone());
            write(2, y);
            0
        }
    }
}

/// A handler native code holds (its word, given up) on a frame's error
/// exit: kept with the last group of the unwind log, as the machine keeps
/// it in the `Ret` of the frame that just left ([`sw_unwind`]'s mode 3), or
/// dropped now if no frame has left. The log holds values, so it's kept as
/// one: a resumption around it that nothing will run.
///
/// # Safety
/// As [`sw_global`]; `handler` is a handler's word native code owns, and
/// gives up.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_unwind_handler(context: *mut Context, handler: u64) {
    // SAFETY: the caller's contract.
    let (run, handler) = unsafe { (&mut *(*context).run, handler_taken(handler)) };
    match run.held.last_mut() {
        Some(group) => {
            let holder = Resume {
                handler,
                rest: Value::Erased,
                pending: Value::Erased,
                op: Value::Erased,
            };
            group.push(Value::Fun(Rc::new(Fun::Resume(Rc::new(holder), false))));
        }
        None => drop(handler),
    }
}

/// A resumption native code holds (its word, given up: a state-passing
/// handler's, while its clause runs) on a frame's error exit, as
/// [`sw_unwind_handler`] does with a handler: kept as a resumption value
/// with the last group of the unwind log, where the machine keeps it in
/// the callee frame's `Ret::Step`, or dropped now if no frame has left
/// (stage NO3 of docs/proposals/native-only.md).
///
/// # Safety
/// As [`sw_global`]; `resume` is a resumption's word native code owns, and
/// gives up.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_unwind_resume(context: *mut Context, resume: u64) {
    // SAFETY: the caller's contract.
    let (run, resume) = unsafe { (&mut *(*context).run, resume_taken(resume)) };
    match run.held.last_mut() {
        Some(group) => group.push(Value::Fun(Rc::new(Fun::Resume(resume, false)))),
        None => drop(resume),
    }
}
