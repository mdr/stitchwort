//! The interface between the machine and native code (stage N1 of
//! docs/proposals/native-compilation.md): what `stitchwort-native`'s
//! compiled code reads and calls, and the one place the machine hands a call
//! to it.
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
//! **The crossing** ([`NativeIslands`]). Native code runs whole reachable
//! islands (the note's §4.6): a function whose island (everything it can
//! call or make) fits the N1 subset. The machine runs `main`'s glue, and
//! where the entry body calls such a function, it hands the call over:
//!
//! - **Counting.** The machine's `Call` counts the step and checks the frame
//!   limit for the island's root, exactly as for a frame it pushes, then
//!   passes its counters in: the steps so far, and the frames pending
//!   including the root's. Native code counts on from there by the
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

use std::mem::MaybeUninit;
use std::rc::Rc;

use stitchwort_core::ResourceError;

use crate::code::{Image, Instr, NO_REG, NumTable};
use crate::ir::{GlobalKind, PrimOp, Program, Shapes};
use crate::machine::Limits;
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
    /// Each global's compiled code, or null: for `Apply`.
    pub functions: *const *const u8,
    /// The run this is part of.
    pub run: *mut NativeRun<'static>,
    /// What compiled code refers to by number ([`Tables`]): it holds no
    /// address of the host's, so the same code can go into an object file.
    pub tables: *const Tables,
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
    /// The machine's cache of global values.
    pub globals: &'a mut [Option<Value>],
    /// Steps so far in this stretch; native code's steps are added.
    pub steps: u64,
    /// Frames pending, the island root's included.
    pub frames: u64,
    pub limits: Limits,
}

/// Native code for some of a program's functions: the machine calls it at
/// the crossing (the module comment).
pub trait NativeIslands {
    /// Whether a call of global `g` from the entry body may run natively.
    fn is_root(&self, g: u32) -> bool;
    /// Whether this call, with these arguments, runs natively. `false`
    /// leaves it to the machine (an island that applies function values
    /// can't take one from outside).
    fn accepts(&self, g: u32, args: &[&Value]) -> bool;
    /// Runs `g` on `args`; the steps it takes are added to `run.steps`.
    fn call(
        &self,
        g: u32,
        args: Vec<Value>,
        run: &mut NativeRun<'_>,
    ) -> Result<Value, ResourceError>;
}

/// Whether `v` holds a function value anywhere inside it.
pub fn holds_function(v: &Value) -> bool {
    let mut pending = vec![v];
    while let Some(v) = pending.pop() {
        match v {
            Value::Fun(_) => return true,
            Value::Data(_, fields) => pending.extend(fields.iter()),
            Value::Delay(_) => return true,
            _ => {}
        }
    }
    false
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

/// Drops registers `n - 1` down to 0 of a frame, as the machine releases a
/// frame (on the way out after an error).
///
/// # Safety
/// `regs` points at `n` initialised values.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_release(regs: *mut Value, n: u64) {
    for i in (0..n as usize).rev() {
        // SAFETY: within the frame's registers.
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
    let g = g as usize;
    if let Some(v) = &run.globals[g] {
        unsafe { out.write(v.clone()) };
        return 1;
    }
    let v = match &run.program.globals[g].kind {
        GlobalKind::Constant { .. } => return 0,
        GlobalKind::Native(op) if op.arity() == 0 => Value::Erased,
        _ => Value::Fun(Rc::new(Fun::Global(g as u32))),
    };
    run.globals[g] = Some(v.clone());
    unsafe { out.write(v) };
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
    run.globals[g as usize] = Some(unsafe { (*v).clone() });
}

/// Whether a native operation can be applied by [`sw_apply_native`]: it
/// computes a value from its arguments (not an effect runtime native or
/// `Text.fold`, which the machine runs on its frames).
pub fn applicable_native(op: PrimOp) -> bool {
    !matches!(
        op,
        PrimOp::Effect(_) | PrimOp::Text(crate::natives::TextNative::TextFold)
    )
}

/// What `Apply` of the function value at `f` to `n` arguments calls: the
/// compiled code of a global function that takes `n`, or 0 for a native
/// operation that takes `n` ([`sw_apply_native`]). Island admission makes
/// sure it's one of those (the native crate's module comment); anything
/// else is an internal error.
///
/// # Safety
/// As [`sw_global`]; `f` points at a live value.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_apply_target(context: *mut Context, f: *const Value, n: u64) -> u64 {
    // SAFETY: as for `sw_global`.
    let (run, functions) = unsafe { (&*(*context).run, (*context).functions) };
    let f = unsafe { &*f };
    if let Value::Fun(fun) = f
        && let Fun::Global(g) = **fun
    {
        match &run.program.globals[g as usize].kind {
            GlobalKind::Function { params, .. } if u64::from(*params) == n => {
                // SAFETY: the table has an entry for every global.
                let code = unsafe { *functions.add(g as usize) };
                if !code.is_null() {
                    return code as u64;
                }
            }
            GlobalKind::Native(op) if u64::from(op.arity()) == n && applicable_native(*op) => {
                return 0;
            }
            _ => {}
        }
    }
    eprintln!("internal error: native code applied {f:?} to {n} arguments, outside its island");
    std::process::abort();
}

/// One `Apply`'s cache of its last target (the native crate's module
/// comment): the function value last applied there, which it keeps alive
/// so that its address can't be reused for another, and that address and
/// its compiled code. Compiled code compares a function value's address
/// with `key` and, if they're the same, calls `code` without asking the
/// runtime. `repr(C)`: compiled code reads `key` and `code` at
/// [`ApplyCache::KEY_AT`] and [`ApplyCache::CODE_AT`].
#[repr(C)]
pub struct ApplyCache {
    pub key: u64,
    pub code: u64,
    pub keep: Value,
}

impl ApplyCache {
    pub const KEY_AT: i32 = std::mem::offset_of!(ApplyCache, key) as i32;
    pub const CODE_AT: i32 = std::mem::offset_of!(ApplyCache, code) as i32;

    pub fn new() -> ApplyCache {
        ApplyCache {
            key: 0,
            code: 0,
            keep: Value::Erased,
        }
    }
}

impl Default for ApplyCache {
    fn default() -> ApplyCache {
        ApplyCache::new()
    }
}

/// [`sw_apply_target`], keeping a compiled target in `cache`.
///
/// # Safety
/// As [`sw_apply_target`]; `cache` points at a live cache.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_apply_cached(
    context: *mut Context,
    f: *const Value,
    n: u64,
    cache: *mut ApplyCache,
) -> u64 {
    // SAFETY: the caller's contract.
    let code = unsafe { sw_apply_target(context, f, n) };
    if code != 0 {
        let (f, cache) = unsafe { (&*f, &mut *cache) };
        cache.keep = f.clone();
        cache.key = words(f)[1];
        cache.code = code;
    }
    code
}

/// `Apply` of the native operation at `f` (taken) to the `n` values at
/// `args` (moved): its value, written to `out` (uninitialised), as the
/// machine's eval/apply computes it.
///
/// # Safety
/// As [`sw_global`]; `f` and `args` point at values native code owns, `out`
/// at space for one.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn sw_apply_native(
    context: *mut Context,
    f: *mut Value,
    args: *mut Value,
    n: u64,
    out: *mut Value,
) {
    // SAFETY: as for `sw_global`; the values are moved out and not used
    // again by the caller.
    let run = unsafe { &*(*context).run };
    let f = unsafe { f.read() };
    let args: Vec<Value> = (0..n as usize)
        .map(|i| unsafe { args.add(i).read() })
        .collect();
    let Value::Fun(fun) = &f else {
        unreachable!("checked by sw_apply_target")
    };
    let Fun::Global(g) = **fun else {
        unreachable!("checked by sw_apply_target")
    };
    let GlobalKind::Native(op) = run.program.globals[g as usize].kind else {
        unreachable!("checked by sw_apply_target")
    };
    let v = {
        let refs: Vec<&Value> = args.iter().collect();
        crate::prims::eval(&run.program.shapes, op, &refs)
    };
    drop(args);
    drop(f);
    unsafe { out.write(v) };
}
