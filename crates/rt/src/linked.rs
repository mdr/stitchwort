//! What an executable built with `--native` carries in place of the
//! program (stage NO6 of docs/proposals/native-only.md, D1300): the tables
//! native code reads, and a literal table from which the runtime builds the
//! constant pool once at start-up. No bodies, no bytecode and no image: the
//! executable runs every body as native code, so it needs only what that
//! code reads by number ([`crate::native_abi::Tables`]) and what the
//! runtime around it needs to know about the program ([`Outline`]).
//!
//! `stitchwort build --native` writes [`encode`]'s bytes into the object;
//! the runtime library reads them with [`decode`]. The format is the
//! codec's style ([`crate::wire`]): LEB128 integers and length-prefixed
//! strings.
//!
//! **Layout.** `SWTB`, the format version, the crate version and the build
//! hash (as the codec checks them: the library must be built from the same
//! code as the compiler that wrote the bytes, since the native code's
//! numbering is that build's); the [`Limits`]; the [`MainRow`]; the
//! [`Shapes`]; per global its kind, its body's number and (for a global with
//! a body) its name; per lambda its parameters; the entry's body number; the
//! operations (`Numbering::ops`); the number tables; and the constant pool.
//!
//! **The pool** is written as its values' nodes in post-order, and read
//! with a stack: a leaf pushes a value, `Data tag n` pops `n` fields and
//! pushes the constructor. A list literal (a `Chars` literal is one) is
//! deep but is read and written without recursion.
//!
//! **Reading is total.** Bytes that aren't such tables give an error:
//! counts are checked against the bytes left, and every pop against the
//! stack. They are trusted to agree with the native code beside them, which
//! the same `build` wrote into the same object.

use std::rc::Rc;

use num_bigint::{BigInt, BigUint, Sign};

use crate::code::Image;
use crate::ir::{GlobalKind, MainRow, PrimOp, Program, Shapes};
use crate::native_abi::Numbering;
use crate::shared::{Arities, Limits, NumTable, body_name};
use crate::value::{Fun, Value};
use crate::wire::{BUILD_HASH, CodecError, Read, Reader, Writer, bad, read_shapes, write_shapes};

const MAGIC: &[u8; 4] = b"SWTB";

/// Bumped when the layout changes.
pub const FORMAT_VERSION: u8 = 1;

/// What the runtime around native code needs to know about a program: its
/// shapes and `main`'s row (for the runner), each global's kind and each
/// lambda's parameters (for applying function values), and the names of
/// the bodies (for the depth note). Made from the program and its image by
/// `run --native` ([`Outline::of`]), and read from the executable's tables
/// by one built with `--native`.
pub struct Outline {
    pub shapes: Shapes,
    pub main_row: MainRow,
    pub globals: Box<[GlobalOutline]>,
    /// Each lambda's number of parameters.
    pub lambda_params: Box<[u32]>,
    /// Each global's body, as the image numbers them, if it has one.
    pub global_code: Box<[Option<u32>]>,
    /// The entry's body.
    pub entry_code: u32,
}

/// A global, as [`Outline`] has it.
pub struct GlobalOutline {
    /// Its full name (`Std.List.map`), for a global with a body; empty for
    /// a native, which the depth note never names.
    pub name: Rc<str>,
    pub kind: Kind,
}

/// A global's kind ([`GlobalKind`] without its body).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// Takes `params` runtime arguments (at least one).
    Function { params: u32 },
    /// Computed when it's first used, and kept.
    Constant,
    /// A native operation, as a value.
    Native(PrimOp),
}

impl Kind {
    /// How many runtime arguments a call passes ([`GlobalKind::params`]).
    pub fn params(self) -> u32 {
        match self {
            Kind::Function { params } => params,
            Kind::Constant => 0,
            Kind::Native(op) => op.arity(),
        }
    }
}

impl Outline {
    /// The outline of `program`, whose image is `image`.
    pub fn of(program: &Program, image: &Image) -> Outline {
        Outline {
            shapes: program.shapes,
            main_row: program.main_row,
            globals: program
                .globals
                .iter()
                .map(|global| GlobalOutline {
                    name: global.name.clone(),
                    kind: match &global.kind {
                        GlobalKind::Function { params, .. } => Kind::Function { params: *params },
                        GlobalKind::Constant { .. } => Kind::Constant,
                        GlobalKind::Native(op) => Kind::Native(*op),
                    },
                })
                .collect(),
            lambda_params: program.lambdas.iter().map(|lambda| lambda.params).collect(),
            global_code: image.global_code.clone().into_boxed_slice(),
            entry_code: image.entry_code,
        }
    }

    /// The depth note for `deepest` (`shared::deepest`), as the machine's.
    pub fn depth_report(&self, deepest: &[(u32, usize)]) -> Option<String> {
        crate::shared::depth_report(deepest, |code| {
            body_name(
                &self.global_code,
                self.entry_code,
                |g| &self.globals[g].name,
                code,
            )
        })
    }
}

impl Arities for Outline {
    fn global_params(&self, g: u32) -> u32 {
        self.globals[g as usize].kind.params()
    }

    fn lambda_params(&self, lambda: u32) -> u32 {
        self.lambda_params[lambda as usize]
    }
}

/// The tables native code reads (`native_abi::Tables` points into them),
/// owned: built from an executable's bytes, where `run --native` borrows
/// the image's.
pub struct LinkedTables {
    /// Boxed, so that it doesn't move when the tables do.
    pub shapes: Box<Shapes>,
    /// The constant pool, as the image's.
    pub pool: Box<[Value]>,
    /// Every body's number tables, in `Numbering`'s order.
    pub num_tables: Box<[NumTable]>,
    /// The operations, in `Numbering`'s order.
    pub ops: Box<[PrimOp]>,
}

/// What [`decode`] reads.
pub struct Linked {
    pub outline: Outline,
    pub tables: LinkedTables,
    pub limits: Limits,
}

// ------------------------------------------------------------------ writing

/// The pool's node tags.
const ERASED: u8 = 0;
const DONE_K: u8 = 1;
const NAT: u8 = 2;
const BIG_NAT: u8 = 3;
const INT: u8 = 4;
const BIG_INT: u8 = 5;
const TEXT: u8 = 6;
const FLOAT: u8 = 7;
const TAG: u8 = 8;
const DATA: u8 = 9;

impl Writer {
    fn signed(&mut self, n: i64) {
        // Zigzag, so that small negative numbers are short.
        self.uint(((n << 1) ^ (n >> 63)) as u64);
    }

    fn big_int(&mut self, n: &BigInt) {
        let (sign, magnitude) = n.clone().into_parts();
        self.u8(match sign {
            Sign::Minus => 0,
            Sign::NoSign => 1,
            Sign::Plus => 2,
        });
        self.big(&magnitude);
    }

    /// `v`'s nodes in post-order (see the module comment). Returns how many.
    fn pool_value(&mut self, v: &Value) -> usize {
        enum Work<'v> {
            Visit(&'v Value),
            Data(u32, usize),
        }
        let mut nodes = 0;
        let mut work = vec![Work::Visit(v)];
        while let Some(item) = work.pop() {
            nodes += 1;
            match item {
                Work::Visit(Value::Data(tag, fields)) => {
                    nodes -= 1;
                    work.push(Work::Data(*tag, fields.len()));
                    work.extend(fields.iter().rev().map(Work::Visit));
                }
                Work::Data(tag, n) => {
                    self.u8(DATA);
                    self.uint(u64::from(tag));
                    self.usize(n);
                }
                Work::Visit(Value::Erased) => self.u8(ERASED),
                Work::Visit(Value::Nat(n)) => {
                    self.u8(NAT);
                    self.uint(*n);
                }
                Work::Visit(Value::BigNat(n)) => {
                    self.u8(BIG_NAT);
                    self.big(n);
                }
                Work::Visit(Value::Int(n)) => {
                    self.u8(INT);
                    self.signed(*n);
                }
                Work::Visit(Value::BigInt(n)) => {
                    self.u8(BIG_INT);
                    self.big_int(n);
                }
                Work::Visit(Value::Text(t)) => {
                    self.u8(TEXT);
                    self.str(t);
                }
                Work::Visit(Value::Float(x)) => {
                    self.u8(FLOAT);
                    self.uint(x.to_bits());
                }
                Work::Visit(Value::Tag(tag)) => {
                    self.u8(TAG);
                    self.uint(u64::from(*tag));
                }
                Work::Visit(Value::Fun(f)) if matches!(**f, Fun::DoneK) => self.u8(DONE_K),
                Work::Visit(other) => {
                    panic!(
                        "internal error: a constant the executable's tables can't hold: {other:?}"
                    )
                }
            }
        }
        nodes
    }
}

/// The tables and literals of `program`, whose image is `image`, for native
/// code that runs under `limits`, as bytes.
pub fn encode(program: &Program, image: &Image, limits: &Limits) -> Vec<u8> {
    let mut w = Writer::default();
    w.bytes.extend_from_slice(MAGIC);
    w.u8(FORMAT_VERSION);
    w.str(env!("CARGO_PKG_VERSION"));
    w.uint(BUILD_HASH);
    w.uint(limits.steps);
    w.usize(limits.frames);
    w.u8(match program.main_row {
        MainRow::Io => 0,
        MainRow::FailIo => 1,
    });
    write_shapes(&mut w, &program.shapes);
    w.usize(program.globals.len());
    for (global, code) in program.globals.iter().zip(&image.global_code) {
        match &global.kind {
            GlobalKind::Function { params, .. } => {
                w.u8(0);
                w.uint(u64::from(*params));
            }
            GlobalKind::Constant { .. } => w.u8(1),
            GlobalKind::Native(op) => {
                w.u8(2);
                w.prim(*op);
            }
        }
        match code {
            Some(code) => {
                w.uint(u64::from(*code) + 1);
                w.str(&global.name);
            }
            None => w.uint(0),
        }
    }
    w.usize(program.lambdas.len());
    for lambda in &program.lambdas {
        w.uint(u64::from(lambda.params));
    }
    w.uint(u64::from(image.entry_code));
    let numbering = Numbering::of(image);
    w.usize(numbering.ops.len());
    for op in &numbering.ops {
        w.prim(*op);
    }
    let tables: Vec<&NumTable> = image
        .codes
        .iter()
        .flat_map(|code| &code.num_tables)
        .collect();
    w.usize(tables.len());
    for table in tables {
        w.usize(table.small.len());
        for (k, target) in &table.small {
            w.uint(*k);
            w.uint(u64::from(*target));
        }
        w.usize(table.big.len());
        for (k, target) in &table.big {
            w.big(k);
            w.uint(u64::from(*target));
        }
        w.uint(u64::from(table.default));
    }
    // The pool: its length, then its nodes, counted first.
    let mut nodes = Writer::default();
    let count: usize = image.pool.iter().map(|v| nodes.pool_value(v)).sum();
    w.usize(image.pool.len());
    w.usize(count);
    w.bytes.extend_from_slice(&nodes.bytes);
    w.bytes
}

// ------------------------------------------------------------------ reading

impl Reader<'_> {
    fn signed(&mut self) -> Read<i64> {
        let n = self.uint()?;
        Ok(((n >> 1) as i64) ^ -((n & 1) as i64))
    }

    fn big_int(&mut self) -> Read<BigInt> {
        let sign = match self.u8()? {
            0 => Sign::Minus,
            1 => Sign::NoSign,
            2 => Sign::Plus,
            t => return bad(format!("no sign tagged {t}")),
        };
        let n = BigInt::from_biguint(sign, self.big()?);
        if n.sign() != sign {
            return bad("an integer whose sign doesn't match its size");
        }
        Ok(n)
    }

    /// `n` pool nodes, read onto a stack: the pool, if it holds `entries`
    /// values at the end.
    fn pool(&mut self, entries: usize, n: usize) -> Read<Vec<Value>> {
        let mut stack: Vec<Value> = Vec::with_capacity(entries);
        for _ in 0..n {
            let v = match self.u8()? {
                ERASED => Value::Erased,
                DONE_K => Value::Fun(Rc::new(Fun::DoneK)),
                NAT => Value::Nat(self.uint()?),
                BIG_NAT => Value::BigNat(Rc::new(self.big()?)),
                INT => Value::Int(self.signed()?),
                BIG_INT => Value::BigInt(Rc::new(self.big_int()?)),
                TEXT => Value::Text(self.str()?),
                FLOAT => Value::float(f64::from_bits(self.uint()?)),
                TAG => Value::Tag(self.u32()?),
                DATA => {
                    let tag = self.u32()?;
                    let fields = self.usize()?;
                    if fields == 0 || fields > stack.len() {
                        return bad(format!("a constructor of {fields} fields"));
                    }
                    let fields = stack.split_off(stack.len() - fields);
                    Value::data_vec(tag, fields)
                }
                t => return bad(format!("no constant tagged {t}")),
            };
            stack.push(v);
        }
        if stack.len() != entries {
            return bad(format!(
                "a pool of {} constants, not {entries}",
                stack.len()
            ));
        }
        Ok(stack)
    }
}

/// Reads what [`encode`] wrote. An error if the bytes aren't tables of
/// this format, version and build, or aren't well formed.
pub fn decode(bytes: &[u8]) -> Result<Linked, CodecError> {
    let mut r = Reader {
        bytes,
        at: 0,
        depth: 0,
    };
    if r.raw(MAGIC.len())? != MAGIC {
        return bad("not the tables of a Stitchwort program");
    }
    let format = r.u8()?;
    if format != FORMAT_VERSION {
        return bad(format!("format version {format}, not {FORMAT_VERSION}"));
    }
    let version = r.str()?;
    if *version != *env!("CARGO_PKG_VERSION") {
        return bad(format!(
            "written by version {version}, not {}",
            env!("CARGO_PKG_VERSION")
        ));
    }
    if r.uint()? != BUILD_HASH {
        return bad("written by a different build of the runtime");
    }
    let limits = Limits {
        steps: r.uint()?,
        frames: r.usize()?,
    };
    let main_row = match r.u8()? {
        0 => MainRow::Io,
        1 => MainRow::FailIo,
        t => return bad(format!("no main row tagged {t}")),
    };
    let shapes = read_shapes(&mut r)?;
    let n = r.count()?;
    let mut globals = Vec::with_capacity(n);
    let mut global_code = Vec::with_capacity(n);
    for _ in 0..n {
        let kind = match r.u8()? {
            0 => Kind::Function { params: r.u32()? },
            1 => Kind::Constant,
            2 => Kind::Native(r.prim()?),
            t => return bad(format!("no global tagged {t}")),
        };
        let (code, name) = match r.u32()? {
            0 => (None, Rc::from("")),
            code => (Some(code - 1), r.str()?),
        };
        globals.push(GlobalOutline { name, kind });
        global_code.push(code);
    }
    let n = r.count()?;
    let mut lambda_params = Vec::with_capacity(n);
    for _ in 0..n {
        lambda_params.push(r.u32()?);
    }
    let entry_code = r.u32()?;
    let n = r.count()?;
    let mut ops = Vec::with_capacity(n);
    for _ in 0..n {
        ops.push(r.prim()?);
    }
    let n = r.count()?;
    let mut num_tables = Vec::with_capacity(n);
    for _ in 0..n {
        let m = r.count()?;
        let mut small = Vec::with_capacity(m);
        for _ in 0..m {
            small.push((r.uint()?, r.u32()?));
        }
        let m = r.count()?;
        let mut big: Vec<(BigUint, u32)> = Vec::with_capacity(m);
        for _ in 0..m {
            big.push((r.big()?, r.u32()?));
        }
        num_tables.push(NumTable {
            small,
            big,
            default: r.u32()?,
        });
    }
    let entries = r.count()?;
    let nodes = r.count()?;
    let pool = r.pool(entries, nodes)?;
    if r.at != bytes.len() {
        return bad("bytes after the tables");
    }
    Ok(Linked {
        outline: Outline {
            shapes,
            main_row,
            globals: globals.into_boxed_slice(),
            lambda_params: lambda_params.into_boxed_slice(),
            global_code: global_code.into_boxed_slice(),
            entry_code,
        },
        tables: LinkedTables {
            shapes: Box::new(shapes),
            pool: pool.into_boxed_slice(),
            num_tables: num_tables.into_boxed_slice(),
            ops: ops.into_boxed_slice(),
        },
        limits,
    })
}
