//! Generated differential tests of the effect runtime
//! (docs/proposals/effect-runtime.md §9.3, stage 4e): random well-typed
//! effectful programs, each run on the reference evaluator (the type
//! checker's own, whose computations are trees), on the native machine of
//! `stitchwort-rt` and as JavaScript under Node, which must print the same
//! and end the same way.
//!
//! A program is a tree of functions over `Nat` that perform the operations of
//! four abilities, `Fail` and `IO`, and handle them with handlers of every
//! shape the runtime treats differently: clauses that discard `k`, resume it
//! once in tail position or not, twice, 0 to 3 times or in one branch; state
//! handlers (`s => k v s'`, which stage 4d runs as a loop at the empty row,
//! and the ones it doesn't fuse); handlers that collect every result; handlers
//! that store `k` in their result and are resumed after they returned, in
//! different branches; a second operation per ability, so handlers have
//! clauses of different shapes; closed, open (`{A | e}`) and concrete rows,
//! with clauses and return clauses that perform the outer row's operations
//! or print; operations forwarded through
//! towers of up to 100 handlers; computations moved between rows (a
//! `translate`) by calls of functions with smaller rows and by up to 100
//! `Fail` handlers that re-raise; effectful `List.map`s that cross many
//! binds; `IO` from `main`; and `Partial` loops in `main` around it all.
//!
//! The programs are made from seeds, a batch of them per module. A fixed
//! number of batches runs by default; `STITCHWORT_EFFECT_FUZZ_BATCHES` runs
//! more, from `STITCHWORT_EFFECT_FUZZ_SEED` (default 1). On a disagreement
//! the program is shrunk (statements removed, handlers simplified, depths
//! reduced) while it still disagrees and still checks, and the test fails
//! with the seed, the smallest program and what each backend printed.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::Instant;

use stitchwort_cli::driver::{Session, par_map};
use stitchwort_cli::run::RunError;

/// The reference evaluator recurses on the Rust stack.
const STACK: usize = 256 * 1024 * 1024;
/// Programs per module: one check of the module and one run per backend
/// covers them all.
const PER_BATCH: usize = 8;
/// Batches run by default (the CI budget).
const DEFAULT_BATCHES: u64 = 64;
/// The modulus that keeps numbers short.
const M: &str = "1000003";

// ---------------------------------------------------------------------------
// Random numbers: SplitMix64, so a seed means the same program everywhere.

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }
    fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.below(xs.len() as u64) as usize]
    }
}

// ---------------------------------------------------------------------------
// Rows: a bit per ability. Bits 0-3 are the user abilities `Ab1`-`Ab4`.

type Row = u8;
const USER: u8 = 4;
const FAIL: Row = 1 << 4;
const IO: Row = 1 << 5;

fn row_names(row: Row) -> Vec<String> {
    let mut names: Vec<String> = (0..USER)
        .filter(|a| row & (1 << a) != 0)
        .map(|a| format!("Ab{}", a + 1))
        .collect();
    if row & FAIL != 0 {
        names.push("Fail".into());
    }
    if row & IO != 0 {
        names.push("IO".into());
    }
    names
}

/// `{Ab1, IO} t`, or `t` for the empty row.
fn comp(row: Row, t: &str) -> String {
    if row == 0 {
        t.to_string()
    } else {
        format!("{{{}}} {t}", row_names(row).join(", "))
    }
}

// ---------------------------------------------------------------------------
// The programs.

#[derive(Clone, Debug)]
enum Pure {
    Lit(u64),
    /// A variable of the function: `v0` is its parameter, the others its
    /// `let`s.
    Var(u32),
    /// The element in a `List.map`'s callback.
    Y,
    Add(Box<Pure>, Box<Pure>),
    Mul(Box<Pure>, Box<Pure>),
}

#[derive(Clone, Debug)]
enum Atom {
    Pure(Pure),
    /// An operation of a user ability.
    Op(u8, Pure),
    /// Its other operation, `peek()`.
    Peek(u8),
    /// A call of another function, whose row may be smaller.
    Call(usize, Pure),
    /// A handler around a call of another function.
    Handle(usize, usize, Pure),
    If(Pure, Box<Atom>, Box<Atom>),
    /// `digest (List.map (y => atom) (List.range n))`.
    Map(u32, Box<Atom>),
    /// `h (() => tower depth (() => body arg))`: `depth` copies of handler
    /// `h`, all forwarding the body's operations except its own ability's,
    /// which the innermost one handles.
    Tower {
        handler: usize,
        depth: u32,
        row: Row,
        body: usize,
        arg: Pure,
    },
    /// `widen depth (() => body arg)`: `depth` `Fail.toResult`s that
    /// re-raise, each moving the computation into the row `row`.
    Widen {
        depth: u32,
        row: Row,
        body: usize,
        arg: Pure,
    },
}

#[derive(Clone, Debug)]
enum Stmt {
    Let(u32, Atom),
    Print(Pure),
    Ensure(Pure, u32),
}

#[derive(Clone, Debug)]
struct Body {
    row: Row,
    stmts: Vec<Stmt>,
    result: Pure,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Direct {
    Discard,
    Tail,
    NonTail,
    Twice,
    TwiceLet,
    Many,
    Branch,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum State {
    Jump,
    Get,
    Put,
    Eta,
    NonTail,
    Twice,
    Discard,
    Branch,
    Mixed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Collect {
    Discard,
    Tail,
    Cons,
    Twice,
    Many,
    Snoc,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Stored {
    Suspend,
    Shifted,
    Sometimes,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Direct(Direct),
    State(State),
    Collect(Collect),
    /// Closed only: `k` stored in a `Paused`, resumed by `explore`.
    Stored(Stored),
    /// Closed only: the same with a state.
    StoredState,
    FailOrElse,
    FailToNat,
    FailToOption,
    /// Handles `Fail` and fails again with a longer message: used only where
    /// `Fail` is in the row outside too.
    FailContext,
    FailCustom,
}

impl Kind {
    /// How many times a clause may resume, at most: what an operation costs
    /// the rest of the handled computation.
    fn factor(self) -> u32 {
        match self {
            Kind::Direct(Direct::Discard)
            | Kind::State(State::Discard)
            | Kind::Collect(Collect::Discard) => 0,
            Kind::Direct(Direct::Twice | Direct::TwiceLet)
            | Kind::State(State::Twice)
            | Kind::Collect(Collect::Twice)
            | Kind::Stored(_)
            | Kind::StoredState => 2,
            Kind::Direct(Direct::Many) | Kind::Collect(Collect::Many) => 3,
            Kind::FailOrElse
            | Kind::FailToNat
            | Kind::FailToOption
            | Kind::FailContext
            | Kind::FailCustom => 0,
            _ => 1,
        }
    }

    fn name(self) -> String {
        match self {
            Kind::Direct(c) => format!("direct/{c:?}"),
            Kind::State(c) => format!("state/{c:?}"),
            Kind::Collect(c) => format!("collect/{c:?}"),
            Kind::Stored(c) => format!("stored/{c:?}"),
            Kind::StoredState => "stored-state".into(),
            Kind::FailOrElse => "fail/orElse".into(),
            Kind::FailToNat => "fail/toResult".into(),
            Kind::FailToOption => "fail/toOption".into(),
            Kind::FailContext => "fail/context (re-raise)".into(),
            Kind::FailCustom => "fail/custom".into(),
        }
    }
}

#[derive(Clone, Debug)]
struct Handler {
    /// 0-3 for `Ab1`-`Ab4`, 4 for `Fail`.
    ability: u8,
    kind: Kind,
    /// Written for the closed row `{A}` rather than `{A | e}`.
    closed: bool,
    /// Written for a concrete row, `{A, R} Nat` to `{R} Nat`, rather than
    /// for `{A | e}`: `R`.
    concrete: Option<Row>,
    /// With `concrete`: an ability of `R` (whose handler resumes at most
    /// once) whose operation the operation clause performs on `v` before it
    /// does what its kind says, with the reply as `v`; the return clause
    /// performs it too.
    clause_op: Option<u8>,
    /// With `concrete`: the operation clause prints `v` first.
    clause_print: bool,
    /// The clause of the second operation, `peek`: 0 resumes in tail
    /// position, 1 not in tail position, 2 discards `k`.
    peek: u8,
    ret: u8,
    c: u64,
    init: u64,
    explore: u32,
}

#[derive(Clone, Debug)]
struct Program {
    bodies: Vec<Body>,
    handlers: Vec<Handler>,
    /// A `Partial` loop in `main` running the program this many times.
    partial: Option<u32>,
    arg: u64,
}

// ---------------------------------------------------------------------------
// The generator. Every function and handler is used once, so a program is a
// tree. Work is kept small: an operation of a handler that resumes more
// than once re-runs the rest of the handled computation, so such operations
// are counted and capped, and kept out of long `map`s.

struct Gen<'r> {
    rng: &'r mut Rng,
    p: Program,
    /// Operations of resuming-many-times handlers still allowed.
    multi_left: u32,
    /// Atoms still allowed.
    size_left: u32,
    features: Vec<String>,
}

/// What the code being generated is inside.
#[derive(Clone, Copy)]
struct Ctx {
    /// Each user ability's handler's factor (only meaningful in `row`).
    factor: [u32; 4],
    depth: u32,
    /// How many times the code runs per run of its function (a `map`).
    times: u32,
    /// Handlers around this code, statically.
    handlers: u32,
}

/// The factor of an ability whose operations may not be performed here: its
/// handler resumes more than once, and so does a handler inside it. An
/// operation of the outer one here would run once per resumption of the
/// inner one, each re-running the rest, so the work would compound.
const BLOCKED: u32 = u32::MAX;

/// `ability` is now handled by a handler of `kind`: its factor, and if that
/// handler resumes more than once, outer such abilities are blocked.
fn set_factor(factor: &mut [u32; 4], ability: u8, kind: Kind) {
    if kind.factor() >= 2 {
        for f in factor.iter_mut() {
            if *f >= 2 {
                *f = BLOCKED;
            }
        }
    }
    factor[ability as usize] = kind.factor();
}

impl Gen<'_> {
    fn feature(&mut self, name: impl Into<String>) {
        self.features.push(name.into());
    }

    fn program(rng: &mut Rng) -> (Program, Vec<String>) {
        let mut g = Gen {
            rng,
            p: Program {
                bodies: Vec::new(),
                handlers: Vec::new(),
                partial: None,
                arg: 0,
            },
            multi_left: 6,
            size_left: 40,
            features: Vec::new(),
        };
        let ctx = Ctx {
            factor: [0; 4],
            depth: 5,
            times: 1,
            handlers: 0,
        };
        g.body(IO, ctx);
        g.p.arg = g.rng.below(20);
        if g.rng.chance(1, 4) {
            g.p.partial = Some(1 + g.rng.below(4) as u32);
            g.feature("partial loop in main");
        }
        (g.p, g.features)
    }

    fn pure(&mut self, vars: u32, y: bool, depth: u32) -> Pure {
        let choice = self.rng.below(if depth == 0 { 3 } else { 5 });
        match choice {
            0 => Pure::Lit(self.rng.below(10)),
            1 | 2 if y && self.rng.chance(1, 2) => Pure::Y,
            1 | 2 => Pure::Var(self.rng.below(vars as u64) as u32),
            3 => Pure::Add(
                Box::new(self.pure(vars, y, depth - 1)),
                Box::new(self.pure(vars, y, depth - 1)),
            ),
            _ => Pure::Mul(
                Box::new(self.pure(vars, y, depth - 1)),
                Box::new(self.pure(vars, y, depth - 1)),
            ),
        }
    }

    /// A function of row `row`; its index.
    fn body(&mut self, row: Row, ctx: Ctx) -> usize {
        let id = self.p.bodies.len();
        self.p.bodies.push(Body {
            row,
            stmts: Vec::new(),
            result: Pure::Lit(0),
        });
        let count = 1 + self.rng.below(if ctx.depth > 0 { 4 } else { 2 });
        let mut stmts = Vec::new();
        let mut vars = 1;
        for _ in 0..count {
            if row & IO != 0 && self.rng.chance(1, 4) {
                let p = self.pure(vars, false, 1);
                stmts.push(Stmt::Print(p));
                self.feature("IO.print");
                if ctx
                    .factor
                    .iter()
                    .enumerate()
                    .any(|(a, f)| row & (1 << a) != 0 && *f >= 2)
                {
                    self.feature("IO under a handler resuming many times");
                }
                if ctx.handlers >= 2 {
                    self.feature("IO forwarded through 2+ handlers");
                }
            } else if row & FAIL != 0 && self.rng.chance(1, 4) {
                let p = self.pure(vars, false, 1);
                stmts.push(Stmt::Ensure(p, self.rng.below(100) as u32));
                self.feature("Fail.ensure");
            } else {
                let atom = self.atom(row, ctx, vars, false);
                stmts.push(Stmt::Let(vars, atom));
                vars += 1;
            }
        }
        // Every `let` reaches the result, so a wrong answer anywhere shows.
        let mut result = self.pure(vars, false, 1);
        for v in 1..vars {
            result = Pure::Add(
                Box::new(Pure::Mul(Box::new(result), Box::new(Pure::Lit(7)))),
                Box::new(Pure::Var(v)),
            );
        }
        self.p.bodies[id].stmts = stmts;
        self.p.bodies[id].result = result;
        id
    }

    /// Some of `row`'s abilities, each kept with probability 3/4.
    fn subrow(&mut self, row: Row) -> Row {
        let mut sub = 0;
        for bit in 0..6 {
            if row & (1 << bit) != 0 && self.rng.chance(3, 4) {
                sub |= 1 << bit;
            }
        }
        sub
    }

    fn may_perform(&self, a: u8, ctx: Ctx) -> bool {
        let f = ctx.factor[a as usize];
        f < 2 || (f != BLOCKED && ctx.times <= 3 && self.multi_left >= ctx.times)
    }

    fn atom(&mut self, row: Row, ctx: Ctx, vars: u32, y: bool) -> Atom {
        self.size_left = self.size_left.saturating_sub(1);
        let deep = ctx.depth > 0 && self.size_left > 0;
        let performable: Vec<u8> = (0..USER)
            .filter(|&a| row & (1 << a) != 0 && self.may_perform(a, ctx))
            .collect();
        // Weights: pure, op, call, handle, if, map, tower, widen.
        let weights = [
            2,
            if performable.is_empty() { 0 } else { 5 },
            if deep { 2 } else { 0 },
            if deep { 6 } else { 0 },
            1,
            if deep && ctx.times == 1 { 1 } else { 0 },
            if deep && ctx.times == 1 { 1 } else { 0 },
            if deep && ctx.times == 1 && row & FAIL != 0 {
                1
            } else {
                0
            },
        ];
        let total: u64 = weights.iter().sum();
        let mut roll = self.rng.below(total);
        let mut choice = 0;
        while roll >= weights[choice] {
            roll -= weights[choice];
            choice += 1;
        }
        let inner = Ctx {
            depth: ctx.depth.saturating_sub(1),
            ..ctx
        };
        match choice {
            0 => Atom::Pure(self.pure(vars, y, 2)),
            1 => {
                let a = self.rng.pick(&performable);
                if ctx.factor[a as usize] >= 2 {
                    self.multi_left -= ctx.times;
                }
                if self.rng.chance(1, 3) {
                    self.feature("second operation (peek)");
                    Atom::Peek(a)
                } else {
                    Atom::Op(a, self.pure(vars, y, 1))
                }
            }
            2 => {
                let sub = self.subrow(row);
                if sub != row {
                    self.feature("call with a smaller row (translate)");
                }
                let b = self.body(sub, inner);
                Atom::Call(b, self.pure(vars, y, 1))
            }
            3 => self.handle(row, inner, vars, y),
            4 => {
                let c = self.pure(vars, y, 1);
                let shallow = Ctx { depth: 0, ..inner };
                let a = self.atom(row, shallow, vars, y);
                let b = self.atom(row, shallow, vars, y);
                Atom::If(c, Box::new(a), Box::new(b))
            }
            5 => {
                let n = self.rng.pick(&[0, 1, 2, 3, 5, 8, 50, 200]);
                if n >= 50 && row & IO != 0 {
                    self.feature("IO across a map of 50+ elements");
                }
                if n >= 50 {
                    self.feature("map of 50+ elements");
                }
                let times = Ctx {
                    times: n.max(1),
                    depth: inner.depth.min(2),
                    ..inner
                };
                let a = self.atom(row, times, vars, true);
                Atom::Map(n, Box::new(a))
            }
            6 => self.tower(row, inner, vars, y),
            _ => {
                let depth = self.rng.pick(&[1, 2, 3, 10, 100]);
                self.feature(format!("translate depth {depth}"));
                let sub = self.subrow(row);
                let b = self.body(sub, inner);
                Atom::Widen {
                    depth,
                    row,
                    body: b,
                    arg: self.pure(vars, y, 1),
                }
            }
        }
    }

    fn user_kind(&mut self, closed: bool) -> Kind {
        let roll = self.rng.below(if closed { 12 } else { 9 });
        match roll {
            0..=2 => Kind::Direct(self.rng.pick(&[
                Direct::Discard,
                Direct::Tail,
                Direct::Tail,
                Direct::NonTail,
                Direct::Twice,
                Direct::TwiceLet,
                Direct::Many,
                Direct::Branch,
            ])),
            3..=5 => Kind::State(self.rng.pick(&[
                State::Jump,
                State::Jump,
                State::Get,
                State::Put,
                State::Eta,
                State::NonTail,
                State::Twice,
                State::Discard,
                State::Branch,
                State::Mixed,
            ])),
            6..=8 => Kind::Collect(self.rng.pick(&[
                Collect::Discard,
                Collect::Tail,
                Collect::Cons,
                Collect::Twice,
                Collect::Many,
                Collect::Snoc,
            ])),
            9 | 10 => {
                Kind::Stored(
                    self.rng
                        .pick(&[Stored::Suspend, Stored::Shifted, Stored::Sometimes]),
                )
            }
            _ => Kind::StoredState,
        }
    }

    fn new_handler(&mut self, ability: u8, kind: Kind, closed: bool) -> usize {
        let h = Handler {
            ability,
            kind,
            closed,
            concrete: None,
            clause_op: None,
            clause_print: false,
            peek: self.rng.below(3) as u8,
            ret: self.rng.below(3) as u8,
            c: self.rng.below(10),
            init: self.rng.below(10),
            explore: 1 + self.rng.below(4) as u32,
        };
        self.feature(kind.name());
        if ability < USER {
            self.feature(if closed {
                "closed-row handler"
            } else {
                "open-row handler"
            });
            if let Kind::State(State::Jump) = kind {
                self.feature(if closed {
                    "state/Jump closed (fused)"
                } else {
                    "state/Jump open"
                });
            }
            self.feature(match kind.factor() {
                0 => "resumes 0 times",
                1 => "resumes once",
                2 => "resumes twice",
                _ => "resumes 0-3 times",
            });
        }
        self.p.handlers.push(h);
        self.p.handlers.len() - 1
    }

    fn handle(&mut self, row: Row, ctx: Ctx, vars: u32, y: bool) -> Atom {
        let free: Vec<u8> = (0..USER).filter(|a| row & (1 << a) == 0).collect();
        let mut options: Vec<u8> = free;
        options.push(4);
        let ability = self.rng.pick(&options);
        let deeper = Ctx {
            handlers: ctx.handlers + 1,
            ..ctx
        };
        if deeper.handlers >= 2 {
            self.feature("handler inside a handler");
        }
        if deeper.handlers >= 3 {
            self.feature("handlers nested 3+ deep");
        }
        if ability == 4 {
            let kind = if row & FAIL != 0 {
                Kind::FailContext
            } else {
                self.rng.pick(&[
                    Kind::FailOrElse,
                    Kind::FailToNat,
                    Kind::FailToOption,
                    Kind::FailCustom,
                ])
            };
            let closed = kind == Kind::FailCustom && self.rng.chance(1, 3);
            let h = self.new_handler(4, kind, closed);
            let body_row = if closed {
                FAIL
            } else {
                self.subrow(row) | FAIL
            };
            if body_row & IO != 0 {
                self.feature("IO forwarded through a Fail handler");
            }
            let factor = if closed { [0; 4] } else { ctx.factor };
            let b = self.body(body_row, Ctx { factor, ..deeper });
            return Atom::Handle(h, b, self.pure(vars, y, 1));
        }
        let closed = self.rng.chance(1, 3);
        let kind = self.user_kind(closed);
        let h = self.new_handler(ability, kind, closed);
        let bit = 1 << ability;
        let (body_row, mut factor) = if closed {
            (bit, [0; 4])
        } else {
            let sub = self.subrow(row);
            if row == 0 {
                self.feature("open-row handler at the empty row");
            }
            (sub | bit, ctx.factor)
        };
        // Some open ones are written for their concrete row instead, and
        // may perform that row's operations in their clauses.
        if !closed && matches!(kind, Kind::Direct(_) | Kind::Collect(_)) && self.rng.chance(1, 3) {
            let outer = body_row & !bit;
            self.p.handlers[h].concrete = Some(outer);
            self.feature("concrete-row handler");
            let calm: Vec<u8> = (0..USER)
                .filter(|&b| outer & (1 << b) != 0 && ctx.factor[b as usize] < 2)
                .collect();
            if !calm.is_empty() && self.rng.chance(2, 3) {
                self.p.handlers[h].clause_op = Some(self.rng.pick(&calm));
                self.feature("clause performs an outer operation");
            }
            if outer & IO != 0 && self.rng.chance(1, 2) {
                self.p.handlers[h].clause_print = true;
                self.feature("clause prints");
            }
        }
        set_factor(&mut factor, ability, kind);
        let b = self.body(body_row, Ctx { factor, ..deeper });
        Atom::Handle(h, b, self.pure(vars, y, 1))
    }

    fn tower(&mut self, row: Row, ctx: Ctx, vars: u32, y: bool) -> Atom {
        let free: Vec<u8> = (0..USER).filter(|a| row & (1 << a) == 0).collect();
        if free.is_empty() {
            return Atom::Pure(self.pure(vars, y, 1));
        }
        let ability = self.rng.pick(&free);
        let kind = Kind::Direct(self.rng.pick(&[
            Direct::Tail,
            Direct::NonTail,
            Direct::Discard,
            Direct::Branch,
            Direct::Twice,
        ]));
        let h = self.new_handler(ability, kind, false);
        let depth = self.rng.pick(&[1, 2, 3, 10, 100]);
        self.feature(format!("handlers nested {depth} deep (tower)"));
        let tower_row = row | (1 << ability);
        let body_row = self.subrow(row)
            | if self.rng.chance(1, 2) {
                1 << ability
            } else {
                0
            };
        if body_row & (1 << ability) != 0 {
            self.feature("tower: innermost of many same handlers handles");
        }
        let mut factor = ctx.factor;
        set_factor(&mut factor, ability, kind);
        let b = self.body(
            body_row,
            Ctx {
                factor,
                handlers: ctx.handlers + depth,
                ..ctx
            },
        );
        Atom::Tower {
            handler: h,
            depth,
            row: tower_row,
            body: b,
            arg: self.pure(vars, y, 1),
        }
    }
}

// ---------------------------------------------------------------------------
// Printing a program as Stitchwort.

const PRELUDE: &str = "import Std (Fail, IO, List, Nat, Option, Result, Text)

ability Ab1 where
  call1: Nat -> {Ab1} Nat
  peek1: () -> {Ab1} Nat

ability Ab2 where
  call2: Nat -> {Ab2} Nat
  peek2: () -> {Ab2} Nat

ability Ab3 where
  call3: Nat -> {Ab3} Nat
  peek3: () -> {Ab3} Nat

ability Ab4 where
  call4: Nat -> {Ab4} Nat
  peek4: () -> {Ab4} Nat

type Paused =
  | Finished (total: Nat)
  | Suspended (offered: Nat) (resume: Nat -> Paused)

-- Resumes a stored resumption in two branches, to `depth` levels.
def explore: Nat -> Paused -> Nat
  | 0, p => 0
  | Succ depth, Finished total => total
  | Succ depth, Suspended v resume => (explore depth (resume (v + 1)) * 31 + explore depth (resume v)) % 1000003

def resumeSum (k: Nat -> {e} Nat): Nat -> {e} Nat
  | 0 => 0
  | Succ n =>
    let before := resumeSum k n
    let after := k n
    (before * 7 + after) % 1000003

def resumeList (k: Nat -> {e} List Nat): Nat -> {e} List Nat
  | 0 => []
  | Succ n =>
    let before := resumeList k n
    let after := k n
    before ++ after

def digest (xs: List Nat): Nat := List.foldLeft (acc x => (acc * 31 + x) % 1000003) 7 xs

def failToNat (prog: () -> {Fail | e} Nat): {e} Nat :=
  match Fail.toResult prog with
    | Ok v => v
    | Err m => 1000 + Text.length m

def collatz: Nat -> {Partial} Nat
  | 1 => 0
  | n => 1 + collatz (if n % 2 == 0 then n / 2 else 3 * n + 1)
";

fn pure_text(p: &Pure) -> String {
    match p {
        Pure::Lit(n) => n.to_string(),
        Pure::Var(v) => format!("v{v}"),
        Pure::Y => "y".into(),
        Pure::Add(a, b) => format!("({} + {})", pure_text(a), pure_text(b)),
        Pure::Mul(a, b) => format!("({} * {} % {M})", pure_text(a), pure_text(b)),
    }
}

struct Printer<'a> {
    p: &'a Program,
    k: usize,
    out: String,
    done_bodies: Vec<bool>,
}

impl Printer<'_> {
    fn body_name(&self, b: usize) -> String {
        format!("p{}b{b}", self.k)
    }
    fn handler_name(&self, h: usize) -> String {
        format!("p{}h{h}", self.k)
    }

    /// The call of handler `h` around the thunk `lam`.
    fn handle_call(&self, h: usize, lam: &str) -> String {
        let hd = &self.p.handlers[h];
        let name = self.handler_name(h);
        match hd.kind {
            Kind::Direct(_) | Kind::Collect(_) | Kind::FailCustom => format!("{name} ({lam})"),
            Kind::State(_) if hd.closed => format!("{name} ({lam}) {}", hd.init),
            Kind::State(_) => format!("{name} {} ({lam})", hd.init),
            Kind::Stored(_) => format!("explore {} ({name} ({lam}))", hd.explore),
            Kind::StoredState => format!("explore {} ({name} ({lam}) {})", hd.explore, hd.init),
            Kind::FailOrElse => format!("Fail.orElse {} ({lam})", hd.c),
            Kind::FailToNat => format!("failToNat ({lam})"),
            Kind::FailToOption => format!("Option.getOrElse {} (Fail.toOption ({lam}))", hd.c),
            Kind::FailContext => format!("Fail.context \"c{h}\" ({lam})"),
        }
    }

    fn atom_text(&mut self, a: &Atom) -> String {
        match a {
            Atom::Pure(p) => pure_text(p),
            Atom::Op(ab, p) => format!("Ab{0}.call{0} {1}", ab + 1, pure_text(p)),
            Atom::Peek(ab) => format!("Ab{0}.peek{0}()", ab + 1),
            Atom::Call(b, p) => {
                self.body(*b);
                format!("{} {}", self.body_name(*b), pure_text(p))
            }
            Atom::Handle(h, b, p) => {
                self.body(*b);
                self.handler(*h);
                let lam = format!("() => {} {}", self.body_name(*b), pure_text(p));
                self.handle_call(*h, &lam)
            }
            Atom::If(c, a, b) => {
                let (a, b) = (self.atom_text(a), self.atom_text(b));
                format!("if {} % 2 == 0 then {a} else {b}", pure_text(c))
            }
            Atom::Map(n, a) => {
                let a = self.atom_text(a);
                format!("digest (List.map (y => {a}) (List.range {n}))")
            }
            Atom::Tower {
                handler,
                depth,
                row,
                body,
                arg,
            } => {
                self.body(*body);
                self.handler(*handler);
                let tower = format!("p{}t{body}", self.k);
                let level = self.handle_call(*handler, &format!("() => {tower} d prog"));
                let ty = comp(*row, "Nat");
                writeln!(
                    self.out,
                    "def {tower}: Nat -> (() -> {ty}) -> {ty}\n  | 0, prog => prog()\n  | Succ d, prog => {level}\n"
                )
                .unwrap();
                let lam = format!(
                    "() => {tower} {depth} (() => {} {})",
                    self.body_name(*body),
                    pure_text(arg)
                );
                self.handle_call(*handler, &lam)
            }
            Atom::Widen {
                depth,
                row,
                body,
                arg,
            } => {
                self.body(*body);
                let widen = format!("p{}w{body}", self.k);
                let inner = comp(self.p.bodies[*body].row, "Nat");
                writeln!(
                    self.out,
                    "def {widen}: Nat -> (() -> {inner}) -> {}\n  | 0, prog => prog()\n  | Succ d, prog =>\n    match Fail.toResult (() => {widen} d prog) with\n      | Ok x => x\n      | Err m => Fail.fail m\n",
                    comp(*row, "Nat")
                )
                .unwrap();
                format!(
                    "{widen} {depth} (() => {} {})",
                    self.body_name(*body),
                    pure_text(arg)
                )
            }
        }
    }

    fn body(&mut self, b: usize) {
        if self.done_bodies[b] {
            return;
        }
        self.done_bodies[b] = true;
        let body = &self.p.bodies[b];
        let mut text = format!(
            "def {} (v0: Nat): {} :=\n",
            self.body_name(b),
            comp(body.row, "Nat")
        );
        for s in &body.stmts {
            match s {
                Stmt::Let(v, a) => {
                    let a = self.atom_text(a);
                    writeln!(text, "  let v{v} := {a}").unwrap();
                }
                Stmt::Print(p) => {
                    writeln!(text, "  IO.print \"p{} ${{{}}}\"", self.k, pure_text(p)).unwrap();
                }
                Stmt::Ensure(p, m) => {
                    writeln!(text, "  Fail.ensure ({} % 5 != 0) \"m{m}\"", pure_text(p)).unwrap();
                }
            }
        }
        writeln!(text, "  {}\n", pure_text(&body.result)).unwrap();
        self.out.push_str(&text);
    }

    fn handler(&mut self, h: usize) {
        let hd = self.p.handlers[h].clone();
        let name = self.handler_name(h);
        let effectful = hd.clause_op.is_some() || hd.clause_print;
        let (ab, op, bit) = if hd.ability == 4 {
            ("Fail".to_string(), "Fail.stop m, k".to_string(), FAIL)
        } else {
            (
                format!("Ab{}", hd.ability + 1),
                format!(
                    "Ab{0}.call{0} {1}, k",
                    hd.ability + 1,
                    if effectful { "u" } else { "v" }
                ),
                1 << hd.ability,
            )
        };
        let c = hd.c;
        let prog = |e: bool| match hd.concrete {
            Some(outer) => format!("(prog: () -> {})", comp(outer | bit, "Nat")),
            None if hd.closed || !e => format!("(prog: () -> {{{ab}}} Nat)"),
            None => format!("(prog: () -> {{{ab} | e}} Nat)"),
        };
        let res = |t: &str| match hd.concrete {
            Some(outer) => comp(outer, t),
            None if hd.closed => t.to_string(),
            None => format!("{{e}} {t}"),
        };
        let direct_ret = match hd.ret {
            0 => "x".to_string(),
            1 => format!("x + {c}"),
            _ => format!("x * {c} % {M}"),
        };
        let outer_op = |arg: &str| {
            hd.clause_op
                .map(|b| format!("Ab{0}.call{0} ({arg})", b + 1))
        };
        // What an effectful clause does first (it binds `v`), then `clause`.
        let block = |clause: String| {
            if !effectful {
                return clause;
            }
            let mut text = String::from("\n");
            if hd.clause_print {
                writeln!(text, "      IO.print \"p{} h{h} ${{u}}\"", self.k).unwrap();
            }
            let v = outer_op("u").unwrap_or_else(|| "u".into());
            writeln!(text, "      let v := {v}").unwrap();
            match clause.strip_prefix('\n') {
                Some(lines) => text.push_str(lines),
                None => write!(text, "      {clause}").unwrap(),
            }
            text
        };
        let peek_name = if hd.ability < USER {
            format!("Ab{0}.peek{0} w, k", hd.ability + 1)
        } else {
            String::new()
        };
        let peek = |clauses: [String; 3]| {
            format!("\n    | {peek_name} => {}", clauses[hd.peek as usize % 3])
        };
        let text = match hd.kind {
            Kind::Direct(clause) => {
                let clause = match clause {
                    Direct::Discard => format!("v + {c}"),
                    Direct::Tail => format!("k (v + {c})"),
                    Direct::NonTail => format!("(k (v + {c}) + v) % {M}"),
                    Direct::Twice => format!("(k v * 3 + k (v + {c})) % {M}"),
                    Direct::TwiceLet => format!(
                        "\n      let second := k (v + {c})\n      let first := k v\n      (first * 5 + second) % {M}"
                    ),
                    Direct::Many => "resumeSum k (v % 4)".into(),
                    Direct::Branch => format!("if v % 2 == 0 then k v else v + {c}"),
                };
                let clause = block(clause);
                let ret = outer_op(&direct_ret).unwrap_or(direct_ret);
                let peek = peek([
                    format!("k {c}"),
                    format!("(k {c} + 1) % {M}"),
                    format!("{c}"),
                ]);
                format!(
                    "def {name} {}: {} :=\n  handle prog() with\n    | return x => {ret}\n    | {op} => {clause}{peek}\n",
                    prog(true),
                    res("Nat")
                )
            }
            Kind::State(clause) => {
                let ret = if hd.ret == 0 {
                    "s => x + s".to_string()
                } else {
                    format!("s => (x * 3 + s) % {M}")
                };
                let clause = match clause {
                    State::Jump => "s => k (v + s) (s + 1)".to_string(),
                    State::Get => "s => k s s".into(),
                    State::Put => "s => k 0 (v + s)".into(),
                    State::Eta => "k v".into(),
                    State::NonTail => format!("s => (k v (s + 1) + s) % {M}"),
                    State::Twice => format!("s => (k v s + k s (s + v)) % {M}"),
                    State::Discard => "s => s + v".into(),
                    State::Branch => "s => if s % 2 == 0 then k v (s + 1) else k s s".into(),
                    State::Mixed => {
                        format!("s => if v % 2 == 0 then (k v s + 1) % {M} else k s (s + 1)")
                    }
                };
                let peek = peek([
                    "s => k s s".into(),
                    format!("s => (k s s + 1) % {M}"),
                    "s => s".into(),
                ]);
                if hd.closed {
                    format!(
                        "def {name} {}: Nat -> Nat :=\n  handle prog() with\n    | return x => {ret}\n    | {op} => {clause}{peek}\n",
                        prog(false)
                    )
                } else {
                    let peek = peek.replace("\n    | ", "\n      | ");
                    format!(
                        "def {name} (init: Nat) {}: {{e}} Nat :=\n  let run: Nat -> {{e}} Nat :=\n    handle prog() with\n      | return x => {ret}\n      | {op} => {clause}{peek}\n  run init\n",
                        prog(true)
                    )
                }
            }
            Kind::Collect(clause) => {
                let ret = if hd.ret == 0 {
                    "[x]".to_string()
                } else {
                    format!("[x, {c}]")
                };
                let clause = match clause {
                    Collect::Discard => "[v]".to_string(),
                    Collect::Tail => "k v".into(),
                    Collect::Cons => "Cons v (k (v + 1))".into(),
                    Collect::Twice => format!("k v ++ k (v + {c})"),
                    Collect::Many => "resumeList k (v % 4)".into(),
                    Collect::Snoc => "k v ++ [v]".into(),
                };
                let clause = block(clause);
                let ret = match outer_op("x") {
                    Some(op) => format!("[{op}]"),
                    None => ret,
                };
                let peek = peek([
                    format!("k {c}"),
                    format!("k {c} ++ [{c}]"),
                    format!("[{c}]"),
                ]);
                format!(
                    "def {name}all {}: {} :=\n  handle prog() with\n    | return x => {ret}\n    | {op} => {clause}{peek}\n\ndef {name} {}: {} := digest ({name}all prog)\n",
                    prog(true),
                    res("List Nat"),
                    prog(true),
                    res("Nat")
                )
            }
            Kind::Stored(clause) => {
                let clause = match clause {
                    Stored::Suspend => "Suspended v (a => k a)",
                    Stored::Shifted => "Suspended v (a => k (a + v))",
                    Stored::Sometimes => "if v % 3 == 0 then k (v + 1) else Suspended v (a => k a)",
                };
                let peek = peek([
                    format!("k {c}"),
                    format!("Suspended {c} (a => k a)"),
                    format!("Finished {c}"),
                ]);
                format!(
                    "def {name} {}: Paused :=\n  handle prog() with\n    | return x => Finished ({direct_ret})\n    | {op} => {clause}{peek}\n",
                    prog(false)
                )
            }
            Kind::StoredState => {
                let peek = peek([
                    "s => k s (s + 1)".into(),
                    "s => Suspended s (a => k a s)".into(),
                    "s => Finished s".into(),
                ]);
                format!(
                    "def {name} {}: Nat -> Paused :=\n  handle prog() with\n    | return x => s => Finished ((x * 100 + s) % {M})\n    | {op} => s => Suspended s (a => k (v + a) (s + 1)){peek}\n",
                    prog(false)
                )
            }
            Kind::FailCustom => format!(
                "def {name} {}: {} :=\n  handle prog() with\n    | return x => {direct_ret}\n    | {op} => Text.length m + {c}\n",
                prog(true),
                res("Nat")
            ),
            Kind::FailOrElse | Kind::FailToNat | Kind::FailToOption | Kind::FailContext => {
                return;
            }
        };
        self.out.push_str(&text.replace("=> \n", "=>\n"));
        self.out.push('\n');
    }
}

/// The definitions of program `k`, and the line of `main` that runs it.
fn render_program(p: &Program, k: usize) -> (String, String) {
    let mut printer = Printer {
        p,
        k,
        out: String::new(),
        done_bodies: vec![false; p.bodies.len()],
    };
    printer.body(0);
    let mut out = printer.out;
    let call = match p.partial {
        None => format!("p{k}b0 {}", p.arg),
        Some(n) => {
            writeln!(
                out,
                "def p{k}loop: Nat -> {{IO, Partial}} Nat\n  | 0 => 0\n  | n =>\n    let a := p{k}b0 (n + {})\n    let b := collatz (n % 8 + 1)\n    (a + b + p{k}loop (n - 1)) % {M}\n",
                p.arg
            )
            .unwrap();
            format!("p{k}loop {n}")
        }
    };
    (out, format!("  IO.print \"p{k} = ${{{call}}}\"\n"))
}

/// A module running `programs`, numbered from `first`.
fn module(programs: &[(usize, &Program)]) -> String {
    let mut out = String::from(PRELUDE);
    out.push('\n');
    let mut main = String::new();
    let partial = programs.iter().any(|(_, p)| p.partial.is_some());
    for (k, p) in programs {
        let (defs, line) = render_program(p, *k);
        out.push_str(&defs);
        main.push_str(&line);
    }
    writeln!(
        out,
        "def main(): {} () :=\n{main}",
        if partial { "{IO, Partial}" } else { "{IO}" }
    )
    .unwrap();
    out
}

// ---------------------------------------------------------------------------
// Running a module on the three backends.

#[derive(Clone, Debug, PartialEq, Eq)]
struct Run {
    stdout: String,
    /// `ok`, `failed: msg`, `resource` or an error.
    end: String,
}

enum Ran {
    Three([Run; 3]),
    /// It didn't check: the diagnostics.
    Rejected(String),
}

const BACKENDS: [&str; 3] = ["reference", "native", "js"];

fn end_of(result: Result<(), RunError>) -> String {
    match result {
        Ok(()) => "ok".into(),
        Err(RunError::Failed(m)) => format!("failed: {m}"),
        Err(RunError::Resource(_)) => "resource".into(),
        Err(e) => format!("error: {e}"),
    }
}

static RUNS: AtomicUsize = AtomicUsize::new(0);
/// Only the first disagreement found is shrunk: the others are reported by
/// seed, which is enough to rerun them.
static SHRINKING: AtomicBool = AtomicBool::new(false);

/// Runs a `run --js` program under Node with `input`.
fn run_js(program: &stitchwort_js::run::Program, input: &str) -> Run {
    use stitchwort_js::run::{EXIT_FAIL, EXIT_RESOURCE};
    let dir: PathBuf = std::env::temp_dir().join(format!(
        "stitchwort-effect-diff-{}-{}",
        std::process::id(),
        RUNS.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).expect("temp dir");
    std::fs::write(dir.join("program.mjs"), &program.module).expect("write program");
    std::fs::write(dir.join("run.mjs"), &program.launcher).expect("write launcher");
    let input_file = dir.join("input.txt");
    std::fs::write(&input_file, input).expect("write input");
    let error_file = dir.join("error.txt");
    let output = Command::new("node")
        .arg(dir.join("run.mjs"))
        .arg(&error_file)
        .stdin(std::fs::File::open(&input_file).expect("open input"))
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .expect("run node (in the nix dev shell)");
    let message = std::fs::read_to_string(&error_file).unwrap_or_default();
    let end = match output.status.code() {
        Some(0) => "ok".into(),
        Some(EXIT_FAIL) => format!("failed: {message}"),
        Some(EXIT_RESOURCE) => "resource".into(),
        code => format!(
            "error: exit {code:?}: {message} {}",
            String::from_utf8_lossy(&output.stderr)
        ),
    };
    let _ = std::fs::remove_dir_all(&dir);
    Run {
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        end,
    }
}

fn run_three(source: &str) -> Ran {
    let mut session = Session::for_stack(STACK);
    if let Err(diagnostics) = session.load("generated.sw", source) {
        let shown: Vec<String> = diagnostics
            .iter()
            .map(|d| stitchwort_cli::render::render(&session.sources, d, false))
            .collect();
        return Ran::Rejected(shown.join("\n"));
    }
    let main = match session.main() {
        Ok(main) => main,
        Err(d) => {
            return Ran::Rejected(stitchwort_cli::render::render(&session.sources, &d, false));
        }
    };
    let mut reference = Vec::new();
    let reference_end = end_of(session.run_main(&main, &mut &b""[..], &mut reference));
    let mut native = Vec::new();
    let native_end = end_of(session.run_main_fast(&main, &mut &b""[..], &mut native));
    let js = match session.extract_program(&main) {
        Ok(program) => run_js(&program, ""),
        Err(d) => Run {
            stdout: String::new(),
            end: format!("error: extract: {}", d.message),
        },
    };
    Ran::Three([
        Run {
            stdout: String::from_utf8_lossy(&reference).into_owned(),
            end: reference_end,
        },
        Run {
            stdout: String::from_utf8_lossy(&native).into_owned(),
            end: native_end,
        },
        js,
    ])
}

fn inconclusive(runs: &[Run; 3]) -> bool {
    runs.iter().any(|r| r.end == "resource")
}

fn agree(runs: &[Run; 3]) -> bool {
    runs[0] == runs[1] && runs[1] == runs[2]
}

/// The lines program `k` printed.
fn lines_of(stdout: &str, k: usize) -> Vec<&str> {
    let tag = format!("p{k} ");
    stdout.lines().filter(|l| l.starts_with(&tag)).collect()
}

fn show_runs(runs: &[Run; 3]) -> String {
    let mut out = String::new();
    for (name, run) in BACKENDS.iter().zip(runs) {
        writeln!(out, "--- {name}: {} ---\n{}", run.end, run.stdout).unwrap();
    }
    out
}

// ---------------------------------------------------------------------------
// Shrinking.

fn subst(p: &mut Pure, var: u32) {
    match p {
        Pure::Var(v) if *v == var => *p = Pure::Lit(1),
        Pure::Add(a, b) | Pure::Mul(a, b) => {
            subst(a, var);
            subst(b, var);
        }
        _ => {}
    }
}

fn subst_atom(a: &mut Atom, var: u32) {
    match a {
        Atom::Pure(p) | Atom::Op(_, p) | Atom::Call(_, p) | Atom::Handle(_, _, p) => subst(p, var),
        Atom::Peek(_) => {}
        Atom::Tower { arg, .. } | Atom::Widen { arg, .. } => subst(arg, var),
        Atom::If(c, x, y) => {
            subst(c, var);
            subst_atom(x, var);
            subst_atom(y, var);
        }
        Atom::Map(_, x) => subst_atom(x, var),
    }
}

/// Simpler versions of atom `a`.
fn atom_shrinks(a: &Atom) -> Vec<Atom> {
    let one = Atom::Pure(Pure::Lit(1));
    match a {
        Atom::Pure(Pure::Lit(_)) => vec![],
        Atom::Pure(_) => vec![one],
        Atom::Op(..) | Atom::Peek(_) => vec![one],
        Atom::Call(_, Pure::Lit(_)) => vec![one],
        Atom::Call(b, _) => vec![one, Atom::Call(*b, Pure::Lit(1))],
        Atom::Handle(_, b, p) => vec![one, Atom::Call(*b, p.clone())],
        Atom::If(_, x, y) => vec![one, (**x).clone(), (**y).clone()],
        Atom::Map(n, x) => {
            let mut v = vec![one, (**x).clone()];
            if *n > 1 {
                v.push(Atom::Map(1, x.clone()));
            }
            v.extend(
                atom_shrinks(x)
                    .into_iter()
                    .map(|x| Atom::Map(*n, Box::new(x))),
            );
            v
        }
        Atom::Tower {
            handler,
            depth,
            row,
            body,
            arg,
        } => {
            let mut v = vec![one, Atom::Call(*body, arg.clone())];
            if *depth > 1 {
                v.push(Atom::Tower {
                    handler: *handler,
                    depth: 1,
                    row: *row,
                    body: *body,
                    arg: arg.clone(),
                });
            }
            v
        }
        Atom::Widen {
            depth,
            row,
            body,
            arg,
        } => {
            let mut v = vec![one, Atom::Call(*body, arg.clone())];
            if *depth > 1 {
                v.push(Atom::Widen {
                    depth: 1,
                    row: *row,
                    body: *body,
                    arg: arg.clone(),
                });
            }
            v
        }
    }
}

/// Simpler versions of `p`, simplest first.
fn shrinks(p: &Program) -> Vec<Program> {
    let mut out = Vec::new();
    if p.partial.is_some() {
        out.push(Program {
            partial: None,
            ..p.clone()
        });
        if p.partial != Some(1) {
            out.push(Program {
                partial: Some(1),
                ..p.clone()
            });
        }
    }
    for (b, body) in p.bodies.iter().enumerate() {
        for (i, stmt) in body.stmts.iter().enumerate() {
            // Without the statement.
            let mut q = p.clone();
            let removed = q.bodies[b].stmts.remove(i);
            if let Stmt::Let(var, _) = removed {
                for s in &mut q.bodies[b].stmts {
                    match s {
                        Stmt::Let(_, a) => subst_atom(a, var),
                        Stmt::Print(x) | Stmt::Ensure(x, _) => subst(x, var),
                    }
                }
                subst(&mut q.bodies[b].result, var);
            }
            out.push(q);
            // With a simpler atom.
            if let Stmt::Let(var, a) = stmt {
                for a in atom_shrinks(a) {
                    let mut q = p.clone();
                    q.bodies[b].stmts[i] = Stmt::Let(*var, a);
                    out.push(q);
                }
            }
        }
        if !matches!(body.result, Pure::Lit(_)) {
            let mut q = p.clone();
            q.bodies[b].result = Pure::Lit(0);
            out.push(q);
        }
    }
    for (h, hd) in p.handlers.iter().enumerate() {
        let simpler = match hd.kind {
            Kind::Direct(Direct::Tail)
            | Kind::State(State::Jump)
            | Kind::Collect(Collect::Tail) => None,
            Kind::Direct(_) => Some(Kind::Direct(Direct::Tail)),
            Kind::State(_) => Some(Kind::State(State::Jump)),
            Kind::Collect(_) => Some(Kind::Collect(Collect::Tail)),
            Kind::Stored(Stored::Shifted) => Some(Kind::Stored(Stored::Suspend)),
            _ => None,
        };
        if let Some(kind) = simpler {
            let mut q = p.clone();
            q.handlers[h].kind = kind;
            out.push(q);
        }
        if hd.ret != 0 || hd.c != 0 || hd.explore > 1 {
            let mut q = p.clone();
            q.handlers[h].ret = 0;
            q.handlers[h].c = 0;
            q.handlers[h].explore = 1;
            out.push(q);
        }
        if hd.peek != 0 {
            let mut q = p.clone();
            q.handlers[h].peek = 0;
            out.push(q);
        }
        if hd.clause_op.is_some() || hd.clause_print {
            let mut q = p.clone();
            q.handlers[h].clause_op = None;
            q.handlers[h].clause_print = false;
            out.push(q);
        }
        if hd.concrete.is_some() && hd.clause_op.is_none() && !hd.clause_print {
            let mut q = p.clone();
            q.handlers[h].concrete = None;
            out.push(q);
        }
    }
    out
}

/// Program `p` alone, if it still disagrees: the runs.
fn disagrees(p: &Program) -> Option<[Run; 3]> {
    match run_three(&module(&[(0, p)])) {
        Ran::Three(runs) if !inconclusive(&runs) && !agree(&runs) => Some(runs),
        _ => None,
    }
}

/// The smallest program found that still disagrees.
fn shrink(mut p: Program, mut runs: [Run; 3]) -> (Program, [Run; 3]) {
    let start = Instant::now();
    'outer: loop {
        for q in shrinks(&p) {
            if start.elapsed().as_secs() > 120 {
                break 'outer;
            }
            if let Some(r) = disagrees(&q) {
                p = q;
                runs = r;
                continue 'outer;
            }
        }
        break;
    }
    (p, runs)
}

// ---------------------------------------------------------------------------
// The test.

struct BatchResult {
    programs: usize,
    features: Vec<String>,
    inconclusive: usize,
    failure: Option<String>,
}

fn batch(seed: u64) -> BatchResult {
    let mut rng = Rng(seed);
    let mut programs = Vec::new();
    let mut features = Vec::new();
    for _ in 0..PER_BATCH {
        let (p, f) = Gen::program(&mut rng);
        programs.push(p);
        features.extend(f);
    }
    let numbered: Vec<(usize, &Program)> = programs.iter().enumerate().collect();
    let source = module(&numbered);
    // `STITCHWORT_EFFECT_FUZZ_DUMP=dir` keeps every module, to read or run.
    if let Ok(dir) = std::env::var("STITCHWORT_EFFECT_FUZZ_DUMP") {
        let _ = std::fs::create_dir_all(&dir);
        let _ = std::fs::write(PathBuf::from(dir).join(format!("seed{seed}.sw")), &source);
    }
    let runs = match run_three(&source) {
        Ran::Rejected(errors) => {
            return BatchResult {
                programs: 0,
                features,
                inconclusive: 0,
                failure: Some(format!(
                    "seed {seed}: a generated program doesn't check (a generator bug):\n{errors}\n--- source ---\n{source}"
                )),
            };
        }
        Ran::Three(runs) => runs,
    };
    if inconclusive(&runs) {
        return BatchResult {
            programs: 0,
            features,
            inconclusive: PER_BATCH,
            failure: None,
        };
    }
    if agree(&runs) {
        return BatchResult {
            programs: PER_BATCH,
            features,
            inconclusive: 0,
            failure: None,
        };
    }
    // Which program: the first whose lines differ.
    let k = (0..PER_BATCH)
        .find(|&k| {
            let lines: Vec<_> = runs.iter().map(|r| lines_of(&r.stdout, k)).collect();
            lines[0] != lines[1] || lines[1] != lines[2]
        })
        .unwrap_or(PER_BATCH - 1);
    let first = !SHRINKING.swap(true, Ordering::Relaxed);
    let failure = match disagrees(&programs[k]) {
        Some(alone) if first => {
            let (small, small_runs) = shrink(programs[k].clone(), alone);
            let small_source = module(&[(0, &small)]);
            let path =
                std::env::temp_dir().join(format!("stitchwort-effect-diff-seed{seed}-p{k}.sw"));
            let _ = std::fs::write(&path, &small_source);
            format!(
                "seed {seed}, program {k}: the backends disagree (rerun with \
                 STITCHWORT_EFFECT_FUZZ_SEED={seed} STITCHWORT_EFFECT_FUZZ_BATCHES=1).\n\
                 Smallest program found (also in {}):\n{small_source}\n{}",
                path.display(),
                show_runs(&small_runs)
            )
        }
        Some(_) => format!(
            "seed {seed}, program {k}: the backends disagree (rerun with \
             STITCHWORT_EFFECT_FUZZ_SEED={seed} STITCHWORT_EFFECT_FUZZ_BATCHES=1 to shrink it)"
        ),
        None => format!(
            "seed {seed}: the backends disagree on the batch, but not on program {k} alone \
             (rerun with STITCHWORT_EFFECT_FUZZ_SEED={seed} STITCHWORT_EFFECT_FUZZ_BATCHES=1).\n\
             --- source ---\n{source}\n{}",
            show_runs(&runs)
        ),
    };
    BatchResult {
        programs: 0,
        features,
        inconclusive: 0,
        failure: Some(failure),
    }
}

fn env_u64(name: &str) -> Option<u64> {
    std::env::var(name).ok().and_then(|v| v.trim().parse().ok())
}

/// The shapes every default run must include, so that a change to the
/// generator that loses one is noticed.
const REQUIRED: &[&str] = &[
    "direct/Discard",
    "direct/Tail",
    "direct/NonTail",
    "direct/Twice",
    "direct/Many",
    "direct/Branch",
    "state/Jump closed (fused)",
    "state/Jump open",
    "state/Eta",
    "state/NonTail",
    "state/Twice",
    "state/Discard",
    "collect/Cons",
    "collect/Twice",
    "collect/Many",
    "stored/Suspend",
    "stored/Sometimes",
    "stored-state",
    "fail/orElse",
    "fail/toResult",
    "fail/toOption",
    "fail/custom",
    "fail/context (re-raise)",
    "closed-row handler",
    "open-row handler",
    "open-row handler at the empty row",
    "resumes 0 times",
    "resumes once",
    "resumes twice",
    "resumes 0-3 times",
    "handler inside a handler",
    "handlers nested 3+ deep",
    "handlers nested 10 deep (tower)",
    "handlers nested 100 deep (tower)",
    "tower: innermost of many same handlers handles",
    "translate depth 10",
    "translate depth 100",
    "call with a smaller row (translate)",
    "IO.print",
    "IO forwarded through 2+ handlers",
    "IO forwarded through a Fail handler",
    "IO under a handler resuming many times",
    "IO across a map of 50+ elements",
    "Fail.ensure",
    "second operation (peek)",
    "concrete-row handler",
    "clause performs an outer operation",
    "clause prints",
    "partial loop in main",
];

#[test]
fn generated_effect_programs_agree_on_all_three_backends() {
    let batches = env_u64("STITCHWORT_EFFECT_FUZZ_BATCHES").unwrap_or(DEFAULT_BATCHES);
    let first = env_u64("STITCHWORT_EFFECT_FUZZ_SEED").unwrap_or(1);
    let seeds: Vec<u64> = (first..first + batches).collect();
    let start = Instant::now();
    let results = par_map(STACK, &seeds, |&seed| batch(seed));
    let elapsed = start.elapsed();
    let mut features: BTreeMap<String, usize> = BTreeMap::new();
    let mut ran = 0;
    let mut skipped = 0;
    let mut failures = Vec::new();
    for r in results {
        ran += r.programs;
        skipped += r.inconclusive;
        for f in r.features {
            *features.entry(f).or_default() += 1;
        }
        failures.extend(r.failure);
    }
    eprintln!(
        "{ran} generated programs agreed on the reference evaluator, native and JS \
         ({batches} batches of {PER_BATCH} from seed {first}) in {:.1} s: {:.1} programs/s; \
         {skipped} skipped for running out of resources",
        elapsed.as_secs_f64(),
        (ran + skipped) as f64 / elapsed.as_secs_f64()
    );
    for (f, n) in &features {
        eprintln!("  {n:6}  {f}");
    }
    // The shrunk one first.
    failures.sort_by_key(|f| !f.contains("Smallest program"));
    assert!(
        failures.is_empty(),
        "{} of {batches} batches failed:\n\n{}",
        failures.len(),
        failures
            .iter()
            .take(5)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n\n")
    );
    if env_u64("STITCHWORT_EFFECT_FUZZ_BATCHES").is_none() {
        let missing: Vec<_> = REQUIRED
            .iter()
            .filter(|f| !features.contains_key(**f))
            .collect();
        assert!(
            missing.is_empty(),
            "shapes the generator didn't make: {missing:?}"
        );
        assert_eq!(
            skipped, 0,
            "programs ran out of resources: the generator's caps are too loose"
        );
    }
}

/// A seed always gives the same programs (the generator has no other
/// source of randomness), so a reported seed reproduces.
#[test]
fn the_generator_is_deterministic() {
    let make = || {
        let mut rng = Rng(7);
        let (p, _) = Gen::program(&mut rng);
        module(&[(0, &p)])
    };
    assert_eq!(make(), make());
}

/// `crates/rt/tests/effect_runtime.rs`'s program whose `IO` operations go
/// through a partial recursion and a forwarding handler.
const CROSSING: &str = r#"import Std (Fail, IO, Nat, Option, Result, Text)

def echo: Nat -> {IO, Partial} Nat
  | 0 => 0
  | n =>
    let line := Option.getOrElse "none" (IO.readLine())
    let shown := Fail.toResult (() =>
      IO.print "${n}: ${line}"
      if line == "stop" then Fail.fail "stopped" else Text.length line)
    match shown with
      | Ok length => length + echo (n - 1)
      | Err message => Text.length message

def main(): {IO, Partial} () :=
  IO.print "total ${echo 4}"
"#;

/// An `IO` operation crossing translation (`Map`) frames on its way to the
/// `run --js` runner, which no source program makes (stage 4c's note):
/// `main` wrapped in two `Effect.mapSig Effect.sigSwap`s at the term level,
/// as `io_operations_cross_translations_on_their_way_to_the_runner` does for
/// the native runner. Each operation is renamed twice and its reply mapped
/// back through both; the output is the reference evaluator's for the
/// unwrapped program.
#[test]
fn io_crossing_translations_runs_alike_in_js() {
    use stitchwort_cli::driver::with_stack;
    use stitchwort_core::{DefId, Icit, Sort, Term};
    with_stack(STACK, || {
        let mut session = Session::for_stack(STACK);
        session
            .load("crossing.sw", CROSSING)
            .expect("crossing.sw checks");
        let main = session.main().expect("a `main`");
        let g = &session.elab.globals;
        let def = |name: &str| {
            DefId(
                g.defs
                    .iter()
                    .rposition(|d| &*d.name == name)
                    .unwrap_or_else(|| panic!("no `{name}`")),
            )
        };
        // Type arguments are erased by the definitions' types.
        let implicit = |id: DefId, n: usize| {
            (0..n).fold(Term::Def(id), |f, _| {
                Term::app_icit(f, Term::Sort(Sort::Type(0)), Icit::Implicit)
            })
        };
        let wrap = |d: Term| {
            Term::app(
                Term::app(
                    implicit(def("Effect.mapSig"), 5),
                    implicit(def("Effect.sigSwap"), 4),
                ),
                d,
            )
        };
        let wrapped = wrap(wrap(main.term().clone()));
        let program = stitchwort_js::run::generate_program(g, session.elab.limits, &wrapped)
            .expect("generating the wrapped main");
        for input in [
            "",
            "a\nbb\n",
            "one\ntwo\nthree\nfour\nfive\n",
            "x\nstop\ny\n",
        ] {
            let mut expected = Vec::new();
            session
                .run_main(&main, &mut input.as_bytes(), &mut expected)
                .expect("the reference runs it");
            let js = run_js(&program, input);
            assert_eq!(js.end, "ok", "with input {input:?}");
            assert_eq!(
                js.stdout,
                String::from_utf8(expected).unwrap(),
                "with input {input:?}"
            );
        }
    });
}
