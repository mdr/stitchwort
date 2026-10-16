//! Running a program's `main`, performing its `IO` operations for real
//! (docs/proposals/text-and-io.md, "`main` and `stitchwort run`";
//! docs/proposals/partial.md §7.5).
//!
//! `main ()` is a partial computation, a `Delay` (a total `main` is lifted
//! into one). The runner steps it (`stitchwort_core::step`): each step runs
//! as far as the next operation, tick (a recursive call) or result. For an
//! operation, it performs it and resumes the step with the reply; at a tick
//! it goes on with the rest; at the result it stops. The loop itself
//! doesn't grow the stack.
//!
//! Ticks are part of what a program means; the runner's limits aren't. Each
//! stretch of evaluation between two operations or ticks is one operation
//! with its own resource budget, so a long interactive run doesn't run out
//! just by running long. A tick limit, for tests only, stops a run as
//! inconclusive.
//!
//! This is the only place where `print` and `readLine` happen for real, and
//! the only place a partial computation runs. The type checker never calls
//! it.

use std::fmt;
use std::io::{self, BufRead, Write};

use stitchwort_core::registry::Builtin;
use stitchwort_core::step::{Machine, Obs};
use stitchwort_core::value::{eval, expand_step, force};
use stitchwort_core::{DataId, ResourceError, Term, Value, native};
use stitchwort_syntax::{Diagnostic, Span};

use crate::driver::Session;

/// What `main` must be. A pure `main : () -> ()` fits too, and so does
/// `main : () -> {IO} ()`: they're passed where a function with more
/// abilities is allowed, like any other argument.
pub const MAIN_TYPE: &str = "() -> {IO, Partial} ()";

/// A program's `main`, ready to run.
pub struct Main {
    /// `main ()`, as a computation in the row `{IO, Partial}`.
    term: Term,
    /// Where `main` is defined.
    pub span: Span,
    /// Whether `main`'s own type is `Partial`.
    pub partial: bool,
}

/// One thing a run did, in order: for tests that compare whole runs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    /// `print` of this payload.
    Print(String),
    /// `readLine`, and what it gave.
    Read(Option<String>),
    /// A tick: one recursive call.
    Tick,
}

/// How a run ended, when nothing went wrong.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// `main` finished.
    Finished,
    /// The tick limit was reached: inconclusive, neither success nor failure.
    OutOfTicks,
}

/// What a run may do, beyond the session's resource limits. Not part of
/// what a program means.
#[derive(Clone, Copy, Debug, Default)]
pub struct Policy {
    /// Stop (inconclusively) once this many ticks have happened. For tests.
    pub max_ticks: Option<u64>,
}

/// Why a run stopped early.
#[derive(Debug)]
pub enum RunError {
    /// Evaluating the program ran out of resources.
    Resource(ResourceError),
    /// Reading standard input failed.
    Read(io::Error),
    /// Line `line` (counting from 1) of the input isn't valid UTF-8.
    InvalidUtf8 { line: usize },
    /// Writing or flushing standard output failed.
    Write(io::Error),
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RunError::Resource(e) => write!(f, "ran out of resources: {e}"),
            RunError::Read(e) => write!(f, "can't read standard input: {e}"),
            RunError::InvalidUtf8 { line } => {
                write!(f, "line {line} of standard input isn't valid UTF-8")
            }
            RunError::Write(e) => write!(f, "can't write standard output: {e}"),
        }
    }
}

impl RunError {
    /// The error to report: `E-RESOURCE`, pointing at `main`, or `E-IO`.
    pub fn diagnostic(&self, main: &Main) -> Diagnostic {
        match self {
            RunError::Resource(e) => {
                Diagnostic::from(*e).with_label(main.span, "while running this program")
            }
            _ => Diagnostic::error("E-IO", self.to_string()),
        }
    }
}

impl From<ResourceError> for RunError {
    fn from(e: ResourceError) -> RunError {
        RunError::Resource(e)
    }
}

/// `main ()`, checked against [`MAIN_TYPE`]. The lambda lets a pure or
/// total `main` through: calling one from code in `{IO, Partial}` is
/// allowed.
const MAIN_CALL: &str = "((\\u -> main ()) : () -> {IO, Partial} ()) ()";

impl Session {
    /// Finds the loaded program's `main`, and checks its type.
    pub fn main(&mut self) -> Result<Main, Diagnostic> {
        let g = &self.elab.globals;
        let Some(index) = g.defs.iter().rposition(|d| &*d.name == "main") else {
            return Err(Diagnostic::error("E-NO-MAIN", "there's no `main` to run")
                .with_note("define `main : () -> {IO} ()`, or `main : () -> {IO, Partial} ()`"));
        };
        let def = &g.defs[index];
        let (span, ty) = (def.span, self.elab.show(&def.ty_value));
        let partial = self
            .elab
            .is_partial(stitchwort_core::DefId(index))
            .unwrap_or(false);
        let expr = self.parse_expression("<main>", MAIN_CALL)?;
        match self.elab.infer_expr_with_builtins(&expr, &[Builtin::Io]) {
            Ok((term, _)) => Ok(Main {
                term,
                span,
                partial,
            }),
            Err(d) if d.code == "E-RESOURCE" => Err(d),
            Err(_) => Err(Diagnostic::error(
                "E-MAIN-TYPE",
                "`main` must have type `() -> {IO} ()` or `() -> {IO, Partial} ()`",
            )
            .with_label(span, format!("this has type `{ty}`"))
            .with_note(
                "a pure `main : () -> ()` is allowed too; other abilities must be handled inside `main`",
            )),
        }
    }

    /// What `main` prints when it's run by the prelude's `simulate` with
    /// scripted input lines: the reference that [`Session::run_main`] is
    /// tested against. Its output is these payloads, each followed by LF.
    ///
    /// A partial `main` can't be run by `simulate`, which is a handler
    /// (docs/proposals/partial.md §7.5): it's run by the runner instead,
    /// with the lines as its input and a limit of [`SIMULATED_TICKS`] ticks.
    /// Reaching the limit is inconclusive, and reported as `E-RESOURCE`.
    pub fn simulate(&mut self, input: &[&str]) -> Result<Vec<String>, Diagnostic> {
        let main = self.main()?;
        if main.partial {
            return self.simulate_partial(&main, input);
        }
        let lines: Vec<String> = input
            .iter()
            .map(|line| {
                let escaped: String = line
                    .chars()
                    .map(|c| format!("\\u{{{:X}}}", u32::from(c)))
                    .collect();
                format!("\"{escaped}\"")
            })
            .collect();
        let source = format!(
            "fst (simulate [{}] ((\\u -> main ()) : () -> {{IO}} ()))",
            lines.join(", ")
        );
        let expr = self.parse_expression("<simulate>", &source)?;
        let builtins = [Builtin::Fst, Builtin::Simulate, Builtin::Io];
        let (term, _) = self.elab.infer_expr_with_builtins(&expr, &builtins)?;
        let g = &self.elab.globals;
        let s = Shapes::new(self);
        let _op = g.budget.operation(self.elab.limits);
        let run = || -> Result<Vec<String>, ResourceError> {
            let mut printed = Vec::new();
            let mut list = force(g, eval(g, &[], &term)?)?;
            while let Value::Ctor(_, 1, cell) = list {
                printed.push(s.text_to_string(self, &cell[0])?);
                list = force(g, cell[1].clone())?;
            }
            Ok(printed)
        };
        run().map_err(Diagnostic::from)
    }

    fn simulate_partial(&self, main: &Main, input: &[&str]) -> Result<Vec<String>, Diagnostic> {
        let text: String = input.iter().map(|l| format!("{l}\n")).collect();
        let mut printed = Vec::new();
        let policy = Policy {
            max_ticks: Some(SIMULATED_TICKS),
        };
        let outcome = self
            .run_loop(
                main,
                &mut text.as_bytes(),
                &mut io::sink(),
                &policy,
                &mut |e| {
                    if let Event::Print(p) = e {
                        printed.push(p);
                    }
                },
            )
            .map_err(|e| e.diagnostic(main))?;
        match outcome {
            Outcome::Finished => Ok(printed),
            Outcome::OutOfTicks => Err(Diagnostic::error(
                "E-RESOURCE",
                format!(
                    "ran out of resources: `main` made more than {SIMULATED_TICKS} recursive calls"
                ),
            )
            .with_label(main.span, "while running this program")
            .with_note("this isn't a failure: there's no answer within the limits")),
        }
    }

    /// Runs `main`, reading lines from `input` and printing to `output`, and
    /// flushes `output` at the end. Evaluating each step between operations
    /// and ticks is one operation, with its own resource limits.
    ///
    /// The contract for reading: input is UTF-8; a trailing LF, and a CR just
    /// before it, are removed; an empty line is `Just ""`; `Nothing` comes
    /// only once nothing remains. Output is flushed before every read. Each
    /// `print` writes its payload, then LF.
    pub fn run_main(
        &self,
        main: &Main,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<(), RunError> {
        let result = self.run_loop(main, input, output, &Policy::default(), &mut |_| {});
        match result {
            Ok(_) => output.flush().map_err(RunError::Write),
            Err(e) => {
                // What was printed before the error still appears. The first
                // error is the one reported.
                let _ = output.flush();
                Err(e)
            }
        }
    }

    /// Runs `main` as [`Session::run_main`] does, within `policy`, telling
    /// `trace` each thing it does, in order. Doesn't flush `output`.
    pub fn run_main_with(
        &self,
        main: &Main,
        input: &mut impl BufRead,
        output: &mut impl Write,
        policy: &Policy,
        trace: &mut dyn FnMut(Event),
    ) -> Result<Outcome, RunError> {
        self.run_loop(main, input, output, policy, trace)
    }

    fn run_loop(
        &self,
        main: &Main,
        input: &mut impl BufRead,
        output: &mut impl Write,
        policy: &Policy,
        trace: &mut dyn FnMut(Event),
    ) -> Result<Outcome, RunError> {
        let g = &self.elab.globals;
        let s = Shapes::new(self);
        let mut lines = 0;
        let mut ticks = 0;
        let mut machine = {
            let _op = g.budget.operation(self.elab.limits);
            Machine::start(g, force(g, eval(g, &[], &main.term)?)?)
        };
        loop {
            if policy.max_ticks.is_some_and(|max| ticks >= max) {
                return Ok(Outcome::OutOfTicks);
            }
            let mut obs = {
                let _op = g.budget.operation(self.elab.limits);
                machine.step(g)?
            };
            // Perform operations until the step ends.
            loop {
                match obs {
                    Obs::Now(_) => return Ok(Outcome::Finished),
                    Obs::Later(rest) => {
                        ticks += 1;
                        trace(Event::Tick);
                        machine = rest;
                        break;
                    }
                    Obs::Call(o, pending) => {
                        let reply = {
                            let _op = g.budget.operation(self.elab.limits);
                            self.perform(&s, o, input, output, &mut lines, trace)?
                        };
                        let _op = g.budget.operation(self.elab.limits);
                        obs = pending.reply(g, reply)?;
                    }
                }
            }
        }
    }

    /// Performs operation `o` of `{IO}`: its reply.
    fn perform(
        &self,
        s: &Shapes,
        o: Value,
        input: &mut impl BufRead,
        output: &mut impl Write,
        lines: &mut usize,
        trace: &mut dyn FnMut(Event),
    ) -> Result<Value, RunError> {
        let g = &self.elab.globals;
        // `{IO}` is `Plus IO NoOp`, so every operation is `L` of an `IO`
        // operation.
        let Value::Ctor(_, _, fields) = force(g, o)? else {
            unreachable!("an operation in `{{IO}}`")
        };
        Ok(match force(g, fields[0].clone())? {
            Value::Ctor(d, c, payload) if d == s.io && c == s.print => {
                let text = s.text_to_string(self, &payload[0])?;
                output
                    .write_all(text.as_bytes())
                    .and_then(|()| output.write_all(b"\n"))
                    .map_err(RunError::Write)?;
                trace(Event::Print(text));
                s.unit()
            }
            Value::Ctor(d, c, _) if d == s.io && c == s.read_line => {
                output.flush().map_err(RunError::Write)?;
                let line = read_line(input, lines)?;
                trace(Event::Read(line.clone()));
                match line {
                    Some(line) => s.just(s.text(&line)),
                    None => s.nothing(),
                }
            }
            _ => unreachable!("an `IO` operation"),
        })
    }
}

/// The tick limit for [`Session::simulate`] of a partial `main`.
pub const SIMULATED_TICKS: u64 = 1_000_000;

/// The next line of input without its line ending, or `None` at the end.
/// `lines` counts the lines read so far.
fn read_line(input: &mut impl BufRead, lines: &mut usize) -> Result<Option<String>, RunError> {
    let mut bytes = Vec::new();
    if input
        .read_until(b'\n', &mut bytes)
        .map_err(RunError::Read)?
        == 0
    {
        return Ok(None);
    }
    *lines += 1;
    if bytes.last() == Some(&b'\n') {
        bytes.pop();
        if bytes.last() == Some(&b'\r') {
            bytes.pop();
        }
    }
    String::from_utf8(bytes)
        .map(Some)
        .map_err(|_| RunError::InvalidUtf8 { line: *lines })
}

/// The prelude's types that `IO` operations and their results are built
/// from, and their constructors.
struct Shapes {
    io: DataId,
    print: usize,
    read_line: usize,
    unit: DataId,
    maybe: DataId,
    text: DataId,
    list: DataId,
    char: DataId,
}

impl Shapes {
    fn new(session: &Session) -> Shapes {
        let g = &session.elab.globals;
        let r = &g.registry;
        let data = |b: Builtin| r.data(b).expect("the prelude declares it");
        let ctor = |b: Builtin| r.ctor(b).expect("the prelude declares it").1;
        Shapes {
            io: data(Builtin::Io),
            print: ctor(Builtin::Print),
            read_line: ctor(Builtin::ReadLine),
            unit: data(Builtin::UnitType),
            maybe: data(Builtin::Maybe),
            text: data(Builtin::Text),
            list: data(Builtin::List),
            char: data(Builtin::Char),
        }
    }

    fn unit(&self) -> Value {
        Value::Ctor(self.unit, 0, Vec::new().into())
    }

    // `Maybe` is `Nothing | Just a`, and `List` is `Nil | Cons a (List a)`.

    fn nothing(&self) -> Value {
        Value::Ctor(self.maybe, 0, Vec::new().into())
    }

    fn just(&self, value: Value) -> Value {
        Value::Ctor(self.maybe, 1, [value].into())
    }

    /// `MkText` of the line's characters, each `MkChar code rfl`.
    fn text(&self, line: &str) -> Value {
        let mut list = Value::Ctor(self.list, 0, Vec::new().into());
        for c in line.chars().rev() {
            let code = native::nat_value(u32::from(c).into());
            let c = Value::Ctor(self.char, 0, [code, Value::Refl].into());
            list = Value::Ctor(self.list, 1, [c, list].into());
        }
        Value::Ctor(self.text, 0, [list].into())
    }

    /// A `Text` value's characters. A checked program's text is always made
    /// of scalar values.
    fn text_to_string(&self, session: &Session, value: &Value) -> Result<String, ResourceError> {
        let g = &session.elab.globals;
        let Value::Ctor(d, 0, fields) = force(g, value.clone())? else {
            unreachable!("a `Text` value")
        };
        debug_assert_eq!(d, self.text);
        let mut out = String::new();
        // A compact list (a literal's) is taken a cell at a time, as matching
        // would.
        let mut list = expand_step(g, force(g, fields[0].clone())?);
        while let Value::Ctor(_, 1, cell) = list {
            let Value::Ctor(_, 0, c) = force(g, cell[0].clone())? else {
                unreachable!("a `Char` value")
            };
            let code = native::as_nat(g, &c[0])?
                .and_then(|n| u32::try_from(n).ok())
                .and_then(char::from_u32)
                .expect("a `Char` holds a scalar value");
            out.push(code);
            list = expand_step(g, force(g, cell[1].clone())?);
        }
        Ok(out)
    }
}
