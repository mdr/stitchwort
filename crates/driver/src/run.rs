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
//! This is the only place where `print`, `readLine` and `readAll` happen
//! for real, and
//! the only place a partial computation runs. The type checker never calls
//! it.

use std::io::{self, BufRead, Write};

use stitchwort_core::registry::Builtin;
use stitchwort_core::step::{Machine, Obs};
use stitchwort_core::value::{eval, expand_step, force};
use stitchwort_core::{DataId, ResourceError, Term, Value, native};
use stitchwort_rt::MainRow;
pub use stitchwort_rt::host::{ConsoleInfo, NoTerminal, Terminal};
use stitchwort_rt::host::{random_seed, read_all, read_bytes, read_line, write_text};
use stitchwort_syntax::{Diagnostic, Span};

use crate::driver::Session;

/// What `main` must be. A pure `main : () -> ()` fits too, and so does any
/// sub-row such as `main : () -> {IO} ()`: they're passed where a function
/// with more abilities is allowed, like any other argument.
pub const MAIN_TYPE: &str = "() -> {IO, Fail, Partial} ()";

/// A program's `main`, ready to run.
pub struct Main {
    /// `main ()`, as a computation in the row `{IO, Partial}`, or
    /// `{IO, Fail, Partial}` for a `main` that may fail.
    term: Term,
    /// Where `main` is defined.
    pub span: Span,
    /// Whether `main`'s own type is `Partial`.
    pub partial: bool,
    /// The row `term` is in: [`MainRow::FailIo`] for a `main` that may fail.
    pub row: MainRow,
}

/// One thing a run did, in order: for tests that compare whole runs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    /// `print` of this payload.
    Print(String),
    /// `readLine`, and what it gave.
    Read(Option<String>),
    /// `readAll`, and what it gave.
    ReadAll(String),
    /// `console`, and what it gave.
    Console(ConsoleInfo),
    /// `keysMode on`.
    KeysMode(bool),
    /// `readBytes`, and what it gave.
    ReadBytes(Option<Vec<u8>>),
    /// `write` of this payload.
    Write(String),
    /// `randomSeed`, and what it gave.
    RandomSeed(u64),
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

pub use stitchwort_rt::host::RunError;

/// Where `main` is defined, for [`RunError::diagnostic`].
impl From<&Main> for Span {
    fn from(main: &Main) -> Span {
        main.span
    }
}

impl Main {
    /// `main ()`, as a computation in the row `{IO, Partial}`, or
    /// `{IO, Fail, Partial}` for a `main` that may fail.
    pub fn term(&self) -> &Term {
        &self.term
    }
}

/// The calls of `name` to try, in order. The lambda lets a pure or total
/// `main` through: calling one from code in a row with more abilities is
/// allowed. The library's names are written from `Std`, which always means
/// the library, whatever the program declares.
///
/// 1. `name ()` in `{IO, Partial}`, for a `name` with abilities among `IO`
///    and `Partial`.
/// 2. `name ()` in `{IO, Fail, Partial}` ([`MAIN_TYPE`]), for a `name` that
///    may also fail. No handler goes around it: the runner
///    performs `Fail.stop msg` itself, as it performs `IO.print`, and stops
///    with [`RunError::Failed`] (docs/proposals/partial-stage-2.md §3).
///
/// The first is tried first so that a `main` without `Fail` runs in the row
/// it always has. The reference evaluator, `stitchwort-rt` and the JS runner
/// each take an operation that reaches the bottom of the run apart in
/// either row (`{IO}` is `Plus IO NoOp`, and `{Fail, IO}` is
/// `Plus Fail (Plus IO NoOp)`).
fn main_calls(name: &str) -> [String; 2] {
    [
        format!("((u => {name} ()) : () -> {{Std.IO, Partial}} ()) ()"),
        format!("((u => {name} ()) : () -> {{Std.IO, Std.Fail, Partial}} ()) ()"),
    ]
}

/// Why a call of a definition to run didn't check.
enum CallError {
    /// Running out of resources, or a failure to parse the call.
    Other(Diagnostic),
    /// The definition's type isn't one that can be run.
    Type {
        span: stitchwort_syntax::Span,
        ty: String,
    },
}

impl Session {
    /// Finds the loaded program's `main`, and checks its type.
    pub fn main(&mut self) -> Result<Main, Diagnostic> {
        let g = &self.elab.globals;
        let main_name = self
            .elab
            .current_namespace()
            .map_or("main".to_string(), |n| format!("{n}.main"));
        let Some(index) = g.defs.iter().rposition(|d| *d.name == *main_name) else {
            return Err(
                Diagnostic::error("E-NO-MAIN", "there's no `main` to run").with_note(
                    "define `def main(): {IO} () := …`, or `def main(): {IO, Partial} () := …`",
                ),
            );
        };
        match self.main_call(index, "main") {
            Ok(main) => Ok(main),
            Err(CallError::Other(d)) => Err(d),
            Err(CallError::Type { span, ty }) => Err(Diagnostic::error(
                "E-MAIN-TYPE",
                "`main` must have type `() -> {IO} ()`, `() -> {IO, Partial} ()`, `() -> {IO, Fail} ()`, or `() -> {IO, Fail, Partial} ()`",
            )
            .with_label(span, format!("this has type `{ty}`"))
            .with_note(
                "a pure `main: () -> ()` is allowed too; other abilities must be handled inside `main`",
            )),
        }
    }

    /// Elaborates a call of the definition `name` at `index` (the first of
    /// [`main_calls`] that checks) as a computation in the row
    /// `{IO, Partial}` or `{IO, Fail, Partial}`.
    fn main_call(&mut self, index: usize, name: &str) -> Result<Main, CallError> {
        let def = &self.elab.globals.defs[index];
        let (span, ty) = (def.span, self.elab.show(&def.ty_value));
        // It has no body to run (docs/proposals/lsp-goal-holes.md, D636).
        if self.elab.is_unfinished(stitchwort_core::DefId(index)) {
            return Err(CallError::Other(
                Diagnostic::error(
                    "E-UNFINISHED",
                    format!(
                        "`{}` isn't finished: it, or something it uses, has an open goal (`?`)",
                        def.name
                    ),
                )
                .with_label(
                    span,
                    "this can't run until every goal it needs is filled in",
                ),
            ));
        }
        let partial = self
            .elab
            .is_partial(stitchwort_core::DefId(index))
            .unwrap_or(false);
        for (call, row) in main_calls(name)
            .into_iter()
            .zip([MainRow::Io, MainRow::FailIo])
        {
            let expr = self
                .parse_internal("<main>", &call)
                .map_err(CallError::Other)?;
            match self.elab.infer_expr(&expr) {
                Ok((term, _)) => {
                    return Ok(Main {
                        term,
                        span,
                        partial,
                        row,
                    });
                }
                Err(d) if d.code == "E-RESOURCE" || d.code == "E-UNFINISHED" => {
                    return Err(CallError::Other(d));
                }
                Err(_) => {}
            }
        }
        Err(CallError::Type { span, ty })
    }

    /// Finds the definition a project's `run` names by its full name
    /// (`Day05.main`), and checks that it can be run: a function from `()`
    /// to `()` with abilities among `IO`, `Fail` and `Partial`.
    pub fn main_named(&mut self, name: &str, project: &str) -> Result<Main, Diagnostic> {
        self.elab.leave_namespace();
        let Some(id) = self.elab.lookup_def(name) else {
            if self.elab.has_key(name) {
                return Err(Diagnostic::error(
                    "E-RUN-TYPE",
                    format!("`{name}` can't be run: it isn't a function"),
                ));
            }
            let prefix = name
                .rsplit_once('.')
                .map_or(String::new(), |(namespace, _)| format!("{namespace}."));
            let nearest = self
                .elab
                .def_keys_under(&prefix)
                .into_iter()
                .map(|key| (stitchwort_elab::edit_distance(name, &key), key))
                .filter(|(distance, _)| *distance <= 2)
                .min();
            let mut d = Diagnostic::error(
                "E-RUN-UNKNOWN",
                format!("there's no `{name}` in project {project}/"),
            );
            if let Some((_, near)) = nearest {
                d = d.with_note(format!("did you mean `{near}`?"));
            }
            return Err(d);
        };
        match self.main_call(id.0, name) {
            Ok(main) => Ok(main),
            Err(CallError::Other(d)) => Err(d),
            Err(CallError::Type { span, ty }) => Err(Diagnostic::error(
                "E-RUN-TYPE",
                format!("`{name}` can't be run: it has type `{ty}`"),
            )
            .with_label(span, "defined here")
            .with_note(
                "a function to run takes `()` and returns `()`, with abilities among IO, Fail and Partial: `() -> {IO} ()`, `() -> {IO, Partial} ()`, `() -> {IO, Fail} ()`, `() -> {IO, Fail, Partial} ()` or `() -> ()`",
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
            "Std.Pair.fst (Std.IO.simulate [{}] ((u => main ()) : () -> {{Std.IO}} ()))",
            lines.join(", ")
        );
        let expr = self.parse_internal("<simulate>", &source)?;
        let (term, _) = self.elab.infer_expr(&expr)?;
        let g = &self.elab.globals;
        let s = Shapes::new(self);
        let _op = g.budget.operation(self.elab.limits);
        // Proofs and types aren't computed (`erase.rs`).
        let _erasing = g.erasure.running();
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
                &mut NoTerminal,
                &policy,
                // As `IO.simulate` records them: `print` and `write` payloads.
                &mut |e| {
                    if let Event::Print(p) | Event::Write(p) = e {
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
    /// The contract for reading: input is UTF-8; for `readLine`, a trailing
    /// LF, and a CR just before it, are removed; an empty line is `Some ""`;
    /// `None` comes only once nothing remains. `readAll` gives everything
    /// that remains, exactly as it is (`""` once nothing does), so a
    /// `readLine` after it gives `None`. Output is flushed before every
    /// read. Each `print` writes its payload, then LF.
    pub fn run_main(
        &self,
        main: &Main,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<(), RunError> {
        self.run_main_on(main, input, output, &mut NoTerminal)
    }

    /// [`Session::run_main`] with `terminal` for `IO.console` and
    /// `IO.keysMode` (docs/proposals/terminal-io.md §4.6). Keys mode is left
    /// on if the run ends without leaving it: putting the terminal back is
    /// the caller's job.
    pub fn run_main_on(
        &self,
        main: &Main,
        input: &mut impl BufRead,
        output: &mut impl Write,
        terminal: &mut dyn Terminal,
    ) -> Result<(), RunError> {
        let result = self.run_loop(
            main,
            input,
            output,
            terminal,
            &Policy::default(),
            &mut |_| {},
        );
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

    /// Lowers `main` for the machine of `stitchwort-rt`, as
    /// [`Session::run_main_fast`] does before running it.
    pub fn lower_fast(&self, main: &Main) -> Result<stitchwort_rt::Program, RunError> {
        stitchwort_rt::lower_main(&self.elab.globals, self.elab.limits, main.term(), main.row)
            .map_err(RunError::Lowering)
    }

    /// Runs `main` on the machine of `stitchwort-rt` (docs/proposals/fast-runtime.md)
    /// instead of the reference evaluator: the same reading and writing, and the
    /// same errors (`RunError`), but not the same step counts, so a program may
    /// run out of resources at a different point, or not at all. Lowers `main`
    /// first; a failure to do so is [`RunError::Lowering`].
    pub fn run_main_fast(
        &self,
        main: &Main,
        input: &mut impl BufRead,
        output: &mut impl Write,
    ) -> Result<(), RunError> {
        self.run_main_fast_on(main, input, output, &mut NoTerminal)
    }

    /// [`Session::run_main_fast`] with `terminal`, as
    /// [`Session::run_main_on`].
    pub fn run_main_fast_on(
        &self,
        main: &Main,
        input: &mut impl BufRead,
        output: &mut impl Write,
        terminal: &mut dyn Terminal,
    ) -> Result<(), RunError> {
        let program = self.lower_fast(main)?;
        stitchwort_rt::run_main_on(
            &program,
            stitchwort_rt::Limits::from_core(self.elab.limits),
            input,
            output,
            terminal,
        )
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
        self.run_loop(main, input, output, &mut NoTerminal, policy, trace)
    }

    fn run_loop(
        &self,
        main: &Main,
        input: &mut impl BufRead,
        output: &mut impl Write,
        terminal: &mut dyn Terminal,
        policy: &Policy,
        trace: &mut dyn FnMut(Event),
    ) -> Result<Outcome, RunError> {
        let g = &self.elab.globals;
        let s = Shapes::new(self);
        // Proofs and types aren't computed (`erase.rs`).
        let _erasing = g.erasure.running();
        let mut lines = 0;
        let mut ticks = 0;
        let mut machine = {
            let _op = g.budget.operation(self.elab.limits);
            Machine::start(g, force(g, eval(g, &[], &main.term)?)?)
        };
        loop {
            let mut obs = {
                let _op = g.budget.operation(self.elab.limits);
                machine.step(g)?
            };
            // Perform operations until the step ends.
            loop {
                match obs {
                    Obs::Now(_) => return Ok(Outcome::Finished),
                    Obs::Later(rest) => {
                        // A limit of `n` allows exactly `n` ticks (docs/proposals/partial.md
                        // §7.4.3): stop on needing the next one.
                        if policy.max_ticks.is_some_and(|max| ticks >= max) {
                            return Ok(Outcome::OutOfTicks);
                        }
                        ticks += 1;
                        trace(Event::Tick);
                        machine = rest;
                        break;
                    }
                    Obs::Call(o, pending) => {
                        let reply = {
                            let _op = g.budget.operation(self.elab.limits);
                            self.perform(&s, o, input, output, terminal, &mut lines, trace)?
                        };
                        let _op = g.budget.operation(self.elab.limits);
                        obs = pending.reply(g, reply)?;
                    }
                }
            }
        }
    }

    /// Steps `term`, a partial computation that performs nothing (a test
    /// that runs partial code, D1183), to its result, as [`Session::run_main`]
    /// steps `main`: each stretch between two ticks is one operation, with
    /// its own resource limits, and there's no tick limit.
    pub(crate) fn run_partial(&self, term: &Term) -> Result<Value, ResourceError> {
        let g = &self.elab.globals;
        let _erasing = g.erasure.running();
        let mut machine = {
            let _op = g.budget.operation(self.elab.limits);
            Machine::start(g, force(g, eval(g, &[], term)?)?)
        };
        loop {
            let _op = g.budget.operation(self.elab.limits);
            match machine.step(g)? {
                Obs::Now(v) => return force(g, v),
                Obs::Later(rest) => machine = rest,
                Obs::Call(..) => unreachable!("a test performs nothing"),
            }
        }
    }

    /// Performs operation `o`, of `{IO}` or of `{Fail, IO}` (see
    /// [`main_calls`]): its reply. `Fail.stop msg` stops the run with
    /// [`RunError::Failed`]; it returns `Empty`, so there's nothing to resume
    /// with.
    #[allow(clippy::too_many_arguments)]
    fn perform(
        &self,
        s: &Shapes,
        o: Value,
        input: &mut impl BufRead,
        output: &mut impl Write,
        terminal: &mut dyn Terminal,
        lines: &mut usize,
        trace: &mut dyn FnMut(Event),
    ) -> Result<Value, RunError> {
        let g = &self.elab.globals;
        // `{IO}` is `Plus IO NoOp`, and `{Fail, IO}` is
        // `Plus Fail (Plus IO NoOp)`: an operation is `L` of an `IO` or `Fail`
        // operation, or `R (L …)` of an `IO` one.
        let mut o = force(g, o)?;
        let op = loop {
            let Value::Ctor(_, side, fields) = o else {
                unreachable!("an operation in `{{IO}}` or `{{Fail, IO}}`")
            };
            let inner = force(g, fields[0].clone())?;
            if side == 0 {
                break inner;
            }
            o = inner;
        };
        Ok(match op {
            Value::Ctor(d, _, payload) if Some(d) == s.fail => {
                return Err(RunError::Failed(s.text_to_string(self, &payload[0])?));
            }
            Value::Ctor(d, c, payload) if d == s.io && c == s.print => {
                let text = s.text_to_string(self, &payload[0])?;
                // `print`, `readLine` and `readAll` leave keys mode first
                // (D1260).
                terminal.keys_mode(false, output)?;
                output
                    .write_all(text.as_bytes())
                    .and_then(|()| output.write_all(b"\n"))
                    .map_err(RunError::Write)?;
                trace(Event::Print(text));
                s.unit()
            }
            Value::Ctor(d, c, _) if d == s.io && c == s.read_line => {
                terminal.keys_mode(false, output)?;
                output.flush().map_err(RunError::Write)?;
                let line = read_line(input, lines)?;
                trace(Event::Read(line.clone()));
                match line {
                    Some(line) => s.just(s.text(&line)),
                    None => s.nothing(),
                }
            }
            Value::Ctor(d, c, _) if d == s.io && c == s.read_all => {
                terminal.keys_mode(false, output)?;
                output.flush().map_err(RunError::Write)?;
                let rest = read_all(input, lines)?;
                let reply = s.text(&rest);
                trace(Event::ReadAll(rest));
                reply
            }
            Value::Ctor(d, c, _) if d == s.io && c == s.console => {
                let console = terminal.console();
                trace(Event::Console(console));
                let nat = |n: u64| native::nat_value(n.into());
                Value::Ctor(
                    s.console_record,
                    0,
                    [
                        s.bool(console.input_is_terminal),
                        s.bool(console.output_is_terminal),
                        nat(console.columns),
                        nat(console.rows),
                    ]
                    .into(),
                )
            }
            Value::Ctor(d, c, payload) if d == s.io && c == s.keys_mode => {
                let on =
                    matches!(force(g, payload[0].clone())?, Value::Ctor(_, c, _) if c == s.true_);
                terminal.keys_mode(on, output)?;
                trace(Event::KeysMode(on));
                s.unit()
            }
            Value::Ctor(d, c, _) if d == s.io && c == s.read_bytes => {
                output.flush().map_err(RunError::Write)?;
                let bytes = read_bytes(input, lines)?;
                trace(Event::ReadBytes(bytes.clone()));
                match bytes {
                    Some(bytes) => {
                        let mut list = Value::Ctor(s.list, 0, Vec::new().into());
                        for &b in bytes.iter().rev() {
                            let b = native::nat_value(u64::from(b).into());
                            list = Value::Ctor(s.list, 1, [b, list].into());
                        }
                        s.just(list)
                    }
                    None => s.nothing(),
                }
            }
            Value::Ctor(d, c, payload) if d == s.io && c == s.write => {
                let text = s.text_to_string(self, &payload[0])?;
                write_text(output, &text)?;
                trace(Event::Write(text));
                s.unit()
            }
            Value::Ctor(d, c, _) if d == s.io && c == s.random_seed => {
                let seed = random_seed();
                trace(Event::RandomSeed(seed));
                native::nat_value(seed.into())
            }
            _ => unreachable!("an `IO` or `Fail` operation"),
        })
    }
}

/// The tick limit for [`Session::simulate`] of a partial `main`.
pub const SIMULATED_TICKS: u64 = 1_000_000;

/// The prelude's types that `IO` operations and their results are built
/// from, and their constructors.
struct Shapes {
    io: DataId,
    print: usize,
    read_line: usize,
    read_all: usize,
    console: usize,
    keys_mode: usize,
    read_bytes: usize,
    write: usize,
    /// `Console`, `IO.console`'s reply: one constructor.
    console_record: DataId,
    /// `Bool`, and `True`'s index.
    bool_: DataId,
    true_: usize,
    false_: usize,
    random_seed: usize,
    /// `Fail`, once its library file has loaded: a `main` that may fail
    /// loads it.
    fail: Option<DataId>,
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
            read_all: ctor(Builtin::ReadAll),
            console: ctor(Builtin::IoConsole),
            keys_mode: ctor(Builtin::KeysMode),
            read_bytes: ctor(Builtin::ReadBytes),
            write: ctor(Builtin::IoWrite),
            console_record: data(Builtin::Console),
            bool_: data(Builtin::Bool),
            true_: ctor(Builtin::True),
            false_: ctor(Builtin::False),
            random_seed: ctor(Builtin::RandomSeed),
            fail: r.loaded_data(Builtin::Fail),
            unit: data(Builtin::UnitType),
            maybe: data(Builtin::Option),
            text: data(Builtin::Text),
            list: data(Builtin::List),
            char: data(Builtin::Char),
        }
    }

    fn unit(&self) -> Value {
        Value::Ctor(self.unit, 0, Vec::new().into())
    }

    fn bool(&self, b: bool) -> Value {
        let c = if b { self.true_ } else { self.false_ };
        Value::Ctor(self.bool_, c, Vec::new().into())
    }

    // `Option` is `None | Some a`, and `List` is `Nil | Cons a (List a)`.

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
