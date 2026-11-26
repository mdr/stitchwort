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
use stitchwort_rt::host::{
    args, print_error, random_seed, read_all, read_bytes, read_line, write_text,
};
use stitchwort_syntax::{Diagnostic, Span};

use crate::driver::Session;

/// What `main` must be. A pure `main : () -> ()` fits too, and so does any
/// sub-row such as `main : () -> {IO} ()`: they're passed where a function
/// with more abilities is allowed, like any other argument.
pub const MAIN_TYPE: &str = "() -> {IO, Fail, Partial} ()";

/// A program's `main`, ready to run.
pub struct Main {
    /// `main ()`, as a computation in the row `{IO, Partial}`, with `Fail`
    /// and `Files` as [`Main::row`] says.
    term: Term,
    /// Where `main` is defined.
    pub span: Span,
    /// Whether `main`'s own type is `Partial`.
    pub partial: bool,
    /// The row `term` is in: which of `Fail` and `Files` it has beside `IO`.
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
    /// `args`, and what it gave.
    Args(Vec<String>),
    /// `printError` of this payload.
    PrintError(String),
    /// A `Files` operation on this path.
    File(std::path::PathBuf),
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

/// The calls of `name` to try, in order, each with the row it is in. The
/// lambda lets a pure or total `main` through: calling one from code in a
/// row with more abilities is allowed. The library's names are written from
/// `Std`, which always means the library, whatever the program declares.
///
/// Each is `name ()` in `{IO, Partial}` with some of `Fail` and `Files`
/// added ([`MainRow::ALL`]), the smallest first, so that a `main` runs in
/// the smallest row it fits; then the same rows for a `main` returning an
/// `ExitStatus`. No handler goes around it: the runner performs
/// `Fail.stop msg` itself, as it performs `IO.print`, and stops with
/// [`RunError::Failed`] (docs/proposals/partial-stage-2.md §3); it performs
/// `Files`' operations on the real disk (docs/proposals/file-io-and-text.md
/// §2). The reference evaluator, `stitchwort-rt` and the JS runner each
/// take an operation that reaches the bottom of the run apart by the row
/// ([`MainRow::layout`]).
fn main_calls(name: &str) -> Vec<(String, MainRow)> {
    let call = |row: MainRow, body: String, result: &str| {
        let abilities: Vec<String> = row.abilities().iter().map(|a| format!("Std.{a}")).collect();
        (
            format!(
                "((u => {body}) : () -> {{{}, Partial}} {result}) ()",
                abilities.join(", ")
            ),
            row,
        )
    };
    let unit = MainRow::ALL
        .iter()
        .map(|&row| call(row, format!("{name} ()"), "()"));
    // A `main` returning an `ExitStatus` runs as its number, which the
    // runners read as the program's status. These come after every row of
    // `()`, so a program that doesn't use `ExitStatus` never loads it.
    let status = MainRow::ALL
        .iter()
        .map(|&row| call(row, format!("Std.ExitStatus.toNat ({name} ())"), "Std.Nat"));
    unit.chain(status).collect()
}

/// What a finished `main` asks for: `()` is status 0; a `main` returning an
/// `ExitStatus` is called through `Std.ExitStatus.toNat` ([`main_calls`]),
/// so its result is a number, [`RunError::Exit`] unless it is 0.
fn exit_of(result: &stitchwort_core::Value) -> Result<(), RunError> {
    match result {
        stitchwort_core::Value::Nat(n) if n.bits() > 0 => {
            Err(RunError::Exit(u8::try_from(&**n).unwrap_or(u8::MAX)))
        }
        _ => Ok(()),
    }
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
        let g = &self.elab.ev();
        let main_name = self
            .elab
            .current_namespace()
            .map_or("main".to_string(), |n| format!("{n}.main"));
        let Some(index) = g.env.defs().iter().rposition(|d| **d.name() == *main_name) else {
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
                "`main` must have type `() -> {IO} ()` or `() -> {IO} ExitStatus`, with any of `Fail`, `Files` and `Partial` added to the row",
            )
            .with_label(span, format!("this has type `{ty}`"))
            .with_note(
                "for example `() -> {Files, IO, Fail} ()`, or `() -> {IO} ExitStatus` to choose the exit status; a pure `main: () -> ()` is allowed too; other abilities must be handled inside `main`",
            )),
        }
    }

    /// Elaborates a call of the definition `name` at `index` (the first of
    /// [`main_calls`] that checks) as a computation in the row
    /// `{IO, Partial}` or `{IO, Fail, Partial}`.
    fn main_call(&mut self, index: usize, name: &str) -> Result<Main, CallError> {
        let def = &self.elab.kernel.env.defs()[index];
        let (span, ty) = (def.span(), self.elab.show(def.ty_value()));
        // It has no body to run (docs/proposals/lsp-goal-holes.md, D636).
        let id = stitchwort_core::DefId(index);
        if self.elab.is_unfinished(id) {
            let (ids, waits) = if self.elab.relies_on_goal(id) {
                (self.elab.goals_relied_on(id), false)
            } else {
                (self.elab.blocked_on(id).into_iter().collect(), true)
            };
            let goals = self.goal_places(&ids);
            let named = crate::reliance::describe_goals(&goals, false);
            let message = match (goals.is_empty(), waits) {
                (true, _) => format!(
                    "`{}` isn't finished: it, or something it uses, has an open goal (`?`)",
                    def.name()
                ),
                (false, false) if goals.iter().all(|g| g.is_error()) => {
                    format!("`{}` relies on {named}, so it isn't run", def.name())
                }
                (false, false) => format!(
                    "`{}` relies on an open goal: {named}, so it isn't run",
                    def.name()
                ),
                (false, true) => format!(
                    "`{}` can't be checked until {}, so it isn't run",
                    def.name(),
                    crate::reliance::until(&goals)
                ),
            };
            return Err(CallError::Other(
                Diagnostic::error("E-UNFINISHED", message).with_label(
                    span,
                    "this can't run while something it needs has a `?` or an error",
                ),
            ));
        }
        let partial = self
            .elab
            .is_partial(stitchwort_core::DefId(index))
            .unwrap_or(false);
        for (call, row) in main_calls(name) {
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
                Err(d) if d.is_resource() || d.code == "E-UNFINISHED" => {
                    return Err(CallError::Other(d));
                }
                Err(_) => {}
            }
        }
        Err(CallError::Type { span, ty })
    }

    /// Finds the definition a project's `run` names by its full name
    /// (`Day05.main`), and checks that it can be run: a function from `()`
    /// to `()` with abilities among `IO`, `Fail`, `Files` and `Partial`.
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
                "a function to run takes `()` and returns `()`, with abilities among IO, Fail, Files and Partial: for example `() -> {IO} ()`, `() -> {IO, Fail} ()`, `() -> {Files, IO, Fail, Partial} ()` or `() -> ()`",
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
        let g = &self.elab.ev();
        let s = Shapes::new(self);
        let _op = g.machine.budget.operation(self.elab.options.limits);
        // Proofs and types aren't computed (`erase.rs`).
        let _erasing = g.machine.erasure.running();
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
        stitchwort_rt::lower_main(
            &self.elab.ev(),
            self.elab.options.limits,
            main.term(),
            main.row,
        )
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
            stitchwort_rt::Limits::from_core(self.elab.options.limits),
            input,
            output,
            terminal,
        )
    }

    /// [`Session::run_main_fast_on`], profiled (`stitchwort run --profile`):
    /// `started` gets the profile as the run starts, and it comes back with
    /// the result, unless `main` couldn't be lowered.
    #[allow(clippy::type_complexity)]
    pub fn run_main_fast_profiling_on(
        &self,
        main: &Main,
        sampling: stitchwort_rt::profile::Sampling,
        input: &mut impl BufRead,
        output: &mut impl Write,
        terminal: &mut dyn Terminal,
        started: impl FnOnce(&std::sync::Arc<stitchwort_rt::profile::Profile>),
    ) -> (
        Result<(), RunError>,
        Option<std::sync::Arc<stitchwort_rt::profile::Profile>>,
    ) {
        let program = match self.lower_fast(main) {
            Ok(program) => program,
            Err(e) => return (Err(e), None),
        };
        let (result, profile) = stitchwort_rt::run_main_profiling_on(
            &program,
            stitchwort_rt::Limits::from_core(self.elab.options.limits),
            sampling,
            input,
            output,
            terminal,
            started,
        );
        (result, Some(profile))
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

    /// [`Session::run_loop_inner`], with the functions that were pending named
    /// if the run recursed too deeply.
    fn run_loop(
        &self,
        main: &Main,
        input: &mut impl BufRead,
        output: &mut impl Write,
        terminal: &mut dyn Terminal,
        policy: &Policy,
        trace: &mut dyn FnMut(Event),
    ) -> Result<Outcome, RunError> {
        let result = self.run_loop_inner(main, input, output, terminal, policy, trace);
        let g = &self.elab.ev();
        match result {
            Err(RunError::Resource(ResourceError::Depth)) => {
                let deepest = g.machine.budget.take_deepest();
                if deepest.is_empty() {
                    return result;
                }
                let parts: Vec<String> = deepest
                    .iter()
                    .map(|&(id, count)| {
                        let name = &g.def(stitchwort_core::DefId(id)).name();
                        format!("`{name}` ({count} frames pending)")
                    })
                    .collect();
                Err(RunError::Deep(parts.join(", ")))
            }
            other => other,
        }
    }

    fn run_loop_inner(
        &self,
        main: &Main,
        input: &mut impl BufRead,
        output: &mut impl Write,
        terminal: &mut dyn Terminal,
        policy: &Policy,
        trace: &mut dyn FnMut(Event),
    ) -> Result<Outcome, RunError> {
        let g = &self.elab.ev();
        let s = Shapes::new(self);
        // Proofs and types aren't computed (`erase.rs`).
        let _erasing = g.machine.erasure.running();
        let mut lines = 0;
        let mut ticks = 0;
        let mut machine = {
            let _op = g.machine.budget.operation(self.elab.options.limits);
            Machine::start(g, force(g, eval(g, &[], &main.term)?)?)
        };
        loop {
            let mut obs = {
                let _op = g.machine.budget.operation(self.elab.options.limits);
                machine.step(g)?
            };
            // Perform operations until the step ends.
            loop {
                match obs {
                    Obs::Now(result) => return exit_of(&result).map(|()| Outcome::Finished),
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
                            let _op = g.machine.budget.operation(self.elab.options.limits);
                            self.perform(&s, o, input, output, terminal, &mut lines, trace)?
                        };
                        let _op = g.machine.budget.operation(self.elab.options.limits);
                        obs = pending.reply(g, reply)?;
                    }
                }
            }
        }
    }

    /// Performs operation `o`, of the row of [`main_calls`]: its reply.
    /// `Fail.stop msg` stops the run with [`RunError::Failed`]; it returns
    /// `Empty`, so there's nothing to resume with.
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
        let g = &self.elab.ev();
        // A row is `Plus A (Plus B … NoOp)`: an operation is `L` of one of
        // the first ability's, or `R` of one of the rest's. Each ability is
        // known by its data type.
        let mut o = force(g, o)?;
        let op = loop {
            let Value::Ctor(_, side, fields) = o else {
                unreachable!("an operation in `main`'s row")
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
            Value::Ctor(d, c, payload) if s.files.as_ref().is_some_and(|f| f.ops == d) => {
                return self.perform_files(s, c, &payload[0], trace);
            }
            Value::Ctor(d, c, payload) if d == s.io && c == s.print_error => {
                let text = s.text_to_string(self, &payload[0])?;
                terminal.keys_mode(false, output)?;
                print_error(output, &text)?;
                trace(Event::PrintError(text));
                s.unit()
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
            Value::Ctor(d, c, _) if d == s.io && c == s.args => {
                let args = args();
                trace(Event::Args(args.to_vec()));
                let mut list = Value::Ctor(s.list, 0, Vec::new().into());
                for arg in args.iter().rev() {
                    list = Value::Ctor(s.list, 1, [s.text(arg), list].into());
                }
                list
            }
            _ => unreachable!("an `IO`, `Fail` or `Files` operation"),
        })
    }

    /// Performs `Files`' operation `c` on `arg`, its argument, on the real
    /// disk ([`stitchwort_rt::files`], which the machine shares): its reply,
    /// a `Result` whose error carries the operation's own path.
    fn perform_files(
        &self,
        s: &Shapes,
        c: usize,
        arg: &Value,
        trace: &mut dyn FnMut(Event),
    ) -> Result<Value, RunError> {
        use stitchwort_rt::files::{self, Failure, Kind};
        let g = &self.elab.ev();
        let f = s.files.as_ref().expect("`Files` is loaded");
        let arg = force(g, arg.clone())?;
        // `write`'s argument is a pair of the path and the text.
        let (path, text) = if c == f.write {
            let Value::Ctor(_, 0, pair) = &arg else {
                unreachable!("`write` of a pair")
            };
            (force(g, pair[0].clone())?, Some(pair[1].clone()))
        } else {
            (arg, None)
        };
        let host = {
            let Value::Ctor(_, 0, fields) = &path else {
                unreachable!("a `Path`")
            };
            let mut parts = Vec::new();
            let mut list = expand_step(g, force(g, fields[0].clone())?);
            while let Value::Ctor(_, 1, cell) = list {
                parts.push(s.text_to_string(self, &cell[0])?);
                list = expand_step(g, force(g, cell[1].clone())?);
            }
            let absolute =
                matches!(force(g, fields[1].clone())?, Value::Ctor(_, b, _) if b == s.true_);
            files::host_path(&parts, absolute)
        };
        trace(Event::File(host.clone()));
        let kind = |k: Kind| {
            let c = match k {
                Kind::File => f.file,
                Kind::Folder => f.folder,
                Kind::Other => f.other,
            };
            Value::Ctor(f.kind, c, Vec::new().into())
        };
        let reply = if c == f.read {
            files::read(&host).map(|text| s.text(&text))
        } else if c == f.write {
            let text = s.text_to_string(self, &text.expect("a pair"))?;
            files::write(&host, &text).map(|()| s.unit())
        } else if c == f.list {
            files::list(&host).map(|entries| {
                let mut list = Value::Ctor(s.list, 0, Vec::new().into());
                for (name, k) in entries.into_iter().rev() {
                    let entry = Value::Ctor(f.entry, 0, [s.text(&name), kind(k)].into());
                    list = Value::Ctor(s.list, 1, [entry, list].into());
                }
                list
            })
        } else if c == f.info {
            files::info(&host).map(|(k, size)| {
                Value::Ctor(
                    f.info_record,
                    0,
                    [kind(k), native::nat_value(size.into())].into(),
                )
            })
        } else {
            unreachable!("a `Files` operation")
        };
        Ok(match reply {
            Ok(value) => Value::Ctor(f.result, f.ok, [value].into()),
            Err(failure) => {
                let (c, fields): (usize, Vec<Value>) = match failure {
                    Failure::NotFound => (f.not_found, vec![path]),
                    Failure::NotPermitted => (f.not_permitted, vec![path]),
                    Failure::NotAFile => (f.not_a_file, vec![path]),
                    Failure::NotAFolder => (f.not_a_folder, vec![path]),
                    Failure::NotText => (f.not_text, vec![path]),
                    Failure::Other(message) => (f.other_error, vec![path, s.text(&message)]),
                };
                let error = Value::Ctor(f.error, c, fields.into());
                Value::Ctor(f.result, f.err, [error].into())
            }
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
    args: usize,
    print_error: usize,
    /// `Fail`, once its library file has loaded: a `main` that may fail
    /// loads it.
    fail: Option<DataId>,
    /// `Files` and what its replies are built from, once its library file
    /// has loaded: a `main` that uses files loads it.
    files: Option<FileShapes>,
    unit: DataId,
    maybe: DataId,
    text: DataId,
    list: DataId,
    char: DataId,
}

/// `Files`' operations and the data types of its replies, with their
/// constructors' indexes.
struct FileShapes {
    ops: DataId,
    read: usize,
    write: usize,
    list: usize,
    info: usize,
    result: DataId,
    ok: usize,
    err: usize,
    kind: DataId,
    file: usize,
    folder: usize,
    other: usize,
    entry: DataId,
    info_record: DataId,
    error: DataId,
    not_found: usize,
    not_permitted: usize,
    not_a_file: usize,
    not_a_folder: usize,
    not_text: usize,
    other_error: usize,
}

impl Shapes {
    fn new(session: &Session) -> Shapes {
        let g = &session.elab.ev();
        let r = &g.env.registry();
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
            args: ctor(Builtin::Args),
            print_error: ctor(Builtin::PrintError),
            fail: r.loaded_data(Builtin::Fail),
            files: r.loaded_data(Builtin::Files).map(|ops| FileShapes {
                ops,
                read: ctor(Builtin::FilesRead),
                write: ctor(Builtin::FilesWrite),
                list: ctor(Builtin::FilesList),
                info: ctor(Builtin::FilesInfo),
                result: data(Builtin::ResultData),
                ok: ctor(Builtin::ResultOk),
                err: ctor(Builtin::ResultErr),
                kind: data(Builtin::FileKind),
                file: ctor(Builtin::FileKindFile),
                folder: ctor(Builtin::FileKindFolder),
                other: ctor(Builtin::FileKindOther),
                entry: data(Builtin::FileEntry),
                info_record: data(Builtin::FileInfo),
                error: data(Builtin::FileError),
                not_found: ctor(Builtin::FileNotFound),
                not_permitted: ctor(Builtin::FileNotPermitted),
                not_a_file: ctor(Builtin::FileNotAFile),
                not_a_folder: ctor(Builtin::FileNotAFolder),
                not_text: ctor(Builtin::FileNotText),
                other_error: ctor(Builtin::FileOtherError),
            }),
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

    /// `MkText` of the line's characters, each `MkChar code byComputing`.
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
        let g = &session.elab.ev();
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
