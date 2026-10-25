//! Live runs (docs/proposals/playground-live-keys.md, D1272): a run that
//! stops when the program asks for input that isn't there yet, returning to
//! its caller with the waiting operation kept, and goes on when input is
//! pushed. The playground's worker uses it so that it's free between keys.
//!
//! - **Same run.** A run fed its input a key per pause does exactly what
//!   one fed it all at once does: the same output, the same routing counts,
//!   the same allocation trace. Waiting only looks at the operation
//!   ([`Runner::read_need`]); the operation is routed once, before the
//!   pause, and performed once, after it.
//! - **Whole reads.** A read is done only once it can be done whole
//!   ([`ReadNeed`]): `readBytes` once a key's bytes are there, `readLine`
//!   once a whole line is, `readAll` at the end of the input. So no read
//!   stops part-way having taken bytes (the bug of §5.2 of the note: a
//!   `read_until` that met "would block" lost what it had read).
//! - **Before waiting**, a read does what it does before reading: it
//!   flushes the output, and `readLine` and `readAll` leave keys mode
//!   (D1260), so the caller sees the screen go back before the line is
//!   typed. Doing it again when the read is performed changes nothing.
//! - **Ctrl-C and Ctrl-\\** stop the run (D1274, as D1248 on a real
//!   terminal): a push holding either drops the pending input, and the next
//!   [`LiveRun::advance`] leaves keys mode and says
//!   [`Advanced::Interrupted`].
//! - **Limits** ([`LiveLimits`]): the machine's step budget is per stretch
//!   already (it resets at each performed operation and each tick); the
//!   output cap applies to the whole run or to each stretch between waits,
//!   as the caller says ([`LimitScope`], D1275).

use std::collections::VecDeque;
use std::io::{self, BufRead, Read, Write};
use std::rc::Rc;

use super::{Driven, Focus, ReadNeed, Routed, RunInput, Runner};
use crate::host::{RunError, Terminal};
use crate::ir::Program;
use crate::machine::{Limits, Machine};
use crate::run::{Policy, RouteCounts};
use crate::value::Value;

/// What a live run's limits are counted over.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LimitScope {
    /// The whole run, as for a run with all its input at the start.
    WholeRun,
    /// Each stretch between two waits for input: each
    /// [`LiveRun::advance`] (D1275). A game that redraws on every key can
    /// play for as long as it likes, and a stretch that loops printing is
    /// still stopped.
    EachStretch,
}

/// How much a live run may do. The time limit is the caller's: a stretch
/// is one [`LiveRun::advance`], so a caller with a timer (the page) counts
/// time over the stretches or over the run as `scope` says.
#[derive(Clone, Copy, Debug)]
pub struct LiveLimits {
    /// The machine's: steps between two operations or ticks, and frames.
    pub machine: Limits,
    /// Bytes the program may print, if limited: more is
    /// [`RunError::OutputLimit`].
    pub max_output: Option<usize>,
    /// What `max_output` is counted over.
    pub scope: LimitScope,
}

/// How a [`LiveRun::advance`] stopped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Advanced {
    /// The program is waiting for input: push some, then advance again.
    Waiting,
    /// `main` finished.
    Finished,
    /// Ctrl-C or Ctrl-\ was pushed: the run is stopped, with keys mode left.
    Interrupted,
    /// The run had already ended: an earlier advance finished, was
    /// interrupted, or failed. Nothing ran.
    Ended,
}

/// A run of `main` that waits for input by returning to its caller.
///
/// Start it with [`LiveRun::new`], then [`LiveRun::advance`] it: each
/// advance runs until `main` finishes or reads input that isn't there yet.
/// Between advances, [`LiveRun::push`] adds input (one key's bytes, or a
/// line, as one read) and [`LiveRun::close`] ends it.
pub struct LiveRun {
    runner: Runner<'static, 'static>,
    input: LiveInput,
    limits: LiveLimits,
    /// Bytes printed in the current scope ([`LimitScope`]).
    written: usize,
    phase: Phase,
}

enum Phase {
    /// Not advanced yet: `main ()`.
    Start(Value),
    /// Waiting for input, with the read in the runner.
    Waiting,
    /// Finished, interrupted or failed.
    Over,
}

impl LiveRun {
    /// A run of `program` (lowered by [`crate::lower_main`]), with
    /// `terminal` for `IO.console` and `IO.keysMode`. Runs nothing of
    /// `main` until the first [`LiveRun::advance`].
    pub fn new(
        program: Rc<Program>,
        limits: LiveLimits,
        terminal: Box<dyn Terminal>,
    ) -> Result<LiveRun, RunError> {
        let mut machine = Machine::shared(program, limits.machine);
        let delay = machine.entry()?;
        Ok(LiveRun {
            runner: Runner::new(machine, limits.machine, Policy::default(), terminal),
            input: LiveInput::default(),
            limits,
            written: 0,
            phase: Phase::Start(delay),
        })
    }

    /// Adds `bytes` to the input as one read: `readBytes` gives them
    /// together (never with the next push's), so a key's escape sequence
    /// stays whole and a lone `ESC` is the Escape key (terminal-io.md
    /// §3.2). A push holding Ctrl-C (3) or Ctrl-\ (28) interrupts the run
    /// instead, dropping all pending input, as a terminal's `ISIG` does.
    /// Ignored once the input is closed or interrupted.
    pub fn push(&mut self, bytes: &[u8]) {
        self.input.push(bytes);
    }

    /// Ends the input (Ctrl-D on an empty line): reads give what's left,
    /// then the end.
    pub fn close(&mut self) {
        self.input.close();
    }

    /// Runs until `main` finishes or waits for input, writing to `output`
    /// and flushing it before returning. An error ends the run, as it ends
    /// [`crate::run_main_on`]'s.
    pub fn advance(&mut self, output: &mut impl Write) -> Result<Advanced, RunError> {
        if let Phase::Over = self.phase {
            return Ok(Advanced::Ended);
        }
        if self.limits.scope == LimitScope::EachStretch {
            self.written = 0;
        }
        if self.input.interrupted {
            self.end();
        }
        let mut out = Capped {
            inner: output,
            written: &mut self.written,
            max: self.limits.max_output,
            full: false,
        };
        if self.input.interrupted {
            // As a terminal is put back when a program is interrupted.
            let left = self.runner.terminal.keys_mode(false, &mut out);
            let flushed = out.flush();
            left?;
            flushed.map_err(RunError::Write)?;
            return Ok(Advanced::Interrupted);
        }
        let driven = match std::mem::replace(&mut self.phase, Phase::Waiting) {
            Phase::Start(delay) => self
                .runner
                .drive(Focus::Eval(delay), &mut self.input, &mut out),
            Phase::Waiting => {
                let waiting = self
                    .runner
                    .waiting
                    .take()
                    .expect("a live run that's waiting has its read");
                let need = self.runner.read_need(&waiting.op).expect("a read");
                if !self.input.ready(need) {
                    // Advanced again with nothing new to read.
                    self.runner.waiting = Some(waiting);
                    return Ok(Advanced::Waiting);
                }
                match self
                    .runner
                    .perform_and_go_on(waiting, &mut self.input, &mut out)
                {
                    Ok(Routed::Performed(focus)) => {
                        self.runner.drive(focus, &mut self.input, &mut out)
                    }
                    Ok(_) => unreachable!("a read for the host is performed"),
                    Err(e) => Err(e),
                }
            }
            Phase::Over => unreachable!("handled above"),
        };
        let flushed = out.flush().map_err(RunError::Write);
        let full = out.full;
        match driven {
            Ok(Driven::Waiting) => {
                flushed?;
                Ok(Advanced::Waiting)
            }
            Ok(Driven::Finished(_)) => {
                self.end();
                flushed?;
                Ok(Advanced::Finished)
            }
            Ok(Driven::OutOfTicks) => unreachable!("a live run has no tick limit"),
            Err(error) => {
                self.end();
                Err(match error {
                    RunError::Write(_) if full => RunError::OutputLimit {
                        max: self.limits.max_output.unwrap_or_default(),
                    },
                    error => error,
                })
            }
        }
    }

    /// Whether the run is waiting for input: it has been advanced, and
    /// hasn't ended.
    pub fn is_waiting(&self) -> bool {
        matches!(self.phase, Phase::Waiting)
    }

    /// How much work routing operations took so far.
    pub fn counts(&self) -> RouteCounts {
        self.runner.counts
    }

    /// The terminal it was started with.
    pub fn terminal(&mut self) -> &mut dyn Terminal {
        &mut *self.runner.terminal
    }

    /// Ends the run, dropping what it was in the middle of.
    fn end(&mut self) {
        self.phase = Phase::Over;
        self.runner.waiting = None;
        self.runner.frames.clear();
        self.runner.marks.clear();
    }
}

/// The input of a live run: the reads pushed and not yet taken, each kept
/// apart, so that `readBytes` gives one at a time.
#[derive(Debug, Default)]
struct LiveInput {
    reads: VecDeque<Vec<u8>>,
    /// How much of the first read has been taken.
    taken: usize,
    closed: bool,
    interrupted: bool,
}

/// Ctrl-C and Ctrl-\, which stop a program rather than reach it.
const INTERRUPTS: [u8; 2] = [3, 28];

impl LiveInput {
    fn push(&mut self, bytes: &[u8]) {
        if self.closed || self.interrupted || bytes.is_empty() {
            return;
        }
        if bytes.iter().any(|b| INTERRUPTS.contains(b)) {
            self.interrupted = true;
            self.reads.clear();
            self.taken = 0;
            return;
        }
        self.reads.push_back(bytes.to_vec());
    }

    fn close(&mut self) {
        self.closed = true;
    }

    /// The bytes not yet taken, read by read.
    fn pending(&self) -> impl Iterator<Item = &[u8]> {
        self.reads.iter().enumerate().map(|(i, read)| {
            if i == 0 {
                &read[self.taken..]
            } else {
                &read[..]
            }
        })
    }
}

impl Read for LiveInput {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = self.fill_buf()?.read(buf)?;
        self.consume(n);
        Ok(n)
    }
}

impl BufRead for LiveInput {
    /// The rest of the first read; nothing at the end of the input; and
    /// "would block" when there's nothing yet, which a run never meets,
    /// since it reads only once [`RunInput::ready`] says so.
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        match self.reads.front() {
            Some(read) => Ok(&read[self.taken..]),
            None if self.closed => Ok(&[]),
            None => Err(io::ErrorKind::WouldBlock.into()),
        }
    }

    fn consume(&mut self, n: usize) {
        if n == 0 {
            return;
        }
        let first = self.reads.front().expect("bytes to consume");
        self.taken += n;
        debug_assert!(self.taken <= first.len());
        if self.taken >= first.len() {
            self.reads.pop_front();
            self.taken = 0;
        }
    }
}

impl RunInput for LiveInput {
    const PAUSES: bool = true;

    fn ready(&mut self, need: ReadNeed) -> bool {
        self.closed
            || match need {
                ReadNeed::Bytes => !self.reads.is_empty(),
                ReadNeed::Line => self.pending().any(|read| read.contains(&b'\n')),
                ReadNeed::All => false,
            }
    }
}

/// Output that passes on at most `max` bytes in its scope, and fails once
/// more is written.
struct Capped<'a, W: ?Sized> {
    inner: &'a mut W,
    written: &'a mut usize,
    max: Option<usize>,
    full: bool,
}

impl<W: Write + ?Sized> Write for Capped<'_, W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let room = match self.max {
            Some(max) => max - *self.written,
            None => buf.len(),
        };
        if room == 0 && !buf.is_empty() {
            self.full = true;
            return Err(io::Error::other("the output limit is used up"));
        }
        let n = self.inner.write(&buf[..room.min(buf.len())])?;
        *self.written += n;
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn line_ready(input: &mut LiveInput) -> bool {
        input.ready(ReadNeed::Line)
    }

    #[test]
    fn each_push_is_one_read() {
        let mut input = LiveInput::default();
        input.push(b"\x1b");
        input.push(b"x");
        assert!(input.ready(ReadNeed::Bytes));
        assert_eq!(input.fill_buf().unwrap(), b"\x1b");
        input.consume(1);
        assert_eq!(input.fill_buf().unwrap(), b"x");
        input.consume(1);
        assert!(!input.ready(ReadNeed::Bytes));
        assert_eq!(
            input.fill_buf().unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
    }

    #[test]
    fn a_line_is_ready_only_when_whole_or_closed() {
        let mut input = LiveInput::default();
        input.push(b"ab");
        assert!(!line_ready(&mut input));
        input.push(b"c\nd");
        assert!(line_ready(&mut input));
        let mut line = Vec::new();
        input.read_until(b'\n', &mut line).unwrap();
        assert_eq!(line, b"abc\n");
        // "d" is left, part of a read already partly taken.
        assert!(!line_ready(&mut input));
        assert!(!input.ready(ReadNeed::All));
        input.close();
        assert!(line_ready(&mut input) && input.ready(ReadNeed::All));
        let mut rest = Vec::new();
        input.read_to_end(&mut rest).unwrap();
        assert_eq!(rest, b"d");
    }

    #[test]
    fn ctrl_c_drops_the_input_and_ignores_what_follows() {
        let mut input = LiveInput::default();
        input.push(b"abc");
        input.push(&[3]);
        assert!(input.interrupted);
        assert!(input.reads.is_empty());
        input.push(b"x");
        assert!(input.reads.is_empty());
    }

    #[test]
    fn the_cap_counts_over_its_scope() {
        let mut sink = Vec::new();
        let mut written = 0;
        let mut out = Capped {
            inner: &mut sink,
            written: &mut written,
            max: Some(4),
            full: false,
        };
        assert!(out.write_all(b"abc").is_ok());
        assert!(out.write_all(b"de").is_err());
        assert!(out.full);
        assert_eq!(sink, b"abcd");
    }
}
