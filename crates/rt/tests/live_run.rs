//! Live runs (`stitchwort_rt::LiveRun`, docs/proposals/playground-live-keys.md
//! §6 step 1): a run that stops whenever it reads input that isn't there
//! yet does exactly what a run with all its input at the start does: the
//! same output, the same routing counts and the same allocation trace,
//! whether it's fed a key per pause or everything at once. Also: a line
//! read across pauses keeps its bytes, Ctrl-C while waiting stops the run,
//! and the output cap's scope.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::io::{self, BufRead, Read, Write};
use std::path::Path;
use std::rc::Rc;

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::project::Target;
use stitchwort_rt::alloc_trace::{self, Trace};
use stitchwort_rt::host::{ConsoleInfo, RunError, Terminal};
use stitchwort_rt::{
    Advanced, LimitScope, LiveLimits, LiveRun, Policy, Program, RouteCounts, lower_main,
    run_main_counting_on,
};

const STACK: usize = 256 * 1024 * 1024;

/// A terminal of 80 by 24 that marks entering and leaving keys mode in the
/// output, as a real one writes its screen setup there.
#[derive(Clone, Copy, Default)]
struct Marking {
    on: bool,
}

impl Terminal for Marking {
    fn console(&mut self) -> ConsoleInfo {
        ConsoleInfo {
            input_is_terminal: true,
            output_is_terminal: true,
            columns: 80,
            rows: 24,
        }
    }

    fn keys_mode(&mut self, on: bool, output: &mut dyn Write) -> Result<(), RunError> {
        if on != self.on {
            self.on = on;
            let mark: &[u8] = if on { b"<keys on>" } else { b"<keys off>" };
            output.write_all(mark).map_err(RunError::Terminal)?;
        }
        Ok(())
    }
}

/// Input given as separate reads, all there at the start: what a live run
/// pushed everything and closed sees, for a run that can't wait.
struct Reads {
    reads: VecDeque<Vec<u8>>,
}

impl Read for Reads {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = self.fill_buf()?.read(buf)?;
        self.consume(n);
        Ok(n)
    }
}

impl BufRead for Reads {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        Ok(self.reads.front().map_or(&[][..], |read| read))
    }

    fn consume(&mut self, n: usize) {
        if n == 0 {
            return;
        }
        let first = self.reads.front_mut().expect("bytes to consume");
        first.drain(..n);
        if first.is_empty() {
            self.reads.pop_front();
        }
    }
}

/// Everything a run did that a pause mustn't change.
#[derive(Debug, PartialEq, Eq)]
struct Ran {
    output: String,
    counts: RouteCounts,
    trace: Trace,
}

fn limits(session: &Session, max_output: Option<usize>, scope: LimitScope) -> LiveLimits {
    LiveLimits {
        machine: stitchwort_rt::Limits::from_core(session.elab.limits),
        max_output,
        scope,
    }
}

/// `main` of a single file, lowered.
fn single(source: &str) -> (Session, Program) {
    let mut session = Session::for_stack(STACK);
    session
        .load("test.sw", source)
        .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
    let main = session.main().expect("`main` has the right type");
    let program = lower_main(
        &session.elab.globals,
        session.elab.limits,
        main.term(),
        main.row,
    )
    .expect("lowers");
    (session, program)
}

/// `Rogue.main` of games/rogue, lowered.
fn rogue() -> (Session, Program) {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../games/rogue/src/Rogue");
    let names = [
        "Generate", "Input", "Level", "Model", "Random", "Render", "Rogue", "Turn",
    ];
    let files = names
        .iter()
        .map(|name| {
            let path = format!("Rogue/{name}.sw");
            let text = std::fs::read_to_string(root.join(format!("{name}.sw"))).expect("a file");
            (path, text)
        })
        .collect();
    let mut session = Session::for_stack(STACK);
    session
        .load_project_sources("rogue", files, &Target::Namespaces(vec!["Rogue".into()]))
        .unwrap_or_else(|e| panic!("doesn't check: {e:#?}"));
    let main = session.main_named("Rogue.main", "rogue").expect("a main");
    let program = session.lower_fast(&main).expect("lowers");
    (session, program)
}

/// A run with all of `reads` there at the start, on the ordinary runner.
fn all_at_once(session: &Session, program: &Program, reads: &[&[u8]]) -> Ran {
    let mut input = Reads {
        reads: reads.iter().map(|read| read.to_vec()).collect(),
    };
    let mut output = Vec::new();
    alloc_trace::start();
    let (result, counts) = run_main_counting_on(
        program,
        stitchwort_rt::Limits::from_core(session.elab.limits),
        &Policy::default(),
        &mut input,
        &mut output,
        &mut Marking::default(),
    );
    let trace = alloc_trace::finish();
    result.unwrap_or_else(|e| panic!("{e}"));
    Ran {
        output: String::from_utf8(output).expect("text"),
        counts,
        trace,
    }
}

/// A live run, pushing `reads` a group at a time: the first group before
/// the first advance, each later one once the run waits. The input is
/// closed with the last group. Also returns how many advances waited.
fn live(program: Rc<Program>, groups: &[&[&[u8]]], limits: LiveLimits) -> (Ran, usize) {
    let mut output = Vec::new();
    alloc_trace::start();
    let mut run = LiveRun::new(program, limits, Box::new(Marking::default()))
        .unwrap_or_else(|e| panic!("{e}"));
    let mut waits = 0;
    let mut groups = groups.iter().peekable();
    loop {
        if let Some(group) = groups.next() {
            for read in *group {
                run.push(read);
            }
            if groups.peek().is_none() {
                run.close();
            }
        }
        match run.advance(&mut output).unwrap_or_else(|e| panic!("{e}")) {
            Advanced::Waiting => waits += 1,
            Advanced::Finished => break,
            other => panic!("{other:?}"),
        }
        assert!(waits < 10_000, "waiting for input that never comes");
    }
    let counts = run.counts();
    drop(run);
    let trace = alloc_trace::finish();
    let ran = Ran {
        output: String::from_utf8(output).expect("text"),
        counts,
        trace,
    };
    (ran, waits)
}

/// A key per pause, and everything at once, live, against the ordinary
/// runner: the same in every way. Returns the waits of the run fed a key
/// per pause, and its output.
fn agree((session, program): (Session, Program), reads: &[&[u8]]) -> (usize, String) {
    let program = Rc::new(program);
    // Once to fill the thread's cache of ASCII characters' cells
    // (`prims::char_value`), which only the first run on a thread
    // allocates, so that every traced run starts alike.
    all_at_once(&session, &program, reads);
    let expected = all_at_once(&session, &program, reads);
    assert_eq!(expected.trace.leaks(), [], "{}", expected.trace.render());
    let limits = limits(&session, None, LimitScope::EachStretch);
    let at_once: Vec<&[&[u8]]> = vec![reads];
    let (together, waits_together) = live(program.clone(), &at_once, limits);
    let one_by_one: Vec<&[&[u8]]> = reads.iter().map(std::slice::from_ref).collect();
    let (separately, waits) = live(program, &one_by_one, limits);
    assert_eq!(waits_together, 0, "everything was there at the start");
    assert_eq!(together.output, expected.output);
    assert_eq!(separately.output, expected.output);
    assert_eq!(together.counts, expected.counts);
    assert_eq!(separately.counts, expected.counts);
    same_trace("all at once", &together.trace, &expected.trace);
    same_trace("a key per pause", &separately.trace, &expected.trace);
    (waits, separately.output)
}

/// The traces event by event, failing at the first difference with the
/// events around it.
fn same_trace(what: &str, got: &Trace, expected: &Trace) {
    let (got, expected) = (got.render(), expected.render());
    let (got, expected): (Vec<&str>, Vec<&str>) =
        (got.lines().collect(), expected.lines().collect());
    if let Some(at) = (0..got.len().max(expected.len())).find(|&i| got.get(i) != expected.get(i)) {
        let around =
            |events: &[&str]| events[at.saturating_sub(8)..(at + 4).min(events.len())].join("\n");
        panic!(
            "{what}: the traces differ at event {at} of {} (expected {}):\n-- got\n{}\n-- expected\n{}",
            got.len(),
            expected.len(),
            around(&got),
            around(&expected)
        );
    }
}

/// examples/accept/terminal-walk.sw: `readBytes` in total code under
/// `Terminal.toIO`.
const WALK: &str = include_str!("../../../examples/accept/terminal-walk.sw");

#[test]
fn the_walk_a_key_per_pause_is_the_walk_all_at_once() {
    with_stack(STACK, || {
        let keys: [&[u8]; 6] = [b"l", b"l", b"\x1b[B", b"j", b"\x1b[D", b"q"];
        let (waits, output) = agree(single(WALK), &keys);
        assert_eq!(
            waits,
            keys.len() - 1,
            "each key but the last was waited for"
        );
        assert!(output.starts_with("<keys on>"), "{output:?}");
        assert!(
            output.ends_with("<keys off>The @ stopped at column 1, row 2.\n"),
            "{output:?}"
        );
    });
}

/// games/rogue: a partial `main`, whose reads happen inside handlers
/// around partial code (`Terminal.toIO`, the game's `Random`), so each
/// pause has captured handler frames on the stack.
#[test]
fn the_roguelike_a_key_per_pause_is_the_roguelike_all_at_once() {
    with_stack(STACK, || {
        stitchwort_rt::host::set_random_source(|| 2026);
        let keys: [&[u8]; 8] = [b"l", b"\x1b[C", b"j", b".", b"h", b"\x1b[A", b"p", b"q"];
        let (waits, output) = agree(rogue(), &keys);
        assert_eq!(
            waits,
            keys.len() - 1,
            "each key but the last was waited for"
        );
        assert!(
            output.ends_with("<keys off>You gave up on level 1, on turn 6.\n"),
            "{output:?}"
        );
    });
}

/// Lines read and echoed until the end of the input, after a key read in
/// keys mode.
const LINES: &str = r#"import Std (IO, List, Nat, Text)

def echo: Nat → {IO} ()
  | 0 => ()
  | Succ fuel =>
    match IO.readLine () with
      | None => IO.print "done"
      | Some line =>
        IO.print "[${line}]"
        echo fuel

def main (): {IO} () :=
  IO.keysMode True
  match IO.readBytes () with
    | None => IO.print "no key"
    | Some bytes =>
      IO.write "a key of ${Nat.toText (List.length bytes)} bytes\r\n"
      echo 100
"#;

/// A line pushed in pieces is read whole, with none of its bytes lost:
/// `readLine` waits until the line ending is there, taking nothing.
#[test]
fn a_line_read_across_pauses_keeps_its_bytes() {
    with_stack(STACK, || {
        let reads: [&[u8]; 7] = [b"\x1b[A", b"ab", b"c\n", b"d", b"e\r\nf", b"g\n", b"tail"];
        let (waits, output) = agree(single(LINES), &reads);
        assert_eq!(
            output,
            "<keys on>a key of 3 bytes\r\n<keys off>[abc]\n[de]\n[fg]\n[tail]\ndone\n"
        );
        // Waits before "ab", "c\n", "d", "e\r\nf", "g\n" and "tail"; not
        // after it, as it came with the end of the input.
        assert_eq!(waits, 6);
    });
}

/// A line read waits with keys mode already left (D1260) and the output
/// flushed: the caller sees the screen go back before the line is typed.
#[test]
fn a_line_read_leaves_keys_mode_before_waiting() {
    with_stack(STACK, || {
        let (session, program) = single(LINES);
        let limits = limits(&session, None, LimitScope::EachStretch);
        let mut run = LiveRun::new(Rc::new(program), limits, Box::new(Marking::default()))
            .unwrap_or_else(|e| panic!("{e}"));
        let mut output = Vec::new();
        assert_eq!(run.advance(&mut output).unwrap(), Advanced::Waiting);
        assert_eq!(output, b"<keys on>");
        run.push(b"x");
        run.push(b"ab");
        output.clear();
        assert_eq!(run.advance(&mut output).unwrap(), Advanced::Waiting);
        assert_eq!(
            String::from_utf8(output.clone()).unwrap(),
            "a key of 1 bytes\r\n<keys off>"
        );
        // Advancing with nothing new runs nothing.
        let counts = run.counts();
        output.clear();
        assert_eq!(run.advance(&mut output).unwrap(), Advanced::Waiting);
        assert_eq!((output.as_slice(), run.counts()), (&b""[..], counts));
        run.push(b"c\n");
        assert_eq!(run.advance(&mut output).unwrap(), Advanced::Waiting);
        assert_eq!(output, b"[abc]\n");
    });
}

/// Ctrl-C while the program waits for a key stops it (D1274, as D1248 on a
/// real terminal): keys mode is left, the rest of the run never happens,
/// and every cell it held is freed.
#[test]
fn ctrl_c_while_waiting_stops_the_run() {
    with_stack(STACK, || {
        let (session, program) = single(WALK);
        let limits = limits(&session, None, LimitScope::EachStretch);
        let mut output = Vec::new();
        // Fills the thread's cache of ASCII characters' cells, so that the
        // traced run allocates none it keeps.
        live(Rc::new(single(WALK).1), &[&[b"q"]], limits);
        alloc_trace::start();
        let mut run = LiveRun::new(Rc::new(program), limits, Box::new(Marking::default()))
            .unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(run.advance(&mut output).unwrap(), Advanced::Waiting);
        run.push(b"l");
        assert_eq!(run.advance(&mut output).unwrap(), Advanced::Waiting);
        assert!(run.is_waiting());
        let before = output.len();
        // The key pushed with it is dropped too, as a terminal flushes its
        // input on an interrupt.
        run.push(b"l");
        run.push(&[3]);
        assert_eq!(run.advance(&mut output).unwrap(), Advanced::Interrupted);
        assert_eq!(&output[before..], b"<keys off>");
        assert!(!run.is_waiting());
        run.push(b"q");
        assert_eq!(run.advance(&mut output).unwrap(), Advanced::Ended);
        drop(run);
        let trace = alloc_trace::finish();
        assert_eq!(trace.leaks(), [], "{}", trace.render());
        assert!(!String::from_utf8(output).unwrap().contains("stopped at"));
    });
}

/// Ctrl-\ stops it too (D1248).
#[test]
fn ctrl_backslash_while_waiting_stops_the_run() {
    with_stack(STACK, || {
        let (session, program) = single(WALK);
        let limits = limits(&session, None, LimitScope::EachStretch);
        let mut run = LiveRun::new(Rc::new(program), limits, Box::new(Marking::default()))
            .unwrap_or_else(|e| panic!("{e}"));
        let mut output = Vec::new();
        assert_eq!(run.advance(&mut output).unwrap(), Advanced::Waiting);
        run.push(&[28]);
        assert_eq!(run.advance(&mut output).unwrap(), Advanced::Interrupted);
    });
}

/// The output cap counts over each stretch between waits, or over the whole
/// run (D1275): the walk prints one frame per key, so a cap of a frame and
/// a half lets it play on per stretch, and stops it over the whole run.
#[test]
fn the_output_cap_counts_over_its_scope() {
    with_stack(STACK, || {
        let keys: [&[u8]; 4] = [b"l", b"l", b"j", b"q"];
        let groups: Vec<&[&[u8]]> = keys.iter().map(std::slice::from_ref).collect();
        let play = |scope: LimitScope, cap: usize| {
            let (session, program) = single(WALK);
            let limits = limits(&session, Some(cap), scope);
            let mut run = LiveRun::new(Rc::new(program), limits, Box::new(Marking::default()))
                .unwrap_or_else(|e| panic!("{e}"));
            let mut output = Vec::new();
            let mut groups = groups.iter();
            loop {
                match run.advance(&mut output) {
                    Ok(Advanced::Waiting) => {
                        for read in *groups.next().expect("a key left") {
                            run.push(read);
                        }
                    }
                    other => return (other, output),
                }
            }
        };
        // How long a frame is, from an uncapped run.
        let (ended, output) = play(LimitScope::EachStretch, usize::MAX);
        assert!(matches!(ended, Ok(Advanced::Finished)));
        let frame = output.len() / (keys.len() + 1);
        let cap = frame * 3 / 2;
        let (ended, _) = play(LimitScope::EachStretch, cap);
        assert!(matches!(ended, Ok(Advanced::Finished)), "{ended:?}");
        let (ended, output) = play(LimitScope::WholeRun, cap);
        assert!(
            matches!(ended, Err(RunError::OutputLimit { max }) if max == cap),
            "{ended:?}"
        );
        assert_eq!(output.len(), cap, "what fits is printed");
    });
}

/// The terminal a live run is given is the one its `IO.keysMode` uses.
#[test]
fn the_terminal_given_is_the_one_used() {
    struct Shared(Rc<RefCell<Vec<bool>>>);
    impl Terminal for Shared {
        fn console(&mut self) -> ConsoleInfo {
            Marking::default().console()
        }
        fn keys_mode(&mut self, on: bool, _output: &mut dyn Write) -> Result<(), RunError> {
            self.0.borrow_mut().push(on);
            Ok(())
        }
    }
    with_stack(STACK, || {
        let (session, program) = single(WALK);
        let seen = Rc::new(RefCell::new(Vec::new()));
        let limits = limits(&session, None, LimitScope::EachStretch);
        let mut run = LiveRun::new(Rc::new(program), limits, Box::new(Shared(seen.clone())))
            .unwrap_or_else(|e| panic!("{e}"));
        let mut output = Vec::new();
        assert_eq!(run.advance(&mut output).unwrap(), Advanced::Waiting);
        run.push(b"q");
        assert_eq!(run.advance(&mut output).unwrap(), Advanced::Finished);
        let seen = seen.borrow();
        assert_eq!((seen.first(), seen.last()), (Some(&true), Some(&false)));
    });
}
