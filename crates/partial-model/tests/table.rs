//! The review's prototype table (review §9), run against the model.
//!
//! Every program with a small trace is run twice, by the machine and by the
//! literal reference equations, and the complete traces (operations, replies
//! and ticks, in order) must agree. Run with `--nocapture` to see the counts.

mod programs;

use std::cell::Cell;
use std::rc::Rc;

use programs::handlers::*;
use programs::*;
use stitchwort_partial_model::delay::{Delay, SigMap};
use stitchwort_partial_model::machine::{self, Obs, Work};
use stitchwort_partial_model::reference::Rules;
use stitchwort_partial_model::runner::*;
use stitchwort_partial_model::typed::*;
use stitchwort_partial_model::val::Val;

/// Run with the machine and with the reference equations; they must agree.
fn both(d: Delay, input: &[&str]) -> (Report, Vec<String>) {
    both_limited(d, input, u64::MAX)
}

/// [`both`], stopping both runs at `max_ticks`.
fn both_limited(d: Delay, input: &[&str], max_ticks: u64) -> (Report, Vec<String>) {
    let mut h1 = Script::with_input(input);
    let policy = Policy {
        max_ticks: Some(max_ticks),
        ..Policy::default()
    };
    let m = run(d.clone(), &mut h1, &policy);
    let mut h2 = Script::with_input(input);
    let r = run_reference(Rules::Draft3, d, &mut h2, max_ticks);
    assert_eq!(m.trace, r.trace, "machine and reference traces differ");
    assert_eq!(m.outcome, r.outcome);
    assert_eq!((m.ticks, m.steps), (r.ticks, r.steps));
    assert_eq!(h1.output, h2.output);
    (m, h1.output)
}

fn finished(r: &Report) -> Val {
    match &r.outcome {
        Outcome::Finished(v) => v.clone(),
        other => panic!("didn't finish: {other:?}"),
    }
}

fn op_print(s: &str) -> Event {
    Event::Op(Val::tag(PRINT, Val::text(s)), Val::Unit)
}

fn op_read(line: Option<&str>) -> Event {
    let reply = match line {
        Some(l) => Val::right(Val::text(l)),
        None => Val::left(Val::Unit),
    };
    Event::Op(Val::tag(READ_LINE, Val::Unit), reply)
}

// --- 1. Exact suspension and observation counts --------------------------

/// `(laters, steps, least fuel)` under draft 3, after checking the machine
/// agrees with the reference.
fn draft3_counts(d: D<Empty, u64>) -> (u64, u64, u64) {
    let (r, _) = both(d.raw.clone(), &[]);
    let fuel = r.ticks;
    let result = finished(&r);
    assert_eq!(run_for(fuel, d.raw.clone()), Fuel::Done(Some(result)));
    if fuel > 0 {
        assert_eq!(run_for(fuel - 1, d.raw.clone()), Fuel::Done(None));
    }
    (r.ticks, r.steps, fuel)
}

#[test]
fn counts_table() {
    let rows: Vec<(&str, D<Empty, u64>, u64)> = vec![
        ("immediate return", immediate().call(7), 0),
        ("one recursive request", countdown().call(1), 1),
        ("two recursive requests", countdown().call(2), 2),
        ("collatzSteps 27", collatz_steps().call(27), 111),
        ("collatzSteps 1", collatz_steps().call(1), 0),
        ("fib 10 (nested, non-tail)", fib().call(10), 176),
    ];
    println!(
        "| program | draft 2: Laters | draft 2: observations | draft 3: Laters | draft 3: observations | draft 3: least fuel |"
    );
    println!("|---|---|---|---|---|---|");
    for (name, d, expected_ticks) in rows {
        let (l2, s2) = counts(Rules::Draft2, d.raw.clone());
        let (l3, s3, fuel) = draft3_counts(d);
        println!("| {name} | {l2} | {s2} | {l3} | {s3} | {fuel} |");
        assert_eq!(l3, expected_ticks, "{name}");
        assert_eq!(
            s3,
            l3 + 1,
            "{name}: one observation per Later, plus the final Now"
        );
        assert_eq!(l2, 2 * l3 + 1, "{name}: draft 2 counts entry and request");
        assert_eq!(s2, l2 + 1, "{name}");
    }
    // The reviewer's numbers for draft 2: 2, 4, 6 and 224 observations.
    assert_eq!(counts(Rules::Draft2, immediate().call(7).raw).1, 2);
    assert_eq!(counts(Rules::Draft2, countdown().call(1).raw).1, 4);
    assert_eq!(counts(Rules::Draft2, countdown().call(2).raw).1, 6);
    assert_eq!(counts(Rules::Draft2, collatz_steps().call(27).raw).1, 224);
}

#[test]
fn collatz_27_fuel() {
    let d = collatz_steps().call(27).raw;
    assert_eq!(run_for(111, d.clone()), Fuel::Done(Some(Val::Nat(111))));
    assert_eq!(run_for(110, d.clone()), Fuel::Done(None));
    assert_eq!(run_for(200, d), Fuel::Done(Some(Val::Nat(111))));
}

#[test]
fn mutual_calls() {
    let eo = even_odd();
    let (r, _) = both(eo.call((true, 10)).raw, &[]);
    assert_eq!(finished(&r), Val::Bool(true));
    assert_eq!(r.ticks, 10);
    let (r, _) = both(eo.call((false, 7)).raw, &[]);
    assert_eq!((finished(&r), r.ticks), (Val::Bool(true), 7));

    // Nested mutual requests: one tick per call after the first.
    let hof = hofstadter();
    for (female, n) in [(true, 10), (false, 10), (true, 15)] {
        let (r, _) = both(hof.call((female, n)).raw, &[]);
        let (value, calls) = hofstadter_calls(female, n);
        assert_eq!(finished(&r), Val::Nat(value));
        assert_eq!(r.ticks, calls - 1);
        println!(
            "hofstadter {} {n} = {value}: {} ticks",
            if female { "F" } else { "M" },
            r.ticks
        );
    }
}

// --- 2. The request translation's boundary -------------------------------
// (The monomorphic helper and the self-returning closure are `compile_fail`
// doctests in `src/typed.rs`: they can't be expressed.)

#[test]
fn recursive_callback_through_row_polymorphic_helper() {
    let (r, _) = both(via_helper().call(5).raw, &[]);
    assert_eq!((finished(&r), r.ticks), (Val::Nat(1), 5));

    // A callback under a lambda, called twice per level: 2 + 4 + 8 requests.
    let (r, _) = both(tree().call(3).raw, &[]);
    assert_eq!((finished(&r), r.ticks), (Val::Nat(8), 14));

    // Callbacks stored in a record, used inside the description.
    let (r, _) = both(stored().call(4).raw, &[]);
    assert_eq!((finished(&r), r.ticks), (Val::Nat(42), 4));

    // A recursive function returning a closure over an already-defined one.
    let f = returns_closure(countdown());
    let d = bind(f.call(3), |g: PFn<Empty, u64, u64>| g.call(5));
    let (r, _) = both(d.raw, &[]);
    assert_eq!((finished(&r), r.ticks), (Val::Nat(0), 3 + 5));
}

// --- 3. Suspended states and fresh `pfix` values -------------------------

#[test]
fn building_runs_nothing_and_a_request_suspends_before_the_callee() {
    let entries = Rc::new(Cell::new(0));
    let f = counted(entries.clone());
    let d = bind(f.call(2), |x| now(x + 1));
    assert_eq!(
        entries.get(),
        0,
        "building `pfix f x` must not run the body"
    );

    let Ok(Obs::Later(rest)) = machine::step(d.raw.clone(), &mut Work::unlimited()) else {
        panic!("expected a Later");
    };
    assert_eq!(
        entries.get(),
        1,
        "entering runs the body once, up to its request"
    );
    let Ok(Obs::Later(rest)) = machine::step(rest, &mut Work::unlimited()) else {
        panic!("expected a Later");
    };
    assert_eq!(
        entries.get(),
        2,
        "the callee runs only when the rest is stepped"
    );
    let Ok(Obs::Now(v)) = machine::step(rest, &mut Work::unlimited()) else {
        panic!("expected Now");
    };
    assert_eq!((v, entries.get()), (Val::Nat(1), 3));
}

#[test]
fn bind_continuations_constructing_fresh_pfix_values() {
    let (r, _) = both(fresh_in_continuation(3).raw, &[]);
    assert_eq!((finished(&r), r.ticks), (Val::Nat(30), 3));

    // `bindD (now x) fresh` steps straight into a `pfix` built during the step.
    let d = bind(now::<Empty, u64>(4), |x| countdown().call(x));
    let (r, _) = both(d.raw, &[]);
    assert_eq!((finished(&r), r.ticks), (Val::Nat(0), 4));
}

// --- 4. Operations, mappings and traces ----------------------------------

#[test]
fn tail_recursion_with_operations() {
    let (r, out) = both(echo().call(0).raw, &["a", "b"]);
    assert_eq!(
        r.trace,
        vec![
            op_read(Some("a")),
            op_print("a"),
            Event::Tick,
            op_read(Some("b")),
            op_print("b"),
            Event::Tick,
            op_read(None),
        ]
    );
    assert_eq!(
        (finished(&r), out),
        (Val::Nat(2), vec!["a".into(), "b".into()])
    );
}

#[test]
fn operations_around_a_non_tail_request_stay_in_order() {
    let (r, out) = both(nest().call(2).raw, &[]);
    assert_eq!(
        r.trace,
        vec![
            op_print("enter 2"),
            Event::Tick,
            op_print("enter 1"),
            Event::Tick,
            op_print("enter 0"),
            op_print("leave 1"),
            op_print("leave 2"),
        ]
    );
    assert_eq!(finished(&r), Val::Nat(3));
    assert_eq!(out.len(), 5);
}

#[test]
fn a_recursive_function_calling_another() {
    let (r, _) = both(outer(nest()).call(2).raw, &[]);
    let inner = [
        op_print("enter 1"),
        Event::Tick, // nest's own request
        op_print("enter 0"),
        op_print("leave 1"),
    ];
    // outer 2 runs nest 1, then requests outer 1, which runs nest 1, then
    // requests outer 0.
    let mut expected = inner.to_vec();
    expected.push(Event::Tick); // outer's request
    expected.extend(inner);
    expected.push(Event::Tick); // outer's request
    assert_eq!(r.trace, expected);
    assert_eq!(finished(&r), Val::Nat(2));
}

#[test]
fn signature_mappings_translate_operations_and_replies() {
    // `ask` becomes `readLine`, and replies come back as lengths.
    let (r, _) = both(sum_asks().call(2).raw, &["a", "bb", "ccc", "dddd"]);
    assert_eq!(
        r.trace,
        vec![
            op_read(Some("a")),
            op_read(Some("bb")),
            Event::Tick,
            op_read(Some("ccc")),
            op_read(Some("dddd")),
            Event::Tick,
        ]
    );
    assert_eq!(finished(&r), Val::Nat(1 + 2 + 3 + 4));

    // A mapping *into* the recursion signature, with a translated reply.
    let (r, _) = both(again().call(2).raw, &[]);
    assert_eq!((finished(&r), r.ticks), (Val::Nat(604), 2));

    // A mapping around a whole recursive computation.
    let d: D<Host, u64> = map_sig(prefix_prints(), nest().call(1));
    let (r, out) = both(d.raw, &[]);
    assert_eq!(out, vec![">enter 1", ">enter 0", ">leave 1"]);
    assert_eq!(r.ticks, 1);
}

// --- 5. Long chains: no host-stack growth --------------------------------
// The default test thread has a small stack; these would overflow it if the
// machine recursed per bind, per frame, or per recursive call.

#[test]
fn a_million_left_nested_binds() {
    let mut d = now::<Empty, u64>(0);
    for _ in 0..1_000_000 {
        d = bind(d, |x| now(x + 1));
    }
    let r = run(d.raw, &mut Script::default(), &Policy::default());
    assert_eq!(
        (r.outcome, r.ticks),
        (Outcome::Finished(Val::Nat(1_000_000)), 0)
    );
}

#[test]
fn deep_non_tail_recursion() {
    let n = 100_000;
    let r = run(
        sum_to().call(n).raw,
        &mut Script::default(),
        &Policy::default(),
    );
    assert_eq!(r.outcome, Outcome::Finished(Val::Nat(n * (n + 1) / 2)));
    assert_eq!(r.ticks, n);
    println!(
        "sumTo {n}: {} ticks, peak frames {} (heap)",
        r.ticks, r.peak_frames
    );
}

#[test]
fn tail_recursion_runs_in_constant_frames() {
    let small = run(
        countdown().call(10).raw,
        &mut Script::default(),
        &Policy::default(),
    );
    let large = run(
        countdown().call(1_000_000).raw,
        &mut Script::default(),
        &Policy::default(),
    );
    assert_eq!(large.ticks, 1_000_000);
    assert_eq!(small.peak_frames, large.peak_frames);
    println!("countdown 1000000: peak frames {}", large.peak_frames);

    // The same for a loop with operations.
    let lines: Vec<String> = (0..10_000).map(|i| i.to_string()).collect();
    let input: Vec<&str> = lines.iter().map(|s| s.as_str()).collect();
    let r = run(
        echo().call(0).raw,
        &mut Script::with_input(&input),
        &Policy::default(),
    );
    assert_eq!(r.outcome, Outcome::Finished(Val::Nat(10_000)));
    assert_eq!(r.peak_frames, small.peak_frames.max(r.peak_frames));
    assert!(r.peak_frames <= 4, "{}", r.peak_frames);
}

#[test]
fn long_chain_of_callbacks_that_observe_with_fuel() {
    // Each callback runs a bounded observation of a fresh partial computation
    // (stage 2's `runFor`, modelled): re-entry nests one level, not a chain.
    let cd = countdown();
    let mut d = now::<Empty, u64>(0);
    for _ in 0..10_000 {
        let cd = cd.clone();
        d = bind(d, move |x| match run_for(5, cd.call(3).raw) {
            Fuel::Done(Some(_)) => now(x + 1),
            other => panic!("{other:?}"),
        });
    }
    let r = run(d.raw, &mut Script::default(), &Policy::default());
    assert_eq!(r.outcome, Outcome::Finished(Val::Nat(10_000)));
}

// --- 6. Foreign operations never run inside a step ------------------------

#[test]
fn a_foreign_call_that_never_returns_is_a_host_request() {
    // `step` has no host to call: the foreign call comes back as data.
    let d = bind(foreign_spin(), |x| now(x + 1));
    match machine::step(d.raw.clone(), &mut Work::limited(100)) {
        Ok(Obs::Call(op, _)) => assert_eq!(
            op,
            Val::tag(FOREIGN, Val::pair(Val::text("spin"), Val::Nat(0)))
        ),
        _ => panic!("expected the foreign call as a request"),
    }
    // A pure fuel-bounded observer surfaces it instead of executing it.
    assert!(matches!(run_for(1, d.raw.clone()), Fuel::Op(_)));

    // Only the runner performs it; the host never returns, so the runner
    // reports where it's stuck.
    let mut host = Script::default();
    let r = run(d.raw.clone(), &mut host, &Policy::default());
    assert!(matches!(r.outcome, Outcome::Blocked(_)));
    assert_eq!(host.performed, 1);

    // A foreign function that does return.
    let mut host = Script::default();
    host.foreign
        .push(("spin".into(), |v| Val::Nat(v.as_nat() + 41)));
    let r = run(d.raw, &mut host, &Policy::default());
    assert_eq!(r.outcome, Outcome::Finished(Val::Nat(42)));
}

// --- 7. Runner policies are separate from ticks ---------------------------

#[test]
fn policies() {
    // An endless loop is inconclusive at the tick limit.
    let policy = Policy {
        max_ticks: Some(1000),
        ..Policy::default()
    };
    let r = run(spin().call(0).raw, &mut Script::default(), &policy);
    assert_eq!((r.outcome, r.ticks), (Outcome::OutOfTicks, 1000));

    // A long but total step exceeds the per-step work budget with no tick.
    let mut d = now::<Empty, u64>(0);
    for _ in 0..10_000 {
        d = bind(d, |x| now(x + 1));
    }
    let policy = Policy {
        max_work_per_step: 1000,
        ..Policy::default()
    };
    let r = run(d.raw, &mut Script::default(), &policy);
    assert_eq!((r.outcome, r.ticks), (Outcome::OutOfWorkInStep, 0));

    // An endless printer stops at the output budget.
    let policy = Policy {
        max_output_bytes: 400,
        ..Policy::default()
    };
    let r = run(forever_print().call(0).raw, &mut Script::default(), &policy);
    assert_eq!(r.outcome, Outcome::OutOfOutput);
    assert_eq!(r.ticks, 100);

    // Cancellation (the playground's Stop button).
    let cancel = Rc::new(Cell::new(true));
    let policy = Policy {
        cancel: Some(cancel),
        ..Policy::default()
    };
    let r = run(forever_print().call(0).raw, &mut Script::default(), &policy);
    assert_eq!(r.outcome, Outcome::Cancelled);
}

// --- 8. Machine and equations agree on generated programs -----------------

struct Lcg(u64);

impl Lcg {
    fn next(&mut self, bound: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) % bound
    }
}

struct Gen;
impl RecSig for Gen {
    type Arg = u64;
    type Res = u64;
}
type GenD = D<Plus<Rec<Gen>, Host>, u64>;

/// Prefix printed lines one level under the recursion signature.
fn prefix_under_rec() -> SigMap {
    SigMap {
        op: Rc::new(|o| match o {
            Val::R(inner) => match &**inner {
                Val::Tag(PRINT, t) => {
                    Val::right(Val::tag(PRINT, Val::text(&format!("+{}", t.as_text()))))
                }
                _ => o.clone(),
            },
            _ => o.clone(),
        }),
        res: Rc::new(|_, r| r),
    }
}

/// A random description body: binds, requests, operations, mappings (some
/// around requests) and calls to another recursive function; with
/// `handlers`, also `foldD` around generated code (nested, with every kind
/// of clause).
fn gen_body(rng: &mut Lcg, depth: u32, n: u64, handlers: bool) -> GenD {
    let choice = match (depth, handlers) {
        (0, _) => rng.next(2),
        (_, false) => rng.next(7),
        (_, true) => rng.next(9),
    };
    match choice {
        0 => now(n),
        1 if n > 0 => recur::<Gen, Host>(n - 1),
        1 => now(0),
        2 => {
            let rest = gen_body(rng, depth - 1, n, handlers);
            bind(print(&format!("p{n}")), move |()| rest.clone())
        }
        3 => {
            let a = gen_body(rng, depth - 1, n, handlers);
            let b = gen_body(rng, depth - 1, n, handlers);
            bind(a, move |x| bind(b.clone(), move |y| now(x + y)))
        }
        4 => map_sig(prefix_under_rec(), gen_body(rng, depth - 1, n, handlers)),
        5 => lift_right::<Rec<Gen>, Host, u64>(nest().call(n % 3)),
        6 => bind(read_line(), |l: Option<String>| {
            now(l.map_or(0, |l| l.len() as u64))
        }),
        _ => gen_handled(rng, depth - 1, n),
    }
}

type GenRow = Plus<Rec<Gen>, Host>;
type BumpD = D<Plus<Bump, GenRow>, u64>;

/// A body in `{Bump | gen's row}`: `bump` operations, binds, and generated
/// bodies (which may recurse, print, read, and handle) lifted into it.
fn gen_bumpy(rng: &mut Lcg, depth: u32, n: u64) -> BumpD {
    let choice = if depth == 0 { rng.next(2) } else { rng.next(4) };
    match choice {
        0 => perform(Val::left(Val::tag(BUMP, Val::Nat(n)))),
        1 => lift_right::<Bump, GenRow, u64>(gen_body(rng, depth, n, true)),
        2 => {
            let a = gen_bumpy(rng, depth - 1, n);
            let b = gen_bumpy(rng, depth - 1, n);
            bind(a, move |x| bind(b.clone(), move |y| now(x + y)))
        }
        _ => {
            let rest = gen_bumpy(rng, depth - 1, n);
            let bump: BumpD = perform(Val::left(Val::tag(BUMP, Val::Nat(n))));
            bind(bump, move |x| bind(rest.clone(), move |y| now(x * 3 + y)))
        }
    }
}

/// `handle (bumpy body) with …`, with a random `return` clause and a random
/// `bump` clause: resume once, never, twice, after printing, or after
/// running partial code (a recursive request of gen's own, or `nest`).
fn gen_handled(rng: &mut Lcg, depth: u32, n: u64) -> GenD {
    let inner = gen_bumpy(rng, depth, n);
    let done_kind = rng.next(3);
    let clause_kind = rng.next(6);
    handle::<Bump, GenRow, u64, u64>(
        move |x| match done_kind {
            0 => now(x),
            1 => now(2 * x + 1),
            _ => bind(print::<GenRow>(&format!("d{x}")), move |()| now(x)),
        },
        move |o, k: Resume<GenRow, u64>| {
            let Val::Tag(BUMP, m) = o else {
                panic!("not a Bump operation: {o:?}")
            };
            let m = m.as_nat();
            match clause_kind {
                0 => k(Val::Nat(m + 1)),
                1 => now(m * 7),
                2 => {
                    let k2 = k.clone();
                    bind(k(Val::Nat(1)), move |a| {
                        bind(k2(Val::Nat(2)), move |b| now(10 * a + b))
                    })
                }
                3 => bind(print::<GenRow>(&format!("h{m}")), move |()| k(Val::Nat(m))),
                4 if n > 0 => bind(recur::<Gen, Host>(n - 1), move |r| k(Val::Nat(r))),
                _ => bind(
                    lift_right::<Rec<Gen>, Host, u64>(nest().call(m % 3)),
                    move |r| k(Val::Nat(r)),
                ),
            }
        },
        inner,
    )
}

#[test]
fn machine_agrees_with_the_equations_on_generated_programs() {
    let mut total_ticks = 0;
    for seed in 0..300u64 {
        let f = pfix::<Gen, Host>(move |n| gen_body(&mut Lcg(seed * 1000 + n), 3, n, false));
        for n in 0..4 {
            let (r, _) = both(f.call(n).raw, &["x", "yy", "zzz", "wwww", "", "v"]);
            total_ticks += r.ticks;
        }
    }
    println!("generated programs: {total_ticks} ticks in all");
    assert!(total_ticks > 100, "the generator should exercise requests");
}

#[test]
fn machine_agrees_with_the_equations_on_generated_programs_with_handlers() {
    let (mut total_ticks, mut total_copies, mut handled) = (0, 0, 0);
    for seed in 0..300u64 {
        let f = pfix::<Gen, Host>(move |n| gen_body(&mut Lcg(seed * 7919 + n), 3, n, true));
        for n in 0..4 {
            let (r, _) = both(f.call(n).raw, &["x", "yy", "zzz", "wwww", "", "v"]);
            total_ticks += r.ticks;
            total_copies += r.copies;
            handled += u64::from(r.copies > 0);
        }
    }
    println!(
        "generated programs with handlers: {total_ticks} ticks, {total_copies} copies of captured frames, in {handled} runs"
    );
    assert!(total_ticks > 100, "the generator should exercise requests");
    assert!(
        handled > 10,
        "the generator should exercise multi-shot handlers"
    );
}

// --- 9. Handlers around partial code (partial-handlers.md, lane A) --------
// Each program runs on the machine and on the equations of §2.3, and its
// complete trace is written out by hand from the source.

fn tick() -> Event {
    Event::Tick
}

#[test]
fn fail_to_result_around_countdown() {
    // Stops at 3: two recursive calls (5 → 4 → 3), then `Err`.
    let (r, _) = both(to_result(countdown_fail().call(5)).raw, &[]);
    assert_eq!(r.trace, vec![tick(), tick()]);
    assert_eq!(finished(&r), err("three"));

    // Never reaches 3: two recursive calls (2 → 1 → 0), then `Ok 0`.
    let (r, _) = both(to_result(countdown_fail().call(2)).raw, &[]);
    assert_eq!(r.trace, vec![tick(), tick()]);
    assert_eq!(finished(&r), ok(Val::Nat(0)));

    // §2.7: resuming zero times drops the rest, loop included.
    // `Fail.toResult (() => { Fail.stop "no"; spin 0 })`.
    let d = bind(stop::<Plus<Fail, Empty>>(0, "no"), |_| {
        spin_in::<Plus<Fail, Empty>>().call(0)
    });
    let (r, _) = both(to_result(d).raw, &[]);
    assert_eq!((finished(&r), r.ticks), (err("no"), 0));
}

#[test]
fn a_state_handler_around_a_loop_adds_no_ticks() {
    let inputs = ["n", "e", "s", "w", "q"];

    // `fromLines inputs (() => play 0)`: the commands come from the handler.
    let (handled, _) = both(from_lines(&inputs, play().call(0)).raw, &[]);
    let mut expected = Vec::new();
    for (turn, command) in inputs.iter().enumerate() {
        expected.push(op_print(&format!("turn {turn}: {command}")));
        expected.push(tick());
    }
    assert_eq!(handled.trace, expected);
    assert_eq!((finished(&handled), handled.ticks), (Val::Nat(5), 5));
    assert_eq!(handled.copies, 0, "a one-shot handler never copies");

    // The same loop unhandled, its commands read from the host: the same
    // ticks, with the reads in the trace.
    let unhandled: D<Host, u64> = map_sig(input_from_host(), play().call(0));
    let (r, _) = both(unhandled.raw, &inputs);
    let mut expected = Vec::new();
    for (turn, command) in inputs.iter().enumerate() {
        expected.push(op_read(Some(command)));
        expected.push(op_print(&format!("turn {turn}: {command}")));
        expected.push(tick());
    }
    expected.push(op_read(None));
    assert_eq!(r.trace, expected);
    assert_eq!((finished(&r), r.ticks), (Val::Nat(5), 5));

    // §5.3: the loop under the handler runs in constant frames.
    let peak = |count: usize| {
        let lines: Vec<String> = (0..count).map(|i| i.to_string()).collect();
        let lines: Vec<&str> = lines.iter().map(|s| s.as_str()).collect();
        let r = run(
            from_lines(&lines, play().call(0)).raw,
            &mut Script::default(),
            &Policy {
                max_output_bytes: usize::MAX,
                ..Policy::default()
            },
        );
        assert_eq!(r.outcome, Outcome::Finished(Val::Nat(count as u64)));
        (r.peak_frames, r.copies)
    };
    let (small, large) = (peak(10), peak(10_000));
    println!(
        "fromLines around play: peak frames {} (10 turns), {} (10,000 turns)",
        small.0, large.0
    );
    assert_eq!(small, large);
}

#[test]
fn collect_in_runs_each_branch_to_its_end_in_order() {
    // Depth-first: the `True` branch's ticks and prints, then the `False`
    // branch's, at each fork.
    let (r, _) = both(collect_in(search().call(2)).raw, &[]);
    assert_eq!(
        r.trace,
        vec![
            op_print("2T"),
            tick(), // search 1, in 2T
            op_print("1T"),
            tick(), // search 0, in 2T 1T
            op_print("1F"),
            tick(), // search 0, in 2T 1F
            op_print("2F"),
            tick(), // search 1, in 2F
            op_print("1T"),
            tick(), // search 0, in 2F 1T
            op_print("1F"),
            tick(), // search 0, in 2F 1F
        ]
    );
    assert_eq!(finished(&r), list(&[3, 1, 2, 0].map(Val::Nat)));
    // Three forks, each resumed twice: the first resumption copies the
    // captured frames (the second may still come), the second moves them.
    assert_eq!(r.copies, 3);
}

#[test]
fn a_first_branch_that_loops_starves_the_second() {
    let (r, out) = both_limited(collect_in(left_loops()).raw, &[], 1000);
    let mut expected = vec![op_print("left")];
    expected.extend(std::iter::repeat_n(tick(), 1000));
    assert_eq!(r.trace, expected);
    assert_eq!(r.outcome, Outcome::OutOfTicks);
    assert_eq!(out, vec!["left"], "the second branch never runs");
}

#[test]
fn a_handler_inside_a_partial_functions_body() {
    // `walk 2`: the handler is under walk's `Tie`; its handled code makes
    // non-tail requests of `tally` (so each `Counter` operation is captured
    // across `tally`'s `Tie` and `Await` frames), prints from inside them
    // (forwarded), and calls `walk 1` (a request forwarded to walk's `Tie`).
    let (r, out) = both(walk().call(2).raw, &[]);
    assert_eq!(
        r.trace,
        vec![
            tick(), // tally 1
            tick(), // tally 0: get = 2
            op_print("tally 1: 2"),
            op_print("tally 2: 3"),
            tick(), // walk 1, from inside the handled code
            tick(), // tally 0, in walk 1 (its own counter: get = 1)
            op_print("tally 1: 1"),
            tick(), // walk 0
            op_print("walk 1: 2"),
            op_print("walk 2: 7"),
        ]
    );
    assert_eq!((finished(&r), r.ticks, out.len()), (Val::Nat(7), 5, 5));
    assert_eq!(r.copies, 0);

    // Deeper, on the machine alone: `tally i` is `i + i (i + 1) / 2` and
    // makes `i` requests, and each level of `walk` one more.
    let n = 100;
    let r = run(
        walk().call(n).raw,
        &mut Script::default(),
        &Policy {
            max_output_bytes: usize::MAX,
            ..Policy::default()
        },
    );
    let tally = |i: u64| i + i * (i + 1) / 2;
    assert_eq!(
        r.outcome,
        Outcome::Finished(Val::Nat((1..=n).map(tally).sum()))
    );
    assert_eq!(r.ticks, n * (n + 1) / 2 + n);
}

#[test]
fn nested_handlers() {
    let climb_trace = vec![
        op_print("climb 1"),
        tick(),
        op_print("climb 2"),
        tick(),
        op_print("climb 3"),
    ];

    // `Fail.toResult (() => runCounter 0 (() => climb 0))`: failing drops the
    // counter's state.
    let d = to_result(run_counter(0, climb().call(0)));
    let (r, _) = both(d.raw, &[]);
    assert_eq!(r.trace, climb_trace);
    assert_eq!(finished(&r), err("three"));

    // `runCounter 0 (() => Fail.toResult (() => climb 0))`: the counter is
    // outside, so its state survives the failure.
    let swapped: D<Plus<Fail, Plus<Counter, Host>>, u64> =
        map_sig(swap_first_two(), climb().call(0));
    let d = run_counter(0, to_result(swapped));
    let (r, _) = both(d.raw, &[]);
    assert_eq!(r.trace, climb_trace);
    assert_eq!(finished(&r), Val::pair(err("three"), Val::Nat(3)));
}

#[test]
fn clauses_that_run_partial_code() {
    // `ask n` is answered by `countDown n`, which prints and recurses in the
    // clause; the `return` clause runs `countDown 1` too. Their ticks count.
    let (r, _) = both(ask_by_counting_down().raw, &[]);
    assert_eq!(
        r.trace,
        vec![
            op_print("cd 2"),
            tick(),
            op_print("cd 1"),
            tick(),
            op_print("cd 0"), // countDown 2 = 3
            op_print("got 3"),
            op_print("cd 1"),
            tick(),
            op_print("cd 0"), // countDown 1 = 1
            op_print("cd 1"), // the return clause
            tick(),
            op_print("cd 0"),
        ]
    );
    assert_eq!((finished(&r), r.ticks), (Val::Nat(100 * 4 + 1), 4));
}
