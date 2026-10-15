//! The review's prototype table (review §9), run against the model.
//!
//! Every program with a small trace is run twice, by the machine and by the
//! literal reference equations, and the complete traces (operations, replies
//! and ticks, in order) must agree. Run with `--nocapture` to see the counts.

mod programs;

use std::cell::Cell;
use std::rc::Rc;

use programs::*;
use stitchwort_partial_model::delay::{Delay, SigMap};
use stitchwort_partial_model::machine::{self, Obs, Work};
use stitchwort_partial_model::reference::Rules;
use stitchwort_partial_model::runner::*;
use stitchwort_partial_model::typed::*;
use stitchwort_partial_model::val::Val;

/// Run with the machine and with the reference equations; they must agree.
fn both(d: Delay, input: &[&str]) -> (Report, Vec<String>) {
    let mut h1 = Script::with_input(input);
    let m = run(d.clone(), &mut h1, &Policy::default());
    let mut h2 = Script::with_input(input);
    let r = run_reference(Rules::Draft3, d, &mut h2, u64::MAX);
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
/// around requests) and calls to another recursive function.
fn gen_body(rng: &mut Lcg, depth: u32, n: u64) -> GenD {
    let choice = if depth == 0 { rng.next(2) } else { rng.next(7) };
    match choice {
        0 => now(n),
        1 if n > 0 => recur::<Gen, Host>(n - 1),
        1 => now(0),
        2 => {
            let rest = gen_body(rng, depth - 1, n);
            bind(print(&format!("p{n}")), move |()| rest.clone())
        }
        3 => {
            let a = gen_body(rng, depth - 1, n);
            let b = gen_body(rng, depth - 1, n);
            bind(a, move |x| bind(b.clone(), move |y| now(x + y)))
        }
        4 => map_sig(prefix_under_rec(), gen_body(rng, depth - 1, n)),
        5 => lift_right::<Rec<Gen>, Host, u64>(nest().call(n % 3)),
        _ => bind(read_line(), |l: Option<String>| {
            now(l.map_or(0, |l| l.len() as u64))
        }),
    }
}

#[test]
fn machine_agrees_with_the_equations_on_generated_programs() {
    let mut total_ticks = 0;
    for seed in 0..300u64 {
        let f = pfix::<Gen, Host>(move |n| gen_body(&mut Lcg(seed * 1000 + n), 3, n));
        for n in 0..4 {
            let (r, _) = both(f.call(n).raw, &["x", "yy", "zzz", "wwww", "", "v"]);
            total_ticks += r.ticks;
        }
    }
    println!("generated programs: {total_ticks} ticks in all");
    assert!(total_ticks > 100, "the generator should exercise requests");
}
