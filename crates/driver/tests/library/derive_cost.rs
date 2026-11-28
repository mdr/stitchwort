//! Guards the checker steps of what a data type with many constructors
//! derives (`==`, `<`, `${…}`, …): they grow about linearly with the number
//! of constructors, since the derived tests and orders compare positions
//! first and match only the first value (docs/proposals/derived-equality.md
//! §5.6, SW-3370). Matching both values, as they did before, made them
//! quadratic: 158 M steps for 94 constructors, against 39 M for 47.
//!
//! Each type is checked on its own, with the prelude's steps taken away.

use stitchwort_driver::driver::{Session, par_map};

const STACK: usize = 64 * 1024 * 1024;

/// A type of `count` constructors, as `fields` writes each: `K0 (m: Nat) | K1
/// | …`, or each with three fields of different kinds. (Not an enumeration:
/// its derived `Finite` is still quadratic.)
fn program(count: usize, fields: &dyn Fn(usize) -> String) -> String {
    let ctors: Vec<String> = (0..count)
        .map(|i| format!("  | K{i}{}", fields(i)))
        .collect();
    format!("type Node =\n{}\n", ctors.join("\n"))
}

/// The steps `program` takes to check.
fn steps(program: &str) -> u64 {
    let mut session = Session::for_stack(STACK);
    load(&mut session, "");
    load(&mut session, program)
}

/// Loads `text` into `session`: the steps it took.
fn load(session: &mut Session, text: &str) -> u64 {
    let before = session.elab.kernel.machine.budget.total_work();
    if let Err(ds) = session.load("derive_cost.sw", text) {
        let text: String = ds
            .iter()
            .map(|d| format!("{}: {}\n", d.code, d.message))
            .collect();
        panic!("the program doesn't check:\n{text}");
    }
    session.elab.kernel.machine.budget.total_work() - before
}

#[test]
fn derived_instances_grow_linearly_with_constructors() {
    let one = |i: usize| {
        if i == 0 {
            " (m: Nat)".to_string()
        } else {
            String::new()
        }
    };
    let three = |_: usize| " (a: Nat) (b: Text) (c: List Node)".to_string();
    let kinds: [(&str, &dyn Fn(usize) -> String); 2] =
        [("one field", &one), ("three fields each", &three)];
    let cases: Vec<(&str, usize, String)> = kinds
        .iter()
        .flat_map(|(name, fields)| [47, 94].map(|n| (*name, n, program(n, *fields))))
        .collect();
    let counts = par_map(STACK, &cases, |(_, _, text)| steps(text));
    let mut failures = Vec::new();
    for pair in cases.chunks(2).zip(counts.chunks(2)) {
        let ((name, ..), [half, full]) = (&pair.0[0], pair.1) else {
            unreachable!()
        };
        println!("{name}: 47 constructors {half} steps, 94 constructors {full}");
        // Linear doubles; quadratic quadruples. Allow some way between, for
        // the parts that are linear in the fields of every constructor.
        if *full * 10 > *half * 26 {
            failures.push(format!(
                "{name}: 94 constructors took {full} steps, {:.1} times 47's {half}",
                *full as f64 / *half as f64
            ));
        }
    }
    // 1.8 M steps after SW-3370 (158 M before), about 0.2 s.
    let full = counts[1];
    if full > 5_000_000 {
        failures.push(format!(
            "one field: 94 constructors took {full} steps, over 5 M"
        ));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `(DecEq.decide a0 b0).holds && ((DecEq.decide a1 b1).holds && …)` over
/// `terms` pairs of `Nat`s: the shape of a derived `==`'s test.
fn decide_chain(terms: usize) -> String {
    let params: Vec<String> = (0..terms)
        .flat_map(|k| [format!("(a{k}: Nat)"), format!("(b{k}: Nat)")])
        .collect();
    let mut body = format!("(DecEq.decide a{0} b{0}).holds", terms - 1);
    for k in (0..terms - 1).rev() {
        body = format!("(DecEq.decide a{k} b{k}).holds && ({body})");
    }
    format!(
        "import Std (Decidable, DecEq, Nat)\ndef same {}: Bool := {body}\n",
        params.join(" ")
    )
}

/// The steps of `decide_chain(terms)`'s definition, the import's taken away.
fn chain_steps(terms: &usize) -> u64 {
    let mut session = Session::for_stack(STACK);
    load(&mut session, "import Std (Decidable, DecEq, Nat)\n");
    load(&mut session, &decide_chain(*terms))
}

/// Guards a chain of `&&` over `Bool`s. Each level's right operand is the
/// whole rest of the chain; taking it out of its branch binder for the
/// conjunction an `if` may use zonks it, so doing that at every level, when
/// no operand is a decided proposition and nothing can use it, was cubic:
/// 1.54 M steps at 32 terms, 6.8 times 16's (SW-3726). What remains grows
/// with the variables in scope (two per term) too, about four times per
/// doubling.
#[test]
fn decide_chains_grow_quadratically() {
    let counts = par_map(STACK, &[16, 32], chain_steps);
    let [half, full] = counts[..] else {
        unreachable!()
    };
    println!("16 terms {half} steps, 32 terms {full}");
    let mut failures = Vec::new();
    if full * 10 > half * 50 {
        failures.push(format!(
            "32 terms took {full} steps, {:.1} times 16's {half}",
            full as f64 / half as f64
        ));
    }
    // 0.24 M steps after SW-3726 (1.54 M before).
    if full > 300_000 {
        failures.push(format!("32 terms took {full} steps, over 300 K"));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Guards what a wide constructor derives. The laws' proofs decide `C a… =
/// C b…` as the equality of the fields' nested pairs (`Pair.decMk`,
/// `Ordering.thenPairEqual`) and state each decision once; reading each
/// field's equation out of one conjunction, `And.left (And.right^k q)`, and
/// stating the decision twice made them cubic in a constructor's fields:
/// 16.9 M steps for a record of 16 `Nat`s and 202 M for 32 (SW-3719,
/// docs/proposals/derived-instances-rethink.md). A record of 8 and of 16
/// fields, and 16 constructors of three fields each.
#[test]
fn derived_instances_of_wide_constructors_stay_cheap() {
    let record = |fields: usize| {
        let fields: Vec<String> = (0..fields).map(|k| format!("(f{k}: Nat)")).collect();
        format!("type Wide = | MkWide {}\n", fields.join(" "))
    };
    let three = |_: usize| " (a: Nat) (b: Text) (c: Bool)".to_string();
    let cases = [record(8), record(16), program(16, &three)];
    let counts = par_map(STACK, &cases, |text| steps(text));
    let [eight, sixteen, many] = counts[..] else {
        unreachable!()
    };
    println!("record of 8 fields {eight} steps, of 16 {sixteen}; 16 constructors of 3: {many}");
    let mut failures = Vec::new();
    // Quadratic quadruples, cubic is eight times and more (9.7 before).
    if sixteen * 10 > eight * 55 {
        failures.push(format!(
            "a record of 16 fields took {sixteen} steps, {:.1} times 8's {eight}",
            sixteen as f64 / eight as f64
        ));
    }
    // 1.33 M and 2.29 M steps after SW-3719 (16.9 M and 5.4 M before).
    if sixteen > 2_000_000 {
        failures.push(format!(
            "a record of 16 fields took {sixteen} steps, over 2 M"
        ));
    }
    // 2.28 M before rule F (SW-4674), 3.11 M after it, 2.58 M once
    // zonking stopped reading back a function-valued `let` such as
    // `%sameIff`'s `%k`, which it never folds (`unify::value_forms`,
    // SW-4905).
    if many > 3_000_000 {
        failures.push(format!(
            "16 constructors of 3 fields took {many} steps, over 3 M"
        ));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
