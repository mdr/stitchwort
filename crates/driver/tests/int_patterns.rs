//! Number patterns on `Int` (docs/proposals/integers.md, "Number patterns on
//! `Int`"): a split on the sign with a number case on the `Nat` field in
//! each branch.
//!
//! Generated matches over `Int` and `Bool` columns are compared with a direct
//! matcher on the source rows, on closed integers (keys near zero and around
//! `±10^30`), and evaluated four ways (natives on and off, each in both
//! evaluators), which must give the same normal form, on open arguments too.
//! Where the keys are small, they're also compared with the old compilation
//! of numbers as `Succ` chains.

use num_traits::ToPrimitive;
use stitchwort_core::native::{self, as_nat};
use stitchwort_core::reference;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{self, Head, Value};
use stitchwort_core::{BigUint, DataId, DefId, Globals, Icit, Term};
use stitchwort_driver::driver::{Session, with_stack};

const STACK: usize = 64 << 20;

/// A large key, beyond any machine integer the evaluators might use.
const BIG: i128 = 1_000_000_000_000_000_000_000_000_000_000;

fn load(session: &mut Session, text: &str) {
    if let Err(d) = session.load("test.sw", text) {
        panic!("doesn't check: {d:#?}\n{text}");
    }
}

/// The last definition called `name`.
fn def(g: &Globals, name: &str) -> DefId {
    DefId(
        g.defs
            .iter()
            .rposition(|d| &*d.name == name)
            .unwrap_or_else(|| panic!("no `{name}`")),
    )
}

fn int_data(g: &Globals) -> DataId {
    g.registry.data(Builtin::Int).expect("`Int` is registered")
}

fn nat(n: u128) -> Value {
    native::nat_value(BigUint::from(n))
}

/// The integer `i`, in its one form.
fn int(g: &Globals, i: i128) -> Value {
    if i >= 0 {
        Value::Ctor(int_data(g), 0, vec![nat(i as u128)].into())
    } else {
        Value::Ctor(int_data(g), 1, vec![nat((-1 - i) as u128)].into())
    }
}

/// The integer a closed value is, if it's one.
fn as_int(g: &Globals, v: &Value) -> Option<i128> {
    match value::force(g, v.clone()).ok()? {
        Value::Ctor(d, c, fields) if d == int_data(g) => {
            let n = as_nat(g, &fields[0]).ok()??.to_i128()?;
            Some(if c == 0 { n } else { -1 - n })
        }
        _ => None,
    }
}

/// `f args` by the machine: its value and normal form.
fn machine(g: &Globals, f: DefId, args: &[Value], level: usize) -> (Value, String) {
    let mut v = value::eval(g, &[], &Term::Def(f)).expect("no limits");
    for a in args {
        v = value::apply_icit(g, v, a.clone(), Icit::Explicit).expect("no limits");
    }
    let v = value::force(g, v).expect("no limits");
    let nf = format!("{:?}", value::quote(g, level, &v).expect("no limits"));
    (v, nf)
}

/// `f args` by the reference evaluator: its normal form.
fn slow(g: &Globals, f: DefId, args: &[Value], level: usize) -> String {
    let mut v = reference::eval(g, &[], &Term::Def(f)).expect("no limits");
    for a in args {
        v = reference::apply_icit(g, v, a.clone(), Icit::Explicit).expect("no limits");
    }
    let v = reference::force(g, v).expect("no limits");
    format!("{:?}", reference::quote(g, level, &v).expect("no limits"))
}

/// `f args` four ways (natives on and off, each in both evaluators), which
/// must agree: the machine's value with natives on, and its normal form.
fn run4(g: &mut Globals, f: DefId, args: &[Value], level: usize, what: &str) -> (Value, String) {
    let (v, on) = machine(g, f, args, level);
    let on_slow = slow(g, f, args, level);
    g.builtins.disable_natives = true;
    let (_, off) = machine(g, f, args, level);
    let off_slow = slow(g, f, args, level);
    g.builtins.disable_natives = false;
    assert_eq!(on, on_slow, "{what}: the evaluators disagree, natives on");
    assert_eq!(
        off, off_slow,
        "{what}: the evaluators disagree, natives off"
    );
    assert_eq!(on, off, "{what}: natives on and off disagree");
    (v, on)
}

/// A pattern on the `Nat` field of `OfNat` or `NegSucc`.
#[derive(Clone, Debug)]
enum Field {
    Num(u128),
    Var,
    Wild,
}

/// A generated pattern.
#[derive(Clone, Debug)]
enum Pat {
    /// An integer literal; `true` writes zero as `-0`.
    Lit(i128, bool),
    /// An `Int` variable, which the right-hand side may return.
    Var,
    Wild,
    OfNat(Field),
    NegSucc(Field),
    Bool(bool),
    BoolVar,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Col {
    Int,
    Bool,
}

#[derive(Clone, Copy, Debug)]
enum Rhs {
    Number(i128),
    /// The row's `i`th `Int` variable.
    Var(usize),
}

struct Generated {
    cols: Vec<Col>,
    rows: Vec<(Vec<Pat>, Rhs)>,
    /// Whether any key is large (the `Succ`-chain compilation can't do those).
    big: bool,
}

/// A closed argument.
#[derive(Clone, Copy, Debug)]
enum Arg {
    Int(i128),
    Bool(bool),
}

fn field_matches(p: &Field, n: i128) -> bool {
    match p {
        Field::Num(k) => *k as i128 == n,
        Field::Var | Field::Wild => true,
    }
}

/// Matches `pat` against `arg`, collecting the values of `Int` variables.
fn matches(pat: &Pat, arg: Arg, vars: &mut Vec<i128>) -> bool {
    match (pat, arg) {
        (Pat::Var, Arg::Int(i)) => {
            vars.push(i);
            true
        }
        (Pat::Var | Pat::Wild | Pat::BoolVar, _) => true,
        (Pat::Lit(k, _), Arg::Int(i)) => *k == i,
        (Pat::OfNat(f), Arg::Int(i)) => i >= 0 && field_matches(f, i),
        (Pat::NegSucc(f), Arg::Int(i)) => i < 0 && field_matches(f, -1 - i),
        (Pat::Bool(b), Arg::Bool(v)) => *b == v,
        _ => panic!("ill-typed generated pattern"),
    }
}

impl Generated {
    /// What the source rows say, tried top to bottom.
    fn expected(&self, args: &[Arg]) -> i128 {
        for (pats, rhs) in &self.rows {
            let mut vars = Vec::new();
            if pats
                .iter()
                .zip(args)
                .all(|(p, a)| matches(p, *a, &mut vars))
            {
                return match rhs {
                    Rhs::Number(n) => *n,
                    Rhs::Var(i) => vars[*i],
                };
            }
        }
        panic!("the generated rows aren't exhaustive");
    }

    fn source(&self, name: &str) -> String {
        fn field(p: &Field, nats: &mut usize) -> String {
            match p {
                Field::Num(k) => k.to_string(),
                Field::Var => {
                    *nats += 1;
                    format!("n{}", *nats - 1)
                }
                Field::Wild => "_".into(),
            }
        }
        fn show(p: &Pat, vars: &mut usize, others: &mut usize) -> String {
            match p {
                Pat::Lit(0, true) => "(-0)".into(),
                Pat::Lit(k, _) if *k < 0 => format!("({k})"),
                Pat::Lit(k, _) => k.to_string(),
                Pat::Var => {
                    *vars += 1;
                    format!("x{}", *vars - 1)
                }
                Pat::BoolVar => {
                    *others += 1;
                    format!("b{}", *others - 1)
                }
                Pat::Wild => "_".into(),
                Pat::OfNat(f) => format!("(OfNat {})", field(f, others)),
                Pat::NegSucc(f) => format!("(NegSucc {})", field(f, others)),
                Pat::Bool(true) => "True".into(),
                Pat::Bool(false) => "False".into(),
            }
        }
        let tys: Vec<&str> = self
            .cols
            .iter()
            .map(|c| if *c == Col::Int { "Int" } else { "Bool" })
            .collect();
        let mut out = format!("def {name} : {} -> Int\n", tys.join(" -> "));
        for (pats, rhs) in &self.rows {
            let (mut vars, mut others) = (0, 0);
            let shown: Vec<String> = pats
                .iter()
                .map(|p| show(p, &mut vars, &mut others))
                .collect();
            let rhs = match rhs {
                Rhs::Number(n) if *n < 0 => format!("({n})"),
                Rhs::Number(n) => n.to_string(),
                Rhs::Var(i) => format!("x{i}"),
            };
            out.push_str(&format!("  | {} => {rhs}\n", shown.join(", ")));
        }
        out
    }
}

/// A small linear congruential generator, so failures are reproducible.
struct Rng(u64);

impl Rng {
    fn below(&mut self, bound: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.0 >> 33) % bound
    }
}

/// The largest small key, either side of zero.
const MAX_KEY: i128 = 3;

fn generate(rng: &mut Rng) -> Generated {
    let cols: Vec<Col> = (0..1 + rng.below(2))
        .map(|_| {
            if rng.below(4) == 0 {
                Col::Bool
            } else {
                Col::Int
            }
        })
        .collect();
    let big = rng.below(4) == 0;
    let key = |rng: &mut Rng| -> i128 {
        if big && rng.below(3) == 0 {
            if rng.below(2) == 0 { BIG } else { -BIG }
        } else {
            rng.below(2 * MAX_KEY as u64 + 1) as i128 - MAX_KEY
        }
    };
    let mut rows = Vec::new();
    for r in 0..1 + rng.below(6) {
        let mut vars = 0;
        let pats: Vec<Pat> = cols
            .iter()
            .map(|c| match c {
                Col::Bool => match rng.below(4) {
                    0 => Pat::Wild,
                    1 => Pat::BoolVar,
                    n => Pat::Bool(n == 3),
                },
                // Mostly literals, so most columns are split by sign.
                Col::Int => match rng.below(12) {
                    0 => Pat::Wild,
                    1 => {
                        vars += 1;
                        Pat::Var
                    }
                    2 => Pat::OfNat(Field::Var),
                    3 => Pat::NegSucc(Field::Wild),
                    4 => Pat::OfNat(Field::Num(key(rng).unsigned_abs())),
                    5 => Pat::NegSucc(Field::Num(key(rng).unsigned_abs() % 3)),
                    6 => Pat::Lit(0, true),
                    _ => Pat::Lit(key(rng), false),
                },
            })
            .collect();
        let rhs = if vars > 0 && rng.below(2) == 0 {
            Rhs::Var(rng.below(vars as u64) as usize)
        } else {
            Rhs::Number(100 + r as i128)
        };
        rows.push((pats, rhs));
    }
    rows.push((vec![Pat::Wild; cols.len()], Rhs::Number(-999)));
    Generated { cols, rows, big }
}

/// Every combination of `choices` for each column.
fn product<T: Clone>(cols: &[Col], choices: impl Fn(Col) -> Vec<T>) -> Vec<Vec<T>> {
    let mut all = vec![Vec::new()];
    for c in cols {
        all = all
            .into_iter()
            .flat_map(|prefix| {
                choices(*c).into_iter().map(move |a| {
                    let mut next = prefix.clone();
                    next.push(a);
                    next
                })
            })
            .collect();
    }
    all
}

fn closed(c: Col) -> Vec<Arg> {
    match c {
        Col::Int => (-MAX_KEY - 2..=MAX_KEY + 2)
            .chain([-BIG - 1, -BIG, -BIG + 1, BIG - 1, BIG, BIG + 1])
            .map(Arg::Int)
            .collect(),
        Col::Bool => vec![Arg::Bool(false), Arg::Bool(true)],
    }
}

fn to_value(g: &Globals, a: Arg) -> Value {
    match a {
        Arg::Int(i) => int(g, i),
        Arg::Bool(b) => Value::Ctor(g.find_data("Bool").unwrap(), usize::from(b), vec![].into()),
    }
}

/// Open arguments for a column, the variable at `level` free in them:
/// unknown values, signs with unknown magnitudes, and `k + x` magnitudes.
fn open(g: &Globals, c: Col, level: usize) -> Vec<Value> {
    let x = Value::var(level);
    match c {
        Col::Int => {
            let d = int_data(g);
            let plus = |k: u128| native::from_view(BigUint::from(k), Some(x.clone()));
            vec![
                int(g, -2),
                x.clone(),
                Value::Ctor(d, 0, vec![x.clone()].into()),
                Value::Ctor(d, 1, vec![x.clone()].into()),
                Value::Ctor(d, 0, vec![plus(2)].into()),
                Value::Ctor(d, 1, vec![plus(MAX_KEY as u128 + 1)].into()),
            ]
        }
        Col::Bool => vec![to_value(g, Arg::Bool(true)), x],
    }
}

/// Generated `Int` matches agree with their source rows, four ways, and
/// with the `Succ`-chain compilation where the keys are small; on open
/// arguments the four ways agree too.
#[test]
fn generated_int_matches_agree_with_the_rows_in_every_evaluator() {
    with_stack(STACK, || {
        let mut rng = Rng(0x1e7_9a77_e2a5_0004);
        let (mut num_cases, mut compared_old) = (0, 0);
        // All the definitions in one module (loading the prelude is the slow
        // part), and the ones with small keys in another, compiled the old way.
        let all: Vec<(String, Generated)> = (0..150)
            .map(|i| (format!("f{i}"), generate(&mut rng)))
            .collect();
        let mut new = Session::new();
        let text: String = all.iter().map(|(n, d)| d.source(n)).collect();
        load(&mut new, &text);
        let mut old = Session::new();
        old.elab.numbers_as_succ = true;
        let small: String = all
            .iter()
            .filter(|(_, d)| !d.big)
            .map(|(n, d)| d.source(n))
            .collect();
        load(&mut old, &small);
        for (name, generated) in &all {
            let text = generated.source(name);
            let g = &mut new.elab.globals;
            let f = def(g, name);
            let body = g.def(f).body().unwrap();
            if body.subterms().any(|(t, _)| matches!(t, Term::NumCase(..))) {
                num_cases += 1;
            }
            let old = (!generated.big).then_some(&old);
            for args in product(&generated.cols, closed) {
                let expected = generated.expected(&args);
                let what = format!("{text}on {args:?}");
                let values: Vec<Value> = args.iter().map(|a| to_value(g, *a)).collect();
                let (v, nf) = run4(g, f, &values, 0, &what);
                assert_eq!(as_int(g, &v), Some(expected), "{what}: {nf}");
                if let Some(old) = &old {
                    let og = &old.elab.globals;
                    let small = args.iter().all(|a| match a {
                        Arg::Int(i) => i.abs() < BIG - 1,
                        Arg::Bool(_) => true,
                    });
                    if small {
                        let values: Vec<Value> = args.iter().map(|a| to_value(og, *a)).collect();
                        let (v, nf) = machine(og, def(og, name), &values, 0);
                        assert_eq!(as_int(og, &v), Some(expected), "old: {what}: {nf}");
                        compared_old += 1;
                    }
                }
            }
            let levels: Vec<usize> = (0..generated.cols.len()).collect();
            let per_column: Vec<Vec<Value>> = generated
                .cols
                .iter()
                .zip(&levels)
                .map(|(c, l)| open(g, *c, *l))
                .collect();
            let mut combos = vec![Vec::new()];
            for choices in &per_column {
                combos = combos
                    .into_iter()
                    .flat_map(|prefix: Vec<Value>| {
                        choices.iter().map(move |v| {
                            let mut next = prefix.clone();
                            next.push(v.clone());
                            next
                        })
                    })
                    .collect();
            }
            for args in combos {
                let what = format!("{text}on open {args:?}");
                run4(g, f, &args, levels.len(), &what);
            }
        }
        assert!(num_cases > 80, "only {num_cases} number cases generated");
        assert!(compared_old > 3000, "only {compared_old} old comparisons");
    });
}

/// `zeroOrOther (NegSucc k)` computes for an unknown `k` (that branch is all
/// catch-all), and `zeroOrOther (OfNat m)` is stuck, four ways.
#[test]
fn the_sign_is_known_and_the_magnitude_is_not() {
    with_stack(STACK, || {
        let mut session = Session::new();
        load(
            &mut session,
            "def zeroOrOther : Int -> Bool\n  | 0 => True\n  | _ => False\n",
        );
        let g = &mut session.elab.globals;
        let f = def(g, "zeroOrOther");
        let d = int_data(g);
        let neg = Value::Ctor(d, 1, vec![Value::var(0)].into());
        let (v, nf) = run4(g, f, &[neg], 1, "NegSucc k");
        let bool_data = g.find_data("Bool").unwrap();
        assert!(
            matches!(v, Value::Ctor(b, 0, _) if b == bool_data),
            "zeroOrOther (NegSucc k) = {nf}"
        );
        let pos = Value::Ctor(d, 0, vec![Value::var(0)].into());
        let (v, nf) = run4(g, f, &[pos], 1, "OfNat m");
        assert!(
            matches!(v, Value::Neutral(Head::Def(_) | Head::Var(_, _), _)),
            "zeroOrOther (OfNat m) = {nf} isn't stuck"
        );
        let big = Value::Ctor(d, 1, vec![nat(BIG as u128)].into());
        run4(g, f, &[big], 0, "NegSucc 10^30");
    });
}
