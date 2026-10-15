//! Number cases (`Term::NumCase`, docs/proposals/number-patterns.md).
//!
//! - The kernel rejects hand-built number cases that are wrong in each way the
//!   proposal lists, and keeps structural evidence from before one.
//! - Evaluation follows the table in the proposal, in both evaluators: a
//!   number case on `k + x` takes the default only when every number is below
//!   `k`, and is otherwise stuck.
//! - The oracle: each number case is expanded into the nested `Zero`/`Succ`
//!   cases it stands for, built from ordinary `case`s. The kernel must accept
//!   the expansion (a number case is conservative), and both must evaluate
//!   alike, on numbers and on open values. Generated pattern matches are also
//!   compared with a direct matcher on the source rows, and with the old
//!   compilation of number patterns as `Succ` chains.

use std::rc::Rc;

use stitchwort_core::check::{declare_def, define_def};
use stitchwort_core::hash::def_hash;
use stitchwort_core::native::{as_nat, nat_value};
use stitchwort_core::reference;
use stitchwort_core::term::{Branch, NumArm};
use stitchwort_core::value::{self, Elim, Head, Value};
use stitchwort_core::{BigUint, DataId, DefId, Globals, Icit, Term};
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_syntax::{SourceMap, Span};

const STACK: usize = 64 * 1024 * 1024;

fn span() -> Span {
    Span::point(SourceMap::new().add("test", ""), 0)
}

fn load(session: &mut Session, text: &str) {
    if let Err(d) = session.load("test.sw", text) {
        panic!("doesn't check: {d:#?}\n{text}");
    }
}

fn session_with(text: &str) -> Session {
    let mut session = Session::new();
    load(&mut session, text);
    session
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

fn nat(g: &Globals) -> DataId {
    g.builtins.nat.expect("the prelude's `Nat`")
}

fn nat_ty(g: &Globals) -> Term {
    Term::Data(nat(g), Vec::new())
}

fn num(n: u64) -> Term {
    Term::Nat(Rc::new(BigUint::from(n)))
}

fn pi(dom: Term, cod: Term) -> Term {
    Term::Pi("x".into(), Icit::Explicit, Rc::new(dom), Rc::new(cod))
}

fn lam(body: Term) -> Term {
    Term::Lam("x".into(), Icit::Explicit, Rc::new(body))
}

fn num_case(ix: usize, arms: Vec<(u64, Term)>, default: Term) -> Term {
    Term::NumCase(
        ix,
        arms.into_iter()
            .map(|(k, body)| NumArm {
                value: Rc::new(BigUint::from(k)),
                body: Rc::new(body),
            })
            .collect(),
        Rc::new(default),
    )
}

/// Declares a definition of type `ty` and defines it as `body` (which may
/// refer to itself as `Term::Def` of the returned id, the next one): the
/// kernel's error code, or "ok".
fn define(g: &mut Globals, ty: Term, body: impl FnOnce(DefId) -> Term) -> &'static str {
    let id = match declare_def(g, &"t".into(), &ty, false, false, span()) {
        Ok(id) => id,
        Err(d) => return d.code,
    };
    match define_def(g, id, &body(id)) {
        Ok(()) => "ok",
        Err(d) => d.code,
    }
}

// The kernel

const SHAPE: &str = "
Shape : Nat -> Type
Shape 404 = Nat
Shape _   = Bool
";

#[test]
fn the_kernel_refines_each_arm_and_nothing_else() {
    let mut session = session_with(SHAPE);
    let g = &mut session.elab.globals;
    let shape = def(g, "Shape");
    // (n : Nat) -> Shape n -> Nat
    let ty = pi(
        nat_ty(g),
        pi(Term::app(Term::Def(shape), Term::Var(0)), nat_ty(g)),
    );
    let body = |arms: Vec<(u64, Term)>, default: Term| lam(lam(num_case(1, arms, default)));
    // In the `404` arm, `s : Shape 404`, which is `Nat`.
    assert_eq!(
        define(g, ty.clone(), |_| body(vec![(404, Term::Var(0))], num(0))),
        "ok"
    );
    // Valid for a different number.
    assert_eq!(
        define(g, ty.clone(), |_| body(vec![(405, Term::Var(0))], num(0))),
        "E-TYPE-MISMATCH"
    );
    // A sibling that would only check if the `404` arm's refinement leaked.
    assert_eq!(
        define(g, ty.clone(), |_| body(
            vec![(404, Term::Var(0)), (405, Term::Var(0))],
            num(0)
        )),
        "E-TYPE-MISMATCH"
    );
    // The default knows nothing: `Shape n` doesn't compute.
    assert_eq!(
        define(g, ty, |_| body(vec![(404, Term::Var(0))], Term::Var(0))),
        "E-TYPE-MISMATCH"
    );
    // (n : Nat) -> n = 404: `rfl` checks in the `404` arm, but not in the
    // default, nor in an arm for a different number.
    let eq = |g: &Globals| {
        pi(
            nat_ty(g),
            Term::Eq(
                Some(Rc::new(nat_ty(g))),
                Rc::new(Term::Var(0)),
                Rc::new(num(404)),
            ),
        )
    };
    let ty = eq(g);
    assert_eq!(
        define(g, ty.clone(), |_| lam(num_case(
            0,
            vec![(404, Term::Refl)],
            Term::Refl
        ))),
        "E-REFL"
    );
    assert_eq!(
        define(g, ty, |_| lam(num_case(
            0,
            vec![(404, Term::Refl), (405, Term::Refl)],
            Term::Refl
        ))),
        "E-REFL"
    );
}

#[test]
fn the_kernel_checks_the_shape_of_a_number_case() {
    let mut session = Session::new();
    let g = &mut session.elab.globals;
    let nat_to_nat = pi(nat_ty(g), nat_ty(g));
    let bool_data = g.find_data("Bool").unwrap();
    let cases: Vec<(&str, Term, Term)> = vec![
        (
            "no numbers",
            nat_to_nat.clone(),
            lam(num_case(0, vec![], num(0))),
        ),
        (
            "a repeated number",
            nat_to_nat.clone(),
            lam(num_case(0, vec![(3, num(1)), (3, num(2))], num(0))),
        ),
        (
            "numbers out of order",
            nat_to_nat.clone(),
            lam(num_case(0, vec![(4, num(1)), (3, num(2))], num(0))),
        ),
        (
            "a variable out of scope",
            nat_to_nat.clone(),
            lam(num_case(1, vec![(3, num(1))], num(0))),
        ),
        (
            "inside an expression",
            nat_to_nat.clone(),
            lam(Term::ctor(
                nat(g),
                1,
                vec![num_case(0, vec![(3, num(1))], num(0))],
            )),
        ),
        (
            "a scrutinee that isn't a number",
            pi(Term::Data(bool_data, Vec::new()), nat_ty(g)),
            lam(num_case(0, vec![(1, num(1))], num(0))),
        ),
    ];
    for (what, ty, body) in cases {
        assert_eq!(define(g, ty, |_| body), "E-MALFORMED", "{what}");
    }
}

#[test]
fn a_number_case_is_no_evidence_for_termination_but_keeps_what_came_before() {
    let mut session = Session::new();
    let g = &mut session.elab.globals;
    let ty = pi(nat_ty(g), nat_ty(g));
    let call = |id: DefId, arg: Term| Term::app(Term::Def(id), arg);
    // `loop n` hidden in an arm, and in the default.
    assert_eq!(
        define(g, ty.clone(), |id| lam(num_case(
            0,
            vec![(404, call(id, Term::Var(0)))],
            num(0)
        ))),
        "E-TERMINATION"
    );
    assert_eq!(
        define(g, ty.clone(), |id| lam(num_case(
            0,
            vec![(404, num(0))],
            call(id, Term::Var(0))
        ))),
        "E-TERMINATION"
    );
    // A predecessor matched before the number case is still smaller inside
    // every arm and the default.
    let nat = nat(g);
    assert_eq!(
        define(g, ty, |id| lam(Term::Case(
            0,
            nat,
            vec![
                Branch {
                    names: vec![],
                    body: Rc::new(num(0)),
                },
                Branch {
                    names: vec!["m".into()],
                    body: Rc::new(num_case(
                        0,
                        vec![(3, call(id, Term::Var(0)))],
                        call(id, Term::Var(0))
                    )),
                },
            ]
            .into(),
        ))),
        "ok"
    );
}

#[test]
fn keys_and_default_are_part_of_the_hash() {
    let session = session_with(
        "
hitA : Nat -> Bool
hitA 404 = True
hitA _   = False

hitB : Nat -> Bool
hitB 405 = True
hitB _   = False

hitC : Nat -> Bool
hitC 404 = True
hitC _   = True

hitD : Nat -> Bool
hitD 404 = True
hitD _   = False
",
    );
    let g = &session.elab.globals;
    let hash = |name| def_hash(g, def(g, name)).unwrap().unwrap();
    assert_ne!(hash("hitA"), hash("hitB"));
    assert_ne!(hash("hitA"), hash("hitC"));
    // A control: the same body hashes the same.
    assert_eq!(hash("hitA"), hash("hitD"));
}

// Evaluation

/// The normal form of `value`, as printed by the reference.
fn normal(g: &Globals, level: usize, value: &Value) -> String {
    format!(
        "{:?}",
        reference::quote(g, level, value).expect("no limits")
    )
}

/// `f arg` by both evaluators, which must agree: its normal form.
fn call_both(g: &Globals, f: DefId, arg: &Value) -> String {
    let fast = value::apply(g, Value::Neutral(Head::Def(f), Vec::new()), arg.clone())
        .and_then(|v| value::force(g, v))
        .expect("no limits");
    let slow = reference::apply_icit(
        g,
        Value::Neutral(Head::Def(f), Vec::new()),
        arg.clone(),
        Icit::Explicit,
    )
    .and_then(|v| reference::force(g, v))
    .expect("no limits");
    let (fast, slow) = (normal(g, 1, &fast), normal(g, 1, &slow));
    assert_eq!(fast, slow, "the evaluators disagree");
    fast
}

fn plus(k: u64, base: Value) -> Value {
    Value::NatAdd(Rc::new(BigUint::from(k)), Rc::new(base))
}

#[test]
fn evaluation_follows_the_table() {
    with_stack(STACK, || {
        let session = session_with("hit : Nat -> Bool\nhit 404 = True\nhit _   = False\n");
        let g = &session.elab.globals;
        let hit = def(g, "hit");
        let bool_data = g.find_data("Bool").unwrap();
        let t = format!("{:?}", Term::Ctor(bool_data, 1, Vec::new()));
        let f = format!("{:?}", Term::Ctor(bool_data, 0, Vec::new()));
        let x = Value::var(0);
        let stuck = |arg: &Value| {
            let shown = call_both(g, hit, arg);
            assert!(shown.starts_with("App(Def"), "not stuck: {shown}");
        };
        let n = |k: u64| nat_value(BigUint::from(k));
        assert_eq!(call_both(g, hit, &n(404)), t);
        assert_eq!(call_both(g, hit, &n(403)), f);
        assert_eq!(call_both(g, hit, &n(405)), f);
        stuck(&x);
        stuck(&plus(404, x.clone()));
        assert_eq!(call_both(g, hit, &plus(405, x.clone())), f);
        stuck(&plus(403, x.clone()));
        // `0 + x` is just `x`.
        stuck(&plus(0, x.clone()));
        // `Succ` around `404 + x` is `405 + x`.
        let succ = Value::Ctor(nat(g), 1, vec![plus(404, x.clone())].into());
        assert_eq!(call_both(g, hit, &succ), f);
        // A metavariable in the tail: stuck, then decided once it's solved.
        let m = g.new_meta(span());
        let pending = plus(403, Value::Neutral(Head::Meta(m), Vec::new()));
        stuck(&pending);
        g.solve_meta(m, n(1));
        assert_eq!(call_both(g, hit, &pending), t);
        // A solved metavariable applied to an argument, inside a prefix.
        let m2 = g.new_meta(span());
        let id = value::eval(g, &[], &lam(Term::Var(0))).unwrap();
        g.solve_meta(m2, id);
        let applied = Value::Neutral(Head::Meta(m2), vec![Elim::App(n(4), Icit::Explicit)]);
        assert_eq!(call_both(g, hit, &plus(400, applied)), t);
    });
}

// The oracle

/// `term`'s case tree with every number case replaced by the nested `case`s
/// on `Zero` and `Succ` it stands for. Each copy of an arm or the default is
/// shifted past the predecessors bound on the way; the kernel's refinement
/// gives the matched variable its value on each path.
fn expand(g: &Globals, term: &Term) -> Term {
    match term {
        Term::Loc(_, t) => expand(g, t),
        Term::Lam(x, i, b) => Term::Lam(x.clone(), *i, Rc::new(expand(g, b))),
        Term::Case(ix, d, branches) => Term::Case(
            *ix,
            *d,
            branches
                .iter()
                .map(|b| Branch {
                    names: b.names.clone(),
                    body: Rc::new(expand(g, &b.body)),
                })
                .collect(),
        ),
        Term::NumCase(ix, arms, default) => {
            let arms: Vec<(BigUint, Term)> = arms
                .iter()
                .map(|a| ((*a.value).clone(), expand(g, &a.body)))
                .collect();
            chain(g, *ix, &arms, &expand(g, default), 0)
        }
        other => other.clone(),
    }
}

/// The `case` at depth `j`: the variable matched is `j` more than the
/// predecessor matched last (or the original variable, at depth 0).
fn chain(g: &Globals, ix: usize, arms: &[(BigUint, Term)], default: &Term, j: usize) -> Term {
    let last = arms.last().expect("a number").0.clone();
    let here = BigUint::from(j);
    let zero = arms
        .iter()
        .find(|(k, _)| *k == here)
        .map_or(default, |(_, body)| body)
        .shift(g, j, 0)
        .unwrap();
    let succ = if here == last {
        default.shift(g, j + 1, 0).unwrap()
    } else {
        chain(g, ix, arms, default, j + 1)
    };
    Term::Case(
        if j == 0 { ix } else { 0 },
        nat(g),
        vec![
            Branch {
                names: vec![],
                body: Rc::new(zero),
            },
            Branch {
                names: vec!["p".into()],
                body: Rc::new(succ),
            },
        ]
        .into(),
    )
}

fn has_num_case(term: &Term) -> bool {
    term.subterms().any(|(t, _)| matches!(t, Term::NumCase(..)))
}

/// Defines the expansion of `f` alongside it, which the kernel must accept.
fn define_expansion(g: &mut Globals, f: DefId) -> DefId {
    let def = g.def(f);
    let (ty, body) = (def.ty.clone(), expand(g, def.body.as_ref().unwrap()));
    let id = declare_def(g, &"expanded".into(), &ty, false, false, span()).unwrap();
    if let Err(d) = define_def(g, id, &body) {
        panic!("the expansion of `{}` doesn't check: {d:#?}", g.def(f).name);
    }
    id
}

/// An argument for a parameter: closed, or open.
#[derive(Clone, Debug)]
enum Arg {
    Nat(u64),
    Bool(bool),
    /// `k + x` for a fresh variable `x` (just `x` when `k` is 0).
    Open(u64),
}

/// `f args`, by the machine: `None` if it's stuck (stays a folded call).
fn run(g: &Globals, f: DefId, args: &[Arg]) -> Option<String> {
    let bool_data = g.find_data("Bool").unwrap();
    let mut value = Value::Neutral(Head::Def(f), Vec::new());
    for (i, arg) in args.iter().enumerate() {
        let arg = match arg {
            Arg::Nat(n) => nat_value(BigUint::from(*n)),
            Arg::Bool(b) => Value::Ctor(bool_data, usize::from(*b), Vec::new().into()),
            Arg::Open(0) => Value::var(i),
            Arg::Open(k) => plus(*k, Value::var(i)),
        };
        value = value::apply(g, value, arg).unwrap();
    }
    let value = value::force(g, value).unwrap();
    if matches!(value, Value::Neutral(Head::Def(_), _)) {
        return None;
    }
    Some(match as_nat(g, &value).unwrap() {
        Some(n) => n.to_string(),
        None => normal(g, args.len(), &value),
    })
}

/// A generated pattern.
#[derive(Clone, Debug)]
enum Pat {
    Num(u64),
    Var,
    Wild,
    Zero,
    Succ(Box<Pat>),
    Bool(bool),
    /// A variable in a `Bool` column (not one the right-hand side uses).
    BoolVar,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Col {
    Nat,
    Bool,
}

/// A generated definition: its columns, and its equations (patterns, and a
/// right-hand side: a number, or the value of the row's `i`th variable).
struct Generated {
    cols: Vec<Col>,
    rows: Vec<(Vec<Pat>, Rhs)>,
}

#[derive(Clone, Copy, Debug)]
enum Rhs {
    Number(u64),
    Var(usize),
}

/// Matches `pat` against `value`, collecting the values of `Nat` variables.
fn matches(pat: &Pat, value: &Arg, vars: &mut Vec<u64>) -> bool {
    match (pat, value) {
        (Pat::Var, Arg::Nat(n)) => {
            vars.push(*n);
            true
        }
        (Pat::Var | Pat::Wild | Pat::BoolVar, _) => true,
        (Pat::Num(k), Arg::Nat(n)) => k == n,
        (Pat::Zero, Arg::Nat(n)) => *n == 0,
        (Pat::Succ(p), Arg::Nat(n)) => *n > 0 && matches(p, &Arg::Nat(n - 1), vars),
        (Pat::Bool(b), Arg::Bool(v)) => b == v,
        _ => panic!("ill-typed generated pattern"),
    }
}

impl Generated {
    /// What the source rows say, tried top to bottom.
    fn expected(&self, args: &[Arg]) -> String {
        for (pats, rhs) in &self.rows {
            let mut vars = Vec::new();
            if pats.iter().zip(args).all(|(p, a)| matches(p, a, &mut vars)) {
                return match rhs {
                    Rhs::Number(n) => n.to_string(),
                    Rhs::Var(i) => vars[*i].to_string(),
                };
            }
        }
        panic!("the generated rows aren't exhaustive");
    }

    fn source(&self, name: &str) -> String {
        fn show(p: &Pat, vars: &mut usize, bools: &mut usize) -> String {
            match p {
                Pat::Num(k) => k.to_string(),
                Pat::Var => {
                    *vars += 1;
                    format!("x{}", *vars - 1)
                }
                Pat::BoolVar => {
                    *bools += 1;
                    format!("b{}", *bools - 1)
                }
                Pat::Wild => "_".into(),
                Pat::Zero => "Zero".into(),
                Pat::Succ(q) => format!("(Succ {})", show(q, vars, bools)),
                Pat::Bool(true) => "True".into(),
                Pat::Bool(false) => "False".into(),
            }
        }
        let tys: Vec<&str> = self
            .cols
            .iter()
            .map(|c| if *c == Col::Nat { "Nat" } else { "Bool" })
            .collect();
        let mut out = format!("{name} : {} -> Nat\n", tys.join(" -> "));
        for (pats, rhs) in &self.rows {
            let (mut vars, mut bools) = (0, 0);
            let shown: Vec<String> = pats
                .iter()
                .map(|p| show(p, &mut vars, &mut bools))
                .collect();
            let rhs = match rhs {
                Rhs::Number(n) => n.to_string(),
                Rhs::Var(i) => format!("x{i}"),
            };
            out.push_str(&format!("{name} {} = {rhs}\n", shown.join(" ")));
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

/// The largest number generated patterns use.
const MAX_KEY: u64 = 6;

fn generate(rng: &mut Rng) -> Generated {
    let cols: Vec<Col> = (0..1 + rng.below(3))
        .map(|_| {
            if rng.below(3) == 0 {
                Col::Bool
            } else {
                Col::Nat
            }
        })
        .collect();
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
                Col::Nat => {
                    // Mostly numbers, so most columns are number cases.
                    let p = match rng.below(10) {
                        0 => Pat::Wild,
                        1 => Pat::Var,
                        2 => Pat::Zero,
                        3 => Pat::Succ(Box::new(Pat::Var)),
                        4 => Pat::Succ(Box::new(Pat::Succ(Box::new(Pat::Var)))),
                        5 => Pat::Succ(Box::new(Pat::Num(rng.below(MAX_KEY)))),
                        _ => Pat::Num(rng.below(MAX_KEY + 1)),
                    };
                    vars += count_vars(&p);
                    p
                }
            })
            .collect();
        let rhs = if vars > 0 && rng.below(2) == 0 {
            Rhs::Var(rng.below(vars as u64) as usize)
        } else {
            Rhs::Number(100 + r)
        };
        rows.push((pats, rhs));
    }
    rows.push((vec![Pat::Wild; cols.len()], Rhs::Number(999)));
    Generated { cols, rows }
}

fn count_vars(p: &Pat) -> usize {
    match p {
        Pat::Var => 1,
        Pat::Succ(q) => count_vars(q),
        _ => 0,
    }
}

/// Every combination of `choices` for each column.
fn product(cols: &[Col], choices: impl Fn(Col) -> Vec<Arg>) -> Vec<Vec<Arg>> {
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
        Col::Nat => (0..=MAX_KEY + 3).map(Arg::Nat).collect(),
        Col::Bool => vec![Arg::Bool(false), Arg::Bool(true)],
    }
}

fn open(c: Col) -> Vec<Arg> {
    match c {
        Col::Nat => vec![
            Arg::Nat(2),
            Arg::Open(0),
            Arg::Open(1),
            Arg::Open(MAX_KEY),
            Arg::Open(MAX_KEY + 1),
        ],
        Col::Bool => vec![Arg::Bool(true), Arg::Open(0)],
    }
}

/// Generated pattern matches, compiled with number cases: they agree with the
/// source rows, with the old compilation (`Succ` chains), and with their
/// expansion, which the kernel accepts.
#[test]
fn generated_matches_agree_with_the_rows_the_old_compilation_and_the_expansion() {
    with_stack(STACK, || {
        let mut rng = Rng(0x5717_c4b0_e7a1_4040);
        let mut num_cases = 0;
        for i in 0..300 {
            let generated = generate(&mut rng);
            let name = format!("f{i}");
            let text = generated.source(&name);
            let mut new = session_with(&text);
            let mut old = Session::new();
            old.elab.numbers_as_succ = true;
            load(&mut old, &text);
            let f = def(&new.elab.globals, &name);
            let f_old = def(&old.elab.globals, &name);
            if has_num_case(new.elab.globals.def(f).body.as_ref().unwrap()) {
                num_cases += 1;
            }
            assert!(!has_num_case(
                old.elab.globals.def(f_old).body.as_ref().unwrap()
            ));
            let g = &mut new.elab.globals;
            let expanded = define_expansion(g, f);
            for args in product(&generated.cols, closed) {
                let expected = generated.expected(&args);
                let what = || format!("{text}on {args:?}");
                assert_eq!(run(g, f, &args).as_deref(), Some(&*expected), "{}", what());
                assert_eq!(
                    run(g, expanded, &args).as_deref(),
                    Some(&*expected),
                    "{}",
                    what()
                );
                assert_eq!(
                    run(&old.elab.globals, f_old, &args).as_deref(),
                    Some(&*expected),
                    "old: {}",
                    what()
                );
            }
            for args in product(&generated.cols, open) {
                assert_eq!(
                    run(g, f, &args),
                    run(g, expanded, &args),
                    "{text}on {args:?}"
                );
            }
        }
        assert!(num_cases > 100, "only {num_cases} number cases generated");
    });
}

/// The examples in the proposal, and the number cases in the prelude and the
/// examples directory: each expansion checks.
#[test]
fn every_number_case_in_the_examples_has_an_expansion_that_checks() {
    with_stack(STACK, || {
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/accept");
        let mut expanded = 0;
        for name in ["number-patterns.sw", "nested-patterns.sw"] {
            let text = std::fs::read_to_string(root.join(name)).unwrap();
            let mut session = session_with(&text);
            let g = &mut session.elab.globals;
            for i in 0..g.defs.len() {
                let id = DefId(i);
                let small = g.def(id).body.as_ref().is_some_and(|b| {
                    has_num_case(b)
                        && b.subterms().all(|(t, _)| match t {
                            Term::NumCase(_, arms, _) => {
                                arms.iter().all(|a| *a.value <= BigUint::from(64u32))
                            }
                            _ => true,
                        })
                });
                if small {
                    define_expansion(g, id);
                    expanded += 1;
                }
            }
        }
        // The prelude's `isSpaceCode` and `digitChar`, and the examples.
        assert!(expanded >= 5, "only {expanded} expanded");
    });
}
