//! Deeply nested programs are an `E-RESOURCE` error, never a crash: every
//! pass that recurses over syntax or terms checks it has stack left first
//! (docs/proposals/stack-safe-evaluation.md, step 4).
//!
//! A stack overflow aborts the whole process, so each test runs in a child
//! process (this test binary again, running just that test): a crash shows up
//! as that test failing. They run with the default limits, in test threads
//! (2 MiB of stack).

use std::process::Command;
use std::rc::Rc;

use stitchwort_core::check as kernel;
use stitchwort_core::hash::def_hash;
use stitchwort_core::{DefId, Limits, ResourceError, Term, pretty};
use stitchwort_driver::driver::Session;
use stitchwort_syntax::{DEFAULT_STACK, SourceMap, parse_module_within};

/// Set in a child process.
const CHILD: &str = "STITCHWORT_NESTING_CHILD";

/// Runs `body` in a child process, as the test called `name`, and checks it
/// passed. A stack overflow in the child is a failure here.
fn isolated(name: &str, body: impl FnOnce()) {
    if std::env::var_os(CHILD).is_some() {
        body();
        return;
    }
    let out = Command::new(std::env::current_exe().expect("the test binary"))
        .args([name, "--exact", "--nocapture", "--test-threads=1"])
        .env(CHILD, "1")
        .output()
        .expect("can run the test binary");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success() && stdout.contains("1 passed"),
        "the child process failed ({}):\n{stdout}\n{stderr}",
        out.status
    );
}

/// What loading a program gave: the first error's code, if any.
fn first_error(session: &mut Session, name: &str, text: &str) -> Option<&'static str> {
    session.load(name, text).err().map(|ds| ds[0].code)
}

/// Finds the smallest `n` for which `program(name, n)` runs out of
/// resources, by doubling and then bisecting: every smaller size checks
/// without errors. Then checks sizes just past it and far past it run out
/// too, rather than crashing. Returns the threshold. Each program is loaded
/// into the same session, under a new `name`.
fn just_past_the_limit(program: impl Fn(&str, usize) -> String) -> usize {
    let mut session = Session::new();
    let mut loads = 0;
    let mut ran_out = |n: usize| {
        loads += 1;
        let name = format!("p{loads}");
        println!("size {n}");
        match first_error(&mut session, &format!("{name}.sw"), &program(&name, n)) {
            None => false,
            Some("E-RESOURCE") => true,
            Some(code) => panic!("size {n}: {code}"),
        }
    };
    let mut hi = 16;
    while !ran_out(hi) {
        hi *= 2;
        assert!(hi < 1 << 24, "never ran out");
    }
    let mut lo = hi / 2;
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if ran_out(mid) {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    for n in [hi + 1, hi + 2, hi + 10, 2 * hi, 10 * hi, 100_000] {
        assert!(ran_out(n), "size {n} checks, but {hi} doesn't");
    }
    println!("threshold {hi}");
    hi
}

fn nested(n: usize, around: &str, inner: &str) -> String {
    format!("{}{inner}{}", around.repeat(n), ")".repeat(n))
}

#[test]
fn nested_applications() {
    isolated("nested_applications", || {
        just_past_the_limit(|x, n| {
            format!(
                "{x}f : Nat -> Nat\n{x}f n = n\n\n{x} : Nat\n{x} = {}\n",
                nested(n, &format!("{x}f ("), "0")
            )
        });
    });
}

#[test]
fn nested_parentheses() {
    isolated("nested_parentheses", || {
        just_past_the_limit(|x, n| format!("{x} : Nat\n{x} = {}\n", nested(n, "(", "0")));
    });
}

#[test]
fn nested_functions_and_function_types() {
    isolated("nested_functions_and_function_types", || {
        just_past_the_limit(|x, n| {
            format!(
                "{x} : {}Nat\n{x} = {}0\n",
                "Nat -> ".repeat(n),
                "\\y -> ".repeat(n)
            )
        });
    });
}

/// `++` is right-associative: the parser recurses for each one.
#[test]
fn long_appends() {
    isolated("long_appends", || {
        just_past_the_limit(|x, n| {
            format!("{x} : List Nat\n{x} = {}\n", vec!["[1]"; n].join(" ++ "))
        });
    });
}

/// `+` is left-associative: the parser loops, building syntax as deep as
/// the sum is long, which the elaborator recurses over.
#[test]
fn long_sums() {
    isolated("long_sums", || {
        just_past_the_limit(|x, n| format!("{x} : Nat\n{x} = {}\n", vec!["1"; n].join(" + ")));
    });
}

/// A block's lines nest: each `let` scopes over the rest.
#[test]
fn long_blocks() {
    isolated("long_blocks", || {
        just_past_the_limit(|x, n| {
            let lines: String = (0..n).map(|i| format!("  let v{i} = {i}\n")).collect();
            format!("{x} : Nat\n{x} =\n{lines}  0\n")
        });
    });
}

/// Literals are flat to parse, but are long chains of constructors once
/// elaborated.
#[test]
fn long_list_literals() {
    isolated("long_list_literals", || {
        just_past_the_limit(|x, n| {
            format!("{x} : List Nat\n{x} = [{}]\n", vec!["1"; n].join(", "))
        });
    });
}

#[test]
fn long_text_literals() {
    isolated("long_text_literals", || {
        just_past_the_limit(|x, n| format!("{x} : Text\n{x} = \"{}\"\n", "a".repeat(n)));
    });
}

/// Only parsed: compiling nested patterns takes time and memory that grow
/// steeply with their depth (TODO.md), long before the stack runs out.
#[test]
fn nested_patterns() {
    isolated("nested_patterns", || {
        let mut sources = SourceMap::new();
        for n in [100, 1_000, 10_000, 100_000] {
            let text = format!("g {} = 0\n", nested(n, "(Cons _ ", "_"));
            let file = sources.add("patterns.sw", &text);
            match parse_module_within(file, &text, DEFAULT_STACK) {
                Ok(_) => assert!(n < 100_000, "{n} parses"),
                Err(ds) => assert_eq!(ds[0].code, "E-RESOURCE", "{n}"),
            }
        }
    });
}

/// `f (f (… x))`, `depth` deep, as a core term.
fn deep_term(f: Term, x: Term, depth: usize) -> Term {
    let mut term = x;
    for _ in 0..depth {
        term = Term::app(f.clone(), term);
    }
    term
}

/// A session with `f : Nat -> Nat` and an export `g : Nat -> Nat`, whose
/// body is then replaced (without checking it) by `\n -> f (f (… n))`.
fn with_deep_definition(depth: usize) -> (Session, DefId) {
    let mut session = Session::new();
    session
        .load(
            "deep.sw",
            "f : Nat -> Nat\nf n = n\n\nexport\ng : Nat -> Nat\ng n = n\n",
        )
        .expect("checks");
    let g = &mut session.elab.globals;
    let f = DefId(g.defs.iter().position(|d| &*d.name == "f").unwrap());
    let id = DefId(g.defs.len() - 1);
    let body = deep_term(Term::Def(f), Term::Var(0), depth);
    g.defs[id.0].body = Some(Rc::new(Term::Lam(
        "n".into(),
        stitchwort_core::Icit::Explicit,
        Rc::new(body),
    )));
    (session, id)
}

/// Terms built directly, for the passes after the elaborator: each would
/// otherwise only see what the passes before it could handle.
#[test]
fn deep_terms_in_later_passes() {
    isolated("deep_terms_in_later_passes", || {
        let (session, id) = with_deep_definition(1_000_000);
        let g = &session.elab.globals;
        let body = g.def(id).body.clone().unwrap();
        {
            let _op = g.budget.operation(Limits::default());
            let def = g.def(id);
            let mut cx = kernel::Ctx::new(g, def.span);
            let e = kernel::check(&mut cx, &body, &def.ty_value).unwrap_err();
            assert_eq!(e.code, "E-RESOURCE");
            assert!(e.message.contains("type checker"), "{}", e.message);
        }
        {
            let _op = g.budget.operation(Limits::default());
            assert_eq!(
                pretty::term_in_full(g, &[], &body),
                Err(ResourceError::Nesting("printer"))
            );
        }
        {
            // For an error message, the part it can't reach is `…`.
            let _op = g.budget.operation(Limits::default());
            assert!(pretty::term(g, &[], &body).contains('…'));
        }
        {
            let _op = g.budget.operation(Limits::default());
            let span = g.def(id).span;
            let e = stitchwort_core::termination::check(g, &body, id, "g", span).unwrap_err();
            assert_eq!(e.code, "E-RESOURCE");
            assert!(e.message.contains("termination"), "{}", e.message);
        }
        {
            // Hashing walks a term with a work list, so any depth hashes.
            let _op = g.budget.operation(Limits::default());
            assert!(def_hash(g, id).unwrap().is_some());
        }
        let e = session.extract().err().expect("too deep to generate");
        assert_eq!(e.code, "E-RESOURCE");
        assert!(e.message.contains("JavaScript"), "{}", e.message);
        assert_eq!(e.labels.len(), 1, "points at the definition");
    });
}

/// Hashing a definition hashes what it refers to first: a long enough chain
/// of definitions runs out.
#[test]
fn long_chains_of_definitions_to_hash() {
    isolated("long_chains_of_definitions_to_hash", || {
        let (mut session, _) = with_deep_definition(1);
        let g = &mut session.elab.globals;
        let first = g.defs.len() - 1;
        for i in 0..1_000_000 {
            let mut def = stitchwort_core::globals::Def {
                name: format!("chain{i}").into(),
                ..clone_def(g.def(DefId(first)))
            };
            def.body = Some(Rc::new(Term::Def(DefId(g.defs.len() - 1))));
            g.defs.push(def);
        }
        let g = &session.elab.globals;
        let _op = g.budget.operation(Limits::default());
        assert_eq!(
            def_hash(g, DefId(g.defs.len() - 1)),
            Err(ResourceError::Nesting("hasher"))
        );
    });
}

fn clone_def(def: &stitchwort_core::globals::Def) -> stitchwort_core::globals::Def {
    stitchwort_core::globals::Def {
        name: def.name.clone(),
        ty: def.ty.clone(),
        ty_value: def.ty_value.clone(),
        body: def.body.clone(),
        arity: def.arity,
        theorem: def.theorem,
        export: false,
        validators: Vec::new(),
        span: def.span,
    }
}

/// An expression typed in, too deep to parse or to print.
#[test]
fn deep_expressions_to_evaluate() {
    isolated("deep_expressions_to_evaluate", || {
        let mut session = Session::new();
        let text = nested(1_000_000, "Succ (", "0");
        let error = session.parse_expression("<input>", &text).unwrap_err();
        assert_eq!(error.code, "E-RESOURCE");
        // `S (S (… Z))` for a data type without a compact form parses (the
        // nesting is built by evaluation) but is too deep to print in full.
        session
            .load(
                "unary.sw",
                "type Unary : Type =\n  | Z\n  | S (u : Unary)\n\n\
                 deep : Nat -> Unary\ndeep Zero = Z\ndeep (Succ n) = S (deep n)\n",
            )
            .expect("checks");
        let expr = session.parse_expression("<input>", "deep 100000").unwrap();
        let error = session.elab.eval_expr(&expr).unwrap_err();
        assert_eq!(error.code, "E-RESOURCE");
        assert!(error.message.contains("printer"), "{}", error.message);
    });
}
