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
use stitchwort_core::ProofMark;

use stitchwort_core::check as kernel;
use stitchwort_core::hash::def_hash;
use stitchwort_core::{DefId, Limits, ResourceError, Term, pretty};
use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_elab::search::Item;
use stitchwort_syntax::{DEFAULT_STACK, SourceMap, parse_module_within};

/// Set in a child process.
const CHILD: &str = "STITCHWORT_NESTING_CHILD";

/// Runs `body` in a child process, as the test called `name` (of this
/// module), and checks it passed. A stack overflow in the child is a failure here.
fn isolated(name: &str, body: impl FnOnce()) {
    if std::env::var_os(CHILD).is_some() {
        body();
        return;
    }
    let out = Command::new(std::env::current_exe().expect("the test binary"))
        .args([
            &format!("nesting::{name}"),
            "--exact",
            "--nocapture",
            "--test-threads=1",
        ])
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
    // The child's output would otherwise be lost: pass on the lines its test
    // writes (`size …` and `threshold …` with `--nocapture`), without
    // libtest's own lines. libtest prints `running 1 test`, then the test's
    // name followed by ` ... ` with the test's first output on the same line,
    // and at the end a bare `ok` and `test result: …`.
    let prefix = format!("test nesting::{name} ... ");
    for line in stdout.lines() {
        let line = line.strip_prefix(&prefix).unwrap_or(line);
        let libtest = line.is_empty()
            || line == "ok"
            || line.starts_with("running ")
            || line.starts_with("test result:");
        if !libtest {
            println!("{line}");
        }
    }
}

/// A stack guard of `kib` KiB as measured with release frames. Debug frames
/// are about 5 times bigger (measured: 4 times is too little for either
/// test below, 5 just enough), so the same programs need a bigger guard to
/// mean the same thing. 6 times 320 KiB still fits the 2 MiB test thread.
fn guard(kib: usize) -> usize {
    let debug_factor = if cfg!(debug_assertions) { 6 } else { 1 };
    kib * 1024 * debug_factor
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
                "def {x}f (n : Nat) : Nat := n\n\ndef {x} : Nat := {}\n",
                nested(n, &format!("{x}f ("), "0")
            )
        });
    });
}

/// The program `def x : Nat := f (f (… 0))`, `n` levels deep, where each
/// application is checked against a known type.
fn nested_applications_program(n: usize) -> String {
    format!(
        "def f (n : Nat) : Nat := n\n\ndef x : Nat := {}\n",
        nested(n, "f (", "0")
    )
}

/// Whether `n` nested applications check with a stack guard of `bytes`.
fn checks_within(n: usize, bytes: usize) -> bool {
    let mut session = Session::new();
    session.elab.options.limits = Limits {
        stack: bytes,
        ..Limits::default()
    };
    first_error(&mut session, "x.sw", &nested_applications_program(n)).is_none()
}

/// Nested applications checked against a known type (`f (f (… 0))` where a
/// `Nat` is expected) take about 7.8 KiB of stack a level natively (SW-4849;
/// 5.1 at SW-3172, which the test was written for): 30 of them check under
/// the playground's guard of 320 KiB (`crates/web/build.rs`), where the
/// limit is 38 natively. In the playground's WebAssembly, whose frames are
/// smaller (about 2.2 KiB a level), the guard allows 99 levels, in Chrome 158
/// and Firefox 160 alike (SW-4849); 30 is well inside both limits.
#[test]
fn nested_applications_under_the_playground_guard() {
    isolated("nested_applications_under_the_playground_guard", || {
        assert!(
            checks_within(30, guard(320)),
            "30 nested applications no longer check under the playground's guard \
             (SW-4849: 38 did)"
        );
    });
}

/// The native stack a nested application takes, as the difference between
/// the smallest guards that let 30 and 10 levels check, per level. Frames
/// grew from 5.1 KiB a level (SW-3172) to 7.8 (SW-4849) over many small
/// changes, none of which a test noticed until the playground's limit
/// slipped; this pins the figure. If it fails, a recent change made the
/// elaborator's recursion over arguments (`check_arg`, `check_value` and
/// what they inline) use more stack: look at the frame sizes with `task
/// stack:peak` and put the rarer arms out of line, or, if the growth is
/// wanted, raise this limit and `nested_applications_under_the_playground_guard`
/// together with the browser figures remeasured (SW-4849).
#[test]
fn nested_applications_stack_per_level() {
    isolated("nested_applications_stack_per_level", || {
        // Smallest guard in KiB under which `n` levels check.
        let smallest = |n: usize| {
            let (mut lo, mut hi) = (0, guard(1024) / 1024);
            assert!(checks_within(n, hi * 1024), "{n} levels need over 1 MiB");
            while hi - lo > 1 {
                let mid = (lo + hi) / 2;
                if checks_within(n, mid * 1024) {
                    hi = mid;
                } else {
                    lo = mid;
                }
            }
            hi
        };
        let (few, many) = (smallest(10), smallest(30));
        let debug_factor = guard(1) / 1024;
        let per_level = (many - few) as f64 / 20.0 / debug_factor as f64;
        println!("stack per level {per_level:.2} KiB ({few} KiB for 10, {many} for 30)");
        assert!(
            per_level < 9.0,
            "nested applications take {per_level:.1} KiB of stack a level (7.8 when SW-4849 \
             measured it; the limit is 9): the playground's 320 KiB guard now allows fewer \
             levels. Find which change made the elaborator's frames bigger (`task stack:peak`), \
             or, if wanted, raise this limit and remeasure the browsers (SW-4849)"
        );
    });
}

/// Two calls of one opaque definition, each 88 levels deep, compared under
/// the playground's guard (SW-3172, SW-3179). The calls are built by
/// evaluation (`up k y` is `f (up k y')`), so checking the program takes no
/// nesting of its own and the depth is all the unifier's: it compares the
/// calls by their arguments, one nested comparison a level.
///
/// Measured in release: 100 levels pass, 105 run out; before SW-3172's
/// smaller unifier frames 72 passed and 76 ran out. 88 is past the old
/// limit and 12% under the new one.
#[test]
fn nested_calls_of_one_definition_unify_under_the_playground_guard() {
    isolated(
        "nested_calls_of_one_definition_unify_under_the_playground_guard",
        || {
            let mut session = Session::new();
            session.elab.options.limits = Limits {
                stack: guard(320),
                ..Limits::default()
            };
            // `up2` differs from `up` only in a `+ 0` that conversion
            // removes, so the two sides are never the same term.
            let program = "opaque def f (n : Nat) : Nat := n\n\n\
                 def up : Nat -> Nat -> Nat\n  | 0, y => y\n  | Succ k, y => f (up k y)\n\n\
                 def up2 : Nat -> Nat -> Nat\n  | 0, y => y\n  | Succ k, y => f (up2 k (y + 0))\n\n\
                 theorem t (y : Nat) : up 88 y = up2 88 y := byComputing\n";
            assert_eq!(first_error(&mut session, "x.sw", program), None);
        },
    );
}

#[test]
fn nested_parentheses() {
    isolated("nested_parentheses", || {
        just_past_the_limit(|x, n| format!("def {x} : Nat := {}\n", nested(n, "(", "0")));
    });
}

#[test]
fn nested_functions_and_function_types() {
    isolated("nested_functions_and_function_types", || {
        just_past_the_limit(|x, n| {
            format!(
                "def {x} : {}Nat := {}0\n",
                "Nat -> ".repeat(n),
                "y => ".repeat(n)
            )
        });
    });
}

/// `++` is right-associative: the parser recurses for each one.
#[test]
fn long_appends() {
    isolated("long_appends", || {
        just_past_the_limit(|x, n| {
            format!("def {x} : List Nat := {}\n", vec!["[1]"; n].join(" ++ "))
        });
    });
}

/// `+` is left-associative: the parser loops, building syntax as deep as
/// the sum is long, which the elaborator recurses over.
#[test]
fn long_sums() {
    isolated("long_sums", || {
        just_past_the_limit(|x, n| format!("def {x} : Nat := {}\n", vec!["1"; n].join(" + ")));
    });
}

/// A long left-nested chain that runs out names its length and how to write
/// it without one (SW-2020, D2844).
///
/// Which pass runs out first depends on the build's frame sizes: the parser
/// (and the lowering after it) may run out before the elaborator or kernel,
/// and the parser's error has no chain note. So parse with a roomy stack,
/// then tighten the session's limit before checking: the run-out is after
/// parsing, and the note comes from the elaborator or the kernel (SW-4850).
#[test]
fn long_chain_notes() {
    isolated("long_chain_notes", || {
        // Room for the parser on any build, even with debug frames.
        const ROOMY: usize = 32 * 1024 * 1024;
        with_stack(ROOMY, || {
            for (op, note) in [
                (
                    "+",
                    "this sum has 2,000 terms; write long sums as a list, `[…].sum`",
                ),
                (
                    "*",
                    "this product has 2,000 terms; write long products as a list, `[…].product`",
                ),
                ("-", "this chain has 2,000 terms; split it with `let`"),
            ] {
                let mut session = Session::for_stack(ROOMY);
                let chain = vec!["1"; 2_000].join(&format!(" {op} "));
                let program = format!("def x : Nat := {chain}\n");
                let file = session.sources.add("x.sw", &program);
                let module = parse_module_within(file, &program, session.elab.options.limits.stack)
                    .expect("a long chain parses with room");
                // Tight enough that checking runs out, as it did before.
                session.elab.options.limits.stack = guard(320);
                let errors = session.elab.elaborate_module(&module);
                let e = errors.first().expect("runs out");
                assert_eq!(e.code, "E-RESOURCE", "{op}");
                assert!(
                    e.message.contains("nested too deeply"),
                    "{op}: {}",
                    e.message
                );
                assert_eq!(
                    e.notes.iter().filter(|n| *n == note).count(),
                    1,
                    "{op}: {}\n{:?}",
                    e.message,
                    e.notes
                );
            }
        });
    });
}

/// A block's lines nest: each `let` scopes over the rest.
#[test]
fn long_blocks() {
    isolated("long_blocks", || {
        just_past_the_limit(|x, n| {
            let lines: String = (0..n).map(|i| format!("  let v{i} := {i}\n")).collect();
            format!("def {x} : Nat :=\n{lines}  0\n")
        });
    });
}

/// A pattern `let` is a `match` whose alternative holds the rest of the
/// block (docs/proposals/syntax-conveniences.md §5.5), so those nest too.
#[test]
fn long_pattern_blocks() {
    isolated("long_pattern_blocks", || {
        just_past_the_limit(|x, n| {
            let lines: String = (0..n)
                .map(|i| format!("  let (v{i}, w{i}) := (1, {i})\n"))
                .collect();
            format!("def {x} : Nat :=\n{lines}  0\n")
        });
    });
}

/// Literals are flat to parse, but would be chains of constructors as deep as
/// they are long once elaborated: a long one is cut into short chains joined
/// by a balanced tree of `append`s, so 100,000 elements check and run
/// (SW-62).
#[test]
fn long_list_literals() {
    isolated("long_list_literals", || {
        let mut session = Session::new();
        if let Err(ds) = session.load("xs.sw", &list_program(100_000)) {
            panic!("{}", ds[0].message);
        }
        let main = session.main().expect("`main` has the right type");
        let mut output = Vec::new();
        session
            .run_main(&main, &mut &b""[..], &mut output)
            .expect("runs");
        assert_eq!(String::from_utf8(output).unwrap(), "100000\n");
    });
}

/// The same under a small stack guard (the playground's is 256 KiB, but its
/// frames are smaller than native ones; see `crates/web/build.rs`), where a
/// single chain of a few hundred elements runs out.
#[test]
fn long_list_literals_with_a_small_guard() {
    isolated("long_list_literals_with_a_small_guard", || {
        let mut session = Session::new();
        session.elab.options.limits = Limits {
            stack: guard(256),
            ..Limits::default()
        };
        if let Err(ds) = session.load("xs.sw", &list_program(100_000)) {
            panic!("{}", ds[0].message);
        }
    });
}

/// A program with a list literal of `n` ones, whose `main` prints its length.
fn list_program(n: usize) -> String {
    format!(
        "import Std (List)\n\ndef xs : List Nat := [{}]\n\ndef main () : {{IO}} () := IO.print (List.length xs).toText\n",
        vec!["1"; n].join(", ")
    )
}

/// A text literal is one compact list in the term however long it is
/// (docs/proposals/compact-text.md, stage 2), so it doesn't nest: four
/// million characters check.
#[test]
fn long_text_literals() {
    isolated("long_text_literals", || {
        let mut session = Session::new();
        let text = format!("def t : Text := \"{}\"\n", "a".repeat(4_000_000));
        assert_eq!(first_error(&mut session, "t.sw", &text), None);
    });
}

/// Only parsed: compiling nested patterns takes time and memory that grow
/// steeply with their depth (TODO.md), long before the stack runs out.
#[test]
fn nested_patterns() {
    isolated("nested_patterns", || {
        let mut sources = SourceMap::new();
        for n in [100, 1_000, 10_000, 100_000] {
            let text = format!(
                "def g : Nat -> Nat\n  | {} => 0\n",
                nested(n, "(Cons _ ", "_")
            );
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
/// body is then replaced (without checking it) by `n => f (f (… n))`.
fn with_deep_definition(depth: usize) -> (Session, DefId) {
    with_deep_definition_in(Session::new(), depth)
}

/// [`with_deep_definition`] in `session`, which may already be recording
/// navigation: recording has to be on before the file loads to index it.
fn with_deep_definition_in(mut session: Session, depth: usize) -> (Session, DefId) {
    session
        .load(
            "deep.sw",
            "def f (n : Nat) : Nat := n\n\nexport def g (n : Nat) : Nat := n\n",
        )
        .expect("checks");
    let g = &mut session.elab.kernel;
    let f = DefId(
        g.env
            .defs()
            .iter()
            .position(|d| &**d.name() == "f")
            .unwrap(),
    );
    let id = DefId(g.env.defs().len() - 1);
    let body = deep_term(Term::Def(f), Term::Var(0), depth);
    g.env
        .def_mut_for_tests(id)
        .set_body_unchecked_for_tests(Some(Rc::new(Term::Lam(
            "n".into(),
            stitchwort_core::Icit::Explicit,
            Rc::new(body),
            ProofMark::Unknown,
        ))));
    (session, id)
}

/// [`with_deep_definition`], but the deep term is the definition's type
/// `(n : Nat) → f (f (… n)) = n`, installed with its evaluation: the
/// closing search, hashing and the printer all walk a lemma's type.
fn with_deep_type(depth: usize) -> (Session, DefId) {
    let (session, id) = with_deep_definition(1);
    with_deep_type_of(session, id, depth)
}

/// [`with_deep_type`] for definition `id` of `session`.
fn with_deep_type_of(mut session: Session, id: DefId, depth: usize) -> (Session, DefId) {
    let g = &mut session.elab.kernel;
    let f = DefId(
        g.env
            .defs()
            .iter()
            .position(|d| &**d.name() == "f")
            .unwrap(),
    );
    let Term::Pi(_, _, nat, _, _) = g.env.defs()[id.0].ty().strip_loc() else {
        panic!("a function type")
    };
    let nat = nat.clone();
    let deep = deep_term(Term::Def(f), Term::Var(0), depth);
    let eq = Term::Eq(Some(nat.clone()), Rc::new(deep), Rc::new(Term::Var(0)));
    let ty = Term::Pi(
        "n".into(),
        stitchwort_core::Icit::Explicit,
        nat,
        Rc::new(eq),
        ProofMark::Unknown,
    );
    let value = {
        let ev = g.ev();
        let _op = ev.machine.budget.operation(Limits::default());
        stitchwort_core::value::eval(&ev, &[], &ty).expect("evaluates")
    };
    g.env
        .def_mut_for_tests(id)
        .set_type_unchecked_for_tests(ty, value);
    (session, id)
}

/// [`with_deep_type`], recording navigation from the file's load: the
/// definition's deep signature is in the index for a hover.
fn with_navigable_deep_type(depth: usize) -> (Session, DefId) {
    let mut session = Session::new();
    session.elab.enable_navigation();
    let (session, id) = with_deep_definition_in(session, 1);
    with_deep_type_of(session, id, depth)
}

/// A hover's type, as deep as a value is (`Nat.iterate 2000 f x`), is
/// printed only as far as the text it may be (SW-4868): the playground's
/// stack is far smaller than the depth of the term.
#[test]
fn hover_prints_only_what_it_shows() {
    isolated("hover_prints_only_what_it_shows", || {
        let (session, _) = with_deep_definition(1);
        let g = &session.elab.ev();
        let f = DefId(
            g.env
                .defs()
                .iter()
                .position(|d| &**d.name() == "f")
                .unwrap(),
        );
        let deep = deep_term(Term::Def(f), Term::Var(0), 100_000);
        // Natively the stack guard would stop a print that goes this deep
        // too; in the browser it doesn't (the engine's stack is not the
        // one it measures), so the printer's own bound is what keeps it off
        // the end there, and this checks what it shows.
        let text = {
            let _op = g.machine.budget.operation(Limits::default());
            pretty::term_shortened(g, &["x".into()], &deep)
        };
        assert!(text.contains('…'), "{text}");
        assert!(text.chars().count() <= 241, "{}", text.chars().count());
        // A term that fits is written in full.
        let small = deep_term(Term::Def(f), Term::Var(0), 3);
        let _op = g.machine.budget.operation(Limits::default());
        assert_eq!(
            pretty::term_shortened(g, &["x".into()], &small),
            "f (f (f x))"
        );
    });
}

/// A definition's signature, as deep as a value's type is, is printed only
/// as far as a hover shows it too (SW-4874): the header is cut with `…`,
/// not printed at any depth.
#[test]
fn hover_cuts_a_deep_signature() {
    isolated("hover_cuts_a_deep_signature", || {
        let (session, _) = with_navigable_deep_type(100_000);
        let index = session.elab.navigation_index(&|_, _| true);
        let symbol = index
            .symbols
            .iter()
            .find(|s| s.name.rsplit('.').next() == Some("g"))
            .expect("the definition is indexed");
        let header = symbol.header.as_deref().expect("a function's header");
        assert!(header.contains('…'), "{header}");
        assert!(
            header.chars().count() <= 4_001,
            "{}",
            header.chars().count()
        );
    });
}

/// Terms built directly, for the passes after the elaborator: each would
/// otherwise only see what the passes before it could handle.
#[test]
fn deep_terms_in_later_passes() {
    isolated("deep_terms_in_later_passes", || {
        let (session, id) = with_deep_definition(1_000_000);
        let g = &session.elab.ev();
        let body = g.def(id).body().unwrap();
        {
            // An argument that is itself an application is checked in a
            // loop, not a level of the stack (SW-3174), so the kernel
            // takes this depth.
            let _op = g.machine.budget.operation(Limits::default());
            let def = g.def(id);
            let mut cx = kernel::Ctx::new(g, def.span());
            assert!(kernel::check(&mut cx, body, def.ty_value()).is_ok());
        }
        {
            // With a location around each argument, each level is a call of
            // `check` again: the kernel runs out rather than crashing.
            let _op = g.machine.budget.operation(Limits::default());
            let def = g.def(id);
            let Term::Lam(_, _, inner, _) = &**body else {
                panic!("a function")
            };
            let Term::App(f, _, _) = &**inner else {
                panic!("an application")
            };
            let mut located = Term::Var(0);
            for _ in 0..1_000_000 {
                located = Term::app((**f).clone(), Term::Loc(def.span(), Rc::new(located)));
            }
            let located = Term::Lam(
                "n".into(),
                stitchwort_core::Icit::Explicit,
                Rc::new(located),
                ProofMark::Unknown,
            );
            let mut cx = kernel::Ctx::new(g, def.span());
            let e = kernel::check(&mut cx, &located, def.ty_value()).unwrap_err();
            assert_eq!(e.code, "E-RESOURCE");
            assert!(e.message.contains("type checker"), "{}", e.message);
        }
        {
            let _op = g.machine.budget.operation(Limits::default());
            assert_eq!(
                pretty::term_in_full(g, &[], body),
                Err(ResourceError::Nesting("printer"))
            );
        }
        {
            // For an error message, the part it can't reach is `…`.
            let _op = g.machine.budget.operation(Limits::default());
            assert!(pretty::term(g, &[], body).contains('…'));
        }
        {
            let _op = g.machine.budget.operation(Limits::default());
            let span = g.def(id).span();
            let e = stitchwort_core::termination::check(g, body, id, "g", span).unwrap_err();
            assert_eq!(e.code, "E-RESOURCE");
            assert!(e.message.contains("termination"), "{}", e.message);
        }
        {
            // Hashing walks a term with a work list, so any depth hashes.
            let _op = g.machine.budget.operation(Limits::default());
            assert!(def_hash(g, id).unwrap().is_some());
        }
        {
            // The same depth in a lemma's type: hashing and the printer walk
            // it, and the closing search counts what its conclusion names
            // (SW-3190).
            let (mut session, id) = with_deep_type(1_000_000);
            {
                let g = &session.elab.ev();
                let _op = g.machine.budget.operation(Limits::default());
                assert!(def_hash(g, id).unwrap().is_some());
            }
            {
                let g = &session.elab.ev();
                let _op = g.machine.budget.operation(Limits::default());
                assert_eq!(
                    pretty::term_in_full(g, &[], g.def(id).ty()),
                    Err(ResourceError::Nesting("printer"))
                );
                assert!(pretty::term(g, &[], g.def(id).ty()).contains('…'));
            }
            // The session's default stack budget is more than a test
            // thread has.
            session.elab.options.limits.stack = 1 << 20;
            let candidates = {
                let _op = session
                    .elab
                    .ev()
                    .machine
                    .budget
                    .operation(Limits::default());
                session
                    .elab
                    .search_candidates(&|item, _| item == Item::Def(id))
            };
            assert_eq!(candidates.len(), 1);
            // A goal that is an instance of the deep conclusion (`n := 0`).
            // Matching it walks both terms with the unifier, which stops
            // at its depth limit, so the candidate runs out of budget
            // and no hit reaches `defs_named` or `named`; those two are
            // covered by `closing`'s own test.
            let (f, nat) = {
                let g = &session.elab.kernel;
                let f = (g.env.defs().iter())
                    .position(|d| &**d.name() == "f")
                    .unwrap();
                let Term::Pi(_, _, nat, _, _) = g.env.defs()[id.0].ty().strip_loc() else {
                    panic!("a function type")
                };
                (DefId(f), nat.clone())
            };
            let zero = || Rc::new(Term::Nat(Rc::new(0u32.into())));
            let deep = deep_term(Term::Def(f), (*zero()).clone(), 1_000_000);
            let target = Term::Eq(Some(nat), Rc::new(deep), zero());
            let snapshot = stitchwort_elab::GoalSnapshot::target_for_tests(target);
            let span = session.elab.ev().def(id).span();
            let goal = session.elab.open_goal_at(&snapshot, span);
            let _op = session
                .elab
                .ev()
                .machine
                .budget
                .operation(Limits::default());
            let goal = goal.expect("a deep goal opens");
            let plans = session.elab.closing_plans(&goal, &candidates, &|_| true, 5);
            assert!(plans.plans.is_empty());
            assert_eq!(plans.found.stats.out_of_budget_items, [Item::Def(id)]);
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
        let g = &mut session.elab.kernel;
        let first = g.env.defs().len() - 1;
        for i in 0..1_000_000 {
            let body = Some(Rc::new(Term::Def(DefId(g.env.defs().len() - 1))));
            g.env
                .push_copy_unchecked_for_tests(DefId(first), format!("chain{i}").into(), body);
        }
        let g = &session.elab.ev();
        let _op = g.machine.budget.operation(Limits::default());
        assert_eq!(
            def_hash(g, DefId(g.env.defs().len() - 1)),
            Err(ResourceError::Nesting("hasher"))
        );
    });
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
                "type Unary : Type =\n  \
                 | Z\n  \
                 | S (u : Unary)\n\n\
                 def deep : Nat -> Unary\n  \
                 | Zero => Z\n  \
                 | Succ n => S (deep n)\n",
            )
            .expect("checks");
        let expr = session.parse_expression("<input>", "deep 100000").unwrap();
        let error = session.elab.eval_expr(&expr).unwrap_err();
        assert_eq!(error.code, "E-RESOURCE");
        assert!(error.message.contains("printer"), "{}", error.message);
    });
}
