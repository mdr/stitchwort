# Stitchwort: evaluation that doesn't overflow the stack

**Status:** draft 2, 15 October 2026. Draft 1 was reviewed; this draft adopts the review's changes and is the basis for implementation. Steps 0 to 4 are done; see [Progress](#progress).

## Progress

**Step 0**, shared constructor fields: commit `02235d8`.

**Step 4**, depth guards for the remaining recursive passes: done.

- **One mechanism.** Each function a pass recurses through first checks how much stack the operation has used, with the measurement step 1 introduced (`Budget::nesting(pass)`, the address of a local against the operation's floor). Going over is `ResourceError::Nesting(pass)`, reported as `E-RESOURCE`: "the program is nested too deeply for the type checker". The plan's "depth counter" is this, counting bytes rather than levels. A count of levels would need a different limit for each build: a level of a `+` chain takes the elaborator about 60 KB of stack in a debug build, and a tenth of that in a release build.
- **The parser** has no `Globals`, so the measurement itself moved to `stitchwort_syntax::stack`, and `Budget` uses it from there. `parse_module_within` and `parse_expression_within` take the stack the parser may use. Sessions pass their limit (`Session::parse_expression` for the CLI and the playground), and `parse_module` keeps a default that's safe on a 2 MiB thread. `expr`, `append_expr` (`++` recurses to the right) and `pattern` check before going deeper, so the parser stops before building deeper syntax.
- **Chains built by loops.** `f a b c …`, `1 + 2 + …` and a block's lines are parsed in a loop but nest as deeply as they're long. So `Expr::span` walks down each side in a loop, and freeing an `Expr` takes it apart on a work list (`impl Drop for Expr`). The elaborator's guards stop their elaboration.
- **The elaborator**: `infer`, `check`, `may_perform`, `comp_check`, `comp_infer`, the pattern compiler, `check_tree`, the automatic binding of type variables, and `Term::shift` (which now takes `Globals`). `mentions_ability` and `first_meta` use work lists. Unification's `solve`, `rename`, `prune` and `zonk` already counted against the budget (step 3).
- **The kernel** checks at its own entry points: `infer`, `check` and `check_case`. The checks that run on a term before it's type-checked (`case_only_in_tree`, `occurs`, `declared_later`, `Term::mentions`) now walk it with a work list (`Term::subterms`), so they can't overflow on a term the checker then rejects. `positive` and `is_type_former` loop.
- **The termination checker** guards its walk (`termination` is now public, for a test).
- **The hasher** walks a term with a work list, in the same order, so hashes are unchanged. Hashing a reference hashes the declaration it refers to first, which recurses once per declaration in a chain of dependencies; that's guarded. `def_hash` and `data_hash` return `Result`, and a test's hash is now computed inside the test's operation. A test whose hashing runs out has no result (and no hash).
- **The JavaScript generator** guards `expr` and `tree`. `generate` takes the limits and runs as one operation with only a stack limit (`Limits::stack_only`), so evaluating checked types still can't run out. An error points at the definition being generated. `Session::extract` wraps it. The export check in `Session::load` runs in the same kind of operation.
- **The printer**, for error messages, shows what it can't reach as `…` and carries on; that doesn't stop the operation. Showing a result (`eval_expr`, for the value and its type) uses `pretty::term_in_full`, which reports `E-RESOURCE` instead of hiding part of the answer. `Elaborator::show` is now an operation of its own.
- **Outside an operation nothing is guarded**, as before. Every pass that ran outside one (test hashing, the export check, generating JavaScript, `Elaborator::show`) now runs inside one.
- **Tests** (`crates/driver/tests/nesting.rs`). Each runs in a child process (the test binary again, running just that test), so a stack overflow is a failed test, not a dead test runner. Removing the parser's guard in `pattern` makes the child crash and only `nested_patterns` fail.
  - For each of nested applications, parentheses, functions and function types, `++` chains, `+` chains, blocks of `let` lines, list literals and text literals: find the smallest size that runs out, by doubling and then bisecting (every smaller size checks), then check that sizes just past it (+1, +2, +10, ×2, ×10) and 100,000 run out too. In a 2 MiB test thread with the default limits, the thresholds are, release (debug): applications 260 (24), parentheses 398 (52), functions 508 (39), `++` 345 (30), `+` 297 (26), `let` lines 354 (27), list and text literals 1,780 (192).
  - Nested patterns are only parsed: compiling them takes time and memory that grow steeply with depth.
  - Terms built directly, a million deep, for the passes after the elaborator, which would otherwise only see what the passes before them could handle: the kernel, the termination checker, the printer (`…`, or `E-RESOURCE` in full), the hasher (any depth hashes), and the JavaScript generator. A chain of a million definitions runs out in the hasher.
  - Expressions to evaluate: a million `Succ (`s doesn't parse; a value 100,000 deep (`S (S (… Z))` of a unary type) is too deep to print in full.
- **Measured** in a release build. The example suite's test (`cargo test --release --test examples`): 0.75 s before and after with 3 threads, and about 1.7 s before and after on one. In the CLI (64 MiB stack), programs 50,000 deep that crashed before (nested applications, parentheses, `+` chains, a test, an export) and every probe at 500,000 now report `E-RESOURCE`; the same programs 5,000 deep check as before.
- **In WebAssembly** (Node 22, and `web/stress.html` in headless Chrome 155): an expression nested 5,000 deep, a sum of 50,000 numbers and evaluating a nested expression crashed with `RangeError: Maximum call stack size exceeded`; now they report `E-RESOURCE`, and every case on the page is as expected. Varying the guard: up to 512 KiB, no case crashed V8; from 640 KiB, elaborating a long sum did. The guard stays at 128 KiB, a margin of 4, which allows little: nesting about 25 deep and list literals of about 200 elements (300 before this step, when the kernel's recursion wasn't guarded).
- **Found:**
  - The pattern compiler takes time and memory that grow about as the cube of the nesting depth: 200 deep takes 2.4 s and 190 MB, 400 deep 17 s and 1.4 GB, and 5,000 deep used 10 GB before it was stopped. That's work, not stack, so it isn't guarded.
  - The elaborator computes an expression's span, and `may_perform` walks it, at every level, so elaborating a chain is quadratic in its length (as before).
  - In a debug build, `the_evaluators_agree_on_the_prelude_and_every_example` overflows its 64 MiB thread in the reference evaluator (also at `5b6faa1`, before this step). Release builds, which `nix flake check` uses, pass.

**Step 3**, conversion, quotation and freeing: done.

- **`conv`** keeps the pairs still to compare on a work list, depth first and left to right, so it stops at the first difference as before. A function type's codomain is only evaluated once its domain has compared equal. Its one remaining recursion is two partially applied uses of the same definition: they're equal if their arguments are, *or else* by eta. A work list can't express "or else", so it compares the arguments with a nested call. The depth of that is the nesting of partially applied definitions in the program, not the size of the data.
- **`unify`** was moved forward from step 5. Checking a proof by `rfl` unifies the two sides in the elaborator before the kernel checks them, so `rfl : allOnes 20000 = allOnes 20000` failed there. It now has the same structure as `conv`, in the same order, so metavariables are solved in the same order as before. Solving one (`solve`, `rename`, `prune`) and `zonk` still recurse over the solution. They count against the budget, so a deep case is `E-RESOURCE`, not a crash.
- **`quote`** builds the term from a list of tasks: values to visit, and terms to assemble from the parts already finished. It still enforces the size limit.
- **`Term`** frees its sub-terms on a work list, like `Values`. It only does so when one of them is uniquely owned, since otherwise freeing just decrements a count.
- **Tests:**
  - The differential tests now also compare the machine's `quote` with the reference's on every definition, and the work-list `conv` with the reference's recursive one. That covers every pair of the prelude's and examples' definitions whose types are convertible (141 pairs in the prelude), plus each definition's type.
  - New stress tests, in 2 MiB test threads: two separately built 100,000-element lists compared as equal, differing at the head, and differing only at the end; printing a 100,000-element list; a proof by `rfl` that two 20,000-element lists are equal; and freeing terms nested a million deep.
- **Measured** in a release build: `lengths 400 3000` unchanged at 0.98 s. Checking and running every example went from 0.87 s to 0.93–0.98 s.
- **In the browser** (headless Chrome, `web/stress.html`): printing a 100,000-element list and comparing two 20,000-element lists in a proof now work. Long list and text literals now report `E-RESOURCE` instead of crashing. Only a deeply nested expression still crashes (the parser, step 4).

**Step 2**, the machine: done.

- **Representation.** Every sub-term the machine evaluates is now behind its own `Rc` (constructor and data arguments, case-branch and definition bodies), so it holds the term it's working on without borrowing from a closure it owns. The workspace forbids `unsafe`.
- **Natives** never call back into the evaluator. One that takes several steps at once (removing shared `Succ`s) returns `Outcome::Again` with new arguments, and the evaluator applies the definition itself. Each evaluator passes in its own `force`. The one place the machine still starts a nested machine is a native forcing an argument that's a solved metavariable, which only happens during elaboration.
- **Freeing moved into this step.** The first run of the machine evaluated `length (replicate 1000000 1)` and then overflowed the stack freeing the list. Constructor fields and closure environments are now a `Values` type whose `Drop` takes uniquely owned contents apart on a work list (reused between frees, so freeing doesn't allocate). It also detaches nested data arguments, spines, `NatAdd` bases, equations and function domains. `Term` still frees recursively.
- **The reference evaluator** (`reference.rs`, feature `reference`) is the previous recursive evaluator, with its own `force`, case-tree walk and `quote`. It shares only data types and the natives.
- **Differential tests** (`crates/driver/tests/differential.rs`):
  - the prelude and every example: each definition applied to 0…n fresh variables, each definition's type, and each test, through both evaluators, compared through the reference `quote`;
  - a case stuck on a metavariable that's then solved;
  - `J` on a variable, on an unsolved metavariable, and on one later solved with `rfl`;
  - a deep evaluation runs in exactly one machine, and the reference starts none.

  Planting a bug the type checker doesn't notice (swapping a stuck `J`'s motive and base) is caught twice, by the prelude comparison and by the `J` test.
- **Measured** in a release build, `lengths 400 3000`:
  - first version 1.29 s, against the recursive evaluator's 0.83 s;
  - after building closure environments in one allocation, evaluating simple sub-terms (variables, numbers, functions, folded definitions) without frames, choosing case branches directly, and boxing the rare large states (applying through the public wrapper, a stuck `J`'s base, `J` eliminations): 0.98 s, about 18% slower.
  - Moving the large states was the main cost. Removing the budget check or iterative freeing changed nothing measurable.
- **Depth:** a million-deep recursion runs in a 2 MiB test thread. `length (replicate 1000000 1)` peaks at about 750 MB, because each frame keeps its environment alive. The default frame limit is 2 million.

**Step 1**, resource errors: done. Where it differs from the plan below, or found something:

- **The budget lives in `Globals`, not in an explicit parameter.** Threading a `&mut Budget` through about 300 call sites as well as changing their return types would have doubled the churn. Instead, an operation starts with `budget.operation(limits)` (or `start`/`restore`), which resets the counters and restores the previous state when it ends. The parts the review cared about still hold: every function returns `Result`, the budget resets per operation, and nothing outside an operation is counted.
- **Depth is measured, not counted.** Until the machine exists, the recursive evaluator guards depth by comparing the address of a local variable with where the operation started: a measurement of stack actually used. This works the same on any thread and in WebAssembly's linear-memory stack, and step 4's depth guards can reuse it. Limits come from the thread's stack size (`Limits::for_stack`). The CLI now runs on a 64 MiB thread, and the examples test on a 16 MiB one.
- **Operations:** each top-level declaration (elaboration and kernel check), each test run, and each `eval` (elaboration, evaluation and printing).
- **Results:** tests have a third outcome, `OutOfResources`, which is never cached and makes `stitchwort test` fail. Declarations get `E-RESOURCE`, pointing at the declaration.
- **Recovery points fixed:**
  - `auto`'s search turned *any* error in a recursive search into "try the next candidate" (`.ok()?`), and so did `coerce` (`lift(…).ok()`). Both now propagate `E-RESOURCE`.
  - Unification's `solve` and `rename`, which used `Option` for "no solution", now keep "no" separate from "ran out".
  - Mutation check: putting the old behaviour back in `auto` isn't caught by the fault-injection test. The budget is sticky: once an operation runs out, every later step fails. So the next candidate fails with `E-RESOURCE` anyway. The two safeguards cover for each other.
- **Invariant relied on:** a module is accepted only if it produces no diagnostics at all. A declaration that fails stays declared without a body, so later declarations in the same module can refer to it. That's safe only because the whole module is then rejected, and the REPL and playground never use a rejected module.
- **Measured** in a release build, `lengths 400 3000`: 0.72 s before and 0.79 s after (10% slower). Recursion 10,000 deep now runs in the CLI (before, 6,000 crashed), and 100,000 deep gives `E-RESOURCE` instead of a crash.
- **Found and fixed: checking evaluated arguments.** To type `f a`, the kernel evaluated `a` and substituted it into `f`'s result type, even when that type didn't mention it. Evaluation is strict, so every closed argument in a program was computed while it was checked. Nested sums (`a + b + c + …`) were re-evaluated at every level, which made checking quadratic in their length.
  - Now an argument, constructor field or data parameter is computed only when a later type mentions it (`Closure::apply_lazy`, `later_types_mention`), in both the kernel and the elaborator.
  - Checking a sum of 64 `length` calls over a 3,000-element list went from 6.21 s to 0.03 s.
  - Still computed: anything inside a type. For `f x == y`, the decision's type is `Decidable (f x = y)`, so checking still computes `f x`. Twenty such tests over 3,000-element lists take 0.10 s to check, against 0.01 s for the same tests written without `==`. Avoiding that needs lazily evaluated values, or a translation of `==` that keeps the operands out of types.

## Changes since draft 1

The review accepted the approach: derive an abstract machine from the existing evaluator. It asked for these changes, all adopted:

- **Exhaustion is a `Result`, not a value.** Draft 1 proposed returning a special neutral value and setting a flag for the driver to check. That doesn't establish what it claimed. A function can ignore the poisoned value and return an ordinary answer, and state could be published before the flag is checked. `eval`, `force`, `quote` and `conv` now return `Result<_, ResourceError>`, with a budget that is shared by one top-level operation.
- **No recursive re-entry.** Once the machine is running, every evaluation request becomes a machine transition, never a call through a public wrapper that starts another machine. Forcing a solved metavariable, applying a closure and running a case tree are machine states.
- **Narrower claims.** Tail calls add no continuation frames; they don't make a loop run in constant *memory*. "Case trees need no frames" is qualified: a scrutinee may be a neutral value whose metavariable has since been solved, and forcing it happens inside the machine.
- **Several resources, several limits.** A frame count doesn't bound memory or time. There's now a work budget (machine transitions) as well as a live-frame limit, both shared across an operation, plus bounds on quotation and output. The cost of native bignum operations is stated, not hidden.
- **Depth guards on every remaining recursive pass.** Deep source terms don't need long literals: `f (f (f … x))` is enough. The parser (during parsing), the elaborator, unification, the kernel (at its own entry points), hashing, the termination checker and JS generation each get a depth guard that reports an error. A larger native stack stays, but only as headroom.
- **Unification is not exempt.** In a dependently-typed language, types can contain large values, such as `P (replicate n 0)`. Unification gets a depth guard now, and an iterative rewrite later that keeps its constraint order.
- **Freeing memory is part of the machine's normal and error paths**, not just a stress test at the end. The design is based on the actual ownership graph, and audits `Clone`, `Debug`, equality and hashing for recursion.
- **The reference evaluator stays independent** of the new code. Differential tests use bounded inputs; tests that might overflow run in a subprocess. More acceptance tests are added (see [Testing](#testing)).
- **Survey corrections:** Lean 4 and Agda are now described concretely, the WebAssembly stack-switching claim is withdrawn, and the panic claim is qualified.
- **Step 0 (new): shared constructor fields.** While auditing `Clone`, we found that copying a constructor value copied all its fields recursively, which made recursion over a list quadratic. This is fixed; see [Step 0](#step-0-done-shared-constructor-fields).

## Summary

Stitchwort's evaluator recurses on the Rust stack. Running a recursive program over a few thousand list elements or characters crashes the process, and a crash can't be caught or reported.

This proposal:
- replaces the evaluator's core with an **abstract machine**: a loop with an explicit stack of pending work on the heap, derived from the existing evaluator by CPS conversion and defunctionalisation;
- makes running out of resources an explicit, inconclusive error that publishes nothing;
- removes or guards recursion in the other passes that walk large values or terms.

Generated JavaScript has the same problem but needs different fixes, so it's out of scope here.

**Success criterion.** Within the documented resource limits, the machine gives the same results as the reference evaluator, and the Rust stack doesn't grow in proportion to how deeply the program recurses. Going over a supported limit produces an inconclusive resource error. Nothing incomplete is published, and cleaning up is safe.

## Background: the language and its evaluator

Stitchwort is a small, strict, pure, total, dependently-typed language, written in Rust.
- Programs are type-checked by a kernel.
- Proved code can be extracted to JavaScript.
- There's a browser playground, which runs the compiler as WebAssembly.

Every function terminates (recursion must be structural), but programs can still recurse deeply.

The evaluator is used by:
- the kernel, to compare types by computing them ("conversion");
- the elaborator, during unification and the search for decision procedures (`auto`);
- the test runner and the `eval` command, to run programs.

It's in the style of normalisation by evaluation:
- **Values** are constructors, lambdas with closures (a shared environment `Rc<[Value]>` plus a term), compact natural numbers (`Value::Nat` holding a bignum, and `Value::NatAdd` for `k + x` with `x` unknown), equality types, and **neutral** values: a variable, metavariable or stuck definition, with a spine of eliminations (applications and `J`).
- **Definitions** compile to case trees. Applying a definition to all its arguments either runs its case tree or, if a case is stuck, stays neutral.
- **Natives** (bignum `add`, `sub`, `mul`, `leq`, `eqNat`, `divFuel`, `decEqNat`, `eqNatRefl`) run when their arguments are numbers.

The core is about 170 lines: `eval`, `apply_icit`, `unfold`, `eval_tree`, `force` and `Closure::apply`, in `crates/core/src/value.rs`. In outline:

```rust
pub fn eval(g: &Globals, env: &[Value], term: &Term) -> Value {
    match term {
        Term::Var(ix) => env[env.len() - 1 - ix].clone(),
        Term::Ctor(d, c, args) => native::ctor(g, *d, *c, args.iter().map(|a| eval(g, env, a)).collect()),
        Term::App(f, a, i) => apply_icit(g, eval(g, env, f), eval(g, env, a), *i),
        Term::Lam(x, i, b) => Value::Lam(x.clone(), *i, Closure { env: env.into(), body: b.clone() }),
        Term::J(motive, base, proof) => match force(g, eval(g, env, proof)) { /* Refl => eval base, neutral => extend spine */ },
        // Data, Pi, Eq, Def, Meta, Nat, Sort, Refl, Ann, Case, Loc ...
    }
}
pub fn apply_icit(g: &Globals, f: Value, arg: Value, icit: Icit) -> Value {
    match f {
        Value::Lam(_, _, closure) => closure.apply(g, arg),            // evaluates the body
        Value::Neutral(Head::Def(id), mut spine) => { spine.push(Elim::App(arg, icit)); unfold(g, id, spine) }
        Value::Neutral(head, mut spine) => { spine.push(Elim::App(arg, icit)); Value::Neutral(head, spine) }
        _ => unreachable!(),
    }
}
// unfold: try a native; else, with all arguments, run the case tree (eval_tree); else stay neutral.
// eval_tree: at a Case node, force the scrutinee (a value in the environment) and pick a branch;
// at a leaf, eval the body.
// force: if a neutral's head is a solved metavariable, apply the solution to the spine (apply_spine).
```

Metavariable solutions live in `Globals` (`metas: RefCell<Vec<Meta>>`), and are cleared after each top-level declaration. `auto` searches decision procedures by trying candidates in turn, and undoes a failed candidate's metavariable solutions (`attempt` in `crates/elab/src/auto.rs`).

### The problem, measured

A user-level call goes `eval` → `apply_icit` → `unfold` → `eval_tree` → `eval`: several Rust frames. In `length (Cons x xs) = Succ (length xs)`, every list element holds those frames until the inner call returns. Text is a list of characters, so every text operation does the same. For `length` of a list literal:

| Build | Stack | Works | Overflows | Stack per element (approx.) |
|---|---|---|---|---|
| debug | 8 MB (main thread) | — | 1,000 | over 8 KB |
| release | 8 MB | 3,000 | 6,000 | 1.4–2.8 KB |

Other observations:
- `cargo test` threads have 2 MB stacks, and a test 200 calls deep crashed the whole test binary.
- In a release build, checking a list literal of 50,000 elements overflows in the kernel's type checker, which recurses over the nested `Cons` term.
- Rust aborts on stack overflow; the error can't be caught.
- The playground runs on Rust's default 1 MB WebAssembly stack. We haven't measured what deep programs do there.

### Step 0 (done): shared constructor fields

`Value::Ctor` held its fields in a `Vec<Value>`. Cloning a list value copied the whole list, recursively, and the evaluator clones on every variable lookup and closure call, so recursion over a list was quadratic. The fields are now `Rc<[Value]>`. This is commit `02235d8`; the table is release-build timings of `length` over a list eight times:

| Elements | Before | After |
|---|---|---|
| 750 | 3.0 s | 0.07 s |
| 1,500 | 11.9 s | 0.12 s |
| 3,000 | 47.1 s | 0.37 s |

Step 0 didn't change the depth limit; 6,000 still overflows. Other `Vec<Value>`s remain: `Value::Data` arguments and neutral spines. They're cloned less often, but the same audit applies (see [Freeing memory and other recursive helpers](#4-freeing-memory-and-other-recursive-helpers)).

## What others do

- **Deriving machines from evaluators.** Ager, Biernacki, Danvy and Midtgaard (2003) derive abstract machines mechanically from recursive evaluators. They closure-convert, convert to continuation-passing style, then **defunctionalise** the continuations, so that each kind of "what to do with the result" becomes a data constructor, and a list of them is the stack. The CEK and Krivine machines come out of call-by-value and call-by-name evaluators this way. Swarm's CESK machine describes itself the same way: "a defunctionalization of a recursive big-step interpreter, where we explicitly keep track of the call stack".
- **Agda's fast reducer** (`TypeChecking/Reduce/Fast.hs`) is the most direct precedent: an abstract machine for reduction during type checking. It has closures, elimination spines, `Eval` and `Match` states, and an explicit control stack whose frames cover case matching, normalisation, forcing, primitives, thunk updates and application. It's call-by-need, and Stitchwort is strict, so we use it as a checklist for our frame inventory, not as a strategy to copy. Nor does it show that every Agda traversal is stack-independent.
- **Lean 4** keeps a recursive kernel, but guards it. Type inference, weak-head reduction and definitional equality use recursion guards and `check_system`, which checks stack and memory, plus interruption and heartbeat checks when requested (`src/kernel/type_checker.cpp`, `src/runtime/interrupt.cpp`). `maxRecDepth` bounds recursion depth; heartbeats give deterministic timeouts. The elaborator's exception handling deliberately propagates runtime and interruption exceptions, instead of treating them as ordinary recoverable failures. The lesson is that recursion depth, stack availability and total work are separate concerns, and running out of resources isn't an ordinary failure.
- **Strong reduction for type checking.** Proof assistants need evaluation of open terms under binders: Leroy and Grégoire's compiled strong reduction, Barras's KAM/KN machines, and Boespflug's untyped NbE for conversion. Our evaluator already handles open terms by producing neutral values, and the machine keeps that unchanged. Coq's bytecode VM is hard on deep non-tail recursion; one paper rewrites code into CPS to avoid it.
- **Growing the native stack (rustc).** `ensure_sufficient_stack` wraps `stacker::maybe_grow` (100 KiB red zone, 1 MiB segments that grow exponentially) "at strategic points". `stacker` uses `psm`, which has a wasm32 backend that changes `__stack_pointer` around an indirect call. That's the stack in linear memory; it doesn't remove nested WebAssembly calls, so it doesn't free us from the engine's call-stack limit. We haven't validated it for our targets. In any case it doesn't replace removing recursion from the evaluator.
- **Freeing long chains.** Rust's automatic drop recurses once per link. One forum report has an `Rc` list aborting at about 40,000 elements. The fix is a loop that detaches children from uniquely-owned nodes. Note that `Rc::get_mut` requires no other strong *or weak* pointers, while `Rc::try_unwrap` requires only one strong pointer. Stitchwort has no `Weak` pointers, so the two agree here.
- **Tail calls in Rust.** `become` is an incomplete nightly feature, with stabilisation hoped for in 2027.
- **WebAssembly.** Rust's wasm targets give a 1 MB linear-memory stack, placed first so that an overflow traps, adjustable with `-C link-args=-z stack-size=…`. The engine's own call-stack limit is separate. `wasm32-unknown-unknown` defaults to `panic=abort`; unwinding can be enabled with extra build requirements. Either way, we don't use panics for resource exhaustion.
- **JavaScript** (for later): V8 and SpiderMonkey don't eliminate tail calls. js_of_ocaml compiles self tail calls to loops and mutual ones through a trampoline, and documents patterns it doesn't cover, so a future JS guarantee should be similarly narrow.

## Proposal

### 1. Resource errors and a per-operation budget

```rust
pub enum ResourceError {
    /// Too many machine transitions: a bound on work.
    Work,
    /// Too many live continuation frames: a bound on depth.
    Depth,
    /// A recursive pass (parser, unifier, kernel, …) went too deep.
    Nesting { pass: &'static str },
    /// Quotation or printing would produce too large a term.
    Size,
}

pub struct Budget { /* limits, and counters used so far */ }
```

- `eval`, `apply`, `force`, `quote` and `conv` take a `&mut Budget` (inside a small evaluation context, alongside `&Globals`) and return `Result<_, ResourceError>`. For `conv`, `Ok(false)` means "computed, and not equal"; `Err` means there's no answer.
- **One budget per top-level operation:** checking one declaration (elaboration plus kernel), running one test, or evaluating one expression. Conversion doesn't get a fresh budget each time it evaluates. The budget lives in the operation's context, not in `Globals`, so it can't leak between operations.
- **Exhaustion is inconclusive, and it propagates.** It's reported as `E-RESOURCE` with the operation, a source location and which limit was hit, never as a type error, a failed test or a passed test. Callers must not turn `Err` into `false`, try an alternative, or keep partial state. Every place that recovers from failure must be audited:
  - `auto`'s `attempt`, which today undoes a failed candidate and tries the next, must propagate `Err` immediately;
  - unification, which must not treat `Err` as "doesn't unify";
  - the test cache, which must not record an exhausted test.
- **Nothing incomplete is published.** A declaration is added to `Globals` only after its elaboration and kernel check complete. On `Err`, its metavariables and obligations are cleared, as on any other error. A test asserts that a fresh check after an exhausted one behaves as if the exhausted one never happened.
- **Diagnostics are cheap.** An exhaustion diagnostic names the operation and location, and doesn't quote or print values, since that could exhaust again.
- **The kernel doesn't rely on its callers.** It returns its own `Result` today. Resource errors become one more way for a kernel check to fail, so acceptance never depends on a driver remembering a protocol.
- **Limits.** Defaults per build: work (transitions), live frames, quotation size, nesting depth for the remaining recursive passes. They're configurable from the CLI, and the playground uses smaller ones. A live-frame limit approximately bounds the continuation stack's memory; it doesn't bound process memory, because values held by the program can grow while the stack stays flat. We don't claim more than that. One machine transition can do expensive bignum arithmetic (`mul` of huge numbers). The work budget doesn't bound that cost tightly, and we say so; a size check on native arguments may come later.

### 2. The machine, derived from the evaluator

Derive the machine from `eval`, `apply_icit`, `unfold`, `eval_tree`, `force` and `apply_spine` by the Ager et al. construction. The control states are roughly these (the final names may differ):

```
Control =
    Eval(term, env)                    -- evaluate a term
  | Apply(function, argument, icit)    -- apply a value
  | Unfold(def, spine)                 -- a definition with its arguments: native, case tree or stuck
  | RunCaseTree(tree, env)             -- walk a case tree; a stuck scrutinee goes to Force first
  | Force(value)                       -- replace a solved metavariable head, replaying its spine
  | Return(value)                      -- give a value to the top frame
```

There's one frame for each non-tail recursive call in today's code:

| Frame | Waiting for | Then |
|---|---|---|
| `AppArg { arg: Term, env, icit }` | the function | evaluate the argument |
| `AppFun { f: Value, icit }` | the argument | `Apply` |
| `Fields { kind: Ctor(d, c) or Data(d), done: Vec<Value>, terms: Rc<…>, next: usize, env }` | the next field | continue, or build the value (through `native::ctor`, which keeps numbers compact) |
| `PiDomain`, `EqParts` | parts of a type | build the type value |
| `JProof { motive, base, env }` | the proof | for `Refl`, `Eval` the base; otherwise evaluate the motive and base, then extend the spine |
| `Replay { spine: Rc<[Elim]>, next: usize }` | the head, after `Force` | apply the next elimination |
| `CaseScrutinee { tree, env }` | a forced scrutinee | pick the branch, or stay stuck |

Rules:
- **No re-entry.** Inside the machine, nothing calls `eval`, `apply`, `force` or `Closure::apply` (the public wrappers); it moves to the corresponding control state instead. Natives that re-apply their own definition after peeling off shared `Succ`s (`sub`, `leq`, `eqNat`, `eqNatRefl` in `native::run_partial`) return an `Apply` request, not a value from a nested call. A test-only counter of machine entries checks that a deep evaluation runs inside exactly one machine.
- **Tail calls add no frames.** `Apply` of a closure becomes `Eval` of its body. This bounds the *continuation*, not total memory: an accumulator can still grow.
- **No quadratic copying.** Frames hold shared slices plus an index (`Rc<[Term]>` and `next`), never cloned tails of vectors.
- **Same behaviour.** The machine keeps evaluation order (function before argument, fields left to right), environment sharing, compact numbers, stuck terms and results, exactly. The language is pure and total, so order can't change results, but keeping it means differential tests compare like with like.
- **Budget accounting.** Each transition counts against work; each push is checked against the live-frame limit. When a limit is hit, the machine returns `Err`, and its frames are freed by the iterative cleanup described next.

The public wrappers (`eval` and so on) run the machine to completion, and are what the kernel, elaborator and driver call.

### 3. Conversion and quotation

- **`conv`** becomes a loop over a work list of pairs (with binder levels). Its result is a conjunction, so order doesn't affect the answer, but the first difference found stops the loop. Closures are compared by applying them to a fresh variable through the machine, under the same budget.
- **`quote`** becomes a post-order traversal with an explicit stack, under the quotation-size limit. A small, independent recursive quoter stays as the test reference, so that a quoting bug can't hide an evaluator disagreement.
- **Unification** gets a depth guard now (`ResourceError::Nesting`). A work-list version comes later. It must keep the current order of constraints, since a metavariable solution affects later comparisons.

### 4. Freeing memory and other recursive helpers

Values can be dropped at any transition: replacing the control state, popping a frame, discarding an unused argument (`(_ => 0) (replicate n 1)`), or abandoning everything on `Err`. So destruction must be iterative everywhere.

- **The ownership graph.** `Value` owns its children through:
  - `Ctor` fields (`Rc<[Value]>`);
  - `Data` arguments (`Vec<Value>`);
  - neutral spines (`Vec<Elim>`, which hold values);
  - closures (an `Rc<[Value]>` environment and an `Rc<Term>` body);
  - `Pi` domains, `NatAdd` bases and `Eq` parts (`Rc<Value>`).

  `Term` owns its children through `Rc<Term>` and `Vec<Term>`. A custom `Drop` for `Value` (and `Term`) detaches the children of uniquely-owned nodes (`Rc::try_unwrap`, or `Rc::get_mut` before taking a slice's contents) into a local work list, and frees them in a loop. Shared parts are left to their other owners.
- **Other recursive helpers.** The derived `Clone` is shallow where fields are `Rc` (now true for constructor fields). `Debug` and the printer recurse, so panic messages and diagnostics must not format deep values; diagnostics go through the bounded quoter. Hashing (`hash.rs`) walks terms, and gets a depth guard.
- **Tests:**
  - shared tails, including freeing the last owner of a shared structure;
  - deep closure environments;
  - long neutral spines;
  - values discarded mid-evaluation;
  - cleanup after exhaustion, with frames still holding deep values.

### 5. Depth guards for the remaining recursive passes

These passes recurse over source terms or elaborated terms:
- the parser;
- the elaborator and unifier;
- the kernel checker;
- hashing;
- the termination checker;
- the JS generator;
- the printer.

Terms can be deep without long literals, so each pass gets a depth counter that returns `ResourceError::Nesting` before the Rust stack runs out.
- **The parser** checks during parsing, before building deep syntax.
- **The kernel** checks at its own entry points, rather than trusting the front end.
- **Limits are conservative for each build**, including debug and WebAssembly, and are tested by subprocess tests that go just past them.

Running the CLI on a thread with a larger stack, and raising the wasm linker stack, give extra headroom. They aren't what turns depth into an error, and how much untouched stack pages cost is platform-dependent, so the design doesn't rely on it.

Compact literals (stage 3 of the text proposal) and iterative versions of these passes come later.

## Testing

**The reference evaluator** is the current recursive one, kept test-only, with its own recursive `eval`, `apply`, `force`, case-tree walk and native fallback. It must not call any function that dispatches into the machine. Sharing immutable data structures is fine. A test checks the independence by evaluating with the machine's entry counter, which must stay at zero.

**Differential tests** run on bounded inputs: every example program's definitions and tests, the existing generated-term fuzz tests, and the native-number tests. The machine and the reference must give identical normal forms, compared through the reference quoter. These cases matter most:
- open terms under several binders;
- cases that are stuck, then unstuck once a metavariable is solved and the neutral is forced;
- `J` with `rfl` and with neutral proofs;
- definitions applied to too few or too many arguments, and mixed implicit arguments;
- long neutral application spines.

**Fault injection.** For small programs, set the work limit to 1, 2, 3, … transitions. Each run must either finish with the right answer or report `E-RESOURCE`. It must never panic, report a pass or fail, cache a result or install a declaration. After an exhausted run, a fresh check in the same session must behave as if the exhausted run never happened.

**Stress tests** run in ordinary 2 MB test threads, and the wasm build runs them under Node. Tests that might overflow the *reference* run in a subprocess, since an overflow kills the test binary.
- Non-tail recursion over a runtime-built list of 10⁶ elements: `length`, `append`, `map`.
- Text operations on 10⁵ characters.
- A tail-recursive loop of 10⁶ steps, with the continuation stack's high-water mark measured separately from other memory.
- Conversion of two *independently allocated* long lists: equal, differing at the head, and differing only at the last element.
- Deep evaluation inside conversion: `rfl : length (replicate 100000 1) = 100000`.
- Freeing a 10⁶-element list, at the end and mid-evaluation.
- Printing a 10⁵-element result, and going over the quotation-size limit.
- Hitting each limit, which must give `E-RESOURCE` with the right category.
- Deep source nesting in each guarded pass: `f (f (… x))`, deeply nested lambdas and function types.

**Benchmarks** with recorded baselines and a regression threshold (20% slower fails review):
- the full example suite;
- the eight-times `length` benchmark from step 0, at 3,000 elements;
- `textSplit`/`textJoin` round trips on 10⁴ characters;
- the generated-rows test.

**Mutation testing** of the machine, in small sharded runs, as was done for the termination checker.

## Plan

0. **Shared constructor fields.** Done (`02235d8`).
1. **`ResourceError` and `Budget`**, threaded through `eval`, `force`, `quote`, `conv` and their callers, still with today's recursive evaluator. That evaluator gets a depth counter, so deep programs fail with `E-RESOURCE` instead of aborting, even before the machine exists. Then the audit of the recovery points (`auto`, unification, test cache), and the fault-injection tests.
2. **The machine**, the independent reference evaluator, the entry counter and the differential tests.
3. **Iterative `Drop`, the `conv` work list and iterative `quote`**, with their stress tests.
4. **Depth guards** in the parser, elaborator, unifier, kernel, hasher, termination checker, JS generator and printer, plus a larger CLI stack as headroom.
5. **Later, separately:** a work-list unifier; JavaScript (self tail calls as loops, trampolines or native text operations); compact literals; a size check on native bignum arguments.

Each step is a commit gated on the full test suite and `nix flake check`.

## Sources

- Ager, Biernacki, Danvy, Midtgaard, [A Functional Correspondence between Evaluators and Abstract Machines](https://www.brics.dk/RS/03/13/), BRICS RS-03-13 / PPDP 2003.
- [CEK machine](https://en.wikipedia.org/wiki/CEK_Machine); Matt Might, [Machine-based interpreters](https://matt.might.net/articles/cesk-machines/); Swarm's [CESK machine](https://hackage-origin.haskell.org/package/swarm-0.3.0.0/docs/Swarm-Game-CESK.html).
- Agda, `src/full/Agda/TypeChecking/Reduce/Fast.hs` (pointed out in review).
- Lean 4, `src/kernel/type_checker.cpp`, `src/runtime/interrupt.cpp`, and the `CoreM` exception-handling API (pointed out in review); Lean 2 [`check_stack`](https://git.mzhang.io/michael/lean2/src/commit/ef069e39b01f931db3f6415763c9b8aff8c586db/src/util/interrupt.h).
- Leroy and Grégoire, [strong reduction](https://xavierleroy.org/publi/strong-reduction.pdf); Barras, [Efficient Reduction in Coq](https://www.lix.polytechnique.fr/~barras/reduction); Boespflug, [Conversion by Evaluation](https://www.cs.mcgill.ca/~mboes/papers/padl10.pdf); [a verified rewriting engine](https://arxiv.org/pdf/2205.00862) (CPS to avoid Coq VM stack limits).
- rustc's [`ensure_sufficient_stack`](https://doc.rust-lang.org/stable/nightly-rustc/src/rustc_data_structures/stack.rs.html); [`stacker`](https://github.com/rust-lang/stacker) and its [docs](https://docs.rs/stacker/latest/stacker/); [rust-lang/rust#128422](https://github.com/rust-lang/rust/issues/128422).
- Iterative drop: [`Rc` list drop overflow](https://users.rust-lang.org/t/how-to-efficiently-drop-a-linked-list-like-structure-based-on-rc-without-triggering-stack-overflow-aborts/17348); [dropping a tree](https://users.rust-lang.org/t/need-help-implementing-drop-for-tree/36864).
- Tail calls: [`become`](https://doc.rust-lang.org/std/keyword.become.html); [Rust should have stable tail calls](https://trifectatech.org/blog/tail-calls-project-goal/).
- WebAssembly: [rustc wasm target spec](https://doc.rust-lang.org/stable/nightly-rustc/src/rustc_target/spec/base/wasm.rs.html); [Increasing rust wasm32 stack size](https://users.rust-lang.org/t/increasing-rust-wasm32-stack-size/73605).
- JavaScript: [js_of_ocaml tail calls](https://ocsigen.org/js_of_ocaml/latest/js_of_ocaml/tailcall.html).
