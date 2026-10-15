# Stitchwort: evaluation that doesn't overflow the stack

**Status:** draft 1, 15 October 2026. For review; nothing is implemented.

## Summary

Stitchwort's evaluator recurses on the Rust stack, so running a recursive program over a few thousand list elements or characters crashes the process. This proposal replaces the evaluator's core with an **abstract machine**: one loop with an explicit stack of pending work on the heap. It's the standard construction (CPS conversion plus defunctionalisation of the continuations), applied to the evaluator we already have. The proposal also covers:
- the other places that walk large values: conversion checking, quoting, and freeing memory;
- turning "too deep" into an ordinary error instead of a process abort;
- how to test the new machine against the current evaluator, which stays as the reference.

Generated JavaScript has the same problem but needs different fixes. It's out of scope here, apart from a note on prior art.

## Background: the language and its evaluator

Stitchwort is a small, strict, pure, total, dependently-typed language, written in Rust. It's a hobby project.
- Programs are type-checked by a kernel.
- Proved code can be extracted to JavaScript.
- There's a browser playground, which runs the compiler as WebAssembly.

Every function terminates (the termination checker enforces structural recursion), so programs are total, but they can still recurse deeply.

The evaluator is used in three places:
- **by the kernel**, to compare types by computing them ("conversion");
- **by the elaborator**, during unification;
- **by the test runner and `eval` command**, to run programs.

It's in the style of normalisation by evaluation:
- **Values** are constructors, lambdas with closures (an environment plus a term), compact natural numbers (`Value::Nat` holding a bignum, and `Value::NatAdd` for `k + x` with `x` unknown), equality types, and **neutral** values: a variable, metavariable or stuck definition, with a spine of eliminations (applications and `J`).
- **Definitions** compile to case trees. Applying a definition to all its arguments either runs its case tree or, if a case is stuck on a neutral value, stays neutral.
- **Natives** (bignum `add`, `sub`, `mul`, `leq`, `eqNat`, `divFuel`, `decEqNat`) run when their arguments are numbers.

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
        Value::Lam(_, _, closure) => closure.apply(g, arg),           // evaluates the body
        Value::Neutral(Head::Def(id), mut spine) => { spine.push(Elim::App(arg, icit)); unfold(g, id, spine) }
        Value::Neutral(head, mut spine) => { spine.push(Elim::App(arg, icit)); Value::Neutral(head, spine) }
        _ => unreachable!(),
    }
}
// unfold: try a native; else, with all arguments, run the case tree (eval_tree), else stay neutral.
// eval_tree: at a Case node, look up the scrutinee (already a value) in the environment and
// pick a branch; at a leaf, eval the body.
```

### The problem, measured

A user-level call goes `eval` → `apply_icit` → `unfold` → `eval_tree` → `eval`: several Rust frames. In `length (Cons x xs) = Succ (length xs)`, the `Succ` can't be built until the inner call returns, so every list element holds those frames. All text operations work this way, because text is a list of characters (docs/proposals/text-and-io.md, stage 1). Here is `length` of a list literal:

| Build | Stack | Works | Overflows | Stack per element (approx.) |
|---|---|---|---|---|
| debug | 8 MB (main thread) | — | 1,000 | over 8 KB |
| release | 8 MB | 3,000 | 6,000 | 1.4–2.8 KB |

Other observations:
- `cargo test` threads have 2 MB stacks. A test recursing 200 deep crashed the whole test binary.
- In a release build, *checking* a list literal of 50,000 elements also overflows: the kernel's type checker recurses over the nested `Cons` term.
- A stack overflow in Rust aborts the process ("fatal runtime error: stack overflow"). It can't be caught or reported as a diagnostic.
- The playground runs on Rust's default WebAssembly stack, 1 MB. We haven't measured what a deep program does there.

This blocks the next milestones: text, then an `IO` ability with a `main` that processes input of arbitrary length.

## What others do

- **Abstract machines from evaluators.** Ager, Biernacki, Danvy and Midtgaard (2003) show how to get an abstract machine from a recursive evaluator mechanically. Closure-convert it, convert it to continuation-passing style, then **defunctionalise** the continuations: each kind of "what to do with the result" becomes a data constructor, and a list of them is the stack. They derive the CEK machine (call-by-value) and Krivine's machine (call-by-name) this way. The construction preserves the evaluator's meaning step by step, which is why we propose to *derive* the machine from our evaluator rather than design one from scratch. Other machine-based interpreters use the same idea, for example Swarm's CESK machine ("a defunctionalization of a recursive big-step interpreter, where we explicitly keep track of the call stack").
- **Strong reduction for type checking.** Proof assistants need evaluation that also works under binders and on open terms (Leroy and Grégoire's compiled strong reduction for Coq; Barras's KAM/KN machines for Coq; Boespflug's untyped NbE for conversion). Our evaluator already handles open terms by computing to neutral values, and the machine keeps that behaviour unchanged. Coq's bytecode VM is known to be hard on deep *non-tail* recursion: one paper reports rewriting code into CPS to avoid it.
- **Growing the native stack (rustc).** rustc wraps recursive tree walks in `ensure_sufficient_stack`. This calls the `stacker` crate's `maybe_grow`, which switches to a fresh heap-allocated stack segment when less than a "red zone" remains (100 KiB red zone, 1 MiB segments that then grow exponentially). The rustc docs advise calling it "at strategic points". `stacker`'s README says it's "a noop" on unsupported platforms. We haven't confirmed whether `wasm32-unknown-unknown` is one, but WebAssembly doesn't let a program switch stacks in the way `stacker` relies on.
- **Turning overflow into an error.** Lean 2 had a `check_stack` primitive that recursive functions call to throw a recoverable exception when stack runs low. From memory, not checked for this draft: Lean 4 has a configurable `maxRecDepth` counter, which reports "maximum recursion depth has been reached" as an ordinary error.
- **Freeing long chains.** Rust's automatic drop of a linked structure recurses once per link. One forum report has an `Rc`-linked list aborting at about 40,000 elements. The usual fix is a custom `Drop` that loops: it takes each child out while the node is uniquely owned (`Rc::get_mut` / `Rc::try_unwrap`) and leaves shared parts alone.
- **Tail calls in Rust.** `become` (explicit tail calls) is still an incomplete nightly feature. A 2026 project goal aims at stabilisation "hopefully in 2027". We can't rely on it.
- **WebAssembly.** Rust's wasm targets ask the linker for a 1 MB stack, placed first in memory so that an overflow traps instead of corrupting static data. It can be changed with `-C link-args=-z stack-size=…`.
- **JavaScript** (for later): V8 and SpiderMonkey don't eliminate tail calls. js_of_ocaml compiles self-recursive tail calls to loops and mutual ones through a trampoline (bouncing every 50 calls by default), and offers a whole-program CPS mode at a performance cost.

## Proposal

### 1. The evaluator core becomes a machine

Derive the machine from the current evaluator by the Ager et al. construction. Each recursive call in `eval`, `apply_icit`, `unfold` and `eval_tree` that isn't in tail position becomes a **frame** recording what to do with its result:

| Frame | Waiting for | Then |
|---|---|---|
| `AppArg { arg: Term, env, icit }` | the function | evaluate the argument |
| `AppFun { f: Value, icit }` | the argument | apply `f` |
| `Fields { kind: Ctor(d, c) or Data(d), done: Vec<Value>, rest, env }` | the next field | continue, or build the constructor (through `native::ctor`, which keeps numbers compact) |
| `PiDomain`, `EqParts` | parts of a type | build the type value |
| `JProof { motive, base, env }` | the proof | for `Refl`, evaluate the base; otherwise evaluate the motive and base, and extend the spine |
| `Spine { rest: Vec<Elim> }` | the head, after a metavariable is replaced (`force`) | apply the rest of the spine |

The machine's state is either *evaluate term `t` in environment `env`* or *return value `v`*, plus `Vec<Frame>`:
- **Applying a closure** replaces the current state with "evaluate its body". There's no frame, so **tail calls run in constant space**.
- **Case trees need no frames.** A scrutinee is a variable that's already a value, so walking the tree is a loop, and its leaf becomes the next state.
- **A stuck case tree** returns the neutral value, as `unfold` does now.
- **Natives** are leaves: they compute directly on bignums. Four of them re-apply their own definition once, after peeling off shared `Succ`s (`sub`, `leq`, `eqNat`, `eqNatRefl`; `native.rs` `run_partial`). That becomes a transition to "apply", not a nested call.

**The public API doesn't change.** `eval`, `apply`, `apply_icit`, `force` and `Closure::apply` become thin wrappers that run the machine to completion, so the kernel, elaborator, natives and driver are untouched.

What it preserves: evaluation order (function before argument, fields left to right), sharing of environments (`Rc<[Value]>`), compact numbers, stuck-term behaviour, and the evaluator's results, exactly. The language is pure and total, so order can't change results. We keep it anyway so that differential tests compare like with like.

### 2. Other code that walks large values

Once a program can build a list of a million elements, everything that walks that list must avoid recursion too:
- **Conversion (`conv`)** and the elaborator's **unification** compare two values. Comparing two long lists recurses once per element. `conv` is a conjunction, so it becomes a loop over a work list of pairs (and levels, for binders). Unification is more involved, because solving one metavariable affects the rest. We propose a work list there too, but in a later step: in practice it compares types, not large data.
- **Quoting (`quote`)** turns values back into terms, for error messages, normal forms and printing results. It becomes a post-order traversal with an explicit stack. The printer already walks list and text spines iteratively.
- **Freeing memory.** Add an iterative `Drop` for `Value`, and probably `Term`. It takes children out of uniquely owned nodes into a local `Vec` and frees them in a loop. We'll confirm with a stress test that drop is a real overflow site here, rather than assume it.

### 3. Large source terms: a safety net, not a rewrite

The parser, elaborator, kernel checker, hasher, termination checker and JS generator all recurse over *source* terms. Those are only deep for very long literals, such as a 50,000-character text. The real fix for that is compact literals, which are stage 3 of the text proposal and have their own soundness questions. Until then:
- the CLI runs its work on a thread with a large stack (for example 256 MB; untouched pages cost no memory);
- the wasm build gets a larger linker stack;
- literals longer than a fixed limit are rejected with a clear error, rather than risking a crash.

### 4. "Too deep" becomes an error

Programs can still legitimately need a lot of memory: a non-tail recursion a million deep keeps a million frames. With frames on the heap, the machine can count them, and stop at a limit with an ordinary diagnostic instead of using all memory or aborting. That matters for the playground and for a future `IO` runner.

The difficulty is that `eval` returns `Value`, and `conv` returns `bool`. There are two options:

- **A. Thread a `Result` through** `eval`, `apply`, `conv`, `quote` and their callers. This is the cleanest, but it's the largest change, touching every caller in the kernel and elaborator.
- **B. A sticky "exhausted" flag** (proposed). On hitting the limit, the machine sets a flag in `Globals` and returns a special neutral value, which can't be converted with anything. The driver checks the flag after each top-level operation (checking a definition, running a test, evaluating an expression), and reports `E-TOO-DEEP` in place of whatever result came back.

  The invariant to maintain: **exhaustion may only ever cause rejection.** A failed `conv` rejects a program and never accepts one. A test that exhausts is reported as exhausted, never as passed or failed. `auto`'s search for decision procedures must not treat exhaustion as a reason to try something else that could then succeed. Panics with `catch_unwind` aren't an option, because the wasm build aborts on panic.

The limit would be a frame count, with a default sized to a memory budget (for example about 256 MB of frames), and configurable.

## Testing

The current recursive evaluator stays in the codebase as a **reference implementation** (test-only), the way native functions are tested against their definitions today.

- **Differential tests:** for every example program's definitions and tests, the existing generated-term fuzz tests, and the native-number tests, the machine and the reference must give identical normal forms (compared by `quote`). For large inputs, the reference runs on a thread with a huge stack.
- **Stress tests**, all run in ordinary 2 MB test threads to show they don't depend on stack size:
  - non-tail recursion over a runtime-built list of 10⁶ elements (`length`, `append`, `map`);
  - text operations on 10⁵ characters;
  - a tail-recursive loop of 10⁶ steps, checking that memory stays flat;
  - conversion of two deep values (`rfl : length (replicate 100000 1) = 100000`);
  - freeing a 10⁶-element list;
  - printing a 10⁵-element result;
  - hitting the depth limit, which must give `E-TOO-DEEP` and never a pass;
  - the same in the wasm build, under Node.
- **Measurements**, as acceptance criteria: peak memory per frame, against the 1.4–2.8 KB per level of today's release build; and the time for the existing test suite and benchmarks, which must not get noticeably slower.
- **Mutation testing** of the machine, in small sharded runs, as was done for the termination checker.

## Plan

1. **The machine and the reference evaluator, with differential tests.** No behaviour change except stack use.
2. **`conv` as a work list, iterative `Drop`, iterative `quote`,** with their stress tests.
3. **The frame limit and `E-TOO-DEEP`** (option B), with the "only ever rejects" tests.
4. **The safety net for large source terms:** big-stack thread, wasm stack size, literal limit.
5. **Later, separately:** unification as a work list; JavaScript (self tail calls as loops, then trampolines or native text operations); compact literals.

Each step is a commit gated on the full test suite and `nix flake check`.

## Questions for the reviewer

1. Is deriving the machine from the existing evaluator (defunctionalised CPS) the right approach, rather than adopting a known machine design such as Krivine's or a ZINC-style machine with strong reduction? Our motivation is a mechanical, checkable correspondence with code that's already trusted.
2. Option B (a sticky exhaustion flag) versus option A (threading `Result`): is the "exhaustion only ever rejects" invariant enough to make B sound? Are there places we've missed where a failed computation could lead to acceptance (for example, search that tries alternatives)?
3. Is the step 3 safety net (big stack, literal limit) acceptable for now, or should the kernel checker and elaborator also stop recursing over terms in this milestone?
4. Is keeping the recursive evaluator as a test-only reference worthwhile, or is it a maintenance burden once the machine is trusted?
5. Anything in the "What others do" survey that's wrong, or a better-known practice we've missed? We'd particularly like pointers on how Lean 4's and Agda's evaluators avoid or bound native stack use.

## Sources

- Ager, Biernacki, Danvy, Midtgaard, [A Functional Correspondence between Evaluators and Abstract Machines](https://www.brics.dk/RS/03/13/), BRICS RS-03-13 / PPDP 2003.
- [CEK machine](https://en.wikipedia.org/wiki/CEK_Machine) (Wikipedia); Matt Might, [Machine-based interpreters](https://matt.might.net/articles/cesk-machines/); Swarm's [CESK machine](https://hackage-origin.haskell.org/package/swarm-0.3.0.0/docs/Swarm-Game-CESK.html).
- Leroy and Grégoire, [strong reduction](https://xavierleroy.org/publi/strong-reduction.pdf); Barras, [Efficient Reduction in Coq](https://www.lix.polytechnique.fr/~barras/reduction); Boespflug, [Conversion by Evaluation](https://www.cs.mcgill.ca/~mboes/papers/padl10.pdf); [Accelerating Verified-Compiler Development with a Verified Rewriting Engine](https://arxiv.org/pdf/2205.00862) (CPS to avoid Coq VM stack limits).
- rustc's [`ensure_sufficient_stack`](https://doc.rust-lang.org/stable/nightly-rustc/src/rustc_data_structures/stack.rs.html); [`stacker`](https://github.com/rust-lang/stacker) and its [docs](https://docs.rs/stacker/latest/stacker/); [rust-lang/rust#128422](https://github.com/rust-lang/rust/issues/128422).
- Lean 2 [`check_stack`](https://git.mzhang.io/michael/lean2/src/commit/ef069e39b01f931db3f6415763c9b8aff8c586db/src/util/interrupt.h).
- Iterative drop: [Rust users forum, `Rc` list drop overflow](https://users.rust-lang.org/t/how-to-efficiently-drop-a-linked-list-like-structure-based-on-rc-without-triggering-stack-overflow-aborts/17348); [dropping a tree](https://users.rust-lang.org/t/need-help-implementing-drop-for-tree/36864).
- Tail calls: [`become` keyword docs](https://doc.rust-lang.org/std/keyword.become.html); [Rust should have stable tail calls](https://trifectatech.org/blog/tail-calls-project-goal/).
- WebAssembly stack: [rustc wasm target spec](https://doc.rust-lang.org/stable/nightly-rustc/src/rustc_target/spec/base/wasm.rs.html); [Increasing rust wasm32 stack size](https://users.rust-lang.org/t/increasing-rust-wasm32-stack-size/73605).
- JavaScript: [js_of_ocaml tail calls](https://ocsigen.org/js_of_ocaml/latest/js_of_ocaml/tailcall.html).
