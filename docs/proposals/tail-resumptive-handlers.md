# Proposal: handlers that resume in tail position, run without capturing

**Status:** proposed, awaiting Matt's review (28 October 2026). Design only. Ticket SW-737.

A `Std.Parse` scan over noise costs about 12 µs per character on the
machine and about 0.2 µs in JS (parser-combinators.md §7.5). Most of the
machine's cost is the effect runtime's own work per operation: building a
resumption, routing the operation through every handler between it and
the one that does the work, and building it again on the way back. This
note describes how handlers run today, what Koka, OCaml 5 and Effekt do
about operations that resume once at the end of their clause, and three
options for Stitchwort.

Tags: **[checked]** means read in the source or measured; **[inferred]**
means worked out from the code or the measurements without being run;
**[speculative]** means a guess.

## In brief

- An operation costs about 27 heap allocations when its handler is the
  only one around it, and **19 more for every handler it crosses** whose
  clause only performs the operation again, as `Parse.optional` and
  `Parse.attempt` do (`k (Parse.mark())`). `findAll` makes 23 routed
  operations, 10 such crossings and 583 allocations per character of noise
  **[checked]** (§1.5).
- Koka runs a clause of the form `k e` (resumes once, last, `k` not used
  otherwise) where the operation is performed, without capturing anything;
  turning that off makes its counter benchmarks 10× slower. It needs
  *evidence passing* (each operation finds its handler directly) and a
  subtle `under` frame for operations the clause itself performs (§2).
- **Option C**: call a state loop's clauses directly, without going
  through `handlePlus` as a partial application. About 4 allocations per
  routed operation; small, local, one lane.
- **Option A**: within today's tree runtime, give each handler a fast path
  for clauses that resume once in tail position, and for clauses that
  only perform the operation again: no resumption handed to the clause, no
  lazy `Bind (Done y) …`, no clause call. About 14 of the 19 allocations
  per crossing **[inferred]**. Provably the same as today by the bind law
  that already justifies lazy resumption (effect-runtime.md §9.2).
- **Option B**: a stack of the running handler loops beside the machine's
  frames, so an operation skips forwarding handlers and runs a pure
  clause of the handler that does the work in place. The biggest gain
  (roughly half of `findAll`'s allocations **[speculative]**), and the
  biggest risk: it is where Koka found the optimisation "surprisingly
  subtle to get correct".
- **Recommendation**: C, then A, then measure `findAll` again; B only if
  that leaves the machine still far behind, and then as its own reviewed
  design.

## 1. How handlers run today

### 1.1 Computations are trees, run by a loop

The library defines a computation as a tree (`Effect.Comp`:
`Done value | Call o rest`) and a deep handler as a fold over it
(`Effect.foldComp`, crates/elab/src/std/core/Effect.sw:12-22). `handle`
elaborates to `foldComp done call c`, where `call` is
`handlePlus (elim clause₁ … clauseₙ) forward`: the ability's eliminator
dispatches the handler's own operations, and every other operation goes to
`forward`, which performs it again outside with the handler around the
rest: `o k => Call (sigInject m o) (y => k (sigReply m o y))`
(crates/elab/src/effects.rs:4206-4338; `handlePlus` is Effect.sw:128-132).
In computation mode an operation call becomes a `Call` of the operation
injected into the row, and effectful arguments are run first with `bind`
(effects.rs:27-31), so a clause `k (Parse.mark())` is `bind (Call mark
Done) (y => k y)`.

At run time the machine replaces `bind`, `foldComp`, `translate` and
`runPure` with natives (crates/rt/src/effect.rs:1-33, `EffectNatives`
at :122-214):

- `bind c k` calls `k x` at once if `c` is `Done x`, and otherwise builds
  a third kind of node, `Bind c k` (crates/rt/src/machine.rs:648-662).
- A fold runs its computation with one loop, `eff_run`
  (machine.rs:693-754). A `Bind` pushes its continuation onto a
  persistent linked list (`pending`, a cell `[k, next]` each); `Done` pops
  one and applies it on a new frame whose result comes back to the loop
  through `Ret::Eff` (a boxed `EffRet`: the handler, the pending list, the
  state); a `Call` ends the loop.
- At a `Call o rest`, `eff_call` (machine.rs:760-820) makes a `Resume`
  (the handler, `rest`, the pending list; effect.rs:247-258), wraps it in a
  function value, and applies the handler's `call` to `o` and that `k`.
- A handler whose result is again a computation (its *carrier* is a tree:
  any row with an ability outside it) resumes lazily: `k y` builds
  `Bind (Done y) r`, with `r` the same resumption made eager, and returns
  it (`resume_lazily`, effect.rs:475-484). Whoever runs the clause's result
  then runs `r y`, which applies `rest y` on a frame returning to a fresh
  `Ret::Eff` for the inner handler (`resume`, machine.rs:825-858). This is
  what keeps resumption from nesting a call per operation; its soundness
  argument is effect-runtime.md §9.2.

So an operation never finds its handler by searching. It *bubbles*: it is
a value that every enclosing fold receives in turn as the result of its
computation. Each fold that doesn't handle it calls its `forward` (or a
user clause that performs it again), which builds a new `Call` with a new
continuation for the next fold out, and so on. Every fold crossed costs a
resumption on the way out and a lazy `Bind` on the way back.

### 1.2 What crossing a re-performing handler costs

`Parse.optional` and `Parse.attempt` handle every `Parse` operation, each
with a clause that performs it again unchanged, for example
`Parse.next passes, k => k (Parse.next passes)`
(crates/elab/src/std/Parse/Parse.sw:309-321, :457-473). When `next`
crosses one of them on its way to `runFrom`:

1. `optional`'s loop meets `Call (next passes) rest`: a `Resume`, a lazy
   `k`, and a call of `handlePlus … o k`, which dispatches through the
   eliminator to the clause.
2. The clause builds `Call (next passes) Done` for the outer row, and
   `bind` turns it and `y => k y` into a `Bind` node: that is the fold's
   result, which goes up to `runFrom`'s loop.
3. `runFrom` handles `next` (its own route, §1.3) and resumes with `y`.
4. `y => k y` runs; `k` is lazy, so it builds `Bind (Done y) r`; the outer
   loop pushes and pops it, applies `r`, which pushes a frame with a new
   `Ret::Eff` for `optional` and applies `rest y`.

That is 19 allocations and 5 extra run-loop steps per crossing (§1.5).

### 1.3 State-passing handlers run as a loop

`Parse.runFrom` is a handler at the empty row whose result is a function
of the state (Parse.sw:119-137). Stage 4d (crates/rt/src/fusion.rs,
effect-runtime.md §9.7) recognises this shape after elaboration and
rewrites each clause `x, k => s => body` to `x, k => jump => s => body′`,
where a `k v s′` in tail position (through `let`, applied lambdas, `if`,
`Decidable.elim` and inlined `match`es; `tail`, fusion.rs:320) becomes
`jump v s′`. The fold becomes `EffectOp::FoldState`: a loop with the state
in a variable. At an operation (machine.rs:796-805) it builds a `Resume`,
a `StateK` function for `k`, a `JumpK` function, a boxed `Ret::Step`, and
applies `call o k jump s`. If the clause returns a `Jumped(v, s′)` value,
`state_step` (effect.rs:356-392, machine.rs:863-893) goes on with
`rest v` and state `s′` on no new frame. Every other use of `k` still gets
a real resumption, so the meaning is the tree's whatever the clause does.

The fused `call` is still `handlePlus (elim …) forward`, a partial
application holding two arguments. Applied to four (`o k jump s`), it is
over-applied (`handlePlus` takes four; a `Ret::Apply` box and a `Vec` keep
the rest) and the eliminator's result is under-applied (a new `Pap`, an
`Rc` and a boxed slice): `apply`, machine.rs:454-491.

### 1.4 JS and native

- **JS** (crates/js/src/effect.rs:253-352) has the same structure in
  JavaScript: `effRun` is the loop, `effFold`/`effFoldLazy` the folds
  (`effFoldLazy`'s `k` builds `{ tag: Bind, c: Done y, k: resume }`),
  `effStateLoop` the 4d loop, which recognises an `EffJump` result.
  `Gen::def_ref` calls the same `fusion` pass (crates/js/src/lib.rs:4138-4157).
  The fused `call` is curried, `call(o)(k)(effJump)(s)`.
- **Native** (crates/native, Cranelift) emits the run loop itself
  (`rt_loop`, `runs_loop` in crates/native/src/n1.rs:365-375) and calls
  leaf helpers in crates/rt/src/native_abi.rs (`sw_eff_begin`,
  `sw_eff_step`, `sw_state_step`, :2190-2520) that build and take apart
  values "exactly as the machine's `eff_run`, `eff_call` and `resume` do,
  in the same order". They share `effect.rs`'s leaves (`state_step`,
  `handler_for`, `resume_lazily`), so the machine and native code can't
  drift; the native agreement tests compare their allocation traces.

### 1.5 Measured

A test harness (not committed; a copy is in the session scratchpad) loads
`Std.Parse` programs, runs each on 20,000 characters of noise on the
machine, and counts heap blocks with a counting global allocator and the
runtime's `EffectCounts`. Release build of `main` at `bc6accb2`, Apple
silicon **[checked]**:

| program, per character | allocations | bytes | bytecode instructions | run-loop steps | routes | lazy resumes | binds | jumps |
|---|---|---|---|---|---|---|---|---|
| `findAll instruction` (day 3's grammar) | 583 | 39,576 | 1,157 | 96 | 23 | 10 | 28 | 11 |
| `skipAll`: one `next`, straight under `runFrom` | 27 | 2,374 | 83 | 3 | 1 | 0 | 1 | 1 |
| the same inside one `optional` | 46 | 3,677 | 105 | 8 | 2 | 1 | 2 | 1 |
| inside two `optional`s | 65 | 4,901 | 127 | 13 | 3 | 2 | 3 | 1 |
| inside a handler of another ability (`next` goes through its generated `forward` and a `translate`) | 60 | 4,558 | 142 | 8 | 4 | 1 | 1 | 1 |

So each re-performing handler crossed adds 19 allocations, 1.3 KB, 5 steps
and 22 bytecode instructions per operation; a generated forward plus the
`translate` that widens `{Parse}` to `{Parse, Poke}` adds 33. In
`findAll`, the 10 crossings are about 190 of the 583 allocations, a third
**[inferred]**. (Times from this harness aren't given: the machine was
under load, and two runs differed threefold.)

Of the 27 allocations for an operation straight under `runFrom`, about 10
are the runtime's route (the `Resume`, `StateK`, `JumpK`, `Ret::Step`,
`Jumped` and `Ret::Eff` values, and four for the over- and
under-application through `handlePlus`) and the rest are the operation's
own tree (its `Call` node, the injected operation, `rest`'s closure, a
`Bind` node and a pending cell) and the program's own data (the `Option`,
the pair, the new state record) **[inferred, from reading
machine.rs:760-893 and the counts above]**.

## 2. What others do

### Koka: evidence passing and tail-resumptive operations

**Effect Handlers, Evidently** (Xie, Brachthäuser, Hillerström, Schuster,
Leijen, ICFP 2020; read in full except the proof appendices). The handlers
in scope are passed down to every operation as an *evidence vector*, so an
operation finds its handler by lookup, not by searching the stack (§4).
With the handler in hand, a clause of the form `op → λx.λk. k e` with
`k ∉ fv(e)` can run "in place": "This is an important optimization that
enables truly efficient effect operations at a cost similar to a virtual
method call" (§1). The implementation (§6.2) tags each clause when the
handler is made: `data pop … = tail : (α → mon μ β) → … | normal : …`,
and `perform_op w x = let (m, h) = w.l in case h.op of | tail f → f x |
normal f → yield m (f x)`. "Since f has already captured its evidence w,
it can still perform operations itself." The price is a restriction:
evidence translation is only coherent for *scoped resumptions*, ones
"applied under the same handler context as it was captured" (§2.2,
§4.5); the formalism gets stuck (`guard`) otherwise. Their JS prototype
was 1.94× faster than Koka's earlier runtime on a counter (§6.5).

**Generalized Evidence Passing for Effect Handlers** (Xie and Leijen,
ICFP 2021; read in full). This lifts the scoped-resumption restriction
and formalises the in-place rule for the first time. The tail-resumptive
form (§2.6) is `op ↦ λx. λk. k e where k ∉ fv(e)`; a clause that resumes
in tail position on every branch counts too ("λx k. if x == 0 then k 1
else k 2 which can be transformed to λx k. k (if x == 0 then 1 else 2)",
footnote 2). In place, `e` must run "under an `under l` frame", which
"ensures that if the operation clause e itself performs operations, these
are resolved correctly with respect to the actual handler up in the
evaluation context" (§2.6); without it, an operation of the clause would
be handled by the handler's own clauses again. They warn that "the
tail-resumptive optimization is surprisingly subtle to get correct — in
particular in combination with unscoped resumptions" (§1), and show why
(§2.12.2): their first `under` fixed the evidence to the vector where the
handler was defined, which "turns out to be unsound": a resumption
captured while the clause ran, and resumed later under a different
handler, would then see the old handler. The fix, `underk`, "re-finds the
correct evidence vector w′ from the current evidence vector w to resume
under" (§4.2), and they prove the optimised program contextually
equivalent to the original (Theorem 5). The benchmarks (§5): turning the
optimisation off "causes Koka to always allocate a resumption and take
the slow path through the monadic bindings making it 10× slower"; with
evidence, nested handlers cost nothing per operation ("the execution times
of the tail-resumptive get and set operations are independent of any other
handlers that are in the context", counter1, counter10). Also relevant:
*bind-inlining* ("if no operation performs a full yield, no allocation
happens along this path", §2.10), which pays off only together with the
in-place rule.

**Koka today.** The book's §3.4.3 ("Tail-Resumptive Operations",
[link](https://koka-lang.github.io/koka/doc/book.html#sec-opfun)) has a
`fun` clause that is tail-resumptive "by construction"; at the call "it
calls it directly as a regular function (except with an adjusted evidence
vector for its context)", giving "a performance cost very similar to
virtual method calls". An effect may also declare an operation `fun`, so
that every handler must define it that way.

### libhandler: Implementing Algebraic Effects in C

Leijen, MSR-TR-2017-23 (§5, "Optimized Tail Resumptions", read in full).
Handlers live on the C stack and are found by a search. For
`op(x) → resume(e)` with `resume ∉ fv(e)`, "we do not need to capture and
restore the context … at all but can directly evaluate the operation
expression e as if it was a regular function call! However, if we leave
the stack in place, we need to take special precautions to ensure that any
operations yielded in the evaluation of e[x ↦ v] are not handled by any
handler in handle_h · X_op": a `yield_op` frame on the handler stack that
makes the search skip from it to past `h` (§5.1, rule `thandle`). The code
(§5.2): `hstack_push_yield(h); value res = op->opfun(NULL,op,arg);
hstack_pop_yield(); return res;`, and `tail_resume` "is now just an
identity function". The counter benchmark went from about 1.3 million to
150 million operations a second, "about 18 instruction cycles" (§4.4,
§5.3).

### OCaml 5

Sivaramakrishnan et al., *Retrofitting Effect Handlers onto OCaml*, PLDI
2021 ([arXiv](https://arxiv.org/abs/2104.00250)). Each handler runs its
computation on a separate heap-allocated stack (a *fiber*); performing
switches to the parent fiber without copying, and continuations are
one-shot. OCaml has no in-place rule: every operation switches stacks,
and the switches are cheap ("23 ns, 5 ns, 11 ns and 7 ns" to create a
fiber, perform, resume and return, §6.3). A handler that doesn't match an
effect forwards it cheaply: "the effect is reperformed by appending the
fiber e to the tail of continuation ke … Thus, continuations are captured
without copying frames. Since every handler closure is evaluated until a
matching one is found, the time taken to handle an effect is linear in the
number of handlers" (§5.4). In the standard library this is
`| None -> reperform eff k last_fiber` in `match_with`
([effect.ml](https://github.com/ocaml/ocaml/blob/5.3/stdlib/effect.ml)),
and `caml_reperform` only links the current fiber onto the continuation
("Append to last_fiber",
[amd64.S](https://github.com/ocaml/ocaml/blob/5.3/runtime/amd64.S)): one
continuation object for the whole route, not one per handler. "We perform
tail-call optimisation so that resumptions at tail positions do not build
up stack" (§5.4). Xie and Leijen measured Koka 1.5× faster than OCaml on
counter1 because "multi-core OCaml always yields up one handler stack
segment at a time and thus each get and set operation needs to pass
through the reader handler" (2021, §5).

### Effekt

Effekt passes handlers as capabilities, lexically: an operation calls the
capability it was given, so there is no search and no forwarding
(Schuster, Brachthäuser, Ostermann, ICFP 2020, summarised in
effect-runtime.md §3). Since release 0.82.0 its optimiser also removes
tail resumptions at compile time (`StaticResumptions`,
[StaticResumptions.scala](https://github.com/effekt-lang/effekt/blob/1e486cd675b49e5c5fb8072c98b1511c411e76a3/effekt/shared/src/main/scala/effekt/core/optimizer/StaticResumptions.scala),
added in [#1471](https://github.com/effekt-lang/effekt/pull/1471)): "a
shift whose context is unknown (inside a call or a closure) …
`shift(p) { {k} => B[resume(k){s}] } ~> B[s]` if every exit resumes", and
"Sound iff every use of `k` is a tail shift, reached only through segments
no shift observes, and every exit is one too". Because handlers are
lexical, running `s` in place needs no `under`: its operations name their
capabilities.

### What carries over

- The tail-resumptive test is the same everywhere: `k` used once, as the
  last thing on every path, and nowhere else. Stitchwort's fusion pass
  already follows tail positions this way for `k v s′`.
- Running a clause *where the operation was* needs the handler without a
  search and, if the clause performs operations, an `under` that is
  re-found dynamically. Stitchwort has neither today: its operations
  bubble (§1.1).
- Running a clause *at the handler, without capturing* needs neither, and
  is the part that fits a tree runtime: it is what stage 4d's jump already
  does for state loops.
- Forwarding can cost one continuation for the whole route (OCaml) or
  nothing (Koka, Effekt); Stitchwort pays a full capture and a lazy resume
  per handler crossed.

## 3. Options

All three keep the runtime's representation (`Done | Call | Bind`, the
persistent pending list), unrestricted multi-shot resumptions, and the
invariant that routing an operation costs at most the handlers and
`translate`s it crosses (effect-runtime.md §9.1.6). None changes the
elaborator, the kernel or any hash.

### C. Call fused clauses directly

**What changes.** `fusion.rs` builds the fused `call` as
`handlePlus (elim …) forward`, a partial application. Instead it emits the
dispatch itself: a function of `o k jump s` that matches `o` (`L`/`R`,
then the ability's constructor) and calls the clause with all four
arguments. The runtime's lowering already inlines case trees inside an
expression (`match_body`, crates/rt/src/lower.rs:865); for JS, `Gen`
would emit the dispatch as a `switch`. The same can be done for every
fold's `call o k`, fused or not, if measuring shows the same
over/under-application there **[speculative until measured]**.

- *Machine and native*: only the lowered term changes; the natives don't.
- *JS*: the emitted `call` changes; `effStateLoop` doesn't.

**Gain.** One `Ret::Apply` (box and `Vec`) and one `Pap` (`Rc` and
slice) per jump: about 4 of the 27 allocations of an operation straight
under `runFrom`, and 44 of `findAll`'s 583 (8%) from its 11 jumps
**[inferred]**; up to twice that if lazy folds' routes have the same
pattern **[speculative]**.

**Risks.** None for meaning: it's the same function, applied all at once.
The allocation traces the native agreement tests compare change, in both
the machine and native code alike. Tests: the existing
`run_lines_agree_with_the_reference_evaluator` (crates/rt/tests/effect_runtime.rs:505,
and crates/cli/tests/extract.rs:39 for JS), `effect_differential.rs`, the
`Parse` library's tests, and AoC answers.

**Work.** One lane.

### A. Tail clauses at the handler, without capturing

**What changes.** A recognition step, beside fusion, marks each
operation clause of a fold as one of:

- *tail*: `x, k => k e` with `k` not free in `e`, on every exit (through
  `let`, `if`, `Decidable.elim` and inlined `match`es, as `fusion::tail`
  does). In computation mode this is `bind e (y => k y)` or `bind e k`; a
  clause that resumes in tail on some paths and not others is not tail.
- *re-perform*: a tail clause whose `e` performs the same operation again,
  unchanged, in the outer row (`k (Parse.next passes)` under
  `Parse.next passes`), and the generated `forward`.
- *other*: anything else; today's path.

The fold's handler record (`Handler::Fold`, effect.rs:221-226) gets the
table, and `eff_call` looks up the operation's constructor (`L`/`R`, then
the ability's tag) before building anything:

- *tail, eager fold* (the empty row, or a value carrier): call the clause
  with `k` erased, and go on with the loop from `rest e` and the same
  pending list. Nothing is captured: this is 4d's jump for handlers
  without a state. (At the empty row `e` can't perform.)
- *tail, lazy fold*: the fold's result is `bind e r`, with `r` the eager
  resumption (`Fun::Resume(…, false)`), instead of `bind e (y => k y)`
  with a lazy `k`. No lazy `Bind (Done y) …`, no `y => k y` closure.
- *re-perform*: don't call the clause at all. The fold's result is
  `Call o′ r`: `o′` is `o` itself where the inner and outer rows encode it
  the same way, otherwise the injected operation, with `r` applying the
  reply first, as `Handler::Translate`'s resumption already does
  (machine.rs:846-851).

Per backend: the machine's `eff_call` and `resume`; native code through
`sw_eff_step`, which shares effect.rs's leaves (so the change is made
once, in effect.rs, for both); JS's `effFold`/`effFoldLazy`/`effFoldCompIn`
get the same table and fast paths.

**Gain.** A re-performing crossing keeps a `Resume`, its function value,
the `Call` node, and the `Ret::Eff` box when resumed: about 5 of today's
19 allocations, and 2 of its 5 extra steps **[inferred]**. For `findAll`,
10 crossings × 14 is about 140 of 583 allocations (24%); with C, about a
third **[inferred]**. Time should fall by somewhat less, since about a
third of an operation's time on the machine is allocating and freeing
(effect-runtime.md §9.11): perhaps 20-30% for `findAll` **[speculative]**.
Tail clauses at the empty row (handlers without a state) lose their whole
route, as state handlers did in 4d.

**Risks.** Each fast path is an instance of the tree's equations, so the
argument is local:

- *Eager tail*: the tree says `call o k = k e`, and the eager `k y` is
  `foldComp d c (rest y)`, so the fold's result is the fold of `rest e`:
  what the loop computes by going on.
- *Lazy tail*: the clause's result is `bind e (y => k_lazy y)` with
  `k_lazy y = Bind (Done y) r`; by `bind (Done y) r ≈ r y`, the law
  effect-runtime.md §9.2 already relies on, this is `bind e r`. It holds
  only because runtime `foldComp` is sealed (§9.2), which it is.
- *Re-perform*: `bind (Call o′ Done) r = Call o′ (y => bind (Done y) r) ≈
  Call o′ r`; with a reply, the same through the `translate` equation.
- Clauses that discard `k`, resume twice, store `k` or resume in some
  branches only are *other* and keep today's path, so multi-shot and stored
  resumptions are untouched.
- The recognition must be exact: a clause misread as tail drops
  whatever else it does with `k`. Its tests should list clause shapes and
  what each is recognised as, as `state_handlers_run_as_a_loop_where_they_fit`
  does for 4d (crates/rt/tests/effect_runtime.rs:382).
- Folds over partial code (`Delay` carriers, `DelayK`) are left alone.

Tests that would show handlers still behave identically: new `-- run:`
lines in examples/extract/effect-handlers.sw and effect-state.sw (checked
against the reference evaluator on the machine and in JS by the two
`run_lines_agree_with_the_reference_evaluator` tests): a tail clause whose
`e` performs an outer operation; a tail clause with an `if`; a clause
that resumes in tail on one branch only; a re-perform with a different
argument (not the same operation unchanged, so only *tail*); a
re-performing handler around a state handler, around a handler that
discards `k`, and around one that resumes twice; and a resumption of an
outer handler, captured while a re-performing handler is in the way,
stored and resumed later under a different handler. `effect_differential.rs`
should generate tail and re-perform clauses (it already generates "resume
it once in tail position"). The effect counts pinned by tests
(steps, resumes, binds) change and are re-pinned.

**Work.** Two lanes: recognition and the machine/native fast paths; then
JS.

### B. A handler stack: skip forwarders, run pure clauses in place

**What changes.** The machine keeps, beside its frames, a stack of the
run loops currently running program code (one entry per frame that will
return to a `Ret::Eff` or `Ret::Step`), each with its handler and, for a
state loop, where its state is. When a loop meets `Call o rest` it walks
that stack outwards before building anything:

- a fold whose clause for `o` is *re-perform* (option A's table) or a
  `translate`: skip it, mapping `o` through its injection and keeping its
  reply for the way back;
- a fold or state loop whose clause for `o` is *tail* and **pure** (the
  handler is at the empty row, as every state loop is): call the clause in
  place; for a state loop, a `jump v s′` writes `s′` into that loop's
  state; map `v` back through the replies kept; and go on with `rest v` in
  the loop where the operation surfaced. Nothing is captured.
- anything else (a non-tail clause, a handler with effects outside it,
  the `IO` runner, a partial frame): stop, and take today's path from the
  innermost fold. Nothing has run except pure injections, so this is
  always safe.

Limiting in-place clauses to pure ones leaves out Koka's `under`: a pure
clause performs nothing, so there is nothing to route past its handler.
A second step (B2) would lower an operation performed directly in
computation mode to a runtime call that returns `Done y` when it was
handled in place, so that `bind (Done y) k` is a direct call and no `Call`
or `Bind` node is built: Koka's bind fast path.

Per backend: the machine (`eff_run`, `eff_call`, the frame push and
return paths); native code's `rt_loop` and helpers, which would need the
same stack, kept in step with native frames; JS's `effRun`/`effFold*`
(a module-level stack pushed and popped around running a computation).

**Gain.** For `findAll`, the 10 crossings (about 190 allocations) and
most of the route to `runFrom` (about 10 per operation, 11 operations)
go: roughly half of the 583 **[speculative]**. B2 would also remove the
operation's own `Call`, `Bind` and pending cells (`findAll` makes 28
binds a character). Nested handlers would stop costing per operation, as
in Koka's counter10.

**Risks.** This is the option where the literature found the bugs.

- The stack must always equal the chain of folds the operation would
  bubble through in the tree. That holds if it is derived from the live
  frames and never stored in a resumption: a resumption resumed later
  under different handlers (Stitchwort allows this; effect-state.sw
  already resumes stored resumptions after their handler returned) must
  see the handlers where it is resumed. Xie and Leijen's first
  formalisation got exactly this wrong (§2.12.2 of their 2021 paper).
- Writing a state loop's state in place must agree with the jump: a
  non-tail `k` of that loop starts a new loop with its own state, so the
  slot must belong to the loop instance, not the handler.
- The walk must stay within the routing invariant (cost bounded by
  handlers crossed, not frames), so the stack can't be found by scanning
  frames.
- Every push and pop is paid on every `Done` the loop delivers (96 steps a
  character in `findAll`), which may eat part of the gain; this needs a
  measured prototype before a decision.
- The allocation traces compared between the machine and native code
  change shape, and both must keep the same stack.

Tests: everything listed for A, plus the two examples of Xie and Leijen
2021 §2.12 written as `-- run:` lines: the "evil" handler that returns its
resumption, resumed under a second reader handler (must give 2, not 1), and
the same performed from inside a tail-resumptive clause; and
`effect_differential.rs` generating towers of re-performing handlers over
state handlers with resumptions stored and resumed elsewhere.

**Work.** A design note of its own with the semantic argument written out
and reviewed, a measured prototype of the stack's cost, then three to
four lanes (machine, native, JS, then B2).

## 4. Recommendation

Do **C**, then **A**, then measure `findAll` and day 3 again. Both are
local, each fast path is an instance of an equation the runtime already
relies on, they change all three backends in step, and together they
should remove about a third of `findAll`'s allocations **[inferred]**. They
also make tail clauses at the empty row as cheap as 4d made state
clauses, which helps any handler, not just `Std.Parse`.

Leave **B** until those numbers are in. It is the only option that makes
nested handlers free per operation, but it adds a second structure that
must track the frames exactly, and its correctness argument is the one the
Koka authors found subtle. If it is wanted, it should come as its own note
with an external review, limited at first to pure clauses (no `under`).

`Std.Parse` stays as written: `optional`, `attempt` and `label` are the
natural way to write these handlers, and the runtime should make them
cheap rather than the library avoid them.

## 5. Questions for the owner

- **Should C and A go ahead now, with B decided only after measuring
  them?** Recommendation: yes. They are small, local and provably the same
  as today; B is a larger change to how operations are routed.
- **Should tail-resumptive clauses be found automatically, or marked in
  the source as Koka's `fun` clauses are?** Recommendation:
  automatically, as fusion already finds `k v s′` and Effekt's optimiser
  finds tail resumptions. A marker would be new syntax for a speed
  property the compiler can see.
- **If B is pursued, should running a clause in place be limited at first
  to handlers at the empty row, whose clauses can't perform anything?**
  Recommendation: yes. It covers `runFrom` and every state loop, and it
  leaves out Koka's `under`, the part that was hardest to get right.

## Sources

- Xie, Brachthäuser, Hillerström, Schuster, Leijen. *Effect Handlers,
  Evidently*. ICFP 2020; MSR-TR-2020-23 with proofs:
  [PDF](https://www.microsoft.com/en-us/research/uploads/prod/2020/07/evidently-with-proofs-5f0b7d860b387.pdf).
  Read in full except appendix C (proofs).
- Xie, Leijen. *Generalized Evidence Passing for Effect Handlers*. ICFP
  2021: [PDF](https://www.microsoft.com/en-us/research/uploads/prod/2021/08/genev-icfp21.pdf).
  Read in full.
- Leijen. *Implementing Algebraic Effects in C*. MSR-TR-2017-23:
  [PDF](https://www.microsoft.com/en-us/research/wp-content/uploads/2017/06/algeff-in-c-tr-v2.pdf).
  Read §§4.4-7 in full.
- Koka book, §3.4.3 Tail-Resumptive Operations:
  [link](https://koka-lang.github.io/koka/doc/book.html#sec-opfun).
- Sivaramakrishnan, Dolan, White, Kelly, Jaffer, Madhavapeddy.
  *Retrofitting Effect Handlers onto OCaml*. PLDI 2021:
  [arXiv](https://arxiv.org/abs/2104.00250). Read §5.4 and §6.3.
  OCaml 5.3 sources: [effect.ml](https://github.com/ocaml/ocaml/blob/5.3/stdlib/effect.ml),
  [amd64.S](https://github.com/ocaml/ocaml/blob/5.3/runtime/amd64.S)
  (`caml_perform`, `caml_reperform`).
- Effekt: [StaticResumptions.scala](https://github.com/effekt-lang/effekt/blob/1e486cd675b49e5c5fb8072c98b1511c411e76a3/effekt/shared/src/main/scala/effekt/core/optimizer/StaticResumptions.scala)
  ([#1471](https://github.com/effekt-lang/effekt/pull/1471), in v0.82.0);
  Schuster, Brachthäuser, Ostermann, *Compiling Effect Handlers in
  Capability-Passing Style*, ICFP 2020, as summarised in
  [effect-runtime.md](effect-runtime.md) §3.
- In this repository: [effect-runtime.md](effect-runtime.md) §9 (the
  runtime's design and §9.2's soundness argument), §9.7 (stage 4d), §9.11
  (the cost of one operation); [parser-combinators.md](parser-combinators.md)
  §7.5 (the `findAll` measurements).
