# A linear-time, stack-safe runtime for effectful code

Status: design note for stage 4 of
[effect-polymorphism.md](effect-polymorphism.md) (SW-409, D1119), 24 Oct
2026. Reviewed in [effect-runtime-review.md](effect-runtime-review.md) and
[effect-runtime-external-review.md](effect-runtime-external-review.md).
**Decided: D1162 (§9)**, which amends the recommendation below and replaces
the staged plan of §7.

Claims about the codebase cite `file:line` and are marked **[checked]** (read
in the source on `main` at `cbf2ac4a`, or run with `target/release/stitchwort`
built from it, Node 22.23.3, on an Apple M4 Pro) or **[inferred]**. Claims
about other languages and papers cite a URL; **[unverified]** marks one I
couldn't confirm in a source. The benchmark and the prototype are in
`bench/effect-runtime/` (Appendix A), so every number here can be rerun.

## 0. Summary

The owner wants one `List.map` that is fast, stack-safe and provable for
pure and effectful callbacks alike. Stages 1 and 2 handle pure callbacks.
This note is about effectful ones.

**The problem, measured.** On `main`, `List.mapIn` with a callback that
performs an operation on every element is quadratic on both backends: 16,000
elements with a counter take 19.6 s natively, and 32,000 don't finish in two
minutes. Printing every element with `IO` is the same (16,000 elements: 39 s).
A `Fail` callback that never fails is linear. In JS, called as an exported
function on Node's normal stack, every effectful `mapIn` overflows the stack
somewhere between 1,000 and 4,000 elements (§1).

**Three causes, not one** (§1.3):

1. `bind` on a `Call` rebuilds the chain of pending `bind`s at every
   operation, so operation `i` costs `i`: quadratic in total. This is the
   classic free-monad problem (Voigtländer 2008).
2. In JS, effectful recursion such as `mapIn` nests a JS call for every
   `bind`, because `bind (Done x) k` calls `k` at once.
3. In JS, a state handler written the usual way (`next u, k => (s => k s
   (s + 1))`) makes a chain of calls, one per operation, each a tail call.
   JS doesn't optimise tail calls, so the chain grows the stack. The native
   runtime does optimise them.

**What the runtime must preserve** (§2): the kernel and the reference
evaluator keep `Comp` as the meaning of a computation. Since stage R2,
programs can't look at a computation tree; only `bind`, `foldComp`,
`translate`, `runPure` and the `IO` runner take one apart. So a backend may
represent computations however it likes, provided those few functions give
the answers the tree would. Proofs never mention the backends, so they stay
valid.

**Recommendation** (§6): keep `Comp`'s two constructors at runtime, but make
`bind` build a node and call nothing, and run every computation with a loop
that keeps the pending continuations on a linked list in the heap. Capturing
the continuation at an operation is then taking a pointer, resuming twice is
fine (the list is never changed), and nothing grows the JS stack. This is
the shape of PureScript's and Scala's stack-safe free monads, of Effekt's JS
runtime, and of Stitchwort's own machine for `Partial` (partial.md §7.4.4).
It replaces four library functions in each backend and nothing else. On top
of it, handlers that pass a parameter (state) run as a loop with the
parameter as a variable, which removes cause 3. A hand-written JS prototype
of both, patched into the generated module, runs every effectful variant at
1,000,000 elements on Node's normal stack in about a second, scaling
linearly, and agrees with the generated module on 60 cases, including
resuming one continuation many times (§5).

Koka's design (evidence passing, operations that resume in place) is faster
for state-like operations but stays quadratic for operations that really
capture a continuation, and Koka's own JS output overflows; OCaml 5's fibers
allow each continuation to be resumed only once. Koka's ideas are kept as
later optimisations; there is no current justification for paying the
architectural cost of CPS (§4, and §9); one-shot designs are rejected
because `Each` resumes twice.

## 1. The problem, measured

### 1.1 What was measured

`bench/effect-runtime/map.sw` maps `x => x + 1`-like callbacks over
`List.range n` and sums the result **[checked]**:

| Variant | What the callback does | Handler |
|---|---|---|
| `plain` | pure, with `List.map` | none |
| `pure` | pure, with `List.mapIn` (the empty row) | none |
| `fail` | `if x < 100000000 then x + 1 else Fail.fail …`: in `{Fail}`, never fails | `Fail.toResult` |
| `failLast` | fails at the last element | `Fail.toResult` |
| `state` | `x + Counter.next()`: an operation on every element | `Counter.number`, a state-passing handler (below) |
| `io` | `IO.print` of every element | `main`'s runner |

```
def Counter.number (prog: () -> {Counter} a): Nat -> a :=
  handle prog() with
    | return x => (s => x)
    | Counter.next u, k => (s => k s (s + 1))
```

Two ways of running it:

- `stitchwort run` (native, `crates/rt`) and `stitchwort run --js`, through
  `bench/effect-runtime/run.sh`: wall time of the whole command, including
  checking the file (about 0.15 s native, 0.26 s JS, the `n = 0` row). Note
  that `run --js` runs the program in a worker thread with a 2 GB stack
  (`crates/js/src/run.rs:57-60`) **[checked]**, so it hides most stack
  overflows.
- The exported functions of the module that `stitchwort build --js` makes,
  called from Node on its normal stack, as a library user or a web page would
  (`bench/effect-runtime/export.mjs`). One timed call per size, after a
  warm-up; the size doubles from 1,000 until the call fails. These times
  include converting the list at the boundary.

### 1.2 Results

Native and `run --js`, seconds of wall time, one run each **[checked]**:

| n | `plain` native | `fail` native | `failLast` native | `state` native | `io` native | `plain` JS | `fail` JS | `state` JS | `io` JS |
|---|---|---|---|---|---|---|---|---|---|
| 1,000 | 0.15 | 0.15 | 0.15 | 0.35 | 0.25 | 0.26 | 0.33 | 0.53 | 0.36 |
| 2,000 | | | | 0.96 | | | | 1.05 | |
| 4,000 | | | | 2.36 | 1.40 | | | 2.40 | 0.67 |
| 8,000 | | | | 5.32 | | | | out of memory | |
| 10,000 | 0.15 | 0.16 | 0.16 | | | 0.26 | 0.38 | | |
| 16,000 | | | | 19.60 | 39.36 | | | out of memory | 10.18 |
| 32,000 | | | | > 120 | | | | out of memory | |
| 64,000 | | | | > 120 | > 60 | | | | > 60 |
| 100,000 | 0.16 | 0.20 | 0.19 | | | 0.28 | 0.86 | | |
| 1,000,000 | 0.31 | 0.63 | 0.60 | | > 60 | 0.38 | 11.65 | | |

(`pure` native is 0.41 s at 1,000,000; `pure` and `failLast` under `run --js`
are 7.66 s and 12.94 s at 1,000,000.) "Out of memory" is Node's "JS heap out
of memory" in the worker **[checked]**.

Exported functions on Node's normal stack, milliseconds **[checked]**:

| n | `plain` | `pureMapIn` | `checked` (`fail`) | `failsLast` | `counted` (`state`) | `countedChecked` (`state` through a `Fail` handler) |
|---|---|---|---|---|---|---|
| 1,000 | 0.5 | 0.3 | 0.6 | 0.4 | 67 | 337 |
| 2,000 | 1.0 | 0.5 | 2.9 | stack overflow | 502 | 1,430 |
| 4,000 | 1.4 | stack overflow | stack overflow | | stack overflow | stack overflow |
| 1,024,000 | 132 | | | | | |

What this shows:

- **Quadratic time** when the callback performs an operation on every
  element (`state`, `io`), on both backends: doubling `n` multiplies the time
  by 2.3 to 4 at the sizes measured, and more beyond 16,000 natively.
  Probe 7 of effect-polymorphism.md found the same (32,000 elements, 62 s).
- **Linear time** when no operation is performed (`fail`) or only one
  (`failLast`), natively: 1,000,000 elements in about 0.5 s of running.
- **JS stack overflow** for every effectful variant called normally, at
  between 1,000 and 4,000 elements. Even with a 2 GB stack, deep JS
  recursion is slow (`fail` at 1,000,000: 11.7 s against 0.4 s for
  `plain`), and the quadratic `state` exhausts the heap at 8,000.
- `pureMapIn`'s overflow is stage 2's job (empty-row specialisation turns
  it into `map`'s loop), not this stage's.

### 1.3 Why

`mapIn`'s `Cons` case elaborates to `bindIn e (f x) (y => bindIn e (mapIn f
xs) (ys => doneIn e (Cons y ys)))`, and in a row with abilities `bindIn` is
`Effect.bind` (`Effect.sw`, `bindIn`) **[checked]**. The generated JS is the
library's definitions, compiled like any others **[checked]**:

```
const $Std$dEffect$dbind = (v4) => (v5) => {
  switch (v4.tag) {
    case "Done": { const v6 = v4.value; return (v5)(v6); }
    case "Call": { const v6 = v4.o; const v7 = v4.rest;
      return { tag: "Call", o: v6, rest: ((v8) => $Std$dEffect$dbind((v7)(v8))(v5)) }; }
  }
  ...
```

**Cause 1: rebuilt chains (quadratic time, both backends).** When element
`i` performs `next`, the computation is `i` `bind`s deep: each earlier
element is waiting, in a `bind`, for the rest of the list. `bind` on a `Call`
returns a new `Call` whose continuation calls `bind` again, so the `Call`
reaches the handler through `i` layers, and resuming it goes back down
through `i` layers before the next element runs. Element `i` costs `i`; `n`
elements cost about `n²/2`. Voigtländer calls this left-nested substitution
over a free monad: "quadratic runtime in n despite exploring only a single
tree path" (§2 of the
[paper](https://www.janis-voigtlaender.eu/papers/AsymptoticImprovementOfComputationsOverFreeMonads.pdf)).
The `io` variant is the same with `main`'s runner in the handler's place:
the runner performs each `Call` that reaches it and resumes it
(`crates/rt/src/run.rs:170-200`) **[checked]**, and every resumption goes
back down through the `bind`s.

**Cause 2: one JS call per `bind` (stack, JS only).** `bind (Done x) k`
calls `k` straight away, and `k` calls `mapIn` on the rest of the list,
which calls `bind` again: three JS frames per element, none of them a tail
call. That's why `checked` overflows at a few thousand elements although
nothing is ever performed. The native runtime has its own frame stack
(`crates/rt/src/lib.rs:8-10`) **[checked]**, so it only uses memory.

**Cause 3: a state handler's chain of tail calls (stack, JS only).** The
clause `next u, k => (s => k s (s + 1))` returns a function. Running the
handled computation to its first `next` gives `f₀`; `f₀ 0` resumes `k 0`,
which runs to the next `next` and returns `f₁`, and `f₀` then calls `f₁ 1`
as its last act, and so on. Each `fᵢ` waits on the JS stack for `fᵢ₊₁`,
because JS engines don't optimise tail calls. So even once causes 1 and 2
are fixed, `counted` overflows at the same size: the prototype of §5 shows
it, and its stack trace at the overflow is the clause
`(v4) => ((v5) => (v5)($Std$dNat$dadd(v4)(1n)))($Std$dEffect$drunPure((v3)(v4)))`
repeated **[checked]**. The native runtime compiles tail calls as jumps
(`TailCall`, `TailApply`, `crates/rt/src/code.rs:93-114`) **[checked]**, so
cause 3 doesn't arise there.

The causes are independent: fixing 1 leaves 2 and 3 in JS; fixing 1 and 2
leaves 3.

## 2. What the runtime must preserve

**The specification is the tree.** The kernel's `Comp` and the library's
definitions of `bind`, `foldComp`, `translate` and `runPure`
(`crates/elab/src/std/core/Effect.sw:12-60, 135-137`) **[checked]** are the
meaning of every effectful program. Proofs reason about them, and the
reference evaluator runs them. None of that changes: stage 4 touches only
the two untrusted backends (`crates/rt/src/lib.rs:1-4`: the runtime "can
only get a program's output wrong, never make a false proof check")
**[checked]**.

**Why the backends are free to choose.** Since stage R2
([proof-reification.md](proof-reification.md), "As built (stage R2)"), a
program outside the library can't name `Done`, `Call`, `foldComp`, `bind`,
`translate` or `runPure` in code that runs (`E-PROOF-ONLY`) **[checked]**.
The library uses them at run time only in the definitions above, in the
row helpers built from them (`doneIn`, `bindIn`, `liftIn`, `lowerIn`,
`widenIn`, `Effect.sw:165-200`) and in what the elaborator generates
(`Done` and `Call` for operations, `bind` for sequencing, `foldComp` for
`handle`, `translate` between rows) **[checked]**. Apart from these, the only
consumers of a computation at run time are the runners, which step `main`'s
`IO` tree (`lift` into `Delay`, `crates/rt/src/run.rs:150, 170-200`)
**[checked]**.

So a computation at run time is an abstract value: something built by
`Done`, `Call` and `bind`, and taken apart only by `foldComp`, `translate`,
`runPure` and the runner. Any representation works if those agree with the
tree. Concretely, writing `≈` for "gives the same result in every use":

```
bind (Done x) k        ≈ k x
bind (Call o r) k      ≈ Call o (y => bind (r y) k)
foldComp d c (Done x)  ≈ d x
foldComp d c (Call o r) ≈ c o (y => foldComp d c (r y))
translate m (Done x)   ≈ Done x
translate m (Call o r) ≈ Call (inject m o) (y => translate m (r (reply m o y)))
runPure (Done x)       ≈ x
```

These are the library's own equations, so an implementation that satisfies
them computes the same values as the tree. The obligation is checked, not
proved: by differential tests against the reference evaluator (§7), as the
backends already are, and in the shape that `crates/partial-model` used for
`Partial`'s machine (a literal transcription of the equations, a machine,
and generated programs whose complete operation traces must agree;
partial.md §7.4.4) **[checked]**.

**What may differ.** When pure code runs. Under the tree, `bind (Done x) k`
evaluates `k x` at once; under a runtime that builds a node, later. Pure
code is total and has no side effects, so the difference shows only in
resource use (stack, memory, time), which the backends already don't share
with the reference evaluator. The order of operations is the tree's in every
design below.

**Multi-shot.** A handler clause may call `k` any number of times:
`Each.collect`'s `fork` clause calls it twice (`Each.sw`, `Each.both`)
**[checked]**, and `k` is an ordinary function that can be stored in the
handler's result. So the runtime must allow a continuation to be resumed
more than once, and later than the clause returns.

**Deep handlers.** `handle` is `foldComp`, so a resumed continuation is
still handled by the same handler (abilities.md, "A deep handler is a
fold") **[checked]**. Operations a handler doesn't handle are re-emitted
outward with a continuation that resumes the inner fold (the generated
`handlePlus … (forward)` in `Fail.toResult`'s JS) **[checked]**.

## 3. What others do

Read in the sources; the two literature summaries behind this section were
made for this note, from the papers' PDFs and the projects' current sources
on GitHub.

### Free monads made fast

- **Codensity** (Voigtländer, MPC 2008,
  [PDF](https://www.janis-voigtlaender.eu/papers/AsymptoticImprovementOfComputationsOverFreeMonads.pdf)).
  Represent a computation by "what to do with its result"; this "makes
  monadic substitution a constant-time operation and can have further
  benefits regarding stack consumption" (§6). The catch, from the next
  paper: converting back to a tree to look at it isn't constant time.
- **Reflection without remorse** (van der Ploeg and Kiselyov, Haskell 2014,
  [PDF](https://okmij.org/ftp/Haskell/zseq.pdf)). CPS "only solve[s]
  performance problems if our usage ... is strictly separated into a build
  ... phase and an observation phase. If we alternate between building and
  observing ... performance problems will resurface" (§3.1). A handler
  alternates: it looks at each operation and resumes. Their fix keeps the
  pending binds as an explicit sequence with constant-time append (§4); a
  logical-cut benchmark goes from quadratic to linear (§6.3).
- **Freer monads** (Kiselyov and Ishii, Haskell 2015,
  [PDF](https://okmij.org/ftp/Haskell/extensible/more.pdf)). `Impure u q`,
  with `q` a queue of continuations (`FTCQueue`); `bind` appends to the
  queue; handlers are deep (`handle_relay`) and may resume more than once
  (the `NDet` handler plugs "first True and then False into the very same
  context", §5). The queue's constant time is an average: removing from the
  front rotates a tree and isn't remembered, so resuming the same
  continuation twice can pay that cost twice ([source](https://okmij.org/ftp/Haskell/extensible/FTCQueue1.hs);
  the consequence for multi-shot is my inference).
- **PureScript and Scala.** `purescript-free` keeps the binds in a
  catenable list "in the spirit of Reflection without Remorse" and runs
  them with a loop the compiler turns into `while`
  ([Free.purs](https://github.com/purescript/purescript-free/blob/master/src/Control/Monad/Free.purs));
  `purescript-aff`'s runner pushes each `bind`'s continuation on a heap list
  ([Aff.js](https://github.com/purescript-contrib/purescript-aff/blob/main/src/Effect/Aff.js)).
  `cats.Free` builds a `FlatMapped` node per `bind` and reassociates in a
  `@tailrec` loop
  ([Free.scala](https://github.com/typelevel/cats/blob/main/free/src/main/scala/cats/free/Free.scala));
  cats-effect's `IO` keeps continuations on heap stacks
  ([IOFiber.scala](https://github.com/typelevel/cats-effect/blob/series/3.x/core/shared/src/main/scala/cats/effect/IOFiber.scala)).
  Both run on JS (PureScript natively, Scala through Scala.js
  **[unverified]** for the Scala.js detail). `Aff` and `IO` resume each
  continuation once; `Free` is an immutable value, so it may be resumed
  more often.

### Handlers compiled for speed

- **Koka: evidence passing** (Xie, Brachthäuser, Hillerström, Schuster,
  Leijen, ICFP 2020,
  [TR](https://www.microsoft.com/en-us/research/uploads/prod/2020/07/evidently-with-proofs-5f0b7d860b387.pdf);
  Xie and Leijen, ICFP 2021,
  [PDF](https://www.microsoft.com/en-us/research/uploads/prod/2021/08/genev-icfp21.pdf)).
  Handlers are passed down as an "evidence vector", so an operation finds
  its handler by lookup. An operation whose clause has the form `λx k. k e`
  (resumes once, as its last act) runs "in place … at a cost similar to a
  virtual method call" (2020 TR §1); turning this off makes the counter
  benchmark "10× slower" (2021 §5). Other operations *yield*: the code is
  translated into a `Pure | Yield` monad, the same shape as `Done | Call`,
  and each bind a yield passes adds one closure to the continuation (2021
  §2.9). So such an operation costs time proportional to the frames between
  it and its handler, which for `mapIn` is the same quadratic as cause 1
  (my inference; the 2020 TR §6.4 says CPS "may be more efficient if one
  often yields"). The C backend returns normally and sets a flag when
  yielding (2021 §2.11). Resumptions are ordinary closures, so multi-shot
  works. In JS, Koka has no trampoline (no match for "trampolin" in its
  sources at commit `198fc3bb`), only self tail calls as loops and tail
  recursion modulo cons, and the Effekt authors report that Koka's JS output
  "leads to a stack overflow for larger numbers"
  ([Schuster et al. 2020 §6](https://se.cs.uni-tuebingen.de/publications/schuster20capability.pdf)).
- **Koka: bind-inlining** (2021 §2.10). Each `bind` is compiled as "if the
  result is `Pure`, continue here; else extend the yield". "If no operation
  performs a full yield, no allocation happens along this path and
  tail-recursive calls are preserved."
- **Effekt: capability passing and its JS runtime** (Schuster,
  Brachthäuser, Ostermann, ICFP 2020,
  [PDF](https://se.cs.uni-tuebingen.de/publications/schuster20capability.pdf)).
  The current JS runtime
  ([effekt_runtime.js](https://github.com/effekt-lang/effekt/blob/master/libraries/js/effekt_runtime.js))
  compiles to CPS: every function takes its continuation and a *meta-stack*
  of segments, one per handler (`{stack, prompt, arena, rest}`). Capturing a
  continuation walks the meta-stack to the handler's prompt and keeps the
  segments as an immutable list (deep, since the handler's own segment is
  included); resuming pushes them back; `RUN_TOPLEVEL` is `while (true) { a
  = a() }`, a trampoline. So: stack-safe, multi-shot, and capturing costs the
  number of handlers crossed, not the number of frames. The price is a heap
  closure per non-tail call and a bounce per jump.
- **Effekt: LLVM backend** (Muhcu et al., ICFP 2025,
  [PDF](https://se.cs.uni-tuebingen.de/publications/muhcu2025multiple.pdf)).
  Segmented stacks with reference counting: resuming once is constant time,
  "we only copy whenever we resume a shared continuation". Reported 2.2×
  faster than OCaml and 10.2× faster than Koka (geometric mean). Not
  applicable to JS, but it shows multi-shot needn't cost the one-shot case
  anything.
- **Links: generalised continuations** (Hillerström, Lindley, Atkey,
  Sivaramakrishnan, FSCD 2017,
  [DROPS](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2017.18);
  JFP 2020,
  [PDF](https://strathprints.strath.ac.uk/71892/1/Hillerstrom_etal_JFP_2020_Effect_handlers_via_generalised_continuations.pdf)).
  The continuation "is composed of alternating pure and handler
  continuations" (§5): the same structure as Effekt's meta-stack. Deep,
  shallow and parameterised handlers; resuming more than once (§2.3). The
  JS backend only CPS-translates effectful code, "crucial in practice for
  performance", and trampolines (§8); the runtime bounces every 60th call
  (`yieldGranularity = 60`,
  [jslib.js](https://github.com/links-lang/links/blob/master/lib/js/jslib.js)).
- **OCaml 5** (Sivaramakrishnan et al., PLDI 2021,
  [arXiv](https://arxiv.org/abs/2104.00250)). Each handler runs on its own
  small heap-allocated stack (a fiber); performing and resuming switch
  stacks without copying (a few nanoseconds each, §6.3). But "our
  continuations are one-shot" (§3); the manual: "OCaml does not support
  multi-shot continuations" ([§24.5](https://ocaml.org/manual/5.3/effects.html)).
  `js_of_ocaml` compiles effects to CPS where an analysis says they may
  occur, and bounces through a trampoline when a depth counter runs out
  (`caml_stack_check_depth`,
  [jslib.js](https://github.com/ocsigen/js_of_ocaml/blob/master/runtime/js/jslib.js));
  its continuations are one-shot too
  ([effects.mld](https://github.com/ocsigen/js_of_ocaml/blob/master/manual/effects.mld)).
  WebAssembly's stack-switching proposal is at phase 3, and also one-shot
  ([proposals](https://github.com/WebAssembly/proposals); Muhcu et al. §1).
- **Unison.** Handlers are shallow: a handler re-handles the continuation
  itself, and "a handler can choose to call the continuation or not, or to
  call it multiple times"
  ([docs](https://www.unison-lang.org/docs/language-reference/abilities-and-ability-handlers/)).
  The interpreter captures a continuation by copying the stack between the
  request and the handler into an immutable array, and copies it back to
  resume (`grabSeg`, `dumpSeg` in
  [Machine.hs](https://github.com/unisonweb/unison/blob/trunk/unison-runtime/src/Unison/Runtime/Machine.hs)
  and `Stack.hs`). So each operation costs the depth of the stack between it
  and its handler: for a non-tail-recursive `map`, quadratic again (my
  inference). There is a newer no-copy path for handlers that resume at most
  once ("affine", `MCode.hs`), whose details I didn't trace. Unison has no
  JS backend.
- **Kotlin coroutines** compile suspending functions to state machines with
  heap frames; "resuming the same continuation more than once is not
  allowed" ([KEEP](https://github.com/Kotlin/KEEP/blob/master/proposals/coroutines.md)).

### In short

| | Cost of `bind` | Cost of an operation that captures `k` | Resume `k` twice | Stack-safe in JS | Pure code pays |
|---|---|---|---|---|---|
| Stitchwort today | left-nested: grows with depth | grows with depth (cause 1) | yes | no | nothing (after stage 2) |
| Codensity alone | constant | grows when observed (RwR §3) | yes | needs a trampoline | a closure per `bind` |
| Freer, type-aligned queue | constant | average constant | yes (average not kept) | not addressed | a queue cell per `bind` |
| Free with a run loop (PureScript, cats) | constant (a node) | constant (heap list) | yes for `Free` | yes | nothing if only effectful code uses it |
| Koka (evidence, yield) | free on the `Pure` path | grows with depth; in place if tail-resumptive | yes | no | nothing |
| Effekt JS (CPS, meta-stack) | a closure | grows with handlers crossed, not frames | yes | yes (trampoline) | nothing if only effectful code is CPS'd |
| OCaml 5 fibers | native call | constant | **no** | `js_of_ocaml`: yes (CPS) | about 1% |
| Unison interpreter | native frames | copies the stack segment | yes | no JS backend | low |

## 4. Candidate designs

Each candidate is judged on Stitchwort's constraints: deep handlers as
folds; `k` resumable any number of times and storable; dependent types
erased before either backend; two backends (the native runtime, which also
runs in the wasm playground, and JS); pure code kept as fast as stage 2 makes
it; and agreement with the tree (§2).

### A. A run loop with heap continuations (recommended)

Keep `Done` and `Call` as they are at run time. Add one internal node,
`Bind c k`, which programs never see. Then:

- `bind c k` builds `Bind c k` and calls nothing. Constant time, no stack.
- One loop, `run(c, pending)`, does the work: on `Bind c k` it pushes `k`
  onto `pending` (a linked list in the heap) and goes on with `c`; on
  `Done v` it pops a continuation and applies it, or stops if none is left;
  on `Call o rest` it stops and returns the operation with `rest` and
  `pending`. Each `bind` is entered once and left once, so reaching the next
  operation is linear in the work done.
- `foldComp done call c` runs `c`; at `Done v` it is `done v`; at an
  operation it is `call o k` with `k = y => foldComp done call` of `rest y`
  continued with the same `pending`. Capturing `k` is keeping a pointer to
  `pending`: no copying, whatever its length.
- `translate` and `runPure` are the same loop with a different ending, and
  the runners use the same loop instead of their own `Done`/`Call` cases.

**Multi-shot**: `pending` is never changed, only extended by new cells, so
resuming `k` twice runs from the same list twice. Both branches share the
cells they have in common.

**Stack safety**: no JS call is nested per `bind` (causes 1 and 2 gone).
Nesting grows only with the number of handlers active at once, and with
resumptions that pure code nests (cause 3, design A′ below).

**Cost**: a `Bind` node and a list cell per `bind`, one dispatch per step.
Effectful code that performs nothing gets slower per element than today's
direct calls on the `Done` path, but stops overflowing; in the prototype,
`checked` (`{Fail}`, never failing) is 4.6 to 5.7 times `plain` at 1,000,000
elements (§5). Pure code is untouched: at the empty row `bindIn` is
application and never reaches `bind` (`Effect.sw`, `bindIn`) **[checked]**,
and stage 2 compiles empty-row code without the row argument.

**Fit**: the change replaces four library functions (`bind`, `foldComp`,
`translate`, `runPure`) in each backend and teaches the two runners about
`Bind`. Codegen for everything else is unchanged. It is also the shape of
the machine Stitchwort already uses for `Partial`: "an abstract machine whose
pending work is an explicit stack of frames on the heap" (partial.md
§7.4.4) **[checked]**, with `Delay`'s `bindD` already a stored node that
calls nothing (partial.md §7.4.1) **[checked]**.

In the native runtime the loop must run on the machine's own frames, as
library code or machine instructions, not as a Rust function that calls
back into the machine: a clause's tail call of `k` must stay a `TailApply`,
or cause 3 reappears as Rust stack depth **[inferred]**.

### A′. Handlers with a parameter (with A, for JS)

A state handler is written as a fold whose result is a function of the
state. Recognise that shape: every clause, `return` included, is a lambda
over the same parameters (`return x => (s => …)`, `op x, k => (s => …)`).
Run such a handler as a loop with the parameter as a variable: a clause body
that ends with `k v s′` sets the parameter to `s′` and continues the loop
with `v`, instead of calling `k`. Uses of `k` anywhere else (not last, under
a lambda, twice) get a real function, so the meaning is unchanged; only the
common tail call is turned into a jump. This is what Links calls a
parameterised handler (JFP 2020 §2), and what Koka's in-place resumption does
for state (2021 footnote 2).

This removes cause 3. It matters mainly in JS; the native runtime already
makes the tail call a jump, but saves a closure per operation.

Recognising the shape is easiest in the elaborator, which sees the clauses
as written: it could emit a parameterised fold (`Effect.foldCompWith`,
defined in the library by `foldComp`, so proofs unfold it as before) that
the backends implement as a loop. Hashes of handlers that use it would
change, which is acceptable while there are no users. The alternative is surface syntax
for handler parameters, as in Links (decision Q2).

### B. Selective CPS with a trampoline and a meta-stack (Effekt, Links)

Compile every effectful function to continuation-passing style, with a
meta-stack of (frames, handler) segments, and run it with a trampoline.
Pure code stays direct.

- Linear, stack-safe, multi-shot, deep: yes, all proven in Effekt's and
  Links' JS runtimes.
- Cost: a closure per non-tail call in effectful code and a bounce per
  jump, similar to A.
- Fit: much larger. Every effectful function's calling convention changes in
  both backends (`crates/js/src/lib.rs` is 5,050 lines; the native runtime's
  lowering and register code would need a second calling convention), and
  the boundary between CPS and direct code needs care wherever effectful
  and pure code meet. Cause 3 still needs A′, because the state chain runs
  in pure code, which selective CPS leaves direct **[inferred]**.
- Gains over A: none that the benchmarks need. A CPS'd function can resume
  without first returning to a loop, which may be faster for deep handler
  stacks **[inferred]**.

### C. Evidence passing with yields (Koka)

Pass handlers down; run tail-resumptive clauses in place; compile other
operations as yields that bubble outward through inlined binds.

- Fast for state-like operations (in place, no allocation).
- An operation that captures `k` bubbles through every frame between it and
  its handler: quadratic for `mapIn` with such an operation (§3), and the JS
  stack holds the frames, so no stack safety. Koka's own JS output
  overflows.
- Fit: needs a calling convention with evidence and a yield check after
  every effectful call in both backends: as large as B.
- Its two good ideas transfer to A as optimisations (D below): in-place
  resumption for tail-resumptive clauses, and a fast path for `bind`.

### D. Fibers or stack switching (OCaml 5, WebAssembly)

Run each handler on its own stack and switch stacks at operations.

- Constant-time operations with no copying, but continuations are one-shot
  in OCaml 5, `js_of_ocaml` and the WebAssembly proposal. Stitchwort's `k`
  is multi-shot (`Each.collect`), so this would need copying stacks on a
  second resume (as Effekt's LLVM backend does) and has no JS
  implementation without CPS. **Rejected** for both backends.

### E. Codensity or a type-aligned queue alone

Represent a computation in CPS (codensity), or keep `Call`'s continuation as
a queue (freer). Either makes `bind` constant time, so cause 1 goes. But
neither bounds the JS stack: `bind (Done x) k` still calls `k` directly
(cause 2), and the queue's average-time guarantee isn't kept under
multi-shot. A is the queue idea with the loop that stack safety needs, and
with a plain linked list, since the loop only ever pushes onto or pops from
the front.

### Optimisations on top of A (later, measured)

- **A fast path for `bind`.** If `c` is already `Done`, call `k` directly,
  but only while a depth counter allows, then fall back to building the
  node (how `js_of_ocaml` bounds its stack). Recovers most of the
  direct-call speed for code that rarely performs.
- **Tail-resumptive clauses in place.** An operation whose clause is `k e`
  needn't capture `k` at all: compute the answer and continue. With A′, the
  state handler's clause is already this.
- **Evidence passing.** An operation that passes through other handlers
  today is re-emitted by each (forwarding, §2). Passing the handler down
  makes the lookup constant. Worth it only if programs nest many handlers.
- **Fusing `translate`s.** Adjacent row mappings compose into one.

Each is a constant factor, not a change in growth, so each should be added
only when a benchmark shows it pays.

## 5. The prototype

To check that A and A′ meet the requirement before recommending them,
`bench/effect-runtime/prototype.mjs` patches the generated module of
`map.sw`: it replaces `bind`, `foldComp`, `translate` and `runPure` with
A's loop (40 lines of JS), and, with `--parameter`, replaces
`Counter.number` with the loop A′ would generate. Everything else is as
generated. `bench/effect-runtime/agree.mjs` then compares the patched and
the generated modules on 60 small cases: every variant at sizes 0 to 500, a
counter inside a `Fail` handler failing at various points
(`countedChecked`), and `Each.collect` over `mapIn` resuming each
continuation twice (`choices`, up to 4,096 results). All 60 agree, for both
patched modules **[checked]**.

Exported functions on Node's normal stack, milliseconds, one run each
**[checked]**:

| n | `plain` | `checked` | `failsLast` | `counted` | `countedChecked` |
|---|---|---|---|---|---|
| generated (today), largest size that works | 1,024,000: 132 | 2,000: 2.9 | 1,000: 0.4 | 2,000: 502 | 2,000: 1,430 |
| A, 2,000 | 1.0 | 2.7 | 0.6 | 1.2 | 4.8 |
| A, 4,000 | 0.5 | 2.4 | 2.7 | stack overflow | stack overflow |
| A, 1,024,000 | 142 | 659 | 1,036 | | |
| A + A′, 64,000 | 27 | 82 | 70 | 41 | 110 |
| A + A′, 256,000 | 51 | 216 | 346 | 145 | 482 |
| A + A′, 1,024,000 | 216 | 1,226 | 549 | 787 | 1,007 |

- **Cause 1 is gone**: `counted` at 2,000 drops from 502 ms to 1.2 ms.
- **Cause 2 is gone**: `checked` and `failsLast` run at 1,024,000 on the
  normal stack.
- **Cause 3 remains under A alone** (`counted` overflows at 4,000; the stack
  trace is the state clause, §1.3) **and goes with A′**.
- **Linear**: from 64,000 to 1,024,000, `counted` grows by 1.7, 2.1, 2.3 and
  2.3 per doubling (the last two include garbage collection, I assume).
- Single runs: `checked` took 659 ms in one run and 1,226 ms in another, so
  differences under a factor of 2 between these columns are noise.

The prototype says nothing about the native runtime, which needs its own
implementation (stage 4a). Its causes are only 1 there (§1.3), which A
removes by the same argument **[inferred]**.

## 6. Recommendation

Adopt **A** in both backends, then **A′**, then optimisations only where
benchmarks justify them.

- A is the smallest change that removes causes 1 and 2: four library
  functions per backend and the two runners. It keeps `Done` and `Call`
  at run time, so the generated code, the erasure decisions shared by the
  backends, and debugging output stay as they are, and differential tests
  compare like with like.
- It supports everything Stitchwort's handlers do (deep, resumed any number
  of times, stored), which rules out D and makes C quadratic.
- It's the design the language already uses for `Partial`, and its testing
  approach (partial-model's reference, machine and generated programs) can
  be reused.
- B gives the same guarantees for a much larger change, and still needs A′.
- A′ is needed in JS for the state handler, the most common handler shape;
  without it `counted` overflows at 4,000 elements whatever else is done.

What this doesn't do: pure non-tail recursion in JS (any `foldRight`-like
pure function) still uses the JS stack. That's not an effects problem; stage
2 handles `map`, and other functions are tracked separately.

## 7. Staged plan (superseded by §9.3)

| Stage | Work | Acceptance |
|---|---|---|
| 4a | Native runtime: `Bind` node, the loop, `foldComp`, `translate`, `runPure` replaced; the `IO` runner and `lift` use the loop. The loop runs on the machine's own frames. A differential test generator in the style of `crates/partial-model`: random programs of nested handlers (state, fail, choice, forwarding through an open-row handler, `translate` between rows), each run on the reference evaluator and the native runtime, outputs and `IO` traces compared | `bench/effect-runtime` `state` and `io` at 1,000,000 elements natively; from 125,000 to 1,000,000, each doubling at most 2.5 times the time; `choices` at 12 agrees; the generated differential tests and the existing rt differential tests pass |
| 4b | JS: the same in the JS prelude and in `run.mjs`'s stepper | `checked`, `failsLast` and `countedChecked` exported, on Node's normal stack, at 1,000,000 elements; linear as in 4a; the same differential tests against JS, and `agree.mjs` |
| 4c | A′: the elaborator emits a parameterised fold for handlers whose clauses are all lambdas over the same parameters; both backends run it as a loop (or surface syntax, per Q2) | `counted` exported, on Node's normal stack, at 1,000,000 elements; `Counter.number`-style handlers in std and AoC unchanged in source; proofs about them check |
| 4d | Optional, one lane each, only with a benchmark showing at least 1.5 times: `bind` fast path with a depth counter, tail-resumptive in place, evidence passing, `translate` fusion | the benchmark; no regression in 4a–4c's acceptance |

Each stage also keeps `plain` within 10% of today (stage 2's guarantee for
pure code).

## 8. Decisions for the owner

Numbers to be assigned on merge.

**Q1. The runtime representation for effectful code.**
(a) **[Recommended]** A: `Done`/`Call` plus an internal `Bind` node, run by a
loop with the pending continuations in a heap list (§4.A).
(b) B: selective CPS with a trampoline and a meta-stack, as Effekt and Links.
(c) C: Koka's evidence passing with yields.
(d) D: fibers or stack switching (rejected: one-shot).
Reason: (a) is linear, stack-safe and multi-shot for the smallest change,
and is already how `Partial` runs; (b) is the same guarantees at several
times the work; (c) is quadratic for operations that capture `k`; (d) can't
resume twice.

**Q2. State-passing handlers in JS (cause 3).**
(a) **[Recommended]** The elaborator recognises handlers whose clauses are
all lambdas over the same parameters and emits a parameterised fold, which
the backends run as a loop. No change to the language.
(b) Surface syntax for a handler's parameters (as Links has), so the shape is
explicit rather than recognised.
(c) Tail calls through a trampoline everywhere in JS: general, but every
call in pure code pays.
(d) Nothing: state handlers stay stack-safe only natively and under
`run --js`.
Reason: (a) covers the way handlers are already written, with no new
syntax; (b) can follow if a handler that should qualify doesn't.

**Q3. Resuming a continuation more than once.**
(a) **[Recommended]** Keep it unrestricted, as today.
(b) Restrict handlers to resume at most once, which would allow fibers and
cheaper capture.
Reason: `Each.collect` needs it, and under A it costs nothing extra.

**Decided (Matt, 24 Oct 2026): D1163 (a)** — exported functions and the playground, on the normal stack, at 1,000,000 elements.

**Q4. The JS stack-safety target.**
(a) **[Recommended]** Exported functions on Node's normal stack and the
playground, at 1,000,000 elements for effectful `mapIn`.
(b) Only `run --js` (which has a 2 GB stack).
Reason: exported functions are how JS users and web pages call Stitchwort,
and they overflow at a few thousand today.

**Q5. Optimisations from Koka (fast `bind`, in-place resumption, evidence
passing).**
(a) **[Recommended]** Later, one at a time, each only with a benchmark
showing at least 1.5 times (stage 4d).
(b) Designed into stages 4a–4c now.
Reason: they change constants, not growth, and each adds a path to test.

## 9. Decision (D1162)

Taken 24 Oct 2026, after the self-review
([effect-runtime-review.md](effect-runtime-review.md)) and the external
review ([effect-runtime-external-review.md](effect-runtime-external-review.md)).
It answers Q1, Q2, Q3 and Q5 of §8 (Q4 is D1163), and amends §6.

### 9.1 What was decided

1. **Representation.** At run time a computation is `Done | Call | Bind`,
   run by an explicit loop. Pending continuations are a persistent,
   immutable linked list: capturing a continuation and resuming it are
   taking a pointer, and a continuation may be resumed any number of
   times, also after its clause has returned (unrestricted multi-shot,
   Q3 (a)). Chunked persistent segments (blocks of continuations with a
   link) are a later experiment, measured against the cons list; mutable
   arrays with copy-on-share are not pursued.
2. **Lazy resumption.** A handler's resumption `k y` returns a suspended
   computation, `Bind (Done y) (z => fold … (rest z))`, instead of running
   the rest of the handled computation at once. The loop that runs the
   handler's result does the resuming, so a clause that calls `k` doesn't
   nest a call per operation.
3. **JS always uses the loop.** `bind` builds a node and calls nothing.
4. **Native keeps `bind (Done x) k = k x` as a direct call.** This is an
   explicit backend invariant, not an optimisation: the native machine's
   frames are on the heap, so a `Bind` node there would pay for a problem
   that backend doesn't have.
5. **State-passing handlers (A′)**, the parameterised empty-row handlers
   whose clauses are all lambdas over the same parameters, are recognised
   and loop-fused as a post-elaboration (backend) optimisation. The
   elaborator doesn't change, no hash changes, and there is no surface
   syntax (Q2: neither (a) nor (b) of §8, but the external review's third
   option).
6. **Invariant: running an operation never inspects ordinary `Comp`
   continuation frames individually.** Routing an operation costs at most
   the number of handlers and `translate`s it crosses, independent of
   control depth. The native `IO` runner's per-operation scan of its frame
   stack is fixed accordingly, and `Comp` continuations stay separate from
   the `Delay`/runner frames in this stage (not one segmented
   continuation, which may come later).
7. **The empty-row non-tail limit.** Empty-row handlers that consume a
   resumption non-tail in pure code (`Cons v (k ())`, `Each.collect`) keep
   JS stack limits this stage. This is a consequence of the current pure
   calling convention, not of the `Comp` representation; selective
   transformation of such clauses (defunctionalising the pure context
   around a resumption, and where needed the pure code through which a
   resumption escapes) is a possible future solution.
8. **Q5.** Koka's optimisations (a fast path for `bind` in JS, in-place
   tail-resumptive clauses, evidence passing) stay later and measured. There
   is no current justification for paying the architectural cost of CPS
   (design B) or of evidence passing as the continuation representation
   (design C): the measurements behind that are hand-written models, so
   they support not choosing them now, not a lasting conclusion.

### 9.2 Why lazy resumption is sound

The library's equation for a deep handler (§2) is

```
foldComp d c (Call o r) ≈ c o (y => foldComp d c (r y))
```

Write `k_eager y = foldComp d c (r y)` for the resumption the tree gives,
and `k_lazy y = Bind (Done y) (z => foldComp d c (r z))` for the one the
runtime gives. When the fold's result (its carrier) is a computation, the
only things that can consume `k_lazy y` are `bind`, the folds, `translate`,
`runPure` and the runners, which all run it with the loop, so

```
run (k_lazy y)
  ≈ bind (Done y) (z => foldComp d c (r z))
  ≈ foldComp d c (r y)                        -- bind (Done x) k ≈ k x
  = k_eager y
```

The cases that might worry:

- **Discarded continuation:** neither version runs anything.
- **Single resumption:** equal by the `bind` law above.
- **Multiple resumptions:** each call builds its own node around the same
  captured, immutable pending list, so each runs from the same point.
- **Stored continuation:** storing the suspended node is storing a value;
  running it later is the same as running it at once, since pure code has
  no side effects.
- **Deep handling:** the fold is still around `r z`, so the resumed
  computation is handled by the same handler.
- **Effects before or after the resumption:** sequencing in the enclosing
  row is `bind`, so operations happen in the tree's order.

This depends on runtime `foldComp` being sealed. Since stage R2 a program
can't call `foldComp` at run time (§2), so every fold that runs comes from
`handle` (or from the library, which has none at run time). R2 is doing
semantic work here, not only hiding an implementation detail.

**A correction found while building 4a.** The reviews said the carrier of
every `handle` is a computation of the enclosing row. That holds only when
the enclosing row has an ability or is the closed empty row. The carrier
is `comp_type(cx, out, t)` (`crates/elab/src/effects.rs:3433`), and
`comp_type` gives (`effects.rs:232-251`) **[checked]**:

| Enclosing row `out` | Carrier | A tree at run time? |
|---|---|---|
| at least one ability | `Comp ops res t` | yes |
| closed and empty (`runPure` around the fold) | `Comp NoOp NoRes t` | yes |
| a bare row variable `{e}` | `CompIn e t` | only when `e` isn't `Empty` |
| `Partial` | `Delay ops res t` | no |

So the backend makes `k` lazy only where it knows the carrier is a tree:
it reads the fold's carrier argument (an erased type argument, present in
the term) at each call of `foldComp`. A `Comp` carrier gets the lazy fold;
`CompIn e t` with `e` a variable gets a fold that tests the row value at
run time (it is a run-time argument of generic code); anything else, or a
`foldComp` not applied to its carrier, gets the eager fold, which is
today's meaning run with the loop. In an empty-row variant, `e` is the
constant `Empty`, so the fold is eager: that is case 7's limit.

### 9.3 Stages

Each stage is one lane, testable on its own, in this order. "1M" is
1,000,000 elements.

| Stage | Work | Acceptance |
|---|---|---|
| 4a | **JS run loop.** In the JS backend: `bind`, `foldComp`, `translate` and `runPure` replaced by a runtime of `Bind` nodes, a loop and a persistent pending list; lazy resumption at `handle` folds by the carrier rule of §9.2; the `run --js` runner steps computations with the loop, its pending list kept apart from its `Delay` frames (it takes computations apart, so it can't be left for later); an option that counts run-loop steps, pushes, pops and resumptions, for tests | Exported functions on Node's default stack at 1M: `checked`, `failsLast`, the reader at the empty row, and the reader, writer, search and state handlers with another ability outside the handler; `run --js` printing 1M lines; the empty-row writer and search documented as overflowing (a test pins the resource error); instrumented counts: steps, pushes and pops at most `C·n`, the same `C` from 1,000 to 100,000; correctness against the reference evaluator for multi-shot, stored resumptions resumed in different branches, 0/1/2/many resumptions, handlers nested 10 and 100 deep, forwarding, repeated `translate`; plain `map` unchanged |
| 4b | **Native run loop.** In `crates/rt`: a `Bind` node only for a computation that isn't `Done` (the invariant of §9.1.4), the loop on the machine's own frames (not a Rust function calling back into the machine), lazy resumption by the same carrier rule, the same counters | The 4a shapes natively at 1M in linear time (instrumented counts as in 4a); native `checked` within 1.2 times today; native empty-row writer/search up to the frame limit, with the documented resource error past it |
| 4c | **Runners and `Partial`.** The native `IO` runner routes an operation by an index of its `Map` and `Tie` frames, never scanning ordinary frames (§9.1.6), in both runners; `Partial` mixed with another forwarded ability; the playground (wasm) | `io` natively and in the playground at 1M; a counter showing routing work at most `C·operations·handlerDepth`, independent of control depth; `Partial` + forwarded ability correct on native, JS and the reference evaluator |
| 4d | **A′ fusion.** A backend pass that recognises empty-row state-passing handlers after elaboration and runs them as a loop with the parameter in a variable, in JS and natively; no elaborator or hash change | `counted` and `countedChecked` exported at 1M on Node's default stack; `Counter.number`-style handlers in std and AoC unchanged in source, their proofs unchanged; a handler that almost fits (a non-tail `k`) still correct |
| 4e | **Generated differential tests**, in the style of `crates/partial-model`: random programs of nested handlers of every shape (state, reader, writer, fail, choice, forwarding through open rows, `translate`, `IO`, `Partial` in `main`), run on the reference evaluator, natively and in JS, outputs and traces compared | the generator's programs agree on all three; the existing differential tests pass |
| 4f | **Allocation**, measured, one lane each: fewer binds per effectful `map` element, a `Bind` node that carries its pending cell, chunked persistent segments, a JS `bind` fast path with a depth counter | each only with a benchmark showing at least 1.5 times (time or GC), judged with heap and GC time, not wall time alone |

Every stage keeps pure `map` within 10% of today (stage 2's guarantee) and
leaves the kernel and the elaborator unchanged, so hashes don't move.

### 9.4 As built: stage 4a

- **Where.** `crates/js/src/effect.rs`: the runtime's JS (`effRun`, the
  loop; `effFold` and `effFoldLazy`; `effTranslate`; `effBind`;
  `effRunPure`), emitted before the generated definitions whenever a
  module uses the effect machinery, and the four library definitions
  replaced by it (`Gen::effect_native`, so they're also never inlined).
  All four or none: the runtime checks the core's shapes (runtime arities,
  `Comp`'s and `SigMap`'s fields) and otherwise leaves the library's code.
- **The carrier rule** (§9.2) is applied in `Gen::def_ref`, at each call of
  `foldComp` with its carrier argument: `effFoldCompLazy` for `Comp …` or
  `CompIn (Ops …) t`; `effFoldCompIn(row)` for `CompIn e t` with `e` a
  run-time row (it tests for `Empty`); the eager fold otherwise.
- **The `run --js` runner** steps a computation with `effRun`, and keeps the
  computation's pending list in its own variable, saved in an `Await`
  frame alongside the continuation; the machine's frames hold only
  `Delay` frames, so routing an operation still walks only `Map` and `Tie`
  frames (§9.1.6 holds in JS). A recursion request is a tail call only if
  nothing is pending either.
- **Counters.** `Options::effect_counters` makes the runtime count steps,
  pushes, pops, routes (an operation reaching a fold or `translate`),
  resumptions and `Bind` nodes, in `globalThis.__stitchwortEffectCounts`.
- **Tests.** `examples/extract/effect-handlers.sw` (resumed 0, 1, 2 and 3
  times, multi-shot `Each` at 1,024 results, a resumption stored in the
  handler's result and resumed after it returned, in different branches
  and twice; handlers nested 10 and 100 deep forwarding outwards; 10 and
  100 `translate`s; state through `Fail`) and
  `examples/extract/effect-runtime.sw` (the shapes), checked against the
  reference evaluator by the `extract` tests;
  `crates/cli/tests/effect_runtime.rs` (every 4a shape at 1M on Node's
  default stack; counts per element constant from 1,000 to 100,000;
  routing per operation and handler constant at depths 1, 10 and 100; the
  empty-row limit pinned); and two `run_js` tests (`IO` across a million
  binds and a forwarding `Fail` handler; a handler inside a partial
  function forwarding `IO`).

**Measured** (exported functions, 1,000,000 elements, Node 22.23.3 on its
default stack, Apple M4 Pro, one call per process, median of 5; heap is
`heapUsed` after the call with the result alive; `bench/effect-runtime`'s
`map.sw` and `shapes.sw`) **[checked]**:

| export | before 4a | after 4a | max RSS | heap after |
|---|---|---|---|---|
| `plain` (pure `map`, median of 11, two rounds) | 97 / 81 ms | 85 / 82 ms | 255 MB | 191 MB |
| `checked` | overflow at 4,000 | 447 ms | 497 MB | 430 MB |
| `failsLast` | overflow at 2,000 | 380 ms | 427 MB | 369 MB |
| `asked` (reader, empty row) | overflow at 2,000 | 485 ms | 502 MB | 435 MB |
| `askedChecked` | overflow at 4,000 | 708 ms | 503 MB | 434 MB |
| `askedIn` | overflow at 4,000 | 538 ms | 501 MB | 434 MB |
| `emittedIn` | overflow at 2,000 | 667 ms | 689 MB | 626 MB |
| `searchedIn` | overflow at 2,000 | 2,085 ms | 1,649 MB | 1,610 MB |
| `counted`, `countedChecked` | overflow at 2,000-4,000 | overflow at 8,000 (4d) | | |
| `emitted`, `searched` | overflow at 2,000 | overflow at 2,000 (§9.1.7) | | |

`plain`'s generated code is unchanged (it never reaches the runtime).
`run --js` with an `IO` print on every element: 16,000 elements took 7.2 s
before and 0.6 s after; 1,000,000 take 1.4 s (whole command). The counts
per element at 100,000 (steps, pushes = pops, routes, resumptions): `checked`
4, 2, 0, 0; `asked` 9, 4, 1, 1; `askedChecked` 13, 5, 3, 2; `searchedIn`
21, 8, 4, 2; `forwarded` through 100 handlers 1.99 routes per operation and
handler crossed (a fold and a `translate` each), the same at 1,000 and
10,000 elements. Heap is the open problem: `emittedIn` is 3.3 times
`plain`'s and `searchedIn` 8.4 times, above the review's suggested bound of
3, which is 4f's to reduce.

## Appendix A. Benchmark and prototype files

In `bench/effect-runtime/`:

- `map.sw`: the variants of §1.1 as exported functions, and a `main` that
  reads a variant and a size.
- `run.sh`: times `stitchwort run` or `run --js` for one variant over several
  sizes: `bench/effect-runtime/run.sh native state 1000 2000 4000`.
- `export.mjs`: times the exported functions on Node's normal stack:
  `stitchwort build --js bench/effect-runtime/map.sw -o OUT`, then
  `node bench/effect-runtime/export.mjs OUT/map.js`.
- `prototype.mjs`: makes the patched modules of §5:
  `node bench/effect-runtime/prototype.mjs OUT/map.js OUT/map-loop.js
  [--parameter]`.
- `agree.mjs`: compares two modules on small inputs:
  `node bench/effect-runtime/agree.mjs OUT/map.js OUT/map-loop.js`.

## Appendix B. Found on the way

- **A `main` with `{IO, Fail}` doesn't run on `main` at `cbf2ac4a`.**
  `stitchwort run examples/accept/main-fail-ok.sw` fails with `E-MAIN-TYPE`:
  "`main` must have type … `() -> {IO, Fail} ()`", pointing at a `main`
  whose type it prints as `() -> {Fail, IO} ()` **[checked]**. The test that
  covers it, `an_unhandled_failure_is_reported_alike` in
  `crates/cli/tests/run_reference.rs`, fails: stdout is empty where
  `reading the numbers` was expected **[checked]**. The benchmark's `main`
  is `{IO}` to avoid it. The cause looks like row order (`{Fail, IO}`
  against `{IO, Fail}`) **[inferred]**, not investigated.
- **`state` under `run --js` exhausts the heap at 8,000 elements**, not the
  stack: the quadratic rebuilding also keeps memory alive **[checked]** for
  the error, **[inferred]** for the reason.
