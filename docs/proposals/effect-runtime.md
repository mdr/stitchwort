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
   JS stack limits this stage. Natively (and in the playground, which runs
   the native runtime compiled to wasm) the limit is the machine's frame
   limit, 2,000,000 frames by default, not a host stack: such a handler
   nests a heap frame per operation, so it runs at 1,000,000 operations and
   ends with the depth resource error past the limit (stage 4b). This is a consequence of the current pure
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
| `counted`, `countedChecked` | overflow at 2,000-4,000 | overflow at 8,000 (run at 1M since 4d, §9.7) | | |
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

### 9.5 As built: stage 4b

- **Where.** `crates/rt/src/effect.rs` (the natives, `EffectOp`; which
  library definitions they replace, `EffectNatives`, by the same checks as
  4a's, all four or none; the carrier rule; `Handler`, `Resume` and the
  counters) and `crates/rt/src/machine.rs` (`State::effect`, `eff_run`, the
  loop, `eff_call`, `resume`). `bind`, `foldComp`, `translate` and
  `runPure` lower to `PrimOp::Effect` natives, compiled to `Instr::Prim`,
  or `Instr::TailPrim` in tail position, which replaces the frame as a tail
  call does.
- **Representation.** A `Bind c k` node is a cell with tag
  `Shapes::bind_node` (one past `Done`'s and `Call`'s tags), which no
  compiled code switches on, since only the natives and the runner take a
  computation apart. The pending list is cells `[k, next]`, `Erased` when
  empty, never changed once made; a resumption is `Fun::Resume`, holding
  the handler, the operation's `rest` and the pending list, with a flag for
  a lazy one.
- **The `Done` invariant (§9.1.4).** `bind (Done x) k` applies `k` to `x`
  directly, a tail call where `bind` was, and builds no node. Only `bind`
  of a `Call` or a `Bind` makes a node. A lazy resumption still makes
  `Bind (Done y) r`: that suspension is the point of laziness, and `bind`
  never sees it as `Done`. Tested: `checked` (whose callback never
  performs anything) at 100,000 elements makes no node and runs the loop
  once (`bind_of_done_is_a_direct_call`).
- **The loop runs on the machine's frames**, like `Text.fold`: applying a
  popped continuation, `done`, `call`, a resumption's `rest`, a
  `translate`'s `inject` and `reply` each go through `apply`, and their
  results come back to the loop through a return kind (`Ret::Eff`,
  `Ret::Then`, `Ret::Inject`), never through a Rust call. So nothing nests
  in Rust (the wasm playground included), and a clause's tail call of `k`
  stays a tail call.
- **The carrier rule** (§9.2) is applied in lowering (`Lowerer::fold`), as
  4a does: `EffectFoldLazy` for a `Comp` carrier, `EffectFoldIn` with the
  row as an extra argument for `CompIn e t` (lazy unless the row is
  `Empty`), the eager fold otherwise, and for a `foldComp` used as a value.
- **The `IO` runner** steps a `Bind` node with `Machine::step_comp`: the
  loop with a handler that stops at the first operation and returns it
  with what was pending folded into its continuation (the operation as it
  was if nothing was pending, so a tail recursion request is still
  recognised). The pending list never enters the runner's frames, so
  `Bind`s are invisible to its routing scan, which is unchanged: it still
  walks the `Delay` frames, as before 4b; indexing them is 4c's (§9.1.6).
- **Counters.** `Machine::effect_counts` (always on: a few integer adds):
  loop steps, pushes, pops, routes, lazy resumptions, and `Bind` nodes made
  by `bind`.
- **Tests.** `crates/rt/tests/effect_runtime.rs`: every 4a shape, and the
  empty-row writer and state handler, at 1,000,000 elements within the
  default limits, and `failsLast` and `searched`; counts per element
  constant from 1,000 to 100,000, pushes equal to pops; routing per
  operation and handler crossed constant at depths 1, 10 and 100; the
  empty-row writer and search reaching the frame limit with the depth
  error (100,000 frames, 1,000,000 elements) and working below it; and
  every `-- run:` line of `effect-runtime.sw` and `effect-handlers.sw`
  against the reference evaluator (the call and the reference's normal
  form lowered as a pair, the machine's two values compared). The IR
  snapshots that mention `bind` show the native; the lowering tests'
  interpreter (`crates/rt/tests/interp`) runs the natives by the library's
  equations.

**Measured** (whole `stitchwort run` of `bench/effect-runtime`'s `map.sw`
and `shapes.sw`, so each includes about 0.2 s of checking; median of 3, or
of 5 interleaved with the build before 4b for the first three rows; max
RSS; Apple M4 Pro, shared with other jobs, load 20-30) **[checked]**:

| variant (n = 1,000,000 unless given) | before 4b | after 4b | max RSS after |
|---|---|---|---|
| `plain` (pure `map`) | 0.29 s | 0.30 s | 400 MB (same) |
| `fail` (`checked`) | 0.59 s | 0.59-0.60 s | 638 MB (same) |
| `failLast` | 0.56 s | 0.61 s | 646 MB (same) |
| `state` (empty-row counter) | 3.77 s at 8,000 | 1.33 s | 540 MB |
| `io` | 3.68 s at 8,000 | 1.06 s | 505 MB |
| `asked` | 4.13 s at 8,000 | 1.15 s | 432 MB |
| `askedChecked` | 7.84 s at 8,000 | 2.01 s | 432 MB |
| `emitted` (empty row) | 6.03 s at 8,000 | 1.19 s | 570 MB |
| `searched` (empty row) | 13.75 s at 8,000 (4 GB) | 3.26 s | 1,301 MB |

So `checked` is within 1.02 times today (the 1.2 criterion), `plain` is
unchanged, and `failLast` is about 1.08 times. In process
(`every_shape_runs_at_a_million_elements`, one call each, under load):
`checked` 0.5 s, `asked` 1.2 s, `askedIn` 1.3 s, `emittedIn` 1.5 s,
`countedIn` 1.7 s, `askedChecked` 2.4 s, `searchedIn` 4.0 s, and
`forwarded` through 10 handlers 13.5 s (eleven routes per operation). The
counts per element at 100,000 (steps, pushes = pops, routes, resumptions,
nodes) are 4a's: `checked` 0, 0, 0, 0, 0 (one step in all); `asked` 9, 4,
1, 1, 3; `askedChecked` 13, 5, 3, 2, 3; `searchedIn` 21, 8, 4, 2, 6;
`forwarded` 1.99 routes per operation and handler at depth 100. AoC's
`stitchwort test --no-cache` takes 14.5 s and 622 MB before and after.
The empty-row writer and search, at JS's stack limit after 4a, run at
1,000,000 natively: each nests a heap frame per operation, so they fail
only past the frame limit (2,000,000 by default).

### 9.6 As built: stage 4c

- **The routing index (§9.1.6).** Both `main` runners (`crates/rt/src/run.rs`
  and the `run --js` runner in `crates/js/src/run.rs`) keep, beside their
  stack of `Delay` frames, `marks`: the positions of the `Map` and `Tie`
  frames, bottom first. Routing an operation walks `marks` from the top, so
  it looks only at the translations and partial functions it crosses or
  stops at, never at the `Bind` frames (a `bindD`'s continuation) or the
  `Await` frames between them. A recursion request answered by a `Tie`
  takes the frames above it into the `Await` with their marks, relative to
  the `Tie`; returning to the `Await` puts both back. Pushing and popping a
  frame keeps `marks` in step, a constant each. The pending list of a
  computation never enters these frames (4a, 4b), so nothing else in the
  runners grows with control depth.
- **Where the old scan hurt.** A non-tail partial recursion leaves an
  `Await` per level, and every operation from the innermost level walked
  all of them: `examples/accept/partial-forwarding.sw` (each level prints
  through a `Fail.toResult` and an `Env` handler whose carrier is a
  `Delay`, and calls a partial function with a smaller row) was quadratic
  on both runners. `bench/effect-runtime`'s `io` was not (its binds are a
  computation's, in the pending list since 4a/4b), and is unchanged.
- **Counters.** `stitchwort_rt::run_main_counting` returns `RouteCounts`
  (operations routed, frames routing looked at, frames below the focus at
  each operation, summed); `stitchwort_js::run::generate_program_with` with
  `Options::effect_counters` makes the JS runner count the same and print
  them to standard error at the end. Both runners give identical counts on
  `partial-forwarding.sw` **[checked]**:

  | depth | operations | frames looked at per operation | frames below per operation |
  |---|---|---|---|
  | 1,000 | 7,252 | 1.000 | 510 |
  | 10,000 | 72,502 | 1.000 | 5,010 |
  | 100,000 | 725,002 | 1.000 | 50,010 |
  | 1,000,000 | 7,250,002 | 1.000 | 500,010 |

  Before 4c the frames looked at were the frames below. Every `print` here
  crosses one `Tie` (`down`'s); a translation (`Map`) frame is crossed
  only by operations from inside the translated partial computation, and
  since a handler can't handle a `Partial` computation and `main` can't be
  both `Fail` and `Partial`, those are recursion requests stopped by that
  computation's own `Tie` **[inferred]** from the rows the elaborator
  allows (E-PARTIAL on a handler around a partial computation **[checked]**).
- **Tests.** `crates/rt/tests/effect_runtime.rs`
  (`routing_work_is_independent_of_control_depth`: depths 1,000 to 100,000,
  frames looked at per operation constant and at most 4, frames below at
  least depth/8; `partial_with_forwarded_abilities_runs_a_million_levels_deep`,
  output checked line by line) and the same two in
  `crates/cli/tests/effect_runtime.rs` for `run --js`. `partial-forwarding.sw`
  is an example, so `run_js` and `run_reference` compare it across the
  native runner, `run --js` and the reference evaluator at 50 levels with
  their usual inputs, and named tests at 2,000 levels (native against JS)
  and 1,000 (native against the reference). `run_js`'s `io` test now
  compares native and JS at 1,000,000 elements too.
- **The playground.** `web/tests/effect-shapes.sw`: the effectful `map`
  shapes (`io`, `ioRead`, `checked`, `asked`, `askedChecked`, `askedIn`,
  `emitted`, `emittedIn`, `searched`, `counted`) behind one `main`.
  `crates/web`'s `effectful_maps_run_at_a_million_elements` runs every one
  at 1,000,000 through the playground's `run` with its resource limits
  (natively, as the crate's tests run); web/tests/browser.mjs's "effectful
  List.map runs at a million elements" runs them in the WebAssembly build
  in headless Chrome, through the page, within its 15-second run limit and
  256 KiB output cap. `io` prints every element, about 6.9 MB, past the
  page's cap, so the browser runs `ioRead` (an `IO.readLine` per element)
  instead, and `io` itself was run on the WebAssembly build's `run` in Node
  with a larger cap.

**Measured** (whole `stitchwort run --no-cache`, about 0.2 s of it
checking; median of 3; max RSS; the build before 4c is `cafdff03`; Apple
M4 Pro) **[checked]**:

| run | before 4c | after 4c | max RSS after |
|---|---|---|---|
| `io` (`map.sw`), 1,000,000, native | 1.22 s | 1.22 s | 507 MB (same) |
| `io`, 1,000,000, `run --js` | 0.96 s | 0.84 s | 458 MB (same) |
| `partial-forwarding.sw`, 20,000 levels, native | 0.64 s | 0.48 s | 55 MB |
| 40,000, native | 1.31 s | 0.74 s | 66 MB |
| 80,000, native | 3.30 s | 1.28 s | 84 MB |
| 1,000,000, native | (quadratic) | 13.4 s | 481 MB |
| 20,000, `run --js` | 1.19 s | 0.41 s | 103 MB |
| 40,000, `run --js` | 3.37 s | 0.49 s | 115 MB |
| 80,000, `run --js` | 14.9 s | 0.62 s | 139 MB |
| 1,000,000, `run --js` | (quadratic) | 3.35 s | 668 MB |

Native per level of `partial-forwarding.sw` is about 13 µs against JS's
3 µs: a sample of the 1,000,000 run puts nearly all of it in the
machine's own work for the level (`Machine::call` and what it runs: the
handlers, `Delay` binds, the text of the number), not in routing; it was
the same before 4c at small depths, where the scan is short (a variant
without `collatz`: 0.25 s at 2,000 levels before, 0.24 s after). AoC's `stitchwort test --no-cache`: 14.7 s and 619 MB
before, 14.8 s and 618 MB after.

The playground's shapes at 1,000,000 (time of the run itself): natively in
`crates/web`'s test, `checked` 0.7 s, `ioRead` 1.5 s, `asked`, `askedIn`,
`emitted`, `emittedIn` 1.5 s, `counted` 1.7 s, `io` 1.9 s, `askedChecked`
2.7 s, `searched` 2.7 s; in the WebAssembly build under Node (the build's
`run`), `checked` 1.0 s, `asked`, `askedIn`, `emitted`, `ioRead` 1.9 s,
`counted` 2.2 s, `emittedIn` 2.4 s, `io` 3.0 s, `askedChecked` 3.3 s,
`searched` 5.3 s; in headless Chrome through the page (its own "Finished
in"), `checked` 0.9 s, `emitted` 1.6 s, `asked`, `askedIn` 1.7 s,
`emittedIn` 1.8 s, `counted` 2.0 s, `askedChecked` 3.0 s, `searched`
3.4 s, and `ioRead` 7.2 s, plus about 9 s for the page to take the
6.9 MB input. `ioRead` in the page is about 4 times its time on the same
build in Node, within the 15-second limit but the closest to it; the
cause isn't investigated (the page's run streams output and flushes it
before every read **[inferred]**, which the Node call doesn't).

### 9.7 As built: stage 4d

- **Where.** `crates/rt/src/fusion.rs` recognises the shape and rewrites
  the fold's arguments, on the core term after elaboration (and after
  empty-row specialisation), for both backends: `Gen::def_ref` in
  `crates/js` and `Lowerer::apply_def` in `crates/rt` call it at each
  `foldComp` before anything else. Nothing in the kernel or the elaborator
  changed, and no hash moved: `hash_stability`'s snapshots only gained the
  new examples' definitions **[checked]**.
- **What is recognised.** A `foldComp` whose carrier is a function type at
  the empty row: `Comp NoOp NoRes (S -> R)` (a `handle` at the closed empty
  row, `runPure` around it), or `CompIn Empty (S -> R)`, which empty-row
  specialisation reduces to `S -> R` itself (a handler written for `{e}`,
  like the tour's `collectLog`, used at the empty row). At the closed empty
  row the return clause and every operation clause must be `Done e`; at the
  empty row any clause will do. A clause whose `e` isn't a lambda is
  eta-expanded (`s => e s`; generated code is pure and total). The
  operation clauses are found as the explicit arguments of the ability's
  eliminator inside `handlePlus`, by erasure (the terms don't reliably say
  which applications are implicit).
- **The rewrite.** Each operation clause `x, k => s => body` becomes
  `x, k => jump => s => body′`, where every `k v s′` in tail position of
  `body` becomes `jump v s′`: tail positions are followed through `let`s,
  applied lambdas (`let r := runPure (k v); r s′` is how the elaborator
  writes `k v s′` at the closed empty row) and both branches of
  `Bool.ifThenElse` and `Decidable.elim` (how `if` on a comparison is
  written), which return their branch's result. At the closed empty row the
  return clause `x => Done e` becomes `x => e`. A fold none of whose clauses
  has a tail `k v s′` is left as it was.
- **The loop.** The fold becomes `effFoldState(comp)` in JS and
  `EffectOp::FoldState` / `FoldStateComp` natively: it builds the state's
  function (`Done` of it at the closed empty row), and that function, given
  the state, runs the 4a/4b loop with the state in a variable. At `Done x`
  it is `done x s`; at an operation it applies the clause to the operation,
  a real `k`, `jump` and the state. `jump v s′` only records its arguments
  (an `EffJump` object; natively a `Fun::Jumped` value no program can
  make). If the clause returns one, the loop goes on with `rest v` and
  state `s′`, calling nothing; anything else is the handler's result.
  Natively the clause's result comes back to the loop through a return kind
  (`Ret::Step`), and the state rides in the loop's `EffRet`, so nothing
  nests in Rust either.
- **Fallbacks.** `k` is always a real resumption: called with `y`, it gives
  the state's function from `rest y` with the pending list where the
  operation was, which runs the same loop when it gets a state. So every use
  of `k` that isn't a tail `k v s′` (not last, twice, many times, under a
  lambda, stored in the result and resumed after the handler returned)
  means what the tree says; only the tail call became a jump. A handler
  that doesn't fit at all keeps 4a/4b's fold: at the closed empty row, one
  with a clause that isn't `Done` of something (`put v, k => k ()`), and
  any handler with an ability outside it, which is lazy already.
- **Tests.** `examples/extract/effect-state.sw`: a handler whose operations
  resume 0, 1 (a jump), 2 (not in tail position), `n` times (under a
  lambda), in either branch of an `if`, and in tail position in one branch
  and not the other, at the closed empty row, at the empty row through an
  open-row handler, and with `Fail` outside (not fused); a resumption
  stored under a lambda in the result and resumed after the handler
  returned, three times, with different answers; a state handler around a
  forwarding handler and around another state handler; a store whose `put`
  is `k ()`, fused at the empty row and not at the closed empty row. Its
  `-- run:` lines are checked against the reference evaluator in JS
  (`extract`) and natively (`run_lines_agree_with_the_reference_evaluator`),
  and `state_handlers_run_as_a_loop_where_they_fit` pins which of them are
  fused by their jump counts. `effect-runtime.sw` gained `countedChecked`,
  `countedOpen` and `logged` (an accumulator writer for `{e}` at the empty
  row); with `counted`, they run at 1,000,000 elements on Node's default
  stack and natively, with jumps equal to the elements and the counts per
  element constant from 1,000 to 100,000, in both backends' tests. The
  empty-row limit test no longer lists `counted`. The lowering tests'
  interpreter runs the new natives by their equations.

**Measured** (Apple M4 Pro, Node 22; the build before is `fcb91599`; JS is
`bench/effect-runtime/once.mjs`, one call per process, median of 5; native
is a whole `stitchwort run` of `map.sw`, median of 5) **[checked]**:

| run (1,000,000 elements) | before 4d | after 4d | max RSS (heap) after |
|---|---|---|---|
| `counted`, JS export | overflow at 4,000 | 583 ms | 523 MB (435 MB) |
| `countedChecked`, JS export | overflow at 4,000 | 800 ms | 529 MB (434 MB) |
| `plain`, JS export | 55 ms | 52 ms | 268 MB (191 MB, same) |
| `checked`, JS export | 460 ms | 459 ms | 524 MB (431 MB, same) |
| `state` (`counted`), native | 1.42 s, 567 MB | 1.22 s | 453 MB |
| `plain`, native | 0.31 s | 0.31 s | 420 MB (same) |
| `fail` (`checked`), native | 0.63 s | 0.61 s | 670 MB (same) |

Natively the jump saves the closure per operation that the clause's state
function was, and its frame: 14% less time and 20% less memory for
`state`. The counts per element at 100,000 (steps, pushes = pops, routes,
resumptions, nodes, jumps), the same in both backends: `counted` and
`countedOpen` 7, 3, 1, 0, 3, 1; `logged` 5, 2, 1, 0, 2, 1; `countedChecked`
11, 4, 3, 1, 3, 1 (its `Fail` handler resumes each forwarded `next`
lazily). AoC's `stitchwort test --no-cache`: 15.8 s and 619 MB before,
15.7 s and 618 MB after.

### 9.8 As built: stage 4e

- **Where.** `crates/cli/tests/effect_differential.rs`: a generator of
  random well-typed effectful programs, and a test that runs them on the
  reference evaluator (`Session::run_main`), natively
  (`Session::run_main_fast`) and as JavaScript under Node (the `run --js`
  program from `Session::extract_program`), in process, and requires the
  same standard output and the same ending from all three. The output is
  the trace: every `IO.print` in a function or a clause, in order, and each
  program's result.
- **The programs.** Each is a tree of functions over `Nat` whose rows are
  drawn from four abilities (`Ab1`-`Ab4`, each with `call: Nat -> Nat` and
  `peek: () -> Nat`), `Fail` and `IO`; every function and handler is used
  once. A function's statements are `let`s of an operation, a call of a
  function with the same or a smaller row (a `translate`), a handler around
  such a call, an `if`, an effectful `List.map` of 0 to 200 elements, a
  tower of 1 to 100 copies of one handler (the body's operations forwarded
  through all of them, or its own ability handled by the innermost), or 1
  to 100 `Fail.toResult`s that re-raise (as many `translate`s), and
  `IO.print`s and `Fail.ensure`s; every `let` reaches the result. Handlers:
  - a plain result (`Nat`), whose `call` clause discards `k`, resumes it
    once in tail position or not, twice (in an expression, or with `let`s
    in the other order), 0 to 3 times through a recursive helper, or in one
    branch of an `if`;
  - state (`Nat -> Nat`): `s => k v s′` (fused by 4d at the empty row),
    `k s s`, `k 0 v`, eta-reduced `k v` (not fused at the closed row), not
    in tail position, twice, discarding, in both branches of an `if`, and
    in tail position in one branch only;
  - a list of every result, then digested: discard, once, `Cons v (k …)`,
    twice, 0 to 3 times, `k v ++ [v]`;
  - stored: `k` kept in a `Paused` result and resumed after the handler
    returned, by `explore`, in two branches to a depth of 1 to 4, with and
    without a state;
  - `Fail`: `orElse`, `toResult`, `toOption`, a custom handler, and
    `Fail.context` where `Fail` is outside too (handled, then raised again);
  - written for the closed row `{A}`, for `{A | e}` (also used where `e` is
    the empty row), or for a concrete row `{A, R}` to `{R}`, whose `call`
    clause may perform an operation of `R` or print before it resumes, and
    whose return clause may perform one; `peek`'s clause resumes in tail
    position, not, or discards, so a handler's clauses differ in shape.

  `main` runs eight programs in turn, each inside a `Partial` loop of 1 to 4
  levels a quarter of the time. Work is capped by construction: operations
  of a handler resuming more than once are counted (at most six per
  program), kept out of `map`s longer than 3, and allowed only for the
  innermost such handler (an outer one's operation inside an inner one's
  region would run once per inner resumption, each re-running the rest:
  an early version made such a program, which ran out of resources
  natively and didn't finish in a minute on the reference evaluator or in
  20 seconds in JS **[checked]**, with the cause **[inferred]** from its shape). The default run requires
  that no program runs out of resources; a longer run counts such modules
  as skipped, not as failures, since the backends may run out at
  different points.
- **Seeds and budget.** Programs come from a SplitMix64 seed per module.
  The test runs 64 modules (512 programs) from seed 1 by default;
  `STITCHWORT_EFFECT_FUZZ_BATCHES` and `STITCHWORT_EFFECT_FUZZ_SEED` run
  more or others, and `STITCHWORT_EFFECT_FUZZ_DUMP=dir` keeps every module.
  The default run also requires every shape above to have been generated
  (a list of 49 names), so a generator change that loses one fails.
- **On a disagreement** the test finds the first program whose lines
  differ, checks that it disagrees alone, and shrinks it (statements
  removed, atoms replaced by `1`, handlers by plain calls, clauses by tail
  resumption, depths to 1, the `Partial` loop dropped) while it still
  checks and still disagrees, for at most two minutes; it fails with the
  seed, the smallest program (also written to the temporary directory) and
  each backend's output. Checked by breaking the JS state loop on purpose
  (the state after a jump off by one): the test failed and shrank
  the first failing program to a three-function program of one state
  handler, then the break was reverted.
- **`IO` crossing a `Map` frame.** No source program sends an `IO`
  operation through a runner's `Map` frame (§9.6), so
  `io_operations_cross_translations_on_their_way_to_the_runner`
  (`crates/rt/tests/effect_runtime.rs`) and
  `io_crossing_translations_runs_alike_in_js` (the new test file) build
  one at the term level: `main` (a partial recursion that reads, prints
  through a forwarding `Fail` handler and stops early on one input) wrapped
  in two `Effect.mapSig Effect.sigSwap`s, so each operation is renamed from
  `L io` to `R io` and back on its way out and its reply mapped back
  through both. Natively the output is the unwrapped program's, with the
  same operations, and the frames routing looks at grow by two per `IO`
  operation; in JS the output is the reference evaluator's for the
  unwrapped program, on four inputs.
- **Found.** No disagreement **[checked]**: the default 512 programs, and
  longer runs of 20,000 programs (seeds 100,000 to 102,499, the generator
  as committed) and 12,000 (seeds 1,000 to 2,499, an earlier version
  without `peek`, concrete rows or effectful clauses), all agree on the
  three backends, with nothing out of resources in the 20,000. So stage 4e
  made no backend change.
- **Measured** (Apple M4 Pro, shared with other jobs, release build, the
  modules checked and run on all cores) **[checked]**: about 100 programs
  a second (104 for the default run, 117 for the 20,000, which took 171 s).
  The default run takes 4.9 s, and the whole test binary, the two
  `Map`-crossing tests included, 6.2 s of wall time with the build already
  done; the native crossing test adds 0.3 s to `crates/rt`'s
  `effect_runtime`. In the default run a program has about six handlers on
  average (2,395 of user abilities, 655 of `Fail`, in 512 programs), and
  every one of the 49 shapes appears at least 13 times: chains of 100
  re-raising `Fail` handlers 14 times, the fused closed-row state handler
  31, towers of 100 handlers 78, stored resumptions 155.

### 9.9 As built: stage 4f, first lane (closed signature maps)

**Measured first, inside the call only.** `bench/effect-runtime/alloc.mjs`
runs one export at 1,000,000 elements after building its input and
collecting garbage, and reports, from `v8.GCProfiler`, the bytes the call
allocated, the time spent collecting during it, and the most heap in use
after a collection (what the run keeps alive). Natively,
`crates/rt/tests/effect_alloc.rs` (an ignored test with a counting global
allocator) reports bytes and blocks allocated and the most bytes live
during the call. Before this lane (main at `a7c0f0f8`; Apple M4 Pro, shared,
load 6-10; JS: Node 22.23.3, median of 5 calls after a warm-up call, two
interleaved rounds; native: median of 3) **[checked]**:

| export | JS time | JS bytes allocated per element | JS GC | JS most live (× `plain`) | native time | native bytes, blocks per element | native most live |
|---|---|---|---|---|---|---|---|
| `plain` | 64 ms | 169 | 38 ms | 133 MB | 81 ms | 550, 1 | 343 MB |
| `checked` | 380-425 ms | 2,029 | 290-330 ms | 384 MB (2.9) | 448 ms | 1,219, 12 | 508 MB |
| `failsLast` | 370-420 ms | 1,983 | 280-330 ms | 328 MB (2.5) | 422 ms | 1,168, 11 | 423 MB |
| `counted` | 500-560 ms | 2,770 | 300-360 ms | 388 MB (2.9) | 1,260 ms | 2,928, 50 | 176 MB |
| `countedChecked` | 640-710 ms | 5,221 | 320-380 ms | 388 MB (2.9) | 2,360 ms | 5,072, 86 | 176 MB |
| `asked` | 480-550 ms | 2,602 | 285-355 ms | 388 MB (2.9) | 1,180 ms | 2,640, 47 | 176 MB |
| `askedChecked` | 600-670 ms | 4,964 | 290-350 ms | 389 MB (2.9) | 2,300 ms | 4,784, 83 | 176 MB |
| `askedIn` | 505-600 ms | 3,107 | 300-380 ms | 388 MB (2.9) | 1,190 ms | 2,640, 47 | 176 MB |
| `emittedIn` | 755 ms | 3,026 | 480 ms | 580 MB (4.4) | 1,240 ms | 2,704, 48 | 328 MB |
| `searchedIn` | 2,510-2,650 ms | 7,680 | 1,890-2,010 ms | 1,492 MB (11.2) | 3,900 ms | 7,456, 129 | 1,464 MB |

(Natively the input list is kept alive throughout, and the machine's frame
stack counts as live: `plain` recurses on frames, which is why its live
memory is above the effectful shapes'.)

**Where it goes, in JS** **[checked]**, from the sampling heap profiler
(collected objects included) and heap snapshots taken mid-run (at element
90,000 of 100,000):

- **GC time is copying what survives, not the garbage.** `checked`'s GC
  time is the same with a young generation of 16, 64 or 256 MB (295, 347,
  286 ms, while the number of scavenges falls from 134 to 8), and the
  scavenges copy 641 MB (313 MB surviving once, 328 MB promoted) against
  `plain`'s 113 MB.
- **What survives is mostly closures and their contexts made by generated
  code.** Per element of `checked`, live mid-run: the `map` continuation
  waiting for the rest of the list (`v8 => doneIn(Cons v7 v8)`, a closure of
  56 bytes), four contexts of 40 bytes (V8 makes a context per curried
  application of `List.map v1 v3 v6`, and one for the `case` block, and
  the continuation keeps the chain alive), and one pending cell of 40
  bytes. The run loop's own share is the cell: 40 of 256 bytes. In
  `searchedIn`, 1,560 bytes per element are live: about 590 the runtime's
  (four pending cells, 160; the fold's resumption, a context and two
  closures, 184; the `translate`'s, 120; the operations they keep, 80),
  about 280 a `SigMap` built for every element (the map object, its two
  closures and their contexts), and the rest generated code's closures and
  contexts.
- **What is allocated is mostly curried partial applications.** Of
  `checked`'s 2,029 bytes per element, about 1,600 are closures and
  contexts made by applying a generated function to fewer arguments than
  it takes (`doneIn(v1)`, `bindIn(v1)(c)`, `effBind(c)`, `map(v1)(v3)`,
  about 96 bytes each); the pending cells are 80.

So the pending list's cells, which chunked persistent segments would
replace, are 10-15% of what survives, and no change to the run loop's data
structures can give 1.5 times on GC time in JS **[inferred]** from these
shares. Natively there's no GC: time goes to the machine's own work and to
allocating and freeing (a sample of `askedChecked` has about 40% of its
time in `malloc`, `free`, `Drop` and `Vec` growth), and an operation costs
about 35 blocks (`asked`'s 47 against `checked`'s 12).

**The change: a closed signature map is built once.** Wherever code calls
a function whose row is smaller, the elaborator wraps the call in
`translate m`, with `m` a closed `SigMap` (`sigCase sigLeft sigFromNo`).
Generated code built `m` on every call: in `searchedIn` once per element,
and every pending choice kept its own copy alive through the `translate`'s
resumption. `stitchwort_rt::hoist` recognises a whole application of a
definition whose result is a `SigMap` and that reads no variable at run
time (its erased arguments aren't looked at); then JS builds it at its
first use and keeps it in a module variable (`(sigmap$0 ??= …)`, with
`var sigmap$0, …;` at the end of the module, so where the first use
happens is where the code built it before), and the native lowering makes
it a constant global (`Std.Effect.sigCase[map 0]`), computed when first
used. Generated code is pure and total, so building a map once means the
same as building it each time; maps are two closures, so keeping one alive
costs nothing. Only maps are hoisted: a closed application in general (a
long `List.range`) would keep its value alive for the whole run. Nothing in
the kernel or the elaborator changed, and no hash moved
(`hash_stability` passes unchanged); the JS snapshots of
`effect-handlers.sw`, `effect-runtime.sw` and `effect-state.sw` changed
where they build a map.

**After** (as above, interleaved with the build before) **[checked]**:

| `searchedIn` | before | after | ratio |
|---|---|---|---|
| JS time (warm, median of 5, two rounds) | 2,649 / 2,512 ms | 1,871 / 1,872 ms | 1.42 / 1.34 |
| JS GC (warm) | 2,012 / 1,888 ms | 1,301 / 1,294 ms | 1.55 / 1.46 |
| JS bytes allocated per element | 7,680 | 7,230 | 1.06 |
| JS most live | 1,492 MB (11.2 × `plain`) | 1,172 MB (8.8 ×) | 1.27 |
| JS, one call per process (`COLD=1`, median of 5) | 2,039 ms, GC 1,423 ms, 1,564 MB | 2,104 ms, GC 1,520 ms, 1,244 MB | 0.97, 0.94, 1.26 |
| JS heap after the call, 4a's measure (`once.mjs`, median of 5) | 1,610 MB (8.4 × `plain`'s 191) | 1,290 MB (6.8 ×) | 1.25 |
| native time | 3,900 ms | 3,706 ms | 1.05 |
| native bytes, blocks per element | 7,456, 129 | 7,168, 124 | 1.04 |
| native most live | 1,464 MB | 1,240 MB | 1.18 |

The other shapes don't build a map per element (`askedChecked`'s
`translate` is around the whole `map`, and the failing branches never run),
so they are unchanged, and so is `plain` (its generated code is the same).
So the memory a search keeps falls by a fifth in both backends. The time
and GC gain in JS holds only when the call isn't the process's first: in a
fresh process the scavenges copy the same bytes before and after (1,185 and
1,181 MB promoted) **[checked]**, which suggests V8 had been allocating the
per-element maps' objects directly in the old generation there
(allocation-site pretenuring), so they cost memory but no copying
**[inferred]**. Against §9.3's bar this lane's change reaches 1.5 times
only on GC time in the warm measurement.

**Which shapes are within 3 times `plain`'s live memory in JS:** `checked`,
`failsLast`, `counted`, `countedChecked`, `asked`, `askedChecked` and
`askedIn` (2.5 to 2.9 times), as before; `emittedIn` (4.4) and
`searchedIn` (8.8) aren't.

**Next** (no ticket): the measurements point at generated code, not the run
loop. A hand-made version of the JS module in which `List.map`, `bindIn`,
`doneIn` and `bind` take all their arguments at once and `map`'s locals are
in its function's context (so the continuation keeps two contexts, not
four) runs `checked` in a fresh process in 344 ms against 447, GC 262 ms
against 337, allocating 1,278 bytes per element against 1,974 and keeping
321 MB against 385 **[checked]**: 1.3 times on time and GC, 1.55 on
allocation, and it would apply to every effectful shape. That is the JS
backend calling a known definition with all its arguments in one call, a
change to code generation in general, not to the effect runtime. Merging
the fold's two resumption closures into one, and chunked segments, would
each touch under a tenth of what survives.

**Tests.** `closed_signature_maps_are_constants` (`crates/rt/tests/effect_runtime.rs`:
`searchedIn` and `askedChecked` each have two map constants) and
`closed_signature_maps_are_built_once` (`crates/cli/tests/effect_runtime.rs`:
`searchedIn`'s JS reads its map from `sigmap$…`). The 4e generator ran
8,000 programs (1,000 batches from seed 1): all agree on the reference
evaluator, natively and in JS, none out of resources **[checked]**.

### 9.10 As built: known calls with all their arguments at once (D1173)

§9.9's "Next" taken: the JS backend calls a known definition with all its
arguments in one call. This changes JS code generation in general, not the
effect runtime. Nothing changed in the kernel, the elaborator or the native
runtime, and no hash moved.

**The calling convention** (`crates/js/src/lib.rs`, `DefInfo::uncurried`):

- A definition with two or more runtime parameters (erased ones don't
  count) is one JS function of all of them, `const f = (v0, v1) => …;`.
  Its empty-row variant gets the same convention, and so does its tail-call
  loop (the loop copies the parameters into slots as before). A definition
  with one runtime parameter is unchanged, because the two forms are the
  same.
- A call with at least the definition's arity of arguments (up to its
  arity, erased ones left out) is one call, `f(a, b)`. Any arguments after
  that are applied to the result one at a time, `f(a, b)(c)`.
- With fewer arguments, a partial application or a use as a value, the
  result is a closure that takes the remaining parameters one at a time, as
  every function value does. The erased ones are taken too, as D922
  requires: `(($p2) => f(v0, $p2))`. Supplied arguments that aren't a
  variable or a literal are computed once, outside the closure (`$s{i}`),
  as D922 already did. The most common value use is a definition with
  nothing supplied but its type arguments, such as an interface's `decEq` or
  `compare` stored in a dictionary, or `noReply` in `sigFromNo`. That
  closure is the same everywhere, so it's made at its first use and kept in
  a module variable, `(f$c ??= ($p0) => ($p1) => f($p0, $p1))`, declared
  with `var` at the end of the module, as the closed signature maps are.
- Natives are written curried, `(m) => (n) => m + n`, and are emitted
  uncurried (`(m, n) => m + n`) by stripping their leading arrows. A native
  whose JS doesn't start with enough arrows would stay curried, but there
  are none. The effect runtime's functions take their arguments together:
  `effBind(c, k)`, `foldComp` as `(done, call, c) => effFold(…)`,
  `translate` as `(m, c) => effTranslate(…)`, the lazy fold
  `effFoldCompLazy(done, call, c)`, the row-testing fold
  `effFoldCompIn(row, done, call, c)` (the row is passed first), and 4d's
  fused fold `effFoldState(comp, done, call, c)(s…)`. `effJump` stays
  curried, because the rewritten clauses receive it as a value.
- Function values (lambdas, variables, record fields) are applied one
  argument at a time, as before. Local lambdas aren't uncurried: a `let`
  bound lambda is a value, and lifted `match`es are top-level definitions,
  which are uncurried.
- **Exports are unchanged.** The wrappers already took JS arguments
  together (`function $$weigh(arg0, arg1)`). Now they call the compiled
  definition the same way, `$Main$dweigh(v0, v1)`. The `.d.ts` snapshots
  are byte-for-byte unchanged.

**Measured** (Apple M4 Pro, shared, load average 4 to 6; Node 22.23.3;
before is main at `5bf2a973`; `alloc.mjs` at 1,000,000 elements, median of
5 calls after a warm-up call; the table gives the median of three
interleaved rounds) **[checked]**:

| export | time before → after | GC before → after | bytes allocated per element | most live |
|---|---|---|---|---|
| `plain` | 65 → 65 ms | 38 → 39 ms | 169 → 168 | 133 → 133 MB |
| `pureMapIn` | 62 → 65 ms | 37 → 41 ms | 169 → 168 | 133 → 133 MB |
| `checked` | 386 → 299 ms | 290 → 240 ms | 2,028 → 793 | 384 → 350 MB |
| `failsLast` | 366 → 248 ms | 277 → 203 ms | 1,983 → 729 | 328 → 296 MB |
| `counted` | 522 → 400 ms | 328 → 240 ms | 2,770 → 1,691 | 388 → 356 MB |
| `countedChecked` | 614 → 500 ms | 300 → 257 ms | 5,220 → 2,930 | 388 → 357 MB |
| `asked` | 467 → 415 ms | 278 → 250 ms | 2,602 → 1,617 | 388 → 356 MB |
| `askedChecked` | 600 → 496 ms | 294 → 248 ms | 4,965 → 2,811 | 388 → 357 MB |
| `askedIn` | 494 → 411 ms | 287 → 242 ms | 3,107 → 1,706 | 388 → 356 MB |
| `emittedIn` | 744 → 467 ms | 467 → 295 ms | 3,026 → 1,634 | 580 → 548 MB |
| `searchedIn` | 1,839 → 1,550 ms | 1,269 → 1,110 ms | 7,257 → 4,430 | 1,172 → 1,140 MB |

`plain` and `pureMapIn` compile to the same code, which differs only by
`List.map$e(f, v0)` for `List.map$e(f)(v0)`. Their differences are within
the rounds' spread (`pureMapIn` before: 62, 61 and 76 ms). In a fresh
process (`COLD=1`, five processes each, interleaved), `checked` took 435 →
339 ms, with GC 323 → 267 ms. That is 1.28 times on time, against the
hand-made module's 1.3 in §9.9. Allocation went from 2,028 to 795 bytes per
element, or 2.55 times, against the hand-made module's 1.55: this change
uncurries every definition, including `ifThenElse`, `Decidable.elim`, the
`Nat` natives and the signature helpers, not only the four in that
experiment. It doesn't move `map`'s locals into its function's context, the
second half of the experiment.

Pure code: the AoC days under `run --js` (the whole process including
elaboration, with the cache warm; median of 5, two interleaved rounds; every
day prints its known answers) **[checked]**: day 4 807-873 → 765-780 ms,
day 8 3,101-3,116 → 2,304-2,369 ms, day 9 1,276-1,302 → 974-993 ms. The
other days run in about 500 ms, nearly all of it elaboration, and are
within 15 ms of before.

**Tests.** `known_calls_pass_their_arguments_together`
(`crates/cli/tests/effect_runtime.rs`) checks that `List.map`, `bindIn` and
`foldComp` take their arguments together and that no curried call of them
is left. `uncurried_definitions_work_every_way_they_are_used`
(`crates/cli/tests/run_js.rs`, checked against the reference evaluator)
covers full, partial and over-application, erased parameters left
unsupplied, a native and a definition passed as values, a tail-recursive
loop and mutual recursion. In `crates/js`, `uncurries_natives` and
`simple_arguments` are unit tests. The JS snapshots changed only in calling
convention. The 4e generator ran 8,000 programs (1,000 batches from seed 1),
and all of them agree on the reference evaluator, natively and in JS, with
none out of resources **[checked]**.

**Not done:** moving a case branch's locals into the function's context
(§9.9's other half). It would need `var`-style hoisting outside loops,
because a loop's turns must keep their own `const`s.

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
- `alloc.mjs`: time, bytes allocated, GC time and the most live heap inside
  one call of an export (§9.9):
  `node --expose-gc bench/effect-runtime/alloc.mjs OUT/shapes.js searchedIn
  1000000 [RUNS]`; `COLD=1` with `RUNS` 1 measures a process's first call.

Natively, `crates/rt/tests/effect_alloc.rs` measures the same exports'
allocation: `cargo test --release -p stitchwort-rt --test effect_alloc --
--ignored --nocapture`.

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
