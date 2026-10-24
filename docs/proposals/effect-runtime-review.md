# How effectful code should run: review of the stage 4 note

Status: self-review and research for D1162 (stage 4 of effect
polymorphism), 24 Oct 2026, to go to an external reviewer. No compiler
changes. It reviews [effect-runtime.md](effect-runtime.md) ("the note"),
written the same day, and is meant to be read **without access to the
repository**: every piece of code it relies on is quoted.

How claims are marked:

- **[measured]**: run by me for this report, on `main` at `06084471`
  (after stage 2 merged), release build, Node 22.23.3, Apple M4 Pro, on a
  machine shared with other work. Times are single runs unless stated, and
  differ by up to 2x between runs of the same thing, so only differences
  well above 2x, or in how times grow, mean anything.
- **[source]**: read in Stitchwort's source.
- **[inferred]**: my reasoning, not tested.
- **[unverified]**: a claim about another system that I couldn't confirm in
  a primary source.

Every claim about another system has a link.

## 0. Summary

**The problem.** Stitchwort runs effectful code as a free-monad tree. On
both backends an operation performed on every element of `List.mapIn` makes
the run quadratic. In JS, every effectful `mapIn` called from Node's normal
stack also overflows at 1,000 to 4,000 elements. I re-measured both.

**The note's proposal** (its design A, plus A′): keep the tree's two
constructors at run time, add an internal `Bind` node, and run computations
with a loop that keeps pending continuations on an immutable linked list in
the heap. A′ runs state-passing handlers as a loop. It is a small change
(four library functions per backend), it is linear, and it allows resuming
a continuation more than once.

**My verdict.** The direction is right, and the literature backs it. It is
the shape of PureScript's `Aff` and `Free`, of Effect-TS, and of Eff's OCaml
backend. My measurements show CPS with a trampoline is no faster, and
generators are unusable. But the note overstates what A and A′ deliver, and
its acceptance tests would not have caught that:

1. **Most handler shapes still overflow in JS under A + A′.** The note
   tested one handler shape (state) plus `Fail`. A reader (`ask, k => k
   7`) overflows at 2,000 elements under A. So do a writer that collects
   into a list (`emit v, k => Cons v (k ())`) and a backtracking search
   (`Each.collect` with a long path) **[measured]**. The note files the fix
   for the reader (tail-resumptive clauses run in place) under optional
   speed-ups, but it is needed for the program to finish at all.
2. **A cheap, general fix the note missed: lazy resumption.** Make the
   handler's `k` return a `Bind` node instead of running the rest at once.
   This is sound because every `handle` folds into a computation of the
   enclosing row. With it, the reader, writer and search run at 1,000,000
   elements in JS whenever another ability remains outside the handler, and
   the reader runs even with none **[measured]**.
3. **One case remains, and it is inherent.** A handler at the outermost
   (empty) row whose clause uses `k`'s result inside a pure expression
   (`Cons v (k ())`, `List.append (k True) (k False)`) is a pure
   non-tail recursion, as deep as the number of operations on one path. No
   change confined to the runtime fixes that in JS. It needs a decision
   (Q2 in §9).
4. **Allocation, not dispatch, is A's cost.** At 1,000,000 elements, about
   80% of A's time in JS is garbage collection pauses (heap 441 MB against
   195 MB for plain `map`) **[measured]**. The note doesn't measure memory.
5. **The native runtime's `IO` runner scans every frame for every
   operation.** If stage 4a moves `Bind` frames onto that frame stack, `io`
   stays quadratic **[source, inferred]**.
6. **Native effectful code that performs nothing would get slower** under A
   for no benefit: the native runtime has no stack problem. The fix is to
   keep `bind (Done x) k = k x` natively.

**Recommendation.** Adopt A, amended:

- lazy resumption in both backends;
- A′ for parameterised handlers at the empty row;
- the native `Done` fast path;
- `IO` routing that does not scan frames;
- broader acceptance: all handler shapes, memory, native non-regression,
  wasm;
- an explicit decision on the empty-row non-tail case.

§8 gives the details and §9 the questions for the reviewer.

## 1. Background: what Stitchwort runs

Stitchwort is a dependently typed language. Its checker (the "kernel") is
trusted. Two *untrusted* backends run programs, and differential tests check
them against a slow reference evaluator:

- a native bytecode machine in Rust (`crates/rt`), which also runs in the
  browser playground compiled to WebAssembly;
- a JS code generator (`crates/js`). Its modules are called from Node or
  from web pages.

The comment at the top of the native runtime says it "can only get a
program's output wrong, never make a false proof check" **[source]**.

### 1.1 Computations are trees

Abilities (algebraic effects) are elaborated into a free monad defined in
the library **[source]**:

```
type Effect.Comp (op: Type) (res: op -> Type) (a: Type): Type =
  | Done (value: a)
  | Call (o: op) (rest: res o -> Comp op res a)

def Effect.foldComp (done: a -> r) (call: (o: op) -> (res o -> r) -> r): Comp op res a -> r
  | Done x => done x
  | Call o rest => call o (y => foldComp done call (rest y))

def Effect.bind: Comp op res a -> (a -> Comp op res b) -> Comp op res b
  | Done x, next => next x
  | Call o rest, next => Call o (y => bind (rest y) next)

def Effect.translate (m: SigMap op1 res1 op2 res2): Comp op1 res1 a -> Comp op2 res2 a
  | Done x => Done x
  | Call o rest => Call (sigInject m o) (r => translate m (rest (sigReply m o r)))

def Effect.runPure: Comp NoOp NoRes a -> a      -- the empty signature: only Done
```

- **Operations.** An operation call `Counter.next()` becomes
  `Call (inject next) (y => Done y)`.
- **Sequencing.** Code in a row with abilities is sequenced with `bind`.
- **Handlers.** `handle … with` becomes `foldComp`, so handlers are deep.
  The operation clauses are dispatched on the operation, and every
  operation the handler doesn't handle is re-emitted outward
  ("forwarded").
- **Rows.** A row is a list of abilities, `{Fail, IO}`. When a call's row
  differs from the caller's, the computation is moved into the caller's
  row with `translate`.
- **Effect polymorphism.** A row may end in a variable, `{e}` or
  `{Fail | e}`. At the empty row, `{e} a` computes to plain `a`. Stage 2
  compiles that case as pure code, so pure callers of `mapIn` run `map`'s
  loop.

### 1.2 Which functions can see a computation's structure

Since stage "R2", a program outside the library cannot use `Done`, `Call`,
`foldComp`, `bind`, `translate` or `runPure` in code that runs. It can use
them in proofs **[source]**. So at run time a computation is abstract:

- it is built by `Done`, `Call`, `bind` and the elaborator's `handle`
  output;
- it is taken apart only by `foldComp`, `translate`, `runPure` and the
  `main` runner.

A backend may therefore represent computations however it likes, provided
those functions agree with the tree. Proofs never mention the backends, so
they are unaffected.

### 1.3 What the generated JS looks like

`List.mapIn` is written as ordinary recursion:

```
def List.mapIn (f: a -> {e} b): List a -> {e} List b
  | Nil => Nil
  | Cons x xs => Cons (f x) (List.mapIn f xs)
```

Its generated JS at a non-empty row (`v1` is the row, `v3` is `f`)
**[source]**:

```js
case "Cons": {
  const v5 = v4.head; const v6 = v4.tail;
  return $Std$dEffect$dbindIn(v1)((v3)(v5))(((v7) =>
    $Std$dEffect$dbindIn(v1)($Std$dList$dmapIn(v1)(v3)(v6))(((v8) =>
      $Std$dEffect$ddoneIn(v1)({ tag: "Cons", head: v7, tail: v8 })))));
}
```

`bind` itself is the library definition, compiled like any other:

```js
const $Std$dEffect$dbind = (v4) => (v5) => {
  switch (v4.tag) {
    case "Done": { const v6 = v4.value; return (v5)(v6); }
    case "Call": { const v6 = v4.o; const v7 = v4.rest;
      return { tag: "Call", o: v6, rest: ((v8) => $Std$dEffect$dbind((v7)(v8))(v5)) }; }
  } };
```

Two handlers, as written and as generated **[source]**:

```
def Env.give (value: Nat) (prog: () -> {Env} a): a :=
  handle prog() with
    | return x => x
    | Env.ask u, k => k value

def Emit.collect (prog: () -> {Emit} a): List Nat :=
  handle prog() with
    | return x => []
    | Emit.emit v, k => Cons v (k ())
```

```js
// Env.give: runPure is around the whole fold; the clause just calls k.
const $Main$dEnv$dgive = (v1) => (v2) => $Std$dEffect$drunPure($Std$dEffect$dfoldComp(
  ((v3) => ({ tag: "Done", value: v3 })))($Std$dEffect$dhandlePlus($Main$dEnv$d$gelim(
  ((v3) => ((v4) => (v4)(v1)))))( /* forward */ ...))((v2)({ tag: "UnitValue" })));

// Emit.collect: the clause needs k's *value*, so runPure is inside the clause.
... ((v2) => ((v3) => ((v4) => ({ tag: "Done", value: { tag: "Cons", head: v2, tail: v4 } }))
     ($Std$dEffect$drunPure((v3)({ tag: "UnitValue" }))))) ...
```

So **the fold that `handle` produces always has a computation of the
enclosing row as its result**.

- If the enclosing row is empty (nothing left outside the handler), a
  single `runPure` is put around the fold.
- Inside a clause, a `runPure` is also put wherever the clause needs `k`'s
  result as a plain value.

The elaborator's comment says the same: the carrier is
`comp_type(cx, out, t)` **[source]**. This matters for §5.2.

## 2. The semantics any runtime must preserve

Write `≈` for "gives the same result in every use". The runtime's versions
of the eliminators must satisfy the library's equations:

```
bind (Done x) k         ≈ k x
bind (Call o r) k       ≈ Call o (y => bind (r y) k)
foldComp d c (Done x)   ≈ d x
foldComp d c (Call o r) ≈ c o (y => foldComp d c (r y))
translate m (Done x)    ≈ Done x
translate m (Call o r)  ≈ Call (inject m o) (y => translate m (r (reply m o y)))
runPure (Done x)        ≈ x
```

These equations bring the following requirements:

- **Multi-shot.** `k` is an ordinary function. A clause may call it any
  number of times, or store it in the handler's result. The standard
  library relies on this: `Each.collect`'s `fork` clause is
  `Each.both (b => k b)`, and `Each.both k = List.append (k True)
  (k False)`.
- **Deep handlers.** A resumed continuation is still handled by the same
  handler.
- **Forwarding and translate.** Unhandled operations pass outward through
  every enclosing handler and `translate` in order, and their replies come
  back through each mapping.
- **Two backends plus wasm.** Native (and the same code in wasm, in the
  playground) and JS.
- **`main` and `Partial`.** `main` is a partial computation, a `Delay`.
  The `IO` runner steps it with a stack-safe abstract machine that already
  has explicit `Bind`, `Map` and `Tie` frames. Handlers inside `main` whose
  row includes `Partial` forward operations through `bindD (lift (Call …))`.
- **Pure code.** Stage 2's guarantee is that pure uses of effect-polymorphic
  functions run as pure code (`mapIn` with a pure `f` runs `map`'s loop).
  Nothing in stage 4 may slow that down.
- **What may differ.** When pure work happens (a `Bind` node delays it), and
  resource use: stack, heap and time. The order of operations may not
  differ.

## 3. The baseline, re-measured

### 3.1 Exported functions called from Node's default stack [measured]

The benchmark is `map.sw`. It maps a callback over `List.range n` and sums
the result. The variants:

- `plain`: pure `List.map`.
- `pureMapIn`: `mapIn` with a pure callback.
- `checked`: a `Fail`-able callback that never fails, under `Fail.toResult`.
- `failsLast`: fails at the last element.
- `counted`: `x + Counter.next()` under the state handler below.
- `countedChecked`: the same inside a `Fail` handler.

```
def Counter.number (prog: () -> {Counter} a): Nat -> a :=
  handle prog() with
    | return x => (s => x)
    | Counter.next u, k => (s => k s (s + 1))
```

| n | plain | pureMapIn | checked | failsLast | counted | countedChecked |
|---|---|---|---|---|---|---|
| 1,000 | 0.5 ms | 0.1 | 0.7 | 1.9 | 64 | 109 |
| 2,000 | 0.7 | 0.2 | 1.1 | **overflow** | 443 | 502 |
| 4,000 | 0.5 | 0.2 | **overflow** | | **overflow** | **overflow** |
| 1,024,000 | 138 | 107 | | | | |

These agree with the note. One thing has changed since the note: stage 2
has merged, so `pureMapIn` now runs at 1,024,000.

### 3.2 Native, whole `stitchwort run` [measured]

These times include about 0.2 s of checking. Each doubling of `n` takes
about four times as long, so the time grows quadratically:

| n | state | asked | emitted | searched | askedChecked |
|---|---|---|---|---|---|
| 4,000 | 1.19 s | 1.27 | 1.36 | 2.09 | 1.37 |
| 8,000 | 4.64 | 6.71 | 5.05 | 8.45 | 9.29 |

The columns other than `state` are the new handler shapes of §5.1. None of
them hit the native frame limit at these sizes.

### 3.3 The note's three causes, checked

**Cause 1: `bind` rebuilds the chain at every operation (quadratic, both
backends).** Confirmed by counting calls of the generated `bind`
**[measured]**:

| n | `counted`: bind calls | per element | `checked`: bind calls |
|---|---|---|---|
| 250 | 32,375 | 129.5 | 500 |
| 500 | 127,250 | 254.5 | 1,000 |
| 1,000 | 504,500 | 504.5 | 2,000 |

`counted` makes exactly `n(n+9)/2` calls; `checked` makes `2n`. This is
Voigtländer's left-nested substitution
([MPC 2008, §2](https://www.janis-voigtlaender.eu/papers/AsymptoticImprovementOfComputationsOverFreeMonads.pdf)).

**Cause 2: a JS call per `bind` on the `Done` path (stack, JS only).**
Confirmed. The stack trace of `checked`'s overflow repeats four frames per
element: `bindIn` → `bind` → `k` → `mapIn` **[measured]**.

**Cause 3: the state handler's chain of tail calls (stack, JS only).**
Confirmed by the note's trace, and by mine under the prototype (§4). But
cause 3 is one instance of a wider problem the note doesn't name, described
in §5.1.

## 4. The note's proposal and prototype

### Design A

Keep `Done` and `Call`. Add one internal node, `Bind c k`. `bind` builds
the node and calls nothing. A loop runs computations, with the pending
continuations on an immutable linked list. The prototype (hand-written JS,
patched into the generated module in place of `bind`, `foldComp`,
`translate` and `runPure`):

```js
const bind = (c) => (k) => ({ tag: "Bind", c, k });

function run(c, stack) {            // stack: null | { k, next }
  for (;;) switch (c.tag) {
    case "Bind": stack = { k: c.k, next: stack }; c = c.c; break;
    case "Done": if (stack === null) return c;
                 c = stack.k(c.value); stack = stack.next; break;
    case "Call": return { tag: "Op", o: c.o, rest: c.rest, stack };
  }
}
function fold(done, call, c, stack) {
  const r = run(c, stack);
  if (r.tag === "Done") return done(r.value);
  const rest = r.rest, pending = r.stack;
  return call(r.o)((y) => fold(done, call, rest(y), pending));   // k: eager
}
// translate: the same, re-emitting each operation through the mapping;
// runPure: run(c, null).value
```

- **Capture.** Capturing `k` keeps a pointer to `pending`.
- **Multi-shot.** The list is never mutated, so resuming `k` twice
  re-runs from the same list.
- **Linearity.** Each `bind` is entered and left once.

### A′: parameterised handlers

When every clause of a handler is a lambda over the same parameter (the
state), the backend runs the handler as a loop with the state in a
variable. The prototype's hand-written version of `Counter.number`:

```js
const number = (prog) => (s0) => {
  let s = s0, r = run(prog(unit), null);
  for (;;) {
    if (r.tag === "Done") return r.value;
    const answer = s; s = s + 1n;            // the clause: k s (s + 1)
    r = run(r.rest(answer), r.stack);
  }
};
```

### Re-run of the prototype [measured]

These are the largest sizes that ran, on Node's default stack. All 60 of
`agree.mjs`'s cases (sizes 0 to 500, nested handlers, multi-shot `choices`
up to 4,096 results) agree, for both patched modules:

| | checked | failsLast | counted | countedChecked |
|---|---|---|---|---|
| A | 1,024,000: 464 ms | 1,024,000: 400 | overflow at 4,000 | overflow at 4,000 |
| A + A′ | 1,024,000: 510 | 1,024,000: 508 | 1,024,000: 615 | 1,024,000: 846 |

These agree with the note's numbers.

## 5. Self-review: where the note is right, and where it is not

### 5.1 Most handler shapes still overflow in JS [measured]

The note's benchmark has two handlers: `Fail.toResult`, whose clause never
calls `k`, and a state handler, which A′ special-cases. Real handlers come
in more shapes. I wrote `shapes.sw` with four more, each over `mapIn` with
one operation per element:

- **`asked`: a reader.** `| Env.ask u, k => k value`. Tail-resumptive, no
  parameter.
- **`emitted`: a writer that collects into a list.**
  `| Emit.emit v, k => Cons v (k ())`. Not tail-resumptive.
- **`askedChecked`.** The reader with a `Fail` handler inside it, which
  forwards `ask`.
- **`searched`: a search with one long path.**
  `Each.collect (() => mapIn (x => Each.each [x]) xs)`. Each element forks
  once, and the second branch stops at once.

The `…In` variants are the same handlers written for an open row
(`{Emit | e}` and so on), with `Fail.toResult` outside. Their clauses are
then effectful code.

Largest size that ran (or the size at which it overflowed), on Node's
default stack:

| | generated today | A | A + lazy `k` (§5.2) |
|---|---|---|---|
| asked | overflow 2,000 | overflow 2,000 | **1,024,000: 758 ms** |
| emitted | overflow 2,000 | overflow 4,000 | overflow 2,000 |
| askedChecked | overflow 4,000 | overflow 8,000 | **1,024,000: 4.5 s** |
| searched | overflow 4,000 | overflow 2,000 | overflow 2,000 |
| askedIn | overflow 4,000 | overflow 4,000 | **1,024,000: 2.8 s** |
| emittedIn | overflow 2,000 | overflow 4,000 | **1,024,000: 2.5 s** |
| searchedIn | overflow 2,000 | overflow 4,000 | **1,024,000: 5.6 s** |

All modules agree on sizes 0 to 300 **[measured]**.

The overflow trace under A is the same for every shape:

```
run loop      c = stack.k(c.value)
fold          const r = $proto$run(c, stack)
fold          return call(r.o)((y) => $proto$fold(...))
clause        ... k value / runPure(k ()) / Each.both(...)
k             $proto$fold(done, call, rest(y), pending)
... repeated once per operation
```

The cause is that a handler clause calls `k`, and `k` (in the note's
design) runs the rest of the computation *inside that call*: to the next
operation, where it calls the clause again. Cause 3 is the special case
where the call is a tail call through a returned function. The note says
"nothing grows the JS stack" (its §0). That is true of `bind`, but not of
handlers, and the note's acceptance tests (only `counted` and `Fail`) would
pass with this hole in place.

### 5.2 Lazy resumption fixes most of it [measured]

Because a `handle`'s fold always produces a computation of the enclosing
row (§1.3), the backend may make `k` lazy: return a node that resumes when
run, instead of resuming now. One line of the prototype (`--lazy-resume`):

```js
return call(r.o)((y) => ({ tag: "Bind", c: { tag: "Done", value: y },
                           k: (z) => fold(done, call, rest(z), pending) }));
```

Now a clause like `k value` returns at once, and the loop that runs the
handler's result does the resuming, so nothing nests.

- **Enclosing row not empty.** The clause body is effectful code: `Cons v
  (k ())` elaborates to `bind (k ()) (rest => Done (Cons v rest))`. So
  every shape is stack-safe, including the multi-shot search (`searchedIn`
  above).
- **Enclosing row empty.** The reader is still fixed, because its clause
  returns `k`'s computation and `runPure` runs it outside. But `Emit.collect`
  and `Each.collect` put `runPure (k …)` inside a pure expression, which
  runs at once and nests. The state handler (`s => runPure (k s) (s + 1)`)
  nests too, so A′ is still needed for it.

Soundness of lazy resumption needs every `foldComp` that runs to have a
computation as its result. That holds for `handle`. The library defines
`foldComp` but no library code calls it at run time **[source: grep of the
standard library]**, and R2 forbids programs from calling it.

Cost: one node per resumption. `map.sw` under lazy resumption still agrees
on all 60 cases, and with A′ runs `counted` at 1,024,000 in 760 ms
**[measured]**.

### 5.3 What is left, and why the runtime can't fix it

Take a handler at the empty row whose clause uses `k`'s value inside pure
code: `Cons v (k ())`, `List.append (k True) (k False)`. As a function, it
is a pure non-tail recursion over the operations on one path. In
`Each.collect`, `k` is even passed to a plain library function
(`Each.both`) whose type says nothing about effects.

In JS that recursion uses the JS stack, like any pure `foldRight`. The
note's §6 says pure non-tail recursion is "not an effects problem". That's
fair for `foldRight`. It is less fair here: the user wrote an ordinary
handler, and the depth comes from the effectful code being handled.

Natively the frames are on the heap, but they still count against the
machine's frame limit (2,000,000 frames by default) **[source]**. A
writer over a few hundred thousand elements may hit it **[inferred]**.

The options, for the reviewer (Q2):

1. Accept it and document it. Offer stack-safe idioms: the `…In`
   variants, or an accumulator parameter (`emit v, k => (acc => k ()
   (Cons v acc))`, a parameterised handler that A′ runs as a loop).
2. Elaborate empty-row handler clauses in "computation mode over the
   empty signature", so that `k` returns a computation and lazy
   resumption applies. This changes what clause bodies mean to the type
   checker: `k` would have type `res -> Comp NoOp NoRes r`, not
   `res -> r`. That breaks `Each.collect`'s lemmas, which rely on `k` being
   a plain function (its comment says so) **[source]**. It also changes
   hashes and user-visible types.
3. A general JS mechanism for deep stacks. Stopify, for example, "can
   simulate an arbitrarily deep stack and proper tail calls"
   ([README](https://github.com/plasma-umass/Stopify);
   [PLDI 2018](https://arxiv.org/abs/1802.02974)) by instrumenting all
   code. That costs pure code too, so it conflicts with stage 2
   **[unverified: I couldn't extract the paper's overhead numbers]**.
   Another option is calling exports on a worker thread with a large
   stack, as `run --js` already does.

### 5.4 The claimed costs: dispatch is cheap, GC is not [measured]

The note says A costs "a `Bind` node and a list cell per `bind`, one
dispatch per step", and reports `checked` at 4.6 to 5.7 times `plain`.
That's true but incomplete. I ran each export once at 1,024,000 elements
with `node --trace-gc`, three runs each. The numbers below are for the
whole process, including building the input list:

| | call time | scavenges | mark-compacts | total GC pause | heap after |
|---|---|---|---|---|---|
| plain (generated) | 56 ms | 13 | 0 | 39 ms | 195 MB |
| checked (A + lazy + A′) | 480–507 ms | 144–147 | 1 | 376–401 ms | 441 MB |
| counted (A + lazy + A′) | 571–594 ms | 158 | 1 | 387–403 ms | 443 MB |
| countedChecked | 1.36–2.06 s | 323 | 2 | 0.88–1.24 s | 444 MB |

- **GC is most of the time.** About 80% of A's run time is GC pauses.
- **Why.** The pending list is *live* for the whole run, because a
  non-tail `mapIn` has `n` pending continuations. So each scavenge copies
  it, and it is promoted to the old generation. Today's direct calls keep
  the same state on the JS stack, which the GC doesn't copy.
- **What is not the cost.** "Megamorphic dispatch" is not the issue. The
  `switch` sees three object shapes, all built by object literals with a
  fixed field order, which V8 handles as polymorphic, not megamorphic
  **[inferred]**.
- **What would help.** Fewer binds per element, and smaller nodes.
  `mapIn`'s `Cons` case makes two binds, two closures and two pending
  cells per element. A specialised effectful `mapIn` with one bind per
  element, or a `Bind` node that carries its cell, would cut this
  **[inferred]**.

This also explains the note's noisy, slightly superlinear times at
1,000,000 elements (2.3x per doubling): heap growth, not the algorithm.

### 5.5 The native runtime: two problems the note's plan would hit

**(a) The `IO` runner scans every frame for every operation.**

The native `main` runner (`crates/rt/src/run.rs`) keeps `Delay` frames
(`Bind`, `Map`, `Tie`, `Await`) in a `Vec`. It routes each operation that
reaches it by walking that `Vec` from the top down to frame 0 **[source]**:

```rust
let mut j = self.frames.len();
while j > 0 {
    j -= 1;
    match &self.frames[j] {
        Frame::Bind(_) | Frame::Await { .. } => {}
        Frame::Map(inject, _) => { /* translate the operation */ }
        Frame::Tie(f) => { /* maybe answer a recursion request */ }
    }
}
```

Today the `Comp`'s binds are inside the `Comp`, not in this `Vec`, so the
scan is short. The note's plan says "the `IO` runner and `lift` use the
loop". If that is done by pushing `Comp` binds as runner frames, every
`print` inside a 1,000,000-element `mapIn` scans up to 1,000,000 frames,
and `io` stays quadratic **[inferred]**.

The runner needs either a separate index of the `Map` and `Tie` frames,
or to keep the `Comp` loop's pending list apart from the `Delay` frames.
Effekt and Links do the latter: the continuation alternates pure segments
and handler frames, so capture costs the number of handlers crossed, not
the number of frames
([Effekt runtime](https://github.com/effekt-lang/effekt/blob/main/libraries/js/effekt_runtime.js);
[Links, JFP 2020 §5](https://strathprints.strath.ac.uk/71892/)).

**(b) A costs native code something for nothing on the `Done` path.**

Natively, the machine's frames are on the heap, so `bind (Done x) k = k x`
uses no Rust stack, and cause 2 does not exist. Building a `Bind` node and
a list cell for every bind only adds allocation. Today native `mapIn` with
`{Fail}` costs 3.4 times `map` (stage 2's table: 3.40 s against 1.00 s for
10,000,000 elements) **[source]**. That ratio could grow.

Stage 1's own requirement 4 for stage 4 was: "pure paths keep today's
speed: a computation that performs nothing costs little more than a direct
call" (effect-polymorphism.md, design F) **[source]**. The note's 4a has
no criterion for it.

The fix: natively, build a `Bind` node only when `c` is not `Done`. This is
the bind-inlining fast path of Koka
([Xie and Leijen, ICFP 2021, §2.7.1](https://www.microsoft.com/en-us/research/uploads/prod/2021/03/multip-tr-v2.pdf)),
with no depth counter needed because the frames are on the heap.

**(c) Where the loop must live.**

The note correctly says the native loop must run on the machine's frames,
not as Rust code that calls back into the machine. This matters even more
in the playground: wasm's stack is small, and a Rust-level recursion per
operation (§5.1's nesting moved into Rust) would overflow it sooner than
native does **[inferred]**. There is a precedent: the machine already has a
return kind for "the next step of `Text.fold`", a higher-order native that
runs on machine frames **[source]**.

### 5.6 What the prototype does and doesn't cover

| Requirement | Covered by the prototype? |
|---|---|
| Multi-shot | Yes: `choices`, 2^12 results; `searchedIn` (lazy) at 1,000,000 forks |
| Nested handlers, forwarding | Yes: `countedChecked`, `askedChecked`, the `…In` variants (`Fail.toResult` forwarding) |
| `translate` | Yes: every `…Checked` and `…In` export goes through a generated `translate` |
| Open rows (`{e}`) | Yes: the `…In` handlers |
| `IO` stepping and the runners | **No.** Exports can't use `IO`. §5.5(a) is the risk |
| `Partial`, `Delay` forwarding (`bindD (lift (Call …))`) | **No** |
| Deep recursion inside handlers | Only since this review (§5.1) |
| Native and wasm | **No**: JS only |
| Memory | **No**: only since this review (§5.4) |

### 5.7 Smaller points

- **Effekt's JS stack safety is narrower than the note says.** The note
  says Effekt's runtime trampolines and pays "a bounce per jump". Effekt's
  current generator thunks only *continuation* calls and the bodies of
  `reset`/`shift`/`resume`. Ordinary calls are plain JS calls
  ([TransformerCps.scala](https://github.com/effekt-lang/effekt/blob/main/effekt/shared/src/main/scala/effekt/generator/js/TransformerCps.scala)).
  So deep non-tail direct recursion may still overflow **[inferred from
  source, not run]**. An open PR proposes thunking only past a depth of
  512, for a 1.06x mean speed-up
  ([PR #1328](https://github.com/effekt-lang/effekt/pull/1328)).
- **Koka's JS backend has no trampoline at all.** It runs Node with
  `--stack-size=100000`
  ([CodeGen.hs](https://github.com/koka-lang/koka/blob/dev/src/Compile/CodeGen.hs)).
  A maintainer acknowledges that "handlers do build up on resumption"
  ([issue #747](https://github.com/koka-lang/koka/issues/747)). The note's
  "Koka's own JS output overflows" holds. Its source was a 2020 paper about
  Koka 0.9, and this is the current evidence.
- **Design B's state handler.** The note says B still needs A′ because the
  state chain runs in pure code. Correct for Stitchwort, where `k`'s type
  is a pure function type. In Effekt, `resume` is itself a control
  operation, so clause bodies are CPS'd. That is the same distinction as
  §5.3.
- **The staged plan's linearity test** ("each doubling at most 2.5 times")
  is too loose to tell `n log n` from linear. It is also too tight for
  single runs with this much GC noise. Use the median of 5 runs, a 2.3x
  bound, and a memory bound.
- **A′ through the elaborator changes hashes.** The note says so and
  accepts it. Since lazy resumption already handles tail-resumptive
  clauses, A′ is needed only for parameterised handlers at the empty row.

## 6. What others do

### 6.1 Free monads with a run loop and heap continuations (the note's family)

**PureScript `Aff`: the closest match to design A.**
([Aff.js](https://github.com/purescript-contrib/purescript-aff/blob/main/src/Effect/Aff.js), `Fiber`/`run`)

- **Mechanism.** On a `BIND` node it does `btail = new Aff(CONS, bhead,
  btail); bhead = step._2; step = step._1`. That is an immutable cons list
  of pending binds, popped in a `while (true)` state machine.
- **Cost and safety.** Push and pop are worst-case O(1).
- **Multi-shot.** Not offered to users: a `runTick` counter rejects a
  second resumption.
- **Production.** It is PureScript's standard async monad. I found no
  published benchmarks **[unverified]**.

**PureScript `Free` and `Run`.**
([Free.purs](https://github.com/purescript/purescript-free/blob/master/src/Control/Monad/Free.purs),
[Run.purs](https://github.com/natefaubion/purescript-run/blob/master/src/Run.purs))

- **Mechanism.** A view plus a catenable list of continuations, "in the
  spirit of Reflection without Remorse … to overcome the quadratic
  complexity of left-associated binds". `CatList` is O(1) amortised, but
  "any single uncons operation may run in O(n) time"
  ([CatList.purs](https://github.com/purescript/purescript-catenable-lists/blob/master/src/Data/CatList.purs)).
- **Stack safety.** Through `tailRecM`.
- **Multi-shot.** Yes: `runChoose` resumes `k true` and `k false`
  ([Choose.purs](https://github.com/natefaubion/purescript-run/blob/master/src/Run/Choose.purs)).
  Whether the amortised bound survives resuming one list twice is
  undocumented **[unverified]**. A plain cons list, as in A, has only
  worst-case O(1) operations, so the question doesn't arise.

**Scala `cats.Free`.**
([Free.scala](https://github.com/typelevel/cats/blob/main/free/src/main/scala/cats/free/Free.scala))

- **Mechanism.** One `FlatMapped` node per bind, reassociated in a
  `@tailrec step`.
- **Multi-shot.** Yes: the structure is immutable.

**cats-effect 3 `IOFiber`.**
([IOFiber.scala](https://github.com/typelevel/cats-effect/blob/series/3.x/core/shared/src/main/scala/cats/effect/IOFiber.scala))

- **Mechanism.** *Mutable* array stacks: a byte stack of frame tags plus
  an object stack.
- **Fast path.** `flatMap` on a `Pure` runs directly. `map` continuations
  recurse on the native stack up to `MaxStackDepth = 512`
  ([IOFiberConstants.java](https://github.com/typelevel/cats-effect/blob/series/3.x/core/jvm/src/main/java/cats/effect/IOFiberConstants.java)).
- **Multi-shot.** No.
- **Evidence.** A published `DeepBindBenchmark` run gives 14,763 ops/s at
  10,000 binds, about 7 ns per bind
  ([cats PR #4211](https://github.com/typelevel/cats/pull/4211)).

**ZIO 2.0.x: depth-limited native recursion, then reify.**
([v2.0.10 FiberRuntime.scala](https://github.com/zio/zio/blob/v2.0.10/core/shared/src/main/scala/zio/internal/FiberRuntime.scala))

- **Mechanism.** Binds recursed on the JVM stack until depth 300. Then it
  threw an exception. Each enclosing frame caught it, appended its
  continuation to a heap array, and rethrew. The loop restarted from the
  heap copy.
- **Later versions.** The current series pushes frames on a heap array
  instead
  ([series/2.x](https://github.com/zio/zio/blob/series/2.x/core/shared/src/main/scala/zio/internal/FiberRuntime.scala)).
- **Multi-shot.** One-shot in every version.
- **Relevance.** This is the general version of the "fast path with a
  depth counter" in §7.

**Effect-TS v3.**
([fiberRuntime.ts at effect@3.17.0](https://github.com/Effect-TS/effect/blob/effect%403.17.0/packages/effect/src/internal/fiberRuntime.ts))

- **Mechanism.** A heap `_stack: Array<Continuation>`, a `while (true)`
  run loop, and a yield every 2,048 operations.
- **Multi-shot.** One-shot. It is a production TypeScript runtime with
  this design.

**Eff compiled to OCaml.**
([Karachalias et al., OOPSLA 2021](https://lirias.kuleuven.be/retrieve/656121))

- **Mechanism.** Uses exactly Stitchwort's free monad (`Return | Call of
  effect * arg * (res -> comp)`) and calls it "sufficiently performant …
  as optimisations remove most of effects anyway".
- **Cost.** The naive encoding is "an order of magnitude slower" than
  hand-written code. The fixes are a purity-aware translation and source
  rewrites that reduce handlers away.

**Freer monads and "Reflection without remorse".**
([freer-simple](https://github.com/lexi-lambda/freer-simple/blob/master/src/Data/FTCQueue.hs);
[van der Ploeg and Kiselyov 2014](https://okmij.org/ftp/Haskell/zseq.pdf);
[Kiselyov and Ishii 2015](https://okmij.org/ftp/Haskell/extensible/more.pdf))

- **Mechanism.** Binds are kept as a type-aligned queue (`|>` O(1),
  `tviewl` "average O(1)").
- **Multi-shot.** Yes, and "the representation preserves the sharing of
  continuations" (Kiselyov and Ishii §5).
- **Stack safety.** Not a concern in lazy GHC.
- **Comparisons.** Benchmarks against other Haskell libraries are only in
  charts ([effectful benchmarks](https://github.com/haskell-effectful/effectful/blob/master/benchmarks/README.md)).

**Stack safety for free.**
([Freeman 2015](https://functorial.com/stack-safety-for-free/index.pdf))

- **Mechanism.** `MonadRec`/`tailRecM`, after Bjarnason's `Gosub` node.
- **Relevance.** It is the origin of the stack-safe `Free` in PureScript
  and cats.

**What this family shows.**

- **Production evidence.** A heap list plus a loop is proven in production
  JS (`Aff`, Effect-TS).
- **The difference from A.** Those runtimes are one-shot, with mutable
  stacks. A's immutable list is what makes multi-shot free.
- **The cost.** Allocation per bind, which Eff reports as an order of
  magnitude before optimisation and §5.4 measures as GC.

### 6.2 CPS with a trampoline and a meta-stack (Effekt, Links, js_of_ocaml)

**Effekt JS.**
([runtime](https://github.com/effekt-lang/effekt/blob/main/libraries/js/effekt_runtime.js);
[PR #619](https://github.com/effekt-lang/effekt/pull/619) moved to CPS in 2024)

- **Mechanism.** Every user definition is CPS'd. Direct style is recovered
  by optimisation passes
  ([PR #777](https://github.com/effekt-lang/effekt/pull/777)), not by
  effect types.
- **Continuations.** The meta-stack is a list of segments
  `{stack, prompt, arena, rest}`. `SHIFT` walks segments to the prompt, so
  capture costs the number of handlers crossed. `RESUME` pushes them back.
- **Multi-shot.** Free, because segments are immutable closures. Mutable
  state uses a snapshottable arena: capture is O(1), restore is
  O(writes since capture).
- **Stack safety.** `RUN_TOPLEVEL` is `while (true) { a = a() }`.
- **Tail resumption.** Resolved statically
  ([StaticResumptions.scala](https://github.com/effekt-lang/effekt/blob/main/effekt/shared/src/main/scala/effekt/core/optimizer/StaticResumptions.scala)).
- **Evidence.** The only Effekt-vs-Koka JS comparison is from 2020, on
  hand-written programs
  ([Schuster et al., ICFP 2020, §6](https://se.cs.uni-tuebingen.de/publications/schuster20capability.pdf)).
  The shared benchmark suite compares native builds only
  ([effect-handlers-bench](https://github.com/effect-handlers/effect-handlers-bench)).

**Links.**
([Hillerström, Lindley, Atkey, JFP 2020](https://strathprints.strath.ac.uk/71892/))

- **Mechanism.** Selective CPS to JS, "based on their purity, which is
  crucial in practice for performance". A trampoline that "periodically
  discards the call stack", which needs a properly tail-recursive CPS
  translation (§8).
- **Server side.** A CEK-style abstract machine with generalised
  continuations (§6). This is the closest published relative of a run loop
  with handler-aware continuations.
- **Multi-shot and handlers.** Yes. Deep, shallow and parameterised
  handlers.
- **Evidence.** No published JS benchmarks: they list them as future work.

**js_of_ocaml.**
([effects.mld](https://github.com/ocsigen/js_of_ocaml/blob/master/manual/effects.mld))

- **Mechanism.** `--effects=cps` partially CPS-transforms the program,
  with an analysis that keeps effect-free code direct, "less effective
  when higher-order functions are heavily used".
- **Double translation.** `--effects=double-translation` keeps both
  versions and chooses at run time.
- **Stack safety.** A depth counter (`caml_stack_check_depth`) bounces to a
  trampoline
  ([jslib.js](https://github.com/ocsigen/js_of_ocaml/blob/master/runtime/js/jslib.js)).
- **Multi-shot.** No: continuations are one-shot.

**Fit for Stitchwort.** It would mean a second calling convention in both
backends and a CPS/direct boundary.

- **Speed.** My micro-benchmark (§7) shows CPS no faster than A on the
  shapes that matter.
- **The open question.** Lazy resumption gets most of B's stack safety
  without a new calling convention. For empty-row handlers, B has the same
  problem as A, because `k` is a pure function by type.

### 6.3 Evidence passing (Koka)

([Xie et al., ICFP 2020](https://www.microsoft.com/en-us/research/uploads/prod/2020/07/evidently.pdf);
[Xie and Leijen, ICFP 2021 TR](https://www.microsoft.com/en-us/research/uploads/prod/2021/03/multip-tr-v2.pdf);
JS runtime [hnd.js](https://github.com/koka-lang/koka/blob/dev/lib/std/core/inline/hnd.js))

- **Mechanism.** Handlers are passed down as an evidence vector.
  - A clause of the form `λx k. k e` runs in place, at "a cost very
    similar to virtual method calls"
    ([book §3.4.3](https://koka-lang.github.io/koka/doc/book.html#sec-opfun)).
    Turning this off makes `counter` "10× slower" (2021 §5).
  - Other operations *yield*: each effectful frame between the operation
    and its prompt appends one closure (`_yield_extend`). So the cost per
    operation is proportional to the depth: quadratic for `mapIn`.
- **Multi-shot.** Yes: resumptions are shared closures, and nqueens
  resumes 12 times "sharing all continuations".
- **Stack.** JS runs with a 100 MB stack and no trampoline (§5.7).
- **Fit.** Its two transferable ideas are bind-inlining and tail-resumptive
  clauses in place. Both apply on top of A. Lazy resumption is a cheap
  dynamic relative of "in place" that needs no syntactic check.

### 6.4 One-shot designs (OCaml 5, WasmFX, JSPI, generators, Kotlin)

**OCaml 5.**
([Sivaramakrishnan et al., PLDI 2021](https://kcsrk.info/papers/retro-concurrency_pldi_21.pdf))

- **Mechanism.** Fibers on small heap stacks. Perform, resume and switch
  take 5 to 23 ns each (§6.3), with a mean 1% overhead on code without
  effects.
- **Multi-shot.** "Our continuations are one-shot" (§3). Cloning was
  removed, with "no immediate plans to bring the feature back"
  ([KC Sivaramakrishnan, Jan 2022](https://discuss.ocaml.org/t/multi-shot-continuations-gone-forever/9072)).

**WebAssembly stack switching (WasmFX).**
([explainer](https://github.com/WebAssembly/stack-switching/blob/main/proposals/stack-switching/Explainer.md);
[proposals](https://github.com/WebAssembly/proposals))

- **Status.** Phase 3. Continuations are "single-shot (aka linear)".
- **Availability.** Behind a flag in Chrome, absent from Firefox and
  Safari ([features.json](https://webassembly.org/features/)).
- **JSPI.** Standardised (phase 5) and shipping, but it suspends only to a
  JS promise, and wasm_of_ocaml reports effects are "slower" with it
  ([effects.mld](https://github.com/ocsigen/js_of_ocaml/blob/master/manual/effects.mld)).
- **Fit for the playground.** Stitchwort's wasm build runs an interpreter
  whose frames are already on the heap. Stack switching would switch an
  almost empty wasm stack, so it offers nothing unless the runtime
  recursed in Rust **[inferred]**.

**JS generators.**

- **Multi-shot.** One-shot. Multi-shot is possible only by replaying from
  the start
  ([effects.js](https://github.com/nythrox/effects.js/blob/master/src/utils.js)),
  which costs O(n) per step.
- **Measured (§7).** `yield*`-nested recursion overflows at 4,000 elements
  and is about 100x slower than A at 1,000.

**Kotlin coroutines.**
([KEEP](https://github.com/Kotlin/KEEP/blob/master/proposals/coroutines.md))

- **Mechanism.** State machines with heap frames.
- **Multi-shot.** "Resuming the same continuation more than once is not
  allowed". Multi-shot would need cloning the state.

**Fit for Stitchwort.** All of these are rejected because `Each` needs
multi-shot. This confirms the note's design D.

### 6.5 Lean 4 and Idris 2 (for completeness)

**Lean 4.**

- **Mechanism.** No algebraic effects. Monads are ordinary functions
  (`EStateM ε σ α := σ → Result ε σ α`), with overhead removed by
  specialisation
  ([Specialize.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Compiler/LCNF/Specialize.lean)).
- **Stack safety.** I found no primary note on stack safety
  **[unverified]**.

**Idris 2.**

- **Mechanism.** `Control.App` is world-passing, not a free monad.
- **JS backend.** It trampolines mutually tail-recursive top-level groups
  ([TailRec.idr](https://github.com/idris-lang/Idris2/blob/main/src/Compiler/ES/TailRec.idr)).
  It has had stack-overflow issues for non-tail recursion
  ([#447](https://github.com/idris-lang/Idris2/issues/447)).

**Fit for Stitchwort.** Neither offers a design for multi-shot handlers.

## 7. New measurements: run loop vs fast path vs CPS vs generators

`bench/effect-runtime/strategies.mjs` hand-writes the same programs for
five runtimes:

- `tree`: today's runtime.
- `loop`: A with lazy `k`.
- `fast`: `loop` plus a `bind` fast path that calls `k` directly while a
  depth counter is below 500, as in js_of_ocaml and cats-effect.
- `cps`: selective CPS with a trampoline every 100 nested continuation
  calls, handlers as CPS computations, and CPS clause bodies (Effekt's and
  Links' shape).
- `gen`: generators.

The programs use JS numbers rather than `BigInt`, and handlers are written
in each strategy's best form. The state handler is a loop in every
strategy, so that only the bind and operation machinery is compared. All
strategies agree on small inputs. Times are in ms, median of 3, from two
separate invocations **[measured]**:

| program | n | tree | loop | fast | cps | gen |
|---|---|---|---|---|---|---|
| state | 1,000 | 9.4 / 10.8 | 0.1 | 0.1 | 0.1 | 13.8 / 14.0 |
| state | 4,000 | 147 / 145 | 0.3 | 0.3 | 0.4 | overflow |
| state | 1,024,000 | overflow | 320 / 322 | 308 / 272 | 328 / 392 | |
| check (no ops) | 1,024,000 | overflow | 220 / 277 | 248 / 282 | 356 / 232 | overflow at 4,000 |
| ioFail (op forwarded through Fail) | 1,024,000 | overflow | 434 / 362 | 397 / 370 | 725 / 447 | overflow at 4,000 |
| search (n forks on one path) | 1,024,000 | overflow at 4,000 | 1,269 / 1,179 | 1,356 / 1,122 | 2,120 / 2,192 | n/a |
| choices (2^n results) | 16 | 143 / 78 | 77 / 64 | 91 / 65 | 82 / 60 | n/a |

What I read from this:

- **CPS is not faster than the run loop.** It is within noise on most
  programs and about 2x slower on `search`. CPS's advantage (resuming
  without returning to a loop) doesn't show at these sizes.
- **Generators are out.** `yield*` delegation is O(depth) per resumption:
  14 ms against 0.1 ms at 1,000. It nests JS frames, and it can't do
  multi-shot.
- **The fast path barely helps `mapIn`.** The recursive call's result is a
  node, not `Done`, once the depth limit is hit, so most binds build nodes
  anyway. It would help code made mostly of short `Done`-path binds (a
  loop over a pure-ish effectful step) **[inferred]**. Natively it is free
  and should be kept (§5.5b).
- **Multi-shot costs no more than single-shot.** `choices` is as fast in
  every linear strategy, and faster than `tree`.

Limits of this benchmark: these are models, not the compiler's output; one
machine; GC noise as in §5.4.

## 8. Recommendation

Adopt design A, as the note recommends, with these changes:

1. **Lazy resumption** (§5.2) in both backends, in 4a and 4b, not as an
   optimisation. `k` returns a node; the loop that runs the handler's
   result resumes it. This makes every handler whose enclosing row is not
   empty stack-safe in JS, and tail-resumptive handlers safe at any row.
2. **A′, narrowed:** parameterised handlers at the empty row (state). This
   is the one common shape lazy resumption doesn't cover.
3. **Native fast path:** natively, `bind (Done x) k` stays a direct call.
   Build a `Bind` node only for a computation that isn't finished.
4. **`IO` routing proportional to handlers, not frames** (§5.5a). Either
   keep the `Comp` pending list separate from the `Delay` frames, or index
   the `Map` and `Tie` frames.
5. **Decide the empty-row non-tail case** (§5.3, Q2). My suggestion: accept
   and document it as a JS stack limit like `foldRight`, and give `Each`
   and writer-style handlers stack-safe idioms, unless the reviewer sees a
   cheaper general fix.
6. **Reduce allocation** after correctness (§5.4). Measure fewer binds per
   `mapIn` element and smaller nodes, judged by GC time, not wall time
   alone.
7. **Broader acceptance** for 4a and 4b. Each item runs on Node's default
   stack and natively, and as a playground (wasm) test at 100,000:
   - every export of `map.sw` and `shapes.sw` at 1,000,000 elements,
     except the empty-row `emitted` and `searched` if Q2 accepts the limit,
     which then get a test that they fail with the documented resource
     error rather than crash;
   - linear growth: median of 5 runs, each doubling at most 2.3x, from
     125,000 to 1,000,000;
   - peak heap at most 3x plain `map`'s at 1,000,000;
   - native `fail` (`checked`) within 1.2x of today;
   - `plain` and `pureMapIn` within 10% of today;
   - a differential generator over nested handlers of all shapes in
     §5.1, including `IO` and `Partial` forwarding inside `main`.

The note's alternatives B (CPS) and C (Koka) stay rejected, for its reasons
plus §7's measurements. D (one-shot fibers or stack switching) stays
rejected.

**Does this differ from the note?** In the core data structure, no. In what
it claims and requires, yes:

- lazy resumption is new;
- A′ shrinks;
- the native fast path and frame-free routing are new requirements;
- the residual limitation is stated and put to a decision instead of
  hidden;
- the acceptance criteria cover handler shapes, memory, native speed and
  wasm.

## 9. Questions for the external reviewer

1. **Lazy resumption.** Is it sound to make a deep handler's `k` return a
   suspended computation? The argument is in §1.3 and §5.2: every runtime
   `foldComp` comes from `handle`, whose result type is a computation of
   the enclosing row, and programs cannot call `foldComp` at run time.
   Is there a case where the extra laziness changes observable behaviour,
   or retains memory badly?
2. **The empty-row non-tail case.** Should it be (a) accepted as a stack
   limit, like pure `foldRight`; (b) fixed by elaborating empty-row clauses
   in computation mode, which changes `k`'s type and breaks
   `Each.collect`'s lemmas; or (c) fixed by a general deep-stack mechanism
   in JS (Stopify-style instrumentation, or exports on a big-stack worker)?
   Is there a fourth option?
3. **The persistent list and GC.** It is an immutable cons list of
   continuations, shared between resumptions. Is there a representation
   with less GC pressure that keeps multi-shot sharing? Candidates: chunked
   immutable segments; a mutable array with a "captured" bit that copies
   on the second resumption, like Effekt's LLVM backend copying shared
   stacks ([Muhcu et al., ICFP 2025](https://se.cs.uni-tuebingen.de/publications/muhcu2025multiple.pdf)).
   Note that copy-on-capture of the whole stack would bring back O(depth)
   per operation.
4. **The native runner.** Is keeping `Comp`'s pending list apart from the
   partial machine's `Delay` frames the right split? Or should both be one
   continuation of alternating segments, as in Links' generalised
   continuations and Effekt's meta-stack?
5. **Recognising A′.** Recognise parameterised handlers in the elaborator
   (no syntax change, hashes of those handlers change), or add handler
   parameters to the surface syntax, as Links has?
6. **Acceptance.** Are §8.7's criteria enough to catch the failures in
   §5? What would you add? For example: handlers nested 10 deep, or
   `translate` inside recursion.
7. **The alternatives.** Do you see a reason to prefer selective CPS (B),
   given §7 and that `k` is a plain function in Stitchwort's types? Or a
   reason to take Koka's evidence passing for forwarding-heavy programs
   now rather than later?

## Appendix A. Files and how to rerun

In `bench/effect-runtime/`. Files the note had: `map.sw`, `run.sh`,
`export.mjs`, `prototype.mjs` and `agree.mjs`. Added for this review:

- `shapes.sw`: the handler shapes of §5.1.
- `shapes.mjs`: times them and checks that modules agree.
- `prototype.mjs --lazy-resume`: lazy resumption.
- `once.mjs`: one call, for `--trace-gc`.
- `strategies.mjs`: the §7 models.
- `run.sh`: `FILE=` times another file.

```
stitchwort build --js bench/effect-runtime/map.sw -o OUT
node bench/effect-runtime/prototype.mjs OUT/map.js OUT/map-lazy-param.js --lazy-resume --parameter
node bench/effect-runtime/agree.mjs OUT/map.js OUT/map-lazy-param.js
node bench/effect-runtime/export.mjs OUT/map-lazy-param.js

stitchwort build --js bench/effect-runtime/shapes.sw -o OUT
node bench/effect-runtime/prototype.mjs OUT/shapes.js OUT/shapes-loop.js
node bench/effect-runtime/prototype.mjs OUT/shapes.js OUT/shapes-lazy.js --lazy-resume
node bench/effect-runtime/shapes.mjs OUT/shapes.js OUT/shapes-loop.js OUT/shapes-lazy.js

node --trace-gc bench/effect-runtime/once.mjs OUT/map-lazy-param.js checked 1024000
FILE=bench/effect-runtime/shapes.sw bench/effect-runtime/run.sh native emitted 4000 8000
node bench/effect-runtime/strategies.mjs
```
