# Proposal: a checked `@[tailrec]` attribute

**Status:** draft 1, 4 November 2026. Ticket SW-1213, from D2308 (Matt: "do a
bit of a design note and see if this is worth adding"). Nothing is built.
Written against commit `12f25310`. Decisions D2310 to D2315 are at the end.

Claims about Stitchwort's code are **[checked]** (read in the source at that
commit). Timings are **[measured]** (run while writing this, described in §1.4) or
**[estimated]**. Claims about other languages are **[cited]** (read in the
source named in §5 while writing) or **[unverified]** (from memory).

## 0. Summary

The programmer writes `@[tailrec]` before a definition. The compiler then
checks that every recursive call in it is in tail position (the call's result
is the definition's result, with nothing left to do afterwards). If one isn't,
the program is rejected with `E-TAILREC`. The error names the call and what
uses its result (`+`, an argument of `Nat.max`, a `let`, a `handle`, a
lambda).

**What the backends do today** (§1):

- **`stitchwort run` (the machine, `crates/rt`) and `--native`
  (`crates/native`)** already run *every* call in tail position without a new
  frame, to any function. So the attribute changes nothing they generate. It
  only tells the programmer that the function is a loop.
- **JavaScript** doesn't eliminate tail calls. The backend turns a
  definition's tail calls *to itself* into a `for (;;)` loop. That includes
  calls through `if`, `if h:`, the case tree, lifted `match`es, `let`s, a
  `decreasing` definition's `%step`, and pairs of mutually recursive
  functions. Everything else uses a JS frame per call, and runs out at a few
  thousand frames.
- **The speed-up is real, but its size depends on the backend**
  ([measured], §1.4, per list element):

  | backend | tail-recursive | not tail-recursive | ratio |
  |---|---:|---:|---:|
  | run (machine) | 57–63 ns | 66–71 ns | 1.1–1.2× |
  | `--native` | 3.8–5.6 ns | 15–24 ns (10,000 deep), 17–71 ns (1,000,000 deep) | 3.4–14× |
  | JavaScript (Node) | 5 ns | 14 ns | 2.8×, and overflows at 6,000–8,000 deep |

**Recommendation: add it, small.** It's a checker on the elaborated term,
next to the termination checker. It has one new error code, and the JS
backend asserts that every `@[tailrec]` definition did compile to a loop.
That is about one lane (**[estimated]** half a day to a day), plus a small one
if local definitions are to take attributes. The promise holds on every
backend from the first version, because JavaScript already loops every form
the checker would accept (§3), and the assertion keeps it so.

## 1. What each backend does with tail calls today

### 1.1 The machine (`stitchwort run`, `stitchwort test`)

`crates/rt` compiles the IR to bytecode (`code.rs`). `Gen::expr` takes a
`tail` flag. It passes the flag through `let` bodies (`Expr::Let` compiles the
value with `false` and the body with the caller's flag), both branches of
`If`, and each arm of a `Switch` **[checked]**. In tail position, a call of a
global is `Instr::TailCall`, an application of a function value is
`TailApply`, and an effect-runtime native is `TailPrim` (`code.rs:651–683`)
**[checked]**.

`TailCall` moves the arguments to `scratch` and calls `State::replace`, which
reuses the frame (`machine.rs:1076–1083`) **[checked]**. So *every* call in
tail position, whether to itself, to another function, or to a closure, runs
in constant frames. This is general tail-call elimination, not only for
self-calls.

Non-tail recursion keeps its frames on the heap (`Vec<Frame>`), up to
`Limits::frames`. The default is the reference evaluator's 2,000,000
(`crates/core/src/budget.rs:104`) **[checked]**. Past that, the result is
`E-RESOURCE` ("it recursed more deeply than allowed"). A non-tail max over a
3,000,000-element list stopped there, and the tail-recursive one finished
**[measured]**.

On top of this, `trmc.rs` runs calls *modulo a constructor* (`Cons (f x)
(map xs f)`) in destination-passing style, with no frame per element
(docs/core.md, "Tail calls as loops") **[checked]**.

`stitchwort test` uses the same machine, falling back to the reference
evaluator (`crates/driver/src/driver.rs:1186`, `Runner::Machine`)
**[checked]**.

### 1.2 Native code (`stitchwort run --native`, `build --native`)

N1 translates the machine's bytecode instruction by instruction with
Cranelift, in Cranelift's `tail` calling convention. "a self tail call is a
jump back to the top, any other tail call a `return_call`", and "A
`TailApply` is a `return_call` … so tail applies run in constant stack"
(`crates/native/src/n1.rs:37–62`) **[checked]**. Native code counts frames
exactly as the machine does (D1253), so non-tail recursion stops at the same
2,000,000 frames **[checked; measured at 3,000,000]**. It runs on a large
thread stack, and measured 1,000,000 deep without trouble **[measured]**.

Where native code shows the difference is speed (§1.4). A loop is a jump. A
non-tail call is a real call and return, plus the bookkeeping, plus a frame
on the machine stack. At 1,000,000 deep that stack is large and cold.

### 1.3 JavaScript (`stitchwort build --js`)

JS engines don't eliminate tail calls (docs/core.md, "Tail calls as loops").
`Gen::self_tail_loop` (`crates/js/src/lib.rs:2641`) compiles a definition
whose body reaches a call to *itself* in tail position as `{ let s0 = v0, …;
for (;;) { const v0 = s0, …; … s0 = next; continue; … } }`. It reaches
through:

- the case tree;
- `let`s;
- both branches of `if` (`Bool.ifThenElse c (_ => a) (_ => b)`) and of
  `if h:` (`Decidable.elim d (h => a) (h => b)`);
- lifted `match`es (`f.%match1`), and the other member of a group that calls
  the definition directly (`isEven`/`isOdd`), both inlined;
- a `decreasing` definition's `%step`, inlined with `%rec` standing for the
  function;
- helpers whose `if` branches hold the call's result (`Show.escapeChars`).

All of this is **[checked]** in the code and docs/core.md.

It also goes beyond tail calls. A call in a constructor's field becomes a
loop building a chain of cells (modulo constructor), and so does `x + f xs`
on `Nat` (modulo addition, with an accumulator `a$ += …`). It tries the most
ambitious form first and falls back to less, the last fallback being plain
direct tail calls (`for (cons, add, inline) in [...]`, `lib.rs:2659`)
**[checked]**.

Still a frame per call (docs/core.md):

- non-tail recursion (`Nat.max x (f xs)`);
- tail calls through a function that isn't inlined (`Option.flatMap`'s
  argument);
- cycles of three or more members that don't call each other directly.

Running out is `StitchwortResourceError`.

I looked at the generated code for the benchmarks **[checked]**:

- the tail-recursive sum's `go` is a `for (;;)` loop;
- the *non-tail* sum `x + total xs` is a loop too (modulo addition: `a$ +=
  v1`);
- the non-tail `Nat.max x (total xs)` is a plain recursive arrow function.

**Effects.** Effectful code is run by the effect runtime's loop, with
pending continuations on a heap list (effect-runtime.md, stage 4a, D1162).
So effectful recursion, tail or not, doesn't grow the JS stack. A non-tail
effectful recursion grows the *heap* instead: it holds one pending
continuation per level **[measured, §1.4]**.

### 1.4 Timings

**Setup.** The main checkout's release binary (built 4 Nov 2026 12:39, with
`native`), and Node 22.23.3 from `nix develop`. Each program is a function
over `List.range n`, summed or maxed, repeated `r` times, so 50,000,000
elements in each run. The sources are below.

**These timings are noisy.** The machine was shared: the load average was
54 to 96 on 10 cores, with other lanes compiling. So wall-clock times were
2–4× CPU times. The machine and native figures are **user CPU time** of the
whole process, minus a run with `r = 0` (start-up, checking and building the
list: 0.15 s for 10,000 elements, 0.23–0.31 s for 1,000,000). The JS figures
are `performance.now()` around the exported call, so Node's start-up is
excluded. Two or three runs each.

```
def go: List Nat → Nat → Nat          -- tail                 def total: List Nat → Nat    -- not tail
  | Nil, acc => acc                                             | Nil => 0
  | Cons x xs, acc => go xs (acc + x)                           | Cons x xs => x + total xs
```

The "max" variants are the same, with `Nat.max acc x` and `Nat.max x (total
xs)`.

**Machine (`stitchwort run`), user CPU s for 50M elements** **[measured]**:

| program | 10,000 deep × 5,000 | 1,000,000 deep × 50 |
|---|---|---|
| sum, tail | 3.05, 3.01, 3.21 | 3.26, 3.16, 3.14 |
| sum, not tail | 3.43, 3.63, 3.61 | 3.69, 3.68, 3.66 |
| max, tail | 3.28, 3.37 | 3.38, 3.39 |
| max, not tail | 3.70, 3.70 | 3.81, 3.62 |

That is about 57–63 ns an element as a loop, against 66–71 ns. A frame push
and pop costs the machine little next to its per-instruction cost.

**Native (`--native`), user CPU s** **[measured]**:

| program | 10,000 deep × 5,000 | 1,000,000 deep × 50 |
|---|---|---|
| sum, tail | 0.43, 0.44, 0.43 | 0.48, 0.48, 0.49 |
| sum, not tail | 1.34, 1.36 | 3.78, 3.76, 3.74 |
| max, tail | 0.37, 0.37 | 0.42, 0.42 |
| max, not tail | 0.90, 0.90 | 1.08, 1.06 |

That is 3.8–5.6 ns an element as a loop, against 15–24 ns at 10,000 deep and
17–71 ns at 1,000,000 deep. This is where the performance argument is
strongest.

The non-tail *sum* at 1,000,000 deep is much slower than the non-tail *max*
(71 against 17 ns). I haven't found out why. It may be `Nat.add`'s results
held across a deep, cold stack.

**JavaScript, ms inside `bench`** **[measured]**:

| program | size | runs |
|---|---|---|
| sum, tail | 10,000 × 5,000 | 1227, 1148, 1717 |
| sum, not tail (a loop, modulo addition) | 10,000 × 5,000 | 1107, 1202, 1378 |
| sum, tail | 1,000,000 × 50 | 2000, 1712, 1540 |
| sum, not tail (a loop) | 1,000,000 × 50 | 1384, 1403, 1760 |
| max, tail | 2,000 × 25,000 | 244, 259, 254 |
| max, not tail | 2,000 × 25,000 | 688, 720, 807 |
| max, not tail | 8,000 × 1 and up | `StitchwortResourceError` (Maximum call stack size exceeded) |

The non-tail max worked at 6,000 elements and overflowed at 8,000 on Node's
default stack. The tail version ran at 1,000,000 elements.

**Effectful recursion**, 1,000,000 operations under a state handler (`bump()`
then the recursive call, against `bump()`, `let r := prog n`, `r + 1`)
**[measured]**:

| | tail | not tail |
|---|---|---|
| run | 0.82 s user, 63 MB peak | 1.00 s, 200 MB |
| `--native` | 0.67 s, 66 MB | 0.80 s, 203 MB |
| JS | 204–349 ms, 46 MB | 557–573 ms, 231 MB |

Both are stack-safe everywhere. The non-tail one costs memory, about 140–185
bytes per pending level.

### 1.5 The reference evaluator and the kernel

The reference evaluator (`crates/core/src/step.rs`) is a loop over states
with an explicit stack of pending work, and "a call in tail position pushes
nothing" (docs/evaluator-speed.md §1) **[checked]**. Its frame limit is the
same 2,000,000. The kernel's own evaluation during type checking (`rfl`,
conversion) is not affected by this proposal. `@[tailrec]` changes no term
and no proof.

## 2. What counts as a tail call

A **recursive call** is a call of the definition itself, of a `match` lifted
out of it (`f.%match1`, which is part of the definition as written), or, in a
`decreasing` definition, of `%rec` inside `f.%step`. A call is in **tail
position** if its result is the definition's result as it stands, with
nothing left to do in this call. Each construct, in the terms the elaborator
produces (§4):

| Construct | Tail position reaches… | Not tail |
|---|---|---|
| Case tree (patterns of the arms) | every arm's right side | — |
| `if c then a else b` (`Bool.ifThenElse`) | both `a` and `b` | the condition `c` |
| `if h: c then a else b` (`Decidable.elim`) | both branches | the decision |
| `a && b`, `a \|\| b` on `Bool` (`if a then b else False`) | `b` | `a` |
| `match e with …`, part of the case tree | every alternative | the scrutinee |
| `match` lifted (`f.%match1 …`) in tail position | its alternatives (checked as part of `f`) | a lifted `match` itself in a non-tail position: every call in it is non-tail |
| `let x := v; body` | `body` | `v` (the result is used by the body) |
| `let x := f n; x` | — | the call: its result is bound and then returned. Write `f n` |
| Local definitions (`def go …` in a block) | the block's last expression, for the owner | a call of the *owner* inside `go`'s body is inside another function (see "lambda") |
| Application `g a b` | — | each argument, including `+`, `*`, `++` and other operators, which are calls |
| `x \|> g a`, `x.g a` | the same as `g x a`: a call of `f` written this way is tail if `g` is `f` | `x` and `a` |
| Constructor `C a b` | — | each field (`Cons x (map xs f)`), see D2311 |
| Lambda `x => …` | — | its body: it runs when something calls it, not as part of this call. So `xs.map (x => f x)` and passing `f` itself unapplied are not tail calls |
| `decreasing` | `%step`'s body, with `%rec y c` standing for `f y c` | as for any other body |
| Effectful sequencing `a; b` and `let x := a; b` (`Effect.bind a (x => b)`) | `b` | `a`: the rest of the block waits for it |
| An operation `op x` | — | (not a recursive call) |
| `handle e with …` | — | `e`, and the clauses: the handler is a fold that waits for `e`'s result, so a recursive call under it adds a handler per level |
| Mutual groups (`isEven`/`isOdd`) | see D2312 | |

**Effects in more detail.** An effectful body is a chain of `bind`s.
`bump(); loop n` is `bind (bump ()) (_ => loop n)`, and the call is the
continuation's whole result. On every backend that means the run loop takes
the computation `loop n` returns, with nothing pending (measured as constant
memory in §1.4). `let r := prog n; r + 1` is `bind (prog n) (r => Done (r +
1))`. The call is the computation being bound, so a continuation is pending
for each level. That is not tail position.

So the rule is the same as for pure code: the call must be the last thing
done. The cost of breaking it is heap, not stack. It's still worth the
attribute's guarantee, because a long effectful loop (a server, a game loop,
reading a file line by line) is exactly where the programmer wants it.

**Under a handler.** For `def run (n: Nat): Nat := handle (… run (n - 1) …)
with h`, each level installs a handler around the inner call, which the
outer one must fold over. So a recursive call anywhere inside `handle … with`
is not in tail position. A tail call *inside* the handled computation to a
function that is itself running under that handler (the `loop` above,
handled once by `countBumps`) is fine: the handler is outside the recursion.

## 3. The promise

> If `f` is marked `@[tailrec]` and checks, then running `f` uses a bounded
> number of frames, whatever its arguments: each recursive call is a turn of
> a loop. On `stitchwort run` and `--native` that is a reused frame, and in
> JavaScript a `for (;;)` loop. In effectful code, the run loop has no
> continuation pending per level.

**Must it hold on every backend?** Yes, and it can at once:

- the machine and native code already eliminate every tail call (§1.1, §1.2);
- the JS backend already makes a loop of every form §2 accepts in the first
  version: self-calls through the case tree, `if`, `if h:`, `let`, lifted
  `match`es and `decreasing`'s `%step`, plus continuations of `bind` (§1.3);
- what JS doesn't loop (three-member cycles, calls through a non-inlined
  higher-order function) the checker refuses anyway, or D2312 leaves out.

The weak point is that JS's loop builder is a cascade of heuristics
(`self_tail_loop`'s six tries). So the recommendation is that **the attribute
also binds the JS backend**. For a `@[tailrec]` definition, if no try
produces a loop, extraction fails with an internal error that names the
definition ("this is a bug in the compiler"). It must never quietly fall back
to a recursive function. A test runs each `@[tailrec]` example at 1,000,000
iterations on Node's default stack.

The weaker promise ("checked tail position; whether it's a loop depends on
the backend") would be easier, but it's the wrong one. In JS, it is exactly
where the stack is 6,000–8,000 frames deep that the programmer needs the
attribute to mean something.

**What it doesn't change:** the term, the kernel's checking, proofs,
equation lemmas and hashes. Like `noReceiver`, the attribute is a
definition-level flag in an elaborator side table, read by the checker and
the JS backend. It isn't part of the content hash (attributes.md §4.4, D598).
Adding it to a definition reruns no test.

## 4. The checker

**Where.** In the elaborator, as a pass after the definition's group has
been admitted, on the elaborated core terms: the owner's body, its lifted
`match`es, and for `decreasing` its `%step`, the body the runtimes run
(`Def::run_body`). Doing it then has two advantages:

- *It sees what the backends see*: `if` is already `Bool.ifThenElse` with
  lambdas, `&&` is already an `if`, `|>` and dot calls are already
  applications, and sequencing is already `bind`.
- *Core terms carry spans*: `Term::Loc(span, …)` (`crates/core/src/term.rs:217`)
  **[checked]**. The termination checker already walks a group's bodies with
  them, labels each recursive call, and treats lifted members as inlined
  (`crates/core/src/termination.rs:154–220`) **[checked]**.

The new walker has the same shape with one extra flag, "in tail position".
It goes in `crates/elab` (a new `tailrec.rs`), not the kernel: it is a
promise about running, not soundness. It knows a short list of library heads
whose lambda arguments are branches: `Bool.ifThenElse`, `Decidable.elim`,
`Effect.bind`'s continuation, and the row coercions the elaborator inserts
around effectful calls, if any turn up.

It runs on the term **before erasure**. Erasure removes only arguments, never
a call's position, so the answer is the same.

**What it rejects** (`E-TAILREC`, one label per offending call, all of them
in one error):

```
[E-TAILREC] Error: `total` is marked @[tailrec], but a recursive call isn't in tail position
   ╭─[ sum.sw:4:18 ]
 4 │   | Cons x xs => x + total xs
   │                     ────┬───
   │                         ╰── its result is added to (`+`) after it returns, so each call keeps a frame
   │ Note: carry the result along instead: `def go: List Nat → Nat → Nat | Nil, acc => acc | Cons x xs, acc => go xs (acc + x)`
```

The labels, by what holds the call:

- an argument: "its result is passed to `Nat.max` after it returns";
- an operator: "its result is added to (`+`) after it returns", and so on,
  using the operator as written;
- a `let`: "its result is bound to `r`, and the block goes on (line 7)", or,
  for `let x := f n; x`, "its result is bound and then returned: write the
  call itself as the result";
- a constructor: "its result goes into a field of `Cons`, which is built
  after it returns". With D2311's recommendation, a note adds "`stitchwort
  run` and JavaScript already build such lists without a frame per element,
  but `@[tailrec]` promises only tail calls";
- a scrutinee or condition: "its result is matched on", or "decides the
  `if`";
- a lambda: "it's inside a function (`x => …`) passed to `List.map`: it runs
  when `List.map` calls it, not as a turn of the loop", or "`total` is
  passed to `List.map` as a function";
- effects: "the block goes on after it: `IO.print "done"` (line 9)";
- a handler: "it's inside `handle … with` (line 5): the handler waits for
  its result, so each call adds a handler";
- a lifted `match` that isn't in tail position: "it's in a `match` whose
  result is used by `+` (line 6)".

Also an error:

- **`@[tailrec]` on a definition with no recursive call.** "`f` is marked
  @[tailrec] but never calls itself." Scala does the same **[unverified]**.
  It catches an attribute left behind when the recursion moved into a helper.
- **On a theorem, instance, synonym, test or `{Partial}` definition** in the
  first version: `E-ATTRIBUTE`, the existing error for a misplaced attribute.
  Partial recursion is run by its own machine, which already loops tail
  requests (partial.md §7.4.4), but its terms are a different shape. Leave
  it until someone needs it.
- **A call to another named member of a mutual group**, unless D2312 says
  otherwise: "calls between mutually recursive definitions aren't covered by
  @[tailrec] yet".

**Placement.** `@[tailrec]` goes on `def`s and on `export def`s. It is
registered in `crates/elab/src/attributes.rs`'s `REGISTRY`, as `noReceiver`
is. Bare names are reserved for language-level attributes there **[checked]**.
On a local definition (the usual home of a `go` with an accumulator), the
parser doesn't keep attributes today (docs/syntax.md, "Attributes":
`E-ATTRIBUTE` on "a local definition"). That's D2314.

**Editor hint, later.** The same walker, run on every recursive definition in
report mode, can tell the language server which recursive calls are turns of
a loop and which keep a frame. That could be a hover line on the definition
("runs as a loop" / "a frame per call: line 4, under `+`") or an inlay after
the call. It's useful without the attribute: it shows the cost of writing `x
+ total xs` at the moment of writing it. Not an error, not a warning, nothing
on the command line. D2315.

## 5. Prior art

- **Scala `@tailrec`.** "A method annotation which verifies that the method
  will be compiled with tail call optimization", and "the compiler will issue
  an error if the method cannot be optimized into a loop" (Scala API docs,
  `scala.annotation.tailrec`) **[cited]**. Only self-calls. Scala optimises
  self tail calls with or without the annotation, so the annotation is purely
  a check **[unverified]**. This is the model for this proposal.
- **Kotlin `tailrec`** is a modifier that *enables* the transformation: "When
  a function is marked with the `tailrec` modifier and meets the required
  formal conditions, the compiler optimizes out the recursion, leaving behind
  a fast and efficient loop". It applies "only when it calls itself as its
  final operation", and not inside `try`/`catch`/`finally` or on `open`
  functions (kotlinlang.org, Functions, "Tail recursive functions")
  **[cited]**. A non-tail call under `tailrec` is a warning, not an error
  **[unverified]**. Without the modifier, nothing is optimised.
- **Clojure `recur`** is a special form, not a check on ordinary calls:
  "`recur` in other than a tail position is an error", "its use in
  tail-position is verified by the compiler", and "There is no tail-call
  optimization and the use of self-calls for looping of unknown bounds is
  discouraged" (clojure.org, Special Forms) **[cited]**. Mutual recursion
  uses `trampoline` **[unverified]**.
- **OCaml `[@tailcall]`** goes on a *call*, not a function. It "can be
  applied to function application in order to check that the call is
  tailcall optimized". A violation is warning 51, `wrong-tailcall-expectation`
  (OCaml manual, Attributes) **[cited]**. OCaml eliminates all tail calls
  anyway. `[@tail_mod_cons]` is a separate opt-in transformation, the one
  `trmc.rs` cites **[checked in trmc.rs]**.
- **Rust `become`.** RFC 3407, "Explicit Tail Calls", still open: "a
  guarantee that function calls are tail-call eliminated via the `become`
  keyword. If this guarantee can not be provided an error is generated
  instead" (rust-lang/rfcs#3407; tracking issue rust-lang/rust#112788, open)
  **[cited]**. A per-call keyword with a guarantee, not a function-level
  attribute.
- **Lean 4** compiles recursive tail calls to gotos and doesn't eliminate
  tail calls to a different function (native-compilation.md §2.1, citing
  *Functional Programming in Lean*) **[cited there]**. There's no checking
  attribute. `partial_fixpoint` needs tail recursion for its reasoning, a
  different purpose (partial.md) **[cited there]**.
- **Idris 2** has no such attribute that I know of **[unverified]**.

So there are two families. A check on the function (Scala, Kotlin) suits a
language where tail calls are only sometimes loops, which is Stitchwort's
position because of JavaScript. A check on the call (OCaml, Rust, Clojure)
suits languages where any tail call can be eliminated. A function-level
attribute is simpler to write and to explain, and fits the existing `@[…]`
syntax. Per-call `[@tailcall]` adds little where every tail call is already
eliminated on two backends out of three.

## 6. Cost, risks, and whether it's worth it

**Cost** **[estimated]**:

- The registry entry, placement, and the side table read by JS: about an
  hour; `noReceiver` is the template.
- The checker (`tailrec.rs`): the walker, the list of branch-heads, labels
  for each case in §4, and the "no recursive call" error. About 300–500
  lines with messages, and 3–4 hours.
- The JS assertion: a flag on `self_tail_loop`'s result. About 1 hour.
- Examples, one per row of §2 (accept and reject, with `-- expect-error:`
  files and their messages); docs/syntax.md's attribute table and a
  paragraph; docs/core.md's error table. About 2 hours.
- Local definitions (D2314): the parser keeps attributes on a block's
  `def`, and `lift.rs` carries them to the lifted definition. About 1–2 hours.

In all, one Sonnet lane (it's near the elaborator, and the wording matters),
about half a day to a day; Opus review isn't needed (no kernel terms).

**Risks:**

- *Elaborator-inserted wrappers.* Row coercions or `liftIn`/`widenIn`
  around an effectful recursive call would make a call that looks like a tail
  call not one, with a confusing error. This needs checking on the effects
  examples early. The fix is either to treat the coercion as transparent if
  the backends do, or to say so in the label.
- *JS heuristics regressing.* The JS backend's loop builder has failed
  quietly before (SW-40's list of things that are "still a frame per call").
  The assertion turns that into a loud failure on exactly the definitions
  that promise a loop. That's a benefit as much as a risk.
- *Two notions of "tail position" drifting.* The checker's (`tailrec.rs`)
  and each backend's. The mitigation is the JS assertion, plus a test that
  runs every `@[tailrec]` example deep on all three backends.
- *Expectations.* Someone may expect `@[tailrec]` to make a function fast on
  `stitchwort run`. There it gains 10–20% (§1.4). The docs should say what
  it promises (bounded frames) and where it is fast (native code, JS).

**Is it worth it?** Yes, as a small feature:

1. *It's cheap and self-contained*: no kernel change, no new runtime
   machinery, one error code.
2. *The benefit is measured where it matters*: 3–14× on native code, 2.8× on
   JavaScript, and on JavaScript the difference between working and
   `StitchwortResourceError` at under 10,000 elements.
3. *It pins down the standard library's loops.* `List.lengthOnto`,
   `foldLeft`, `Nat.digitsAcc` and the rest are loops today because a
   heuristic found them. With the attribute (and the JS assertion), a change
   that breaks one is an error, not a silent frame per element.
4. *It's a teaching aid* when written by the programmer, and with the editor
   hint, for code they didn't think about.

What it is *not* worth doing now: modulo-constructor promises,
mutual-group loops in JS, per-call attributes, partial definitions. Each is a
later stage if a real program needs it.

## 7. Decisions

- **D2310: add `@[tailrec]`?** *Problem:* there's no way to state that a
  function must run as a loop. A non-tail call slips in silently and costs a
  frame per call (3–14× slower natively, and a stack overflow under 10,000
  deep in JS). *Change:* a checked attribute on definitions and exports.
  `E-TAILREC` names each recursive call that isn't in tail position and what
  uses its result. A definition marked `@[tailrec]` with no recursive call is
  an error too. The JS backend fails loudly if it can't make a marked
  definition a loop. *Effect:* the promise of §3 on all three backends, with
  no change to terms, proofs or hashes. **[rec: yes]**
- **D2311: strict tail calls only, not "modulo a constructor" or "modulo
  `+`"?** *Problem:* `stitchwort run` and JS already run `Cons (f x) (map xs
  f)` without a frame per element, and JS also loops `x + total xs`, but
  neither is a tail call. *Change:* `@[tailrec]` accepts only real tail calls,
  as Scala's and Kotlin's do. The error for a call in a constructor's field
  says that this case is already cheap on some backends, but not promised.
  *Effect:* a simple rule that holds on every backend, including native code,
  which only gets constructors through `trmc.rs` and doesn't get addition.
  **[rec: yes; a separate `@[tailrec.cons]` later only if a program needs
  it]**
- **D2312: leave out mutual groups in the first version?** *Problem:* JS
  loops a pair of definitions that call each other directly, but not a
  cycle of three or more. *Change:* in the first version, `@[tailrec]` covers
  a definition's calls to itself, its lifted `match`es and `decreasing`'s
  `%step`. A call to another named member of its group is refused with "not
  covered by @[tailrec] yet". *Effect:* the promise holds without new JS work.
  A later stage could compile a whole marked group as one JS loop with a
  state switch. **[rec: yes, self-recursion only for now]**
- **D2313: in effectful code, the rule is the same as in pure code?**
  *Problem:* effectful recursion is already stack-safe everywhere, thanks to
  the run loop, so "tail" there is about memory (63 MB against 200 MB at
  1,000,000 operations). *Change:* a call is in tail position if it is the
  last thing in the block (the continuation's result). A call bound by `let`
  and used, followed by more statements, or inside `handle … with` is not.
  *Effect:* a long effectful loop is guaranteed constant memory. A handler
  inside the recursion is reported as such. **[rec: yes]**
- **D2314: allow `@[tailrec]` on local definitions?** *Problem:* the natural
  place for a tail-recursive helper is a local `def go` with an accumulator,
  and attributes aren't allowed there today. *Change:* the parser keeps
  attributes on a block's `def`, and lifting carries them to `f.go`. Only
  `tailrec` is allowed there; any other attribute is `E-ATTRIBUTE` as now.
  *Effect:* `@[tailrec] def go …` inside a definition works, in the same
  lane. **[rec: yes]**
- **D2315: an editor hint for every recursive call, later?** *Problem:* the
  cost of a non-tail call is invisible until it overflows. *Change:* after
  `@[tailrec]` lands, the language server uses the same walker to show, for
  each recursive definition, "runs as a loop" or "a frame per call (line 4,
  under `+`)", as a hover line or an inlay. Not a warning, nothing on the
  command line. *Effect:* the information without the attribute. **[rec:
  yes, as a backlog ticket after D2310's lane]**

## Appendix: reproducing the timings

The programs are in the session's scratchpad, not the repo. Each is:

```
import Std (IO, List, Nat)

<go/total as in §1.4>

def rep (xs: List Nat): Nat → Nat → Nat
  | Zero, acc => acc
  | Succ k, acc => rep xs k (acc + total xs)

export def bench (n: Nat) (r: Nat): Nat := rep (List.range n) r 0

def main(): {IO} () :=
  IO.print "${rep (List.range 10000) 5000 0}"
```

They were run with `/usr/bin/time -p stitchwort run [--native] file.sw`, and
for JS with `stitchwort build --js file.sw -o dir`, then a driver that imports
`bench` and times one call with `performance.now()`. The effectful pair used
`ability Counter where bump: () → {Counter} ()` and the state handler of
`examples/accept/mutual.sw`'s `countBumps`.
