# Making `Std.Parse` cheap at run time (SW-2327)

SW-2327, 8 Nov 2026, Opus, paper lane (no builds or runs). It builds on the
measured profile in [docs/reviews/SW-2296-native-profiles.md](../reviews/SW-2296-native-profiles.md)
and doesn't repeat it. Claims are marked **[read]** (seen in the code, with
file:line), **[measured]** (from SW-2296), **[inferred]** (worked out from
the code and the counts, not measured) or **[estimated]** (a guess at an
effect, with the reasoning).

## 0. Summary

**The problem, for a user.** A program that parses its input with
`Std.Parse` runs about 75 times slower than the same program in Lean. AoC
2020 day 18 (`expressions`) and 2024 day 3 (`scan`) take about 37 s each
natively against Lean's 0.5 s, and almost all of that time is parsing
**[measured]**. Anyone writing an AoC day the recommended way, with
`Parse.all` or `Parse.eachLine`, gets this.

**Why.** The time doesn't go into reading characters. It goes into the
machinery that runs `Parse` as an effect (§1):

1. **Every `let x := parser()` in parsing code makes a closure, a node, two
   run-loop steps and an indirect call**, because the parser below it
   performed an operation, so it returned a "computation still waiting"
   value instead of a result. That is where the 137 M closures and most of
   the 258 M effect steps of `expressions` come from.
2. **Every operation crosses every `optional`, `attempt` and `label` it is
   nested in**, and each of those handlers takes it, performs it again
   outwards, and resumes. `oneOf`, `many`, `sepBy` and `chainLeft` are all
   built on `optional`, so a parser nested a few combinators deep pays that
   several times per operation.
3. **Most of the calls this machinery makes go through native code's slow
   apply path**: resumptions, `DoneK` and `JumpK` are runtime function
   values, not compiled closures, so each goes through
   `sw_apply_prepare`, which collects its arguments into a heap `Vec`.
4. Beside the effects, **error bookkeeping runs on the success path**: a
   failed alternative formats its "expected 'mul('" text at once, even
   though nearly every such failure is backed out of and never shown.

**Recommendation.** Make tail-resumptive operations cheap for every effect,
not only `Parse`, in four stages. An operation whose handler only
answers it and carries on, which is every `Parse` operation except `stop`
and `fatal`, should run as a direct call where it is performed, with no
continuation built. That is Koka's design, which effect-runtime.md (D1162,
§9.1 item 8) left "later and measured". It is now measured. First come
two cheap stages that pay off on their own: fast paths for the runtime's
own function values (stage 1) and lazy error messages in `Std.Parse`
(stage 2). Then handlers that only pass an operation on are skipped
(stage 3). Then operations run in place, with a continuation closure made
only when something really suspends (stage 4, a design note first).
User code, `Std.Parse`'s API and every parser proof stay as they are; only
stage 2 changes `Std.Parse`'s private state (§3, D3401).

**What it should do** (all **[estimated]**, §2): stage 1 about 1.2–1.3×
on the parsing programs, stage 2 about 1.1–1.5× (most on `scan`), stage 3
about 1.2–1.5×, stage 4 about 3–6× on what is left. Together that takes
`expressions` and `scan` from about 37 s to roughly 3–6 s. Closing the rest
of the gap to Lean needs a different input representation (§2.6), which I
don't recommend now.

## 1. Where the three measured costs come from

### 1.1 How a parser runs today

`Parse` is an ability (`crates/elab/src/std/Parse/Parse.sw:48-65`). Its
runner `Parse.runFrom` is a handler whose clauses take the state and answer
each operation (`Parse.sw:128-148`). The elaborator turns direct-style code
into computations: `let x := p(); rest` becomes `bind (p()) (x => rest)`.
At run time a computation is `Done | Call | Bind`, run by a loop that keeps
the continuations waiting on a heap list (effect-runtime.md §9.1).

Natively:

- `bind c k` is inline: `sw_bind` looks at `c`. On `Done x` it calls `k x`
  directly; otherwise it builds the node `Bind c k` and returns it
  (`crates/native/src/n1.rs:3739-3790`, `crates/rt/src/native_abi.rs:2303-2325`)
  **[read]**. `k` is a closure, made *before* `bind` looks at `c`, so it is
  allocated whichever way `c` turns out **[read: `bind` takes `k` as an
  operand already built]**.
- An operation is `Call op DoneK`: a node whose continuation is the runtime
  value `DoneK` (`crates/rt/src/code.rs:261`, `:637`) **[read]**.
- The run loop `rt_loop` takes one node at a time (`sw_eff_step`,
  `native_abi.rs:2511`): a `Bind` pushes its `k` (one step), a `Done` with
  something pending pops a `k` and applies it (another step), and a `Call`
  goes to the handler **[read]**.
- `runFrom` is a state-passing handler, so `crate::fusion` turns its tail
  `k v s′` into a jump and runs it as a loop with the state in a variable
  (effect-runtime.md §9.7). The jump is the runtime value `JumpK`
  (`native_abi.rs:2115`) **[read]**.
- `optional`, `attempt`, `label`, `labelWhole` and `sectionLine` are
  handlers too (`Parse.sw:339-351`, `540-555`, `593-608`, `627-649`,
  `489-502`). They have an open row (`{Parse}` outside), so they are lazy
  folds: a clause's `k y` gives `Bind (Done y) r`, `r` a resumption, for
  the outer loop to run (`crates/rt/src/effect.rs:475-488`) **[read]**.

### 1.2 Cost 1: effect steps and freed closures, from `bind`

When a parser performs an operation, its `Call` goes back up through every
effectful function between the operation and the handler. Each of their
`bind`s sees a `Call`, not a `Done`, so each builds a `Bind` node holding
its continuation closure. The loop then pushes each continuation (one step)
and later pops and applies it (one step). The closure is freed after.

So, roughly, **every effectful `let` in the parser costs one closure, one
node, two steps and one apply** whenever anything under it performed,
which in a parser is almost always. The counts agree **[inferred from the
measured counts]**:

| per input character | `expressions` (6.83 M chars: 18,967 × 180, parsed twice) | `scan` (3.59 M chars) |
|---|---:|---:|
| closures made (`sw_closure`) | 20 | 33 |
| effect steps (`sw_eff_step`) | 38 | 57 |
| slow-path applies (`sw_apply_prepare`) | 38 | 69 |

Steps are about twice the closures in `expressions`, as one push and one pop
per continuation predicts. Some of the closures aren't continuations: the
thunks passed to `optional` and `many`, `List.find`'s predicate in `pick`,
`many`'s `value => manyFuel …`. That is why the ratio isn't exact. Closure
frees are 15.6% of `expressions`, `sw_eff_step` 19.4% **[measured]**.

Which combinators: in `expressions`, `Parse.chainLeft` (`Parse.sw:467-473`)
binds `first`, then `many`'s loop (`manyFuel`, `:371-376`) binds `before`
and `optional parser`, and `manyStep` (`:385-390`) binds `mark()`. The
operator (`operator` in Day18, through `Parse.pick`, `:317-322`) binds the
`List.find` over `Parse.literal`. Then `operand`'s `oneOf` (`:360-368`)
wraps the number alternative in `optional`, and `Parse.nat` binds `span`.
That is about seven effectful `let`s per operand in a chain. For `scan`,
`findAllFuel` (`:560-568`) runs at *every* character: `skipNoise()`,
`attempt`, `text "mul("`, a failed `note` and `stop`, then `pick`'s two
`literal`s, two `note`s, a `stop`, a `reset` and a `next`. That is why
`scan` makes more of everything per character.

### 1.3 Cost 2: handlers that pass operations on

`optionalFrom`'s clause for `span` is `k (Parse.span passes)`
(`Parse.sw:342`): it performs `span` again, outwards, and resumes its own
continuation with the answer. An operation inside *d* of these handlers is
therefore taken *d+1* times, and each time **[read: `sw_eff_step`'s `Call`
path, `effect.rs:475-517`]**:

- the clause is applied;
- it performs the operation again (`Call op DoneK`, a new node);
- `bind` makes a `Bind` with the clause's `k`;
- the outer loop routes it;
- the answer comes back through `DoneK` (an apply), the lazy resumption
  (`Bind (Done y) r`, an apply and a node) and the eager resumption `r`
  (`RESUME_CODE`, an apply into `rt_resume`).

How deep is *d*? In `expressions` every operand after the first in a chain
sits inside `many`'s `optional`. A bracketed operand's whole inside is one
level deeper again. The number alternative of `oneOf` adds one more. In
part 2 there are two chains per level (`*` over `+`), so two `optional`s
per bracket. On the real input, lines nest brackets two or three deep, so
*d* of 3–6 is typical **[inferred from Day18.sw and the input; not
counted]**. Every chain also ends with a failed `optional` (`pick` fails
on both operators), which costs two `literal`s, two `note`s, a `stop` and
a `reset`.

The design this follows chose forwarding deliberately and kept "evidence
passing" for later, "worth it only if programs nest many handlers"
(effect-runtime.md, "Optimisations on top of A"). Parsers are those
programs.

A library-side way out isn't available: an `optional` that the runner
handles itself would need an operation taking a parser,
`try: (() → {Parse} a) → {Parse} Option a`. An operation's argument
mustn't mention its own ability (docs/core.md:372, Landin's knot)
**[read]**.

### 1.4 Cost 3: the slow apply path

`sw_apply_prepare` (`native_abi.rs:1912`) already has a fast path for a
partial application given exactly its remaining arguments (`:1935-1985`)
**[read]**. What falls through to the general path, which first copies the
arguments into a `Vec` (`:1987`), is the effect runtime's own function
values:

- `DoneK` (`:2107`), at the end of every operation;
- `JumpK` (`:2115`), at every jump of `runFrom`'s loop;
- lazy resumptions (`:2128`) and eager resumptions (`:2138`), at every
  forwarding handler;
- `bind` applied as a value (`:2070`).

In `expressions` there are about as many slow applies as effect steps
(262 M against 258 M). That fits "a few runtime values per operation and
per forwarding handler" **[inferred]**. The counts don't split
`sw_apply_prepare` by kind, so this is stage 0's first measurement.

The 305 M apply-cache misses are a separate cost. `rt_loop` applies every
continuation in the program from one call site, and that site's cache
holds one target (`crates/native/src/n1/runtime.rs:30`, "the site's
cache"), so it misses almost every time **[read: one cache per site;
inferred: it thrashes]**. A miss costs a call to `sw_apply_cached` but not
the `Vec`.

### 1.5 Not effects: error bookkeeping and allocation on the success path

- A failed `text` or `pick` word notes `Literal text`, and
  `Parse.State.add` formats it at once with `"'${text}'"`
  (`Parse.sw:80`). Then `expect` compares it with every text already
  expected (`any (== what)`) and appends it with `++ [what]` (`:75`). In
  `scan` that happens three times per character of noise, at a new furthest
  point each time, for messages that are thrown away when the attempt is
  backed out of **[read; share not measured]**.
- `Parse.text` turns its `Text` into a `List Char` on every call
  (`expected.toList`, `:211`), and so does `pick`, for each word on every
  try (`:318`). `operator` in Day18 also rebuilds its list of
  `(word, operator)` pairs on every call.
- Every reading operation makes a new `Mark` and a new `State` record
  (`advance`, `:98-99`), and `span` builds the list of characters it took
  (`List.span`).

Haskell's parsers avoid the first point by building error messages lazily
(Megaparsec's hints, attoparsec's failure continuation). Lean's `Parsec`
builds the error string only on the failing path.

## 2. Options

The effects on the two programs are **[estimated]** from the shares above,
not measured.

### 2.1 A. Fast paths in native `Apply` for the runtime's function values

**Change.**
- Give each of `DoneK`, `JumpK` and lazy and eager resumptions a direct case in the apply
  stub, keyed like `ApplyCache` on the value's first word, or handle them
  in `sw_apply_prepare` before the `Vec` is made. Each is a leaf (a node
  or a jump to `rt_resume`) that needs no argument vector.
- Give `rt_loop`'s continuation site a small polymorphic cache, 4 entries
  say.
- Move the remaining general path's arguments into the plan without a `Vec`.

**Effect.** Removes most of `sw_apply_prepare`'s 22% and its `Vec` frees,
and some of the misses: about 1.2–1.3× on `expressions` and `scan`. It also
helps every effectful program (`bridge`, `disk`, matcher's parse).

**Cost.** 60–90 min, near the native ABI. Allocation traces stay the same
if the clones and drops keep the machine's order, which the current code
is careful about (`native_abi.rs:1925-1935`).

**Rules out.** Nothing. It doesn't change the number of steps, closures or
nodes, so it is a constant factor on top of the real problem.

**Proofs, users.** Unaffected.

### 2.2 B. Specialising combinators to their arguments (SW-2135 widened)

**Change.** Copies of `many`, `optional`, `oneOf` and `chainLeft` for the
known parser lambdas at each call. With constants hoisted, `"mul(".toList`
is computed once (compute-once.md).

**Effect.** It removes the thunk closures and their applies, and the
per-call `toList`s. It doesn't remove the handler, the `Call` nodes, the
`bind` continuations or the forwarding, because specialisation copies pure
structure and the effect machinery is the same in the copy. About
1.05–1.15× on these two programs. SW-2135 is worth doing for matcher and
dijkstra (lean-runtime-speed.md §3.3), but it is not the lever for
parsing.

**Proofs, users.** Unaffected.

### 2.3 C. A `Parse`-specific lowering (`Parse` compiled as a state-passing loop)

**Change.** The backend recognises `Std.Parse`'s handlers and compiles a
`{Parse} a` function as `Parse.State → (Ok a State | Stop State | Fatal)`,
the shape of Lean's `Parsec` (`String.Iterator → ParseResult α`) and of the
Lean ports in `bench/compare/lean/Compare/Expressions.lean`. Operations
become inline state updates, `optional` a function that calls its body and
looks at the result.

**Effect.** The largest single step: about 4–8× **[estimated]**.

**Cost.** The backend would hold `Parse`-specific knowledge: which
definitions are `Std.Parse`'s handlers, and that the clauses of
`optionalFrom` and the rest are what they say. That is a trust question
(backend-trust.md): an error there changes what a program means, and only
the differential tests would catch it. It is also a second code path for
one ability: a user's own `Parse` handler (Day08 and Day09 of 2020 call
`runFrom` and `optionalFrom` directly) would fall back to the general path,
and its speed would drop off a cliff for reasons a user can't see.

**Rules out.** Nothing permanently, but it would be thrown away by D.

### 2.4 D. Operations in place, for every effect (Koka's design)

**Change.** At an operation, before building a `Call`, the runtime looks up
the nearest handler of that ability on a handler stack kept in the context.
If that handler's clause for the operation is **tail-resumptive** (`k e`,
or `k v s′` in a state-passing handler: what `fusion.rs` already
recognises), the clause runs where the operation is, its answer is the
operation's value, and the parser carries on: no node, no continuation, no
step. If the clause is **abortive** (`stop`, `fatal`: `k` unused) or
general (resumes twice, or not in tail position), the `Call` is built as
today. Three pieces follow:

1. **Transparent forwarding.** A clause that is exactly `k (op x)` for the
   same operation is marked, and lookup skips that handler for that
   operation. `optional` then costs nothing per operation it passes on,
   only at `stop`. This is useful without the rest, as stage 3, inside
   today's loop: a forwarded `Call` is re-emitted outwards with an eager
   resumption, without calling the clause, `DoneK` or the lazy `Bind`.
2. **Clauses that run in place under their own handler's outer context.**
   `labelFrom`'s `note` clause performs `note` outwards, so it must run with
   the handlers inside it out of view. Koka does this by yielding to a
   specific handler (a prompt), and the run loop must pass a `Call` aimed
   at a further handler on untouched. That is a change to the loop's
   semantics, which needs §9.2-style soundness reasoning.
3. **Lazy continuation closures.** Once most `bind`s see `Done`, compile
   `bind c (x => body)` with a literal lambda as "if `c` is `Done x`, run
   `body` here; else make the closure and the node". The closure is then
   made only when something really suspends. This is what removes the
   137 M closures.

A state-passing handler's state, today a variable of `rt_loop`, must be
readable by a clause run in place. It would live in the handler stack's
entry, set by the loop each time it resumes a continuation. Whether that
is sound with resumptions used more than once (`Each`) is the heart of the
design note this needs. My reading is that it is, because a fused loop
runs one continuation at a time and passes the state explicitly at every
`k v s′`, but this is **[inferred]** and not argued in full here.

**What others do.**
- **Koka** splits operations into `fun` (tail-resumptive, called in place
  through evidence) and `ctl` (captures the continuation). Its own parser
  library, `std/text/parse`, uses `fun satisfy` and `fun current-input`
  for reading, `final ctl fail` to fail and `ctl pick` for choice, whose
  handler resumes `True`, then `False` from the saved input
  (koka-lang/koka `lib/std/text/parse.kk`) **[read, web]**. So Koka's
  parsers pay for a continuation only at choice points. D gives us that
  without new syntax: Stitchwort finds tail-resumptive clauses itself, as
  it already does for state-passing handlers (D1162 item 5).
- **attoparsec, Megaparsec and Angstrom** use continuation-passing parsers
  (success and failure continuations; Megaparsec has four) over a byte or
  text buffer. GHC's `INLINE` and `SPECIALIZE` pragmas, or OCaml's
  inlining, then fuse the combinators into straight code. This is
  option C in another form: a library representation chosen for speed.
  It gives up direct style, so it isn't open to us without changing what
  users write.
- **Lean's `Parsec`** is a state-passing function, `@[inline]` on its
  monad operations, with errors built only on failure. The comparison's
  Lean ports don't even use it: they are hand-written loops over a
  `ByteArray`.

**Effect.** On these programs, every reading operation becomes a direct
call, and handlers that pass an operation on cost nothing. What remains is
the operations' own work (a new `State` and `Mark` per read, `span`'s
list), handler installation per `optional`, and `stop`'s real
continuation capture. About 3–6× on top of stages 1–3 **[estimated]**.
It helps every effect whose handler answers in place: `State`-like
handlers at an open row (effect-runtime.md §9.11, option B, is the same
problem), `Fail` that doesn't fail, and user abilities.

**Cost.** The largest: a design note (Opus, 90 min) for the handler stack,
prompts, the state in place and its soundness, then three or four
implementation lanes. Allocation traces and effect counts change, so the
native agreement tests' expectations are regenerated, and the machine must
do the same (the native runtime shares its leaves with the machine,
`n1.rs:31-35`).

**Rules out.** Nothing. Multi-shot resumption keeps working through the
general path.

**Proofs, users.** Unaffected: the meaning of a computation is still the
`Comp` tree (effect-runtime.md §0, "What the runtime must preserve"), and
proofs never mention the backends.

### 2.5 E. Library changes inside `Std.Parse`, API kept

**Change.**
- Keep problems unformatted in `Parse.State`: `expected` as a list of
  `Parse.Problem`, formatted in `Parse.State.failure` or `describe`, so a
  failure that is backed out of costs a cons, not a text, a scan and an
  append.
- Compute `text`'s and `pick`'s character lists once per call site (with B's
  hoisting) or hold the words as `List Char` already.
- In `findAllFuel`, test the attempt's result with one `match` instead of
  two `Option.map`s with closures (`Parse.sw:566-567`).

**Effect.** `scan`, where three formatted notes per character are a large
part of the work outside the effect machinery: about 1.2–1.5×. `expressions`:
about 1.05–1.1× (it fails less often per character).

**Cost.** 60 min, Sonnet. The messages must stay byte for byte the same.
The parse error tests pin them.

**Proofs.** `Parse.Reads` and `Parse.Runs` quantify over every state and
say nothing about its failure fields (`Reads.sw:45-48`, `Runs.sw:37-40`,
and Runs.sw:54's "the state's other fields (what a failure would report)"
are free). One lemma names `Parse.State.note` (`Reads.sw:1179`) **[read]**.
So re-proving should be small, but it is a change to `Std.Parse`'s
definitions, hence D3401.

**Users.** `Parse.State` is public. A user who builds one by hand (none in
`aoc/` does, as far as grep shows) would see its fields change.

### 2.6 What none of this reaches

`Parse.Mark` holds the rest of the input as a `List Char` (`Parse.sw:31`),
and the proofs are stated with it everywhere (`state.at.rest = read ++
rest`). A list cell per character, and `span` copying what it took, are
what keep us from Lean's byte loops. Changing that means re-proving
`Parse.Reads` and `Parse.Runs`. It is a later question, worth asking only
after D shows what remains.

`scan` could also skip noise with `findAllStarting` (`Parse.sw:581`),
which would make it many times faster. But the Lean port tries every
position too (`Scan.lean`, `parseInstructions`), so changing only ours
would make the comparison unfair. Calls I made: leave day 3 as it is, and
make `findAll` cheap instead.

## 3. Recommendation and stages

Do D, the general design, not C. It reaches about the same speed on
`Std.Parse`, puts no knowledge of `Std.Parse` in the backend, and speeds up
every effect a user writes. Get there by stages that each pay off and each
have a measurement (`task profile:native -- expressions scan bridge`):

| Stage | What | Expected **[estimated]** | Measured by |
|---|---|---|---|
| 0 | Counts: `sw_apply_prepare` split by kind of function value; the effect counts (binds, pushes, pops, routes, resumes, jumps, operations per ability) in the call-counts report | (no speed-up) | That slow applies are mostly `DoneK`, `JumpK` and resumptions, and that binds ≈ closures ≈ steps / 2 (§1.2). If not, revise stages 1 and 4 before starting them. |
| 1 | Option A: apply fast paths for the runtime's values, a polymorphic cache at `rt_loop`'s site, no `Vec` | 1.2–1.3× on expressions and scan, some on bridge and disk | `sw_apply_prepare` and miss counts fall by most of their 262 M / 305 M; time |
| 2 | Option E: lazy problems, words as lists once, `findAll` without closures | scan 1.2–1.5×, expressions about 1.05× | time; `sw_ctor` count on scan; parse error tests and `Parse.Reads` / `Parse.Runs` check unchanged |
| 3 | D.1: transparent forwarding in today's loop | 1.2–1.5× on expressions | effect steps and resumes per character fall (stage 0's counts) |
| 4a | Design note: operations in place (handler stack, prompts, state in place, soundness with multi-shot) | (paper) | Matt's decisions |
| 4b–d | D.2 then D.3, as the note stages them | 3–6× on what is left | closures and steps per character near 0 on expressions; time |

Calls I made (reversible, not D questions):
- the order above. Stages 1 and 2 are independent and can run side by side.
  Stage 3 is the first piece of 4 and stands alone.
- B (SW-2135) goes ahead on its own merits; parsing doesn't wait for it.
- Day 3 isn't changed for the benchmark (§2.6).

### 3.1 Stage 0's counts (SW-2335, measured)

The cost model holds. Per input character (expressions / scan): closures 20.1 / 33.1,
effect steps 37.8 / 57.1, slow-path applies 38.4 / 69.2, as predicted; steps are 1.9 / 1.7
times the closures. Of the slow-path applies, the effect runtime's own values (DoneK,
JumpK, resumptions) are 48% / 44%, and the fast-path PAP, which still calls
`sw_apply_prepare`, is the largest single kind at 38%. The run loop's continuation call
site misses its one-entry cache on 86% / 100% of pops, and the caches of DoneK, JumpK and
resumption sites never fill, so those sites make two runtime calls where one would do.
Re-dispatch depth wasn't measurable without a field on `Call` (SW-2347), so stage 3's
size is still an estimate. D3400: Matt, 8 Nov 2026, yes (SW-2339 designs it).

## 4. Decisions for Matt

**D3400:** for the parsers' speed, invest in making tail-resumptive
operations cheap for every effect (option D, Koka's "operations in place"),
rather than a lowering special to `Std.Parse` (option C)? [rec: yes.
About the same speed for `Std.Parse` (estimated), no `Std.Parse`
knowledge in the backend, and every user ability and `State`-like handler
gets it too. It is the item effect-runtime.md (D1162) left "later and
measured", and SW-2296 has now measured it.]

**D3401:** may `Std.Parse`'s internals change (its state keeps problems
unformatted and formats them only for the message), with the same API and
the same messages, and with any `Parse.Reads` or `Parse.Runs` lemma that
names them re-proved? [rec: yes. The proofs are stated over every state
and leave its failure fields free, so the change is small. Users see no
difference unless they build a `Parse.State` by hand, which no AoC day
does.]

## 5. What I didn't cover

- Nothing was run (paper lane). Every share in §2 is estimated. Stage 0
  checks the cost model of §1 before money is spent on it.
- The handler-installation cost of `optional` (the clause closures and
  handler record per call) wasn't read in detail.
- `bridge`, `disk` and matcher's parse weren't traced per combinator. I
  assume the same mechanisms, at a smaller share.
- The JS backend: D would need the same design there (effect-runtime.md's
  A′ is shared), which the stage 4a note should cover.
- The soundness argument for state in place with multi-shot resumptions
  (D.2) is only sketched.

## Tickets to file

In order. Stages 1 and 2 can run in parallel, after 0.

1. **Stage 0: effect and apply counts in the call-counts report.** Split
   `sw_apply_prepare` by kind of function value (`DoneK`, `JumpK`, lazy
   resumption, eager resumption, `StateRun`, partial application,
   native, other) and print the effect runtime's counts (binds, pushes,
   pops, routes, resumes, jumps, operations per ability). Sonnet, 30 min.
   Tests: `task test:one -- call_counts`. Then profile `expressions` and
   `scan` with `task profile:native` and add the numbers to this note.
2. **Stage 1: native apply fast paths for the effect runtime's values.**
   Option A (§2.1). Opus (native ABI, clone and drop order), 60–90 min.
   Tests: the native agreement tests for effects
   (`run_lines_agree_with_the_reference_evaluator`,
   `state_handlers_run_as_a_loop_where_they_fit`), `effect_differential`.
   Measure: `task profile:native -- expressions scan bridge`.
3. **Stage 2: `Std.Parse` without eager error formatting.** Option E
   (§2.5), if D3401 is yes. Sonnet, 60 min. Tests: `Std.Parse` checks,
   including Reads.sw and Runs.sw; the parse error message tests; AoC 2024
   day 3 and 2020 day 18 checks. Measure: profile `scan`.
4. **Stage 3: transparent forwarding clauses.** D.1 in today's loop
   (§2.4). Opus (effect runtime semantics), 60–90 min. Tests:
   `examples/extract/effect-state.sw` and effect-runtime examples on both
   backends, `effect_differential`, the native agreement tests. Measure:
   effect steps and resumes per character on `expressions`.
5. **Stage 4a: design note, operations in place.** D.2 and D.3, with the
   handler stack, prompts, a state-passing handler's state in place, lazy
   continuation closures, JS, and the soundness argument with multi-shot
   resumption, as a new section of effect-runtime.md or its own proposal.
   If D3400 is yes. Opus, 90 min, paper. It names its implementation lanes
   (4b–d, Opus, 60–90 min each).
6. **SW-2135** (specialisation widened) stays as it is. It isn't absorbed
   here: §2.2 explains why it doesn't carry the parsers.
