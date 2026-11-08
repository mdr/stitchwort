# Operations in place, for every effect (SW-2339)

SW-2339, 8 Nov 2026, Opus, paper lane (no builds or runs). It follows D3400
(Matt, 8 Nov 2026: "special case parsing feels desperate and much better if
we can avoid it and do something a bit more generic"), and builds on
[parse-runtime.md](parse-runtime.md) (SW-2327, §1 for where the time goes,
§2.4 for option D) and [effect-runtime.md](effect-runtime.md) (D1162, §2 for
what the runtime must preserve, §9 for what is built). It doesn't repeat
them. Claims are marked **[read]** (seen in the code, with file:line),
**[measured]** (from SW-2296 or effect-runtime.md), **[inferred]** (worked
out, not checked by running anything), **[estimated]** (a guess at an
effect, with the reasoning) or **[lit]** (from a paper or a project's
sources, cited). SW-2335's stage 0 counts haven't landed on `main`, so every
effect below is estimated from SW-2296's counts.

## 0. Summary

**The problem, for a user.** Every time effectful code performs an
operation, the runtime treats it as something that might need to pause the
program: each function between the operation and its handler wraps what it
still has to do in a closure and a node, a loop takes those apart again,
and the answer comes back through several runtime function values. That is
the right thing for an operation like `Each.fork` or `Parse.stop`, which
really does pause or abandon the program. But almost every operation is
answered on the spot: `Parse.span` reads some characters and carries on,
`Counter.bump` adds one and carries on. For those, all the pausing
machinery is wasted. In `Std.Parse` it is most of the run time: AoC 2020
day 18 and 2024 day 3 take about 37 s natively against Lean's 0.5 s
**[measured, SW-2296]**, and a `Counter.bump` costs about 17 times a pure
loop turn (effect-runtime.md §9.11) **[measured]**.

**The change.** When an operation is performed, the runtime looks up the
handler that will answer it, on a stack of handler entries it keeps beside
its frames. If that handler's clause for the operation only answers and
carries on (it calls `k` once, as its last act: "tail-resumptive"), the
runtime calls the clause right there, with the handlers inside it out of
view, and the operation's answer is simply the result of that call. Nothing
pauses, so nothing is built. Handlers that only pass the operation on
(`optional`'s `span` clause, and every handler's generated forwarding of
other abilities' operations) are stepped over in the lookup. Everything
else (a clause that resumes twice, keeps `k`, or resumes it not last)
takes today's path, unchanged. Users write nothing new, and no proof or
hash moves: this is a change to the two untrusted runtimes only.

**What it should do** (all **[estimated]**, §5): once in place (stages B–D
of §6), about 2–3× on `expressions` and `scan` on top of the cheap stages
already filed (SW-2336, SW-2337), and a further 1.2–1.5× when bind's
closure is built only when something really pauses (stage E). About
1.2–1.5× on `bridge` and on matcher's and disk's parsing. 2–3× on a
closed-row state handler's operation (`counted`). We'd know by the effect
counts per input character (loop steps, `Bind` nodes and resumptions near
zero on `expressions`) and `task profile:native`.

**Soundness** (§3): sound, with one condition the design must enforce,
which Koka gets for free and Stitchwort doesn't: the handler the runtime
looks up when an operation is *made* must be the one that will *fold* it.
In Stitchwort a computation is a value, so it can be made in one place and
handled in another (a constant `current: {State Nat} Nat`, a computation
stored in a list, a handler's body evaluated before the handler starts).
The design answers this with a "consumer link" (§2.2): an operation runs in
place only if every frame between it and its handler is known to hand its
result straight to that handler. Where the runtime can't tell, it takes
today's path. Forgetting a case costs speed, never correctness.

## 1. Three facts about today's runtime that shape the design

parse-runtime.md §1 traces where an operation's time goes. Three further
facts decide what an in-place design has to do here, and where it must
differ from Koka's.

1. **Operations have no names at run time, only places in a row.** A row
   `{A, B | e}` is a chain of `Plus`es, and an operation of `B` is the
   value `R (L op)` (`crates/elab/src/std/core/Effect.sw:33-35`,
   `crates/elab/src/effects.rs:7-10`) **[read]**. A handler's step is
   `handlePlus elim forward` (`Effect.sw:141-145`): `L o` goes to the
   clauses, `R o` to the generated `forward`, which re-performs it in the
   handler's outer row along a mapping `m`: `o k => Call (sigInject m o)
   (y => k (sigReply m o y))` (`effects.rs:4921-5050`) **[read]**. Calls
   between rows are wrapped in `translate`, which renames each operation on
   the way out and maps its answer on the way back (`Effect.sw:60-63`). So
   "the nearest handler of this ability" is not a lookup by name: it is a
   walk outwards through folds and translates, renaming the operation at
   each translate and forward, until a fold sees it as `L`.
2. **A handler's body runs, up to its first operation, before the handler
   starts.** `handle parser() with …` is `foldComp done step (parser ())`
   (`docs/core.md:392`), and both backends evaluate the argument first.
   Today that doesn't matter: `parser ()` only builds a `Call` value, and
   the fold's loop takes it from there. But an operation that runs where it
   is made must find its handler already installed.
3. **A computation is a value.** A signature can be a computation that
   isn't a function (`current: {State Nat} Nat`), a constant computed once
   and kept; and where a parameter, constructor field, list item or tuple
   part has a `Comp` type, a computation "is passed as it is and not run"
   (`docs/syntax.md:817`, `crates/elab/src/check.rs:4180-4219`) **[read]**.
   So a `Call` can be made in one dynamic context and folded in another.
   If `current` ran `get` in place the first time it was used, every later
   use would see that first answer, which is wrong. Koka, OCaml and Effekt
   have no computation values (an effect happens when code runs), so none
   of them has this problem to solve.

And one fact that helps: **the run loop already knows which handler is
running.** Each loop activation carries its handler (`EffRet { handler,
pending, state, ret }`, `crates/rt/src/machine.rs:793-798`; natively, the
`rt_loop` frame, `crates/native/src/n1/runtime.rs:6-12`) **[read]**. A
continuation the loop applies runs inside that activation; a clause it
applies runs outside it, with the fold's own `ret`
(`machine.rs:858-864`) **[read]**. That is exactly deep-handler scoping: a
clause's own operations go to the next handler out (`docs/core.md:393`). So
the handler stack below is not a new notion, only an index of activations
the machine already has, kept so that an operation can find its handler
without walking the frames between (the invariant of effect-runtime.md
§9.1.6).

## 2. The design

### 2.1 Handler entries

The machine's state (and native code's `Context`,
`crates/rt/src/native_abi.rs:408`) gains a stack of **entries**, one per
running loop activation, innermost last:

| field | what |
|---|---|
| `kind` | a fold with known clauses (§2.3), a fold with an opaque step, a state-passing fold (stage 4d), a `translate`, `runPure`, the runner's `Step`, a `Delay` fold |
| `clauses` | for a fold with known clauses: per operation of its ability, the clause value and its class (§2.3) |
| `forward` | the generated forward's mapping `m` (inject and reply), when recognised |
| `inject`, `reply` | for a `translate` |
| `state` | a state-passing fold's state (§2.7) |
| `outer_linked` | whether this activation's result goes straight to the entry below (§2.2) |
| `serial` | a number unique to this activation, for aimed unwinds (§2.6) |

An entry is pushed when an activation begins (a fold, `translate` or
`runPure` native starts its loop; a resumption or a state handler's
function of the state starts one) and popped when its loop ends (a `Done`
with nothing pending, or a `Call` it hands out). In the machine these are
the places that make and deliver `Ret::Eff` (`machine.rs:638, 793, 908,
951, 994`); natively, `rt_loop`'s entry and exit **[read]**. A push and a
pop are a constant each, so the entry stack is to activations what 4c's
`marks` are to the runner's frames.

**The fold's body runs under its entry.** To fix fact 2, a fold whose body
is an expression is lowered with the body as a thunk, which the fold native
applies after pushing the entry, as it applies a continuation. When the
body is already `f ()` for a variable `f` (as `handle parser() with` is),
the thunk is `f` itself, so no closure is made. The same for `translate`
and `runPure`. Evaluating the body later is invisible: building a
computation is pure (effect-runtime.md §2, "What may differ").

### 2.2 The consumer link

The danger is fact 3: an operation made somewhere whose result will be
folded by a handler other than the entries above it. Rather than find
every such place, the design marks the places where it is *known* that the
result goes straight to the current activation, and runs operations in
place only there.

A **consuming position** is one of these, and nothing else:

1. the body of a continuation the loop applies (its result goes back to
   the loop);
2. the body thunk of a fold, `translate` or `runPure`, applied under its
   new entry;
3. the first argument of a `bind` whose own position is consuming;
4. the tail position of a frame that is linked (below);
5. a clause run in place (§2.5), if its handler's entry is `outer_linked`.

A frame is **linked** if it was entered from a consuming position. The
machine keeps one number, `linked_depth`: the frame depth of the frame
currently known to be linked, if any. A call from a consuming position sets
it to the callee's depth and puts the old value back when the call returns;
a tail call from a linked frame keeps it (same depth); any other call
leaves it alone, so the callee, one deeper, isn't linked. An operation is
eligible to run in place only if it is made in a consuming position of a
frame whose depth equals `linked_depth`.

Pure code pays nothing: only calls in consuming positions, which exist only
in effectful code, store the number. Native code already passes the frame
count from frame to frame (`native_abi.rs:416-418`, "compiled code passes
the count on") **[read]**, so the test at an operation is a load and a
compare.

Each entry records `outer_linked`: whether the fold, `translate` or
`runPure` call that started it was itself in a consuming position of a
linked frame. A lookup (§2.4) may cross an entry outwards only if it is.
Everything unknown falls on the safe side:

- a constant is evaluated in a fresh frame entered from no consuming
  position (`Ret::Const`, `machine.rs:1085`), so `current` builds its
  `Call` as today;
- a computation passed as a value (a `Comp` parameter, field or list item)
  is an argument, not a consuming position, so it is built as today and
  folded later by whoever takes it;
- a fold whose body couldn't be thunked had its body evaluated as an
  ordinary argument, so its operations are built as today;
- the row helpers `bindIn`, `liftIn`, `lowerIn` and `widenIn`
  (`Effect.sw:185-215`) are ordinary library calls, so code that goes
  through them builds its operations as today, until stage E lowers them as
  natives with consuming arguments (empty-row specialisation removes most
  of them first).

### 2.3 Which clauses can run in place

When the backends lower a `foldComp` whose step has the elaborator's shape
(`handlePlus (A.elim clause₁ … clauseₙ) forward`), a static pass, beside
`crates/rt/src/fusion.rs` and sharing its walk of tail positions
(`fusion.rs:314-460`: `let`s, applied lambdas, `if`, `Decidable.elim`,
inlined `match`es), gives each clause `x, k => body` a class:

| class | when | example |
|---|---|---|
| **Forward** | `body` is `k (op′ x)`, or `k op′()`: it performs one operation of the outer row, with the clause's own argument or `()`, and resumes with the answer (as elaborated: `bind (Call o′ DoneK) (y => k y)`) | every reading clause of `optionalFrom`, `attemptFrom`, `labelFrom` and `sectionLineFrom` (`Parse.sw:339-351, 540-555, 593-608, 489-502`) |
| **Tail** | every occurrence of `k` is `k e` in tail position (following binds' continuations too), and `k` occurs nowhere else | `labelFrom`'s `note`: `if … then k () else k (Parse.note problem)`; a reader's `ask` |
| **Abort** | `k` doesn't occur | `stop` in `optionalFrom` (`Parse.reset start; None`) and `runFrom` (`Err state.failure`); `Fail`'s `fail` |
| **General** | anything else: `k` twice, not last, under a lambda, stored | `Each`'s `fork`; a state clause `k v s` not in tail position |

For a state-passing fold (stage 4d) the classes are the same with `k v s′`
(already a `jump v s′` after fusion) in place of `k e`: `runFrom`'s
`span`, `next`, `literal`, `mark`, `reset` and `note` are Tail (both arms
of `next`'s `match` jump), `stop` and `fatal` Abort.

The generated `forward` is recognised by its shape from `effects.rs:4933`
in each of its four variants (plain, bare row with `lowerIn`/`liftIn`,
partial, divergence-indexed). Only the plain and bare-row forms are made
transparent; a forward into a partial row stays opaque (the lookup stops
there).

The lowering passes the classified clauses and the forward's mapping to a
new fold native (or a new form of the existing ones), so the entry can hold
them. A fold whose step doesn't have the shape gets an entry with an opaque
step: lookups stop there, and its operations take today's path.

### 2.4 Performing an operation

An operation as the elaborator writes it is `Call O DoneK`, with `O` the
operation injected into the row by constructors (`R (L (Parse.span
passes))`), and in computation mode it is the first argument of a `bind` or
a tail result **[read: effects.rs:28-30]**. The lowering recognises this
shape and compiles it as a **perform** of `O`, which at run time does:

1. If the position isn't eligible (§2.2), build `Call O DoneK` as today.
2. Walk the entries from the innermost, with `o := O` and an empty list of
   replies:
   - a `translate`: `o := inject o`, remember `reply` with this `o`;
   - a fold, `o = R o′`: its forward, if transparent: `o := sigInject m
     o′`, remember `sigReply m o′`; otherwise stop;
   - a fold, `o = L o′`: look at the clause for `o′`'s constructor. Forward:
     `o :=` the outer operation it performs, and carry on. Tail or Abort:
     this is the **target**; go to 3. General: stop;
   - anything else (opaque step, `Step`, `Delay`, `runPure`): stop.
   Before crossing an entry outwards, it must be `outer_linked`; if not,
   stop.
3. "Stop" means build `Call O DoneK` as today: nothing has been run, so
   the general path sees exactly what it sees now. Lookup work is counted
   as routing (it costs at most the entries crossed, as today's routing
   does, effect-runtime.md §9.1.6).
4. At a target: run its clause in place (§2.5). If it gives an answer `y`,
   apply the remembered replies, innermost last, and the perform's value is
   `Done y′`; for a perform that is a `bind`'s first argument, the
   continuation is applied to `y′` directly, as `bind (Done x) k` already
   is natively (§9.1.4).

The replies of the row mappings are usually `o x => x`
(`sigLeft`, `sigRight`, `swapReply`), but they are called, not assumed:
the cost is a call per translate crossed, as today. Recognising identity
replies statically is a later, measured step.

### 2.5 Running a clause in place

The clause runs with the entry stack cut back to just below the target
(the entries from the target inwards are set aside and restored after), so
its own operations reach the next handler out, as `docs/core.md:393` says
they must. Its frame is linked if the target's entry is `outer_linked`, so
its own operations can run in place in turn. This is Koka's "evaluated
under the evidence vector in which the handler was defined" (Xie and
Leijen 2021 §2.6, the `under` frame) **[lit]**.

The clause is given the operation's argument and, for `k`, a runtime value
`InPlaceK` that records its argument (as `JumpK` records `jump v s′`,
`crates/rt/src/effect.rs:512-517`): applied to `e` it gives `Resumed e`
(for a fold whose carrier is a computation, `Done (Resumed e)`), a value no
program can make. Its result is then one of:

- `Resumed y` (or `Done (Resumed y)`): the clause resumed. `y` is the
  answer.
- for a state-passing fold, `Jumped y s′`: the same, and the entry's state
  becomes `s′` (§2.7).
- anything else: the clause didn't resume *yet* (it performed an outer
  operation that went the general path, so its result is a `Call` or a
  `Bind`), or it never will (Abort). Then §2.6.

### 2.6 When the clause doesn't resume at once: the aimed unwind

The clause has run, and its effects have happened, so the operation can't
fall back to the general path. Its result `C` must become the target
handler's result, as the tree says (`foldComp d c (Call o r) = c o (y =>
foldComp d c (r y))`): with `k` used only last, that result is `C` with
every final `Resumed y` replaced by "resume the computation from the
perform with `y`".

The perform returns a new internal node, `Aimed serial C`, carrying the
target entry's serial. On its way out:

- each `bind` treats it as it treats a `Call`: it makes a `Bind` node, so
  the continuation from the perform to the target is collected as it is
  for any operation today;
- each loop between the perform and the target forwards it outwards
  untouched, with a plain resumption (no clause called, no `inject`, no
  `reply`: the replies were remembered at the perform, which wraps them
  into the node's first continuation);
- the target's loop, seeing its own serial, makes the resumption `k` as it
  would for a `Call` and returns `bind C (v => match v | Resumed y => k y |
  v => Done v)` as the handler's result (for a state-passing fold, its
  loop's `state_step` on `C`, which is a plain value there).

An Abort clause's `C` never contains `Resumed`, so the continuation is
dead. Then the node is `Aimed serial C abort`, `bind` passes it on without
making a node, and loops drop what they hold: the abort costs what it
costs today, minus the dead `Bind` nodes. `Parse.stop` inside `optional`
is this case. No program sees the node: it exists only between a perform
and its target, and a serial is unique to an activation, so an aimed node
can't reach a handler of the same shape in another resumption.

Koka keeps the frames between the perform and the handler and puts an
`under` frame in them, which then has to be restored correctly when a
captured resumption is resumed elsewhere (Xie and Leijen 2021 §2.12.2:
"the formalization of under is tricky to get right"; their first version
was unsound) **[lit]**. Here the clause's suspended rest is a tree run
outside the handler, as the tree semantics runs a clause, so there is no
`under` to capture. That is a deliberate simplification: the price is that
a clause that pauses costs as much as today's path, which is fine, since
pausing is the rare case.

### 2.7 Handler state in place

A state-passing fold's state today is a variable of its loop (`EffRet`'s
`state`, `machine.rs:793-798`; `rt_loop`'s, `runtime.rs:17-26`)
**[read]**. It moves into the activation's entry. The loop reads it from
there at an operation that goes the general path and at the end (`done v
s`), and writes it on a jump; an in-place clause is called with it and its
`Jumped y s′` writes `s′`. Nothing else holds it.

That is sound because an entry belongs to one activation, and an
activation runs one computation, front to back. Every other use of `k`
already makes a new activation with its own state: a state handler's real
`k` is a `StateK` whose function of the state starts a fresh loop
(`effect.rs:496-510`, `machine.rs:650-655`) **[read]**. So two runs of the
same continuation never share an entry (§3.3, multi-shot).

### 2.8 The machine and native code in agreement

Native code already shares the effect runtime's leaves with the machine,
"so the two can't drift" (`effect.rs:325-331`, `n1.rs:26-34`), and its
agreement tests compare outputs, effect counts and allocation traces
**[read]**. The new pieces follow the same rule:

- the entry stack, the lookup, the clause classes and the aimed node's
  handling are Rust leaves in `crates/rt/src/effect.rs` (or a new
  `inplace.rs` beside it), called by the machine and by native code's
  runtime bodies alike;
- running a clause in place is a call from compiled code (a runtime body,
  as `rt_loop` and `rt_resume` are), so its frame is a machine frame in the
  machine and a native frame natively, counted the same;
- `linked_depth` lives in the machine's `State` and in `Context`, set and
  restored at the same instructions.

The reference evaluator doesn't change: it is the specification.

### 2.9 JavaScript

The JS backend always builds a `Bind` node (§9.1.3) and has no frame
count, so the consumer link would need its own mechanism there (a depth
variable kept by generated code). It keeps today's path. Its output still
agrees with the others, which is what the differential tests check
(effect-runtime.md §9.8); only its speed differs. Whether to bring it
along is D3410.

## 3. Soundness

### 3.1 What must hold

The meaning of every effectful program is the `Comp` tree and the
library's equations for `bind`, `foldComp`, `translate` and `runPure`
(effect-runtime.md §2). Proofs never see a backend
(`crates/rt/src/lib.rs:1-4`: the runtime "can only get a program's output
wrong, never make a false proof check"). So the obligation is: every
program prints the same output, ends the same way and makes the same
`IO` operations in the same order as the reference evaluator, with
resource limits as the only allowed difference (D2543: a limit fails,
never changes an answer). Nothing in the kernel changes, so `docs/core.md`
doesn't (D3210 doesn't apply).

### 3.2 The argument

Take an eligible perform of `O` at frame `F`, and the entries `a₁ … aₙ`
the lookup crosses before the target `h` (§2.4).

1. *The frames from `F` to `a₁`'s loop are a `bind` context.* Each is
   linked, so each was entered from a consuming position: its pending work
   is "bind the result with a continuation" or "return it". So the
   activation's computation is `E₁[Call O DoneK]` with `E₁` made of
   `bind`s, followed by its pending list `p₁`. This is where the consumer
   link does its work: without it, `F`'s result could be stored, and the
   step would be false.
2. *Crossing an entry is what the general path would do.* By `bind (Call o
   r) k = Call o (y => bind (r y) k)`, `E₁[Call O DoneK] = Call O K₁`. At
   `a₁`, if it's a translate, `translate m (Call o r) = Call (inject m o)
   (y => translate m (r (reply m o y)))`; if it's a fold forwarding `R o′`,
   its generated forward gives `Call (sigInject m o′) (y => k (sigReply m
   o′ y))`; if it's a Forward clause, it gives `bind (Call o′ DoneK) (y => k
   y) = Call o′ k`. In each case the result is a `Call` of the renamed
   operation, whose continuation is the old one, deep-folded by `a₁`,
   after the reply. Because `a₁` is `outer_linked`, that `Call` is the
   computation of the next activation, in a `bind` context again. By
   induction, at `h`'s loop the computation is `Call O_h K` where `K y`
   runs every remembered reply and then the frames from `F`, under the
   folds `a₁ … aₙ`.
3. *The target's clause.* `foldComp d c (Call O_h K) = c O_h k` with `k y
   = foldComp d c (K y)`. The clause runs with exactly the entries below
   `h`, which is the context `h`'s result is consumed in (it is
   `outer_linked`), so by induction on the number of entries its own
   performs are sound. Since `k` occurs only last, `c O_h k = C[k]` for a
   computation `C` in which `k` appears only as the final step. Running
   `C[InPlaceK]`:
   - gives `Resumed y`: then `C[k]` has done its work and become `k y`
     (the `bind` law, `bind (Done x) f = f x`, for each in-place outer
     operation). `k y = foldComp d c (K y)`, which is the frames from `F`
     carrying on with `y` after the replies, under `a₁ … aₙ` and `h`,
     whose entries are still there. That is what the perform does.
   - gives anything else: §2.6 rebuilds `C[k]` exactly (the `Bind` nodes
     on the way out are `K`; the target's `match` puts `k` where
     `Resumed` is). For an Abort clause `k` doesn't occur, so dropping `K`
     changes nothing.
4. *State.* For a state-passing fold, stage 4d's loop already satisfies
   "the loop's state is the state the tree's fold function would be
   applied to now" (§9.7). An in-place jump changes it exactly as the
   loop's jump does: the loop sets the state to `s′` and goes on with
   `rest y`; the perform sets it to `s′` and goes on with `K y`, which is
   `rest y` (step 2).

Steps 1–3 are the shape of Koka's correctness theorem for tail-resumptive
operations under generalised evidence passing (Xie and Leijen 2021 §3.2:
in-place evaluation "under" the handler's evidence is equivalent to
yielding) **[lit]**. What is new here is step 1's dependence on the
consumer link.

### 3.3 The cases that might worry

- **Resuming a continuation twice.** In-place never makes a resumption, so
  multi-shot only arises on the general path, which is unchanged. A
  resumption resumed twice starts two activations, each with its own
  entry and state (§2.7). An operation inside either looks up the entries
  that exist when it runs, which are the handlers that fold that run, as
  the tree's `k y = foldComp d c (rest y)` says.
- **A resumption kept and resumed after its handler returned**
  (effect-runtime.md §9.8's "stored" shapes). The same: a resumption
  carries the pending list, not entries, and the entries outside it are
  those of whoever resumes it, which is the tree's meaning. This is where
  the design must *not* follow Koka's evidence-passing translation, which
  passes the evidence statically and so needs "scoped resumptions": it
  "raises a runtime error" for a resumption applied under a different
  handler context (Xie and Leijen 2021 §2.12) **[lit]**. Stitchwort allows
  unrestricted stored resumptions (D1162, Q3 (a)), so the evidence must be
  dynamic, as Koka's own runtime keeps it (`ctx→w`, §2.11) **[lit]**.
- **Handlers inside handlers.** Entries nest as activations do. A clause in
  place sees only the entries below its handler, so an inner handler can't
  catch its own handler's operations.
- **Forwarding and renaming.** Rows can't hold an ability twice
  (`E-DUPLICATE`, `docs/core.md:378`), so there is no masking operator
  (Koka's `mask`); every renaming is a `translate` or a forward, and the
  lookup applies both as the tree does (step 2).
- **Abort.** §2.6. A loop between the perform and the target drops its
  pending list and handler exactly as it would if its computation had
  been abandoned by the target's clause today.
- **`Partial` and `IO`.** A `Delay` fold, the runner and `runPure` stop the
  lookup, so `IO` and recursion requests are never run in place, and
  effect-runtime.md §9.6's routing is unchanged.
- **A computation made in one place and folded in another** (fact 3).
  Built as today, by §2.2: its position isn't consuming.

### 3.4 What changes, exactly

None of these is output; all are already free to differ between backends.

- **Effect counts** (`EffectCounts`, `effect.rs:308-323`): loop steps,
  pushes, pops, routes, lazy resumptions and `Bind` nodes fall; new counts
  for performs in place, forwards crossed, aimed unwinds and entries looked
  at. Tests that pin counts per element (`crates/rt/tests/effect_runtime.rs`,
  `crates/cli/tests/effect_runtime.rs` for JS, which doesn't change) get
  new expected numbers; the machine's and native code's must stay equal.
- **Steps.** A step is a frame entered (`machine.rs:22-24`,
  `shared.rs:16-30`) and each loop iteration counts one (`machine.rs:775`)
  **[read]**. Fewer frames are entered and fewer iterations run, so a run
  uses fewer steps between two `IO` operations. A program that ran out of
  steps may now finish; none that finished can now run out, except through
  lookup work (§2.4 charges a step per entry looked at, so it is bounded by
  what routing charged before) **[inferred]**. The answers don't change
  (D2543).
- **Frames.** A clause in place runs on top of the perform's frames, not at
  its handler's level, and an outer clause in place on top of that. So
  peak depth grows by the clauses' own depth times the handlers crossed: a
  constant per perform, freed before the program carries on. The depth
  error can therefore come a few frames earlier for a program already at
  the 2,000,000-frame limit **[inferred]**.
- **Allocation traces.** Far fewer allocations (no `Call` node per perform,
  no `Bind` nodes, resumptions, `EffRet` boxes or lazy nodes on the
  in-place path), in a new order. Both backends make the same change
  through shared leaves, so their traces still agree with each other.
- **Error messages.** Unchanged: resource errors keep their kinds and
  texts, and no new error is possible.

### 3.5 What can't be made sound, or isn't attempted

- Running in place where the consumer isn't known. Not attempted: §2.2
  falls back.
- A clause that uses `k` other than last (State's `k v s` under a lambda,
  `Each`). Can't be done in place without a real continuation, which the
  perform site doesn't have (the frames between are machine frames, not a
  tree). General path.
- An open-row state handler (`Counter.from` under `{IO}`, §9.11 option B)
  isn't fused today, so its state is a closure per operation. In place it
  is a Tail clause of a lazy fold whose result is a function of the state;
  making that fast is §9.11 B's own argument, stage F below, and may not
  be worth it.

## 4. Literature and comparable languages

effect-runtime.md §3 summarises Koka, Effekt, Links, OCaml 5 and Unison as
runtimes. This section adds only what bears on operations in place.

- **Koka** (Xie, Brachthäuser, Hillerström, Schuster, Leijen, "Effect
  Handlers, Evidently", ICFP 2020; Xie and Leijen, "Generalized Evidence
  Passing for Effect Handlers", ICFP 2021,
  [PDF](https://www.microsoft.com/en-us/research/uploads/prod/2021/08/genev-icfp21.pdf))
  **[lit]**. Each handler's evidence is `(m, h, w)`: its marker, its
  clauses, and the evidence vector it was defined under (§2.6); a
  tail-resumptive clause is evaluated in place under an `under` frame that
  restores `w`. With canonical (sorted) evidence vectors a known row finds
  its handler at a constant offset, an open row by `find_ev` (§2.11). The
  measured lessons (§5): with the tail-resumptive optimisation off,
  `counter` is "10× slower", taking "the slow path through the monadic
  bindings"; bind inlining (a `Pure` fast path at every bind) adds 25%;
  with ten unused handlers in between, Koka's time doesn't change while
  implementations without evidence or in-place "get slower with each added
  handler due to the linear search". The 2020 paper's translation needs
  scoped resumptions; the 2021 semantics doesn't, at the cost of a subtle
  `under` (§2.12.2, quoted in §2.6 above). Surface: `fun` (in place, may
  perform), `val`, `ctl` (captures `k`), `final ctl` (never resumes). The
  language makes the programmer choose; Stitchwort finds the class itself,
  as fusion.rs already does for state handlers.
- **OCaml 5** (Sivaramakrishnan et al., "Retrofitting Effect Handlers onto
  OCaml", PLDI 2021, [arXiv](https://arxiv.org/abs/2104.00250)) **[lit]**.
  No in-place path: every `perform` switches to the handler's fiber and
  allocates a continuation object; lookup goes "up one handler stack
  segment at a time", so each handler crossed costs (as measured by Xie and
  Leijen's `counter1` and `counter10`). Fast because the switch is cheap,
  but continuations are one-shot, which rules it out for us
  (effect-runtime.md §4 D).
- **Effekt** (Schuster, Brachthäuser, Ostermann, "Compiling Effect Handlers
  in Capability-Passing Style", ICFP 2020; Brachthäuser et al., "Effects,
  Capabilities, and Boxes", OOPSLA 2022) **[lit, from memory: not
  re-checked]**. Handlers are lexically scoped capabilities passed as
  arguments, so an operation is a call on a known object, and for
  second-class capabilities the handler abstraction is eliminated
  entirely. That depends on the language being designed around lexical
  handlers and second-class functions; Stitchwort's handlers are dynamic
  (an operation goes to the nearest enclosing handler of its row), so
  capability passing would change the language, not the runtime.
- **Eff** (Karachalias, Koprivec, Pretnar, Schrijvers, "Efficient
  Compilation of Algebraic Effect Handlers", OOPSLA 2021) **[lit, from
  memory]**. Compiles to OCaml with source-level optimisations that push
  handlers into the code they handle and specialise them, removing
  handlers whose operations can be resolved statically. Closer to
  Stitchwort's SW-2135 specialisation than to a runtime technique.
- **Links** (Hillerström, Lindley et al., JFP 2020) and **Frank** (Lindley,
  McBride, McLaughlin, "Do Be Do Be Do", POPL 2017) **[lit, from memory]**.
  Links' generalised continuations alternate pure and handler frames (as
  our entries would); no tail-resumptive optimisation is described. Frank's
  implementation is an interpreter of its semantics, not a performance
  design.
- **Unison** **[read, effect-runtime.md §3]**: copies the stack segment per
  operation, with a newer path for handlers that resume at most once. No
  in-place answer.
- **Haskell libraries** **[from memory; not re-checked]**. `polysemy` and
  `fused-effects` are free(r)-monad or carrier encodings that are fast only
  when GHC specialises and inlines the handler into the program, and slow
  otherwise (Alexis King, "Effects for Less", ZuriHac 2020). `eff` (King)
  keeps a handler vector in a reader-like context and uses GHC's
  delimited-continuation primops only for control operations: the same
  split as here. `effectful` and `cleff` keep handlers in a mutable
  environment over `IO` and run every operation as a direct call: very
  fast, but they give up multi-shot continuations (no non-determinism),
  which we can't. The `Ev.Eff` library (Xie and Leijen, Haskell 2020) is
  Koka's evidence passing as a library, and in the 2021 paper's benchmarks
  GHC inlines it to almost nothing.
- **Lean** has no handlers: effects are monad transformers, and `EStateM`
  (state and exceptions in one state-passing function, `@[inline]`
  everywhere) is what its `IO` and `Parsec`-style code compile to
  **[from memory]**. That is option C of parse-runtime.md for every monad.
- **Others in the "tail-resumptive" literature.** Leijen, "Implementing
  Algebraic Effects in C" (APLAS 2017): `libhandler`, with tail-resumptive
  operations as plain calls, the fastest entry in Xie and Leijen's
  `counter` (1.5× Koka, "it does no allocation at all") **[lit]**. Ghica et
  al., "High-level Effect Handlers in C++" (OOPSLA 2022): separate
  "plain" and tail-resumptive handler classes that never capture
  **[from memory]**.

**What carries over.** Every fast system answers tail-resumptive
operations with a call where they are performed, and every one that is
also multi-shot (Koka, `eff`) keeps a dynamic handler context and runs the
clause under the handler's own outer context. None of them has
computations as values, which is the one thing the consumer link is for.

## 5. Options compared

Effects are on top of SW-2336 (apply fast paths) and SW-2337 (lazy parse
errors) **[estimated]**, from SW-2296's shares: effect steps 15–19%,
`sw_apply_prepare` 22% (mostly the runtime's own function values,
parse-runtime.md §1.4), closure frees 15.6%, and the node and box
allocations around them.

| | A. Dynamic entry stack with the consumer link (this note) | B. Koka evidence passing as parameters | C. Capability passing (Effekt) | D. Today's loop plus forwarding skips only (SW-2338) |
|---|---|---|---|---|
| How the handler is found | walk of entries, renaming at translates and forwards | evidence vector passed to every effectful function, offset or `find_ev` | a capability argument the program names | not found: ops travel to the loop as today |
| Expressions, scan | 2–3× (stages B–D), 1.2–1.5× more with E | similar to A | similar | 1.2–1.5× |
| Matcher's parse, bridge, disk | 1.2–1.5× | similar | similar | 1.05–1.2× |
| State-like handlers (`counted`) | 2–3× (no `Call`, step, push or pop per op) | similar | similar | none |
| Open-row state (`Counter` under `IO`) | needs stage F | similar after F's equivalent | similar | none |
| Cost | 5 lanes of 60–90 min (§6) | a second calling convention for effectful code in both backends (effect-runtime.md §4 B, C), plus the consumer problem anyway (fact 3) | a language change: capabilities in the surface, or inferred | 1 lane |
| Risk | the consumer link is a new backend invariant; falls back safely | evidence captured in closures needs scoped resumptions, or Koka's `under`, which its authors first got wrong | user-visible | low |
| Rules out | nothing: general path kept | stored resumptions resumed elsewhere, unless `under` is done in full | dynamic handlers as Stitchwort has them | nothing; subsumed by A |

B's one advantage is constant-time lookup with sorted evidence. Here
lookup is linear in the entries crossed, but forwards and translates are
crossed without calling anything, and parsers nest a handful (d of 3–6,
parse-runtime.md §1.3). If lookup shows up in profiles later, an entry can
cache, per ability position, the index of the nearest entry that handles
it; that is B's benefit without its calling convention.

## 6. Recommendation and stages

**Do A.** It answers the common operation with a call, as every fast
effect system does; it keeps unrestricted multi-shot and stored
resumptions, which rule out evidence passed as parameters; and it needs no
new syntax and no change to `Std.Parse`, the elaborator's output or any
proof. Its one new idea, the consumer link, exists to keep computations as
values correct, and it fails safe.

Stages, each a lane with a measurement. The flag `in_place` (on the
machine's and native code's options, off by default) lets stages C and D
land without breaking the native agreement tests; stage D turns it on and
the flag goes.

| Stage | What | Expected **[estimated]** | Measured by |
|---|---|---|---|
| A | **Clause classes.** The static pass of §2.3 (Forward, Tail, Abort, General; transparent generated forwards), sharing fusion.rs's tail walk; the lowering passes clauses and mapping to the fold native; a census of classes over std, `aoc/` and `bench/compare` | none | the census: share of performs whose handler clause is Tail, Abort or Forward in `expressions`, `scan`, `bridge` |
| B | **SW-2338 on stage A**: Forward clauses and transparent forwards skipped in today's loop | 1.2–1.5× on expressions | effect steps and resumes per input character |
| C | **Entries and the consumer link, machine only, behind the flag.** Entry stack, `linked_depth`, thunked fold bodies, lookup; in place for Tail, Abort and Forward with the aimed unwind and state in entries | on the machine, comparable to D's native estimate | effect counts per element on `bench/effect-runtime` and `effect-state.sw` shapes |
| D | **Native code**: the same through the shared leaves and runtime bodies; flag on, then removed; count expectations regenerated | 2–3× on expressions and scan, 1.2–1.5× on bridge, 2–3× on `counted` | `task profile:native -- expressions scan bridge`; call-counts: `sw_eff_step` and `sw_bind`'s node branch near zero per character |
| E | **Closures only when something pauses**: `bind c (x => body)` with a literal lambda compiled as "if `c` is `Done x`, run `body` here, else make the closure and node" (parse-runtime.md §2.4 D.3); `bindIn`, `liftIn`, `lowerIn` as natives with consuming arguments | 1.2–1.5× on expressions and scan | `sw_closure` per character |
| F (optional) | **Open-row state in place** (effect-runtime.md §9.11 B), with its own soundness section added to this note first | up to a third on `bump` (§9.11) | `bench/native/effects.sw` instructions per operation |

Stages A and B are worth doing even if the rest stops. E depends on D
(before it, most binds see a `Call`, so the fast path rarely fires). F can
be dropped if D and E bring the effect programs within the target the
comparative-speed epic sets; JS (D3410) is separate.

**Sequencing note for the orchestrator** (not a D question): SW-2336's
fast paths are mostly for `DoneK`, `JumpK` and resumptions, which stage D
removes from the hot path. It is cheap and helps the general path, so it
needn't be dropped, but if lanes are short, A–D come first.

## 7. Calls I made

- Dynamic entries, not evidence parameters (§5): needed for stored
  resumptions.
- The consumer link as a frame depth, not a per-frame bit or types: free
  for pure code, no type information needed in the backends.
- Fold bodies as thunks, with `f` itself for `f ()`, rather than an
  instruction that pushes the entry before the body in the same frame:
  simpler, one closure per handler at most.
- A clause that pauses goes the aimed-unwind way, not Koka's `under`:
  nothing to capture, at the price of today's cost for a paused clause.
- Replies of row mappings are called, not assumed to be identities, until
  measured.
- A flag during stages C and D, removed in D.
- Lookup is a linear walk; a per-entry cache only if profiles ask.
- JS keeps today's path for now.
- Lookup charges a step per entry looked at, so steps never exceed
  today's.

## 8. Decisions for Matt

**D3410:** bring the JavaScript backend along (the same design, with its
own depth tracking), or leave it on today's path, correct but slower,
until a JS program needs the speed? [rec: leave it. `run --js` and
exported JS agree with the others on output, which the differential tests
keep checking; the playground runs the native runtime compiled to wasm,
so it gets the speed anyway. Doing JS means a second implementation of
the consumer link for no measured need.]

**D3411:** say in the language guide which handler clauses are cheap ("a
clause that resumes once, as its last step, runs where the operation is
performed; one that resumes twice, keeps `k` or resumes it before doing
more pauses the program"), once stage D lands? [rec: yes, a short
paragraph in `docs/guide/08-abilities.md`. It is the one performance fact
a handler writer can act on, and Koka makes the same distinction visible
with `fun` and `ctl`. No new syntax.]

## 9. What I didn't cover

- Nothing was run (paper lane). Every effect is estimated from SW-2296's
  counts; stage A's census is the first check.
- The exact runtime representation of `Resumed`, `Aimed` and the entry
  stack in native code's `Context`, and the native unwind log's handling
  of an entry when a run fails (`runtime.rs:35-42`): stage D's to design,
  following NO2's rules.
- Divergence-indexed folds (`foldCompD`, `translateD`, `Effect.sw:329-340`)
  weren't traced; I assume they reach the same natives or stay opaque.
- How often `outer_linked` is false in practice (handlers whose fold call
  isn't in a consuming position): the census should count it.
- The SW-2335 counts, which hadn't landed.

## 10. Stage A census

SW-2348, 8 Nov 2026. `stitchwort_rt::clauses` gives each clause of a
`foldComp` or `foldCompD` whose step is `handlePlus (A.%elim …) forward`
one of §2.3's classes, reading the bodies the runtime lowers (generic
bodies, with row eliminators at `Empty` inlined, and empty-row variants).
State-passing folds are classed on fusion.rs's own rewrite of their
clauses: Tail if every `k v s′` became a jump and no other `k` is left. The
lowering doesn't use the classes yet; nothing a backend does has changed.
The census is `clause_census` in `crates/rt/tests/it/clause_kinds.rs`
(ignored by default: it loads all of `aoc/`, about a minute, 5 s with a
warm check cache) **[measured]**. Theorems, and `match`es lifted from
them, are left out: they never run.

| | folds | Forward | Tail | Abort | General | fused state folds |
|---|---|---|---|---|---|---|
| std, generic bodies and variants | 37 (2 unrecognised) | 23 | 7 | 33 | 57 | 1 (`runFrom`) |
| `aoc/`'s own definitions | 0 | | | | | |
| `expressions`, `bridge`, `disk`, `octopus`, `dijkstra`, `memory-game` (reachable from `main`) | 2: `optionalFrom`, `runFrom` | 6 | 6 | 4 | 0 | 1 |
| `scan` | 3: + `attemptFrom` | 12 | 6 | 6 | 0 | 1 |
| `matcher` | 3: + `labelWholeFrom` | 6 | 6 | 6 | 6 | 1 |

Each library handler (generic body; variants alike unless said):

| handler | clauses |
|---|---|
| `Parse.optionalFrom`, `attemptFrom`, `sectionLineFrom` | 6 Forward (`span` … `note`), `stop` and `fatal` Abort |
| `Parse.labelFrom` | 5 Forward, `note` Tail, 2 Abort |
| `Parse.runFrom` | fused; 6 Tail (`next`'s and `literal`'s through their `match`es), 2 Abort |
| `Parse.labelWholeFrom` | 6 General, 2 Abort: a state handler at `{Parse}`, not fused, so each `k` is under the state's lambda |
| `Fail.toResult`, `toOption`, `orElse`, `recover`, `context`, `toAbort`; `Abort.orElse`, `orFail`, `toOption` | Abort |
| `Each.collect`, `collectIn` | `fork` General (twice, under `both`'s lambda), `stop` Abort |
| `IO.simulateWith`, `Terminal.toIO`, `simulate`, `scriptedHost` | all General: open-row state handlers (§3.5, stage F) |

What this says for the next stages **[inferred from the counts]**:

- **Everything the benchmarks perform goes to Forward, Tail or Abort
  clauses**, except `matcher`'s `labelWhole`. AoC writes no handlers of its
  own, so the library's handlers are the whole story.
- **The consumer link blocks nothing statically.** 29 of the 37 folds are
  in a consuming position of their body; the other 8 are the open-row state
  handlers (`let run := handle …; run input []` under row helpers), whose
  clauses are all General anyway. Whether a definition's own frame is
  linked is a run-time fact this census can't see; stage C's counts will.
  `runFrom`'s fold is the body of a `runPure` that is itself a `let`'s
  value (`let go := …; go initial`): its activation starts at `go
  initial`, which stage C must treat as the fold's start.
- **`Fail`'s handlers reach the runtime as `foldCompD` on a variable
  divergence index** in their generic bodies: the runtime calls the
  library's `foldCompD`, whose `foldComp` sees the step as an opaque
  function, so a lookup stops there. Only their empty-row variants are a
  `foldComp` with known clauses, and those still forward with `callD` (the
  Divergence form), not the plain `Call`. Stage B's and C's recogniser of
  forwards must take `callD … Total …` too, or the backends must
  specialise `foldCompD` at `Total`.
- `effect-state.sw`'s `Store.keep` (`put v, k => k ()`) isn't fused, since
  that clause isn't `Done` of a function; there `put` is Tail and `get`
  General.
- Not counted: how many *performs* each class answers at run time (the
  note's stage A measure). That needs a counter in the effect runtime,
  which is a runtime change; stage C's in-place counts give it directly.

## Tickets to file

In order. A first; B and C can run side by side after it; D after C; E
after D; F only if wanted.

1. **Stage A: classify handler clauses** (§2.3). New pass beside
   `crates/rt/src/fusion.rs`, the fold native given clauses and mapping,
   no behaviour change; census over std, `aoc/` and `bench/compare`
   printed by a test. Opus (generated-term shapes, near fusion), 60–90
   min. Tests: unit tests classifying `Parse.runFrom`, `optionalFrom`,
   `attemptFrom`, `labelFrom`, `sectionLineFrom`, `Fail`'s handlers,
   `Each.collect` and the shapes of `examples/extract/effect-state.sw` and
   `effect-handlers.sw`; `task test:one -- state_handlers_run_as_a_loop_where_they_fit`
   (fusion unchanged). Absorbs the recogniser half of SW-2338.
2. **Stage B: SW-2338 rebased on stage A** (forwarding skipped in today's
   loop). Opus, 60–90 min, as SW-2338 states. Tests as SW-2338's.
3. **Stage C: entries, consumer link and in place on the machine, behind
   a flag** (§2.1–2.7). Opus (effect runtime semantics), 90 min. Tests:
   `run_lines_agree_with_the_reference_evaluator` on `effect-state.sw`,
   `effect-handlers.sw`, `effect-runtime.sw` with the flag on and off; a
   new example with a computation constant, a computation in a list
   handled later, a stored resumption resumed under a different handler, a
   handler inside a pure function used in an effectful one, and an
   in-place clause whose outer operation pauses (each against the
   reference evaluator); `effect_differential` default run with the flag
   on. Measure: counts per element on `bench/effect-runtime`.
4. **Stage D: in place in native code; flag on and removed.** Opus (native
   ABI, unwind log, drop order), 90 min. Tests: the native agreement tests
   for effects, `effect_differential`, `crates/rt/tests/effect_runtime.rs`
   with regenerated count expectations. Measure: `task profile:native --
   expressions scan bridge`, with the call-counts build. Then the guide
   paragraph if D3411 is yes (Sonnet, 15 min).
5. **Stage E: bind's closure made only when something pauses; row helpers
   as natives.** Opus (lowering, both backends' agreement), 60–90 min.
   Tests: lowering IR snapshots that mention `bind`, the native agreement
   tests, `bind_of_done_is_a_direct_call`. Measure: `sw_closure` per
   character on `expressions`.
6. **Stage F (optional): open-row state handlers in place**, a soundness
   section first (effect-runtime.md §9.11 B). Opus, 90 min. Measure:
   `bench/native/effects.sw` instructions per `bump`.
