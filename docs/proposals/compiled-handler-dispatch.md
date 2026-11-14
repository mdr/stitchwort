# Compiled handler dispatch (SW-2498)

SW-2498, 9 Nov 2026, Opus, paper lane (nothing built or run; SW-2493's bytecode dump and scratch
program were read). It designs option 2 of
[SW-2493](../reviews/SW-2493-parse-operation-cost.md) §7.2, and sits beside
[effect-runtime-allocation.md](effect-runtime-allocation.md) (R1-R7; R4 is SW-2464, awaiting
D3437) and [operations-in-place.md](operations-in-place.md) (stages C-D dropped by D3430; whether
to reopen them is SW-2493's first question to Matt). Claims are marked **[measured]** (a counter
or profile, cited), **[read]** (seen in the code or in SW-2493's `--pc-map` dump, file and
function named), **[inferred]** (worked out from measured numbers or the code, not checked by
running anything) or **[estimated]** (a guess at an effect, with the rule given).

## 0. Summary

**The problem.** Every time a handler answers an operation, the runtime reaches the clause through
two partial applications: the handler's step is `handlePlus (A.%elim clause₁ … clauseₙ) forward`,
a partial application of `handlePlus` holding a partial application of the ability's eliminator,
which holds every clause. Applying a partial application copies everything it holds into the call,
so each operation copies all of the handler's clauses (eight for `Std.Parse`) and the eliminator
then drops all but one. For a state handler such as `Parse.runFrom` the clause is then given two
of its four arguments, which builds a third partial application, applied at once to the other two.
And each handler start (`optional`, `attempt`, once per `many` round) builds a closure for every
clause plus the two partial applications. On SW-2493's floor (`Tick`, an operation whose handler
does nothing) this step is about 1.85 K of 5.7 K instructions per operation **[measured, from
shares]**, and widening the ability from one operation to eight adds 0.47 K more **[measured]**.

**The change.** Lower each handler's step to **one dispatch closure**: a function of the operation
and `k` (and, for a fused state handler, of `jump` and the state too) whose body switches on the
operation's `L`/`R` tag and then on its constructor, with each clause's body inlined in its arm.
It captures the handler's free variables once. It is a rewrite in the runtimes' lowering
(`crates/rt`), after the kernel has checked the program: the same term β- and η-reduced, so no
kernel term, hash, proof or elaborator output changes. The effect runtime itself doesn't change
in the first stage: `Handler::Fold { call }` and `Handler::State { call }` hold a function value
today and go on holding one; it is a closure instead of a partial application. The machine and
native code both run the lowered IR, so both get it from one change. The JavaScript backend keeps
its own lowering (a decision below).

**What it should do** (all **[estimated]**, §6): per `Std.Parse` operation answered by `runFrom`,
1.0 to 1.7 K fewer instructions (central 1.4 K); per handler start, 1.5 to 1.9 K fewer. On today's
counts that is **9 to 14% fewer instructions on `expressions` and 11 to 18% on `scan`** (central
about 11.5% and 14.5%), roughly 8 to 13% on `bridge`, and something for every effectful program
in proportion to its operations. Results, messages and the effect runtime's counts are unchanged;
the machine's step counts fall (frames entered), so a step limit is reached later, never sooner.

**Staged** (§7): stage 1 is the lowering change, measured first on SW-2493's scratch loops (go if
`Tick` falls from 5,683 to 5,080 instructions per operation or below, and the eight-operation
ability costs within 100 of `Tick`), then on the comparison programs (kept at 60% of the central
prediction). Two optional stages follow it, each measured alone: the loop calling the dispatch
directly instead of through the generic apply (0.2 to 0.35 K a route), and a state clause's
`jump v s′` compiled as a return instead of an allocated `Jumped` (SW-2493's option 6, which the
dispatch makes simple).

**Against operations in place** (§4.5): complementary, not a replacement. The dispatch removes
1.0 to 1.7 K of an operation's 6.8 to 9.2 K; running in place removes 4 to 6 K. If in place is
reopened, the dispatch is what it would call, and it is what brings in place's residual down to
SW-2493's emulated 0.3 to 3.7 K; without it in place would still pay this 1-1.7 K per operation.
Do the dispatch first either way.

## 1. Today's representation, and why each operation copies the clauses

### 1.1 What `handle` becomes

`handle body with | return v => r | op₁ x, k => c₁ | …` is elaborated
(`crates/elab/src/effects.rs`, `handle`) to **[read]**

```text
foldComp done (handlePlus (A.%elim [params] [r] (x k => c₁) … (x k => cₙ)) forward) body
```

- `A.%elim` is generated with the ability (`crates/elab/src/lib.rs`, after `%res`): one equation
  per operation, `A.%elim c₁ … cₙ (opᵢ x) k = cᵢ x k`. Its runtime arity is n + 2.
- `handlePlus fl fr o k` (`crates/elab/src/std/core/Effect.sw`) sends `L o` to `fl o k` and `R o`
  to `fr o k`. Its runtime arity is 4.
- `forward` is the generated `o k => Call (sigInject m o) (y => k (sigReply m o y))`, or one of
  its partial, bare-row and divergence variants.
- A state handler at the empty row is then rewritten by `crates/rt/src/fusion.rs` (stage 4d):
  each clause becomes `x k jump s => body′`, with tail `k v s′` replaced by `jump v s′`, and the
  step is still `handlePlus (A.%elim c₁′ … cₙ′) forward`. `crates/rt/src/clauses.rs` (stage A)
  and stage B's `Classifier::reperforms` read the same shape.

### 1.2 How it is lowered and run

The runtime's lowering (`crates/rt/src/lower.rs`) makes each clause a closure (consecutive
lambdas are one closure, `Lowering::lambda`), `A.%elim c₁ … cₙ` an `Expr::PartialApp` holding n
values, and `handlePlus … forward` an `Expr::PartialApp` holding that and the forward's closure.
The fold native's handler keeps the result as its `call` (`effect::handler_for`,
`Handler::Fold { call }`; `effect::state_handler`, `Handler::State { call }`) **[read]**.

From SW-2493's `--pc-map` of its scratch program **[read]**:

- `Std.Parse.optional/lambda38`, a handler start: nine `Closure` instructions with no captures
  and one capturing `start` (the clauses, the return clause, the forward), `Pap` of `Parse.%elim`
  over eight, `Pap` of `handlePlus` over two, then the fold native.
- `Std.Effect.handlePlus`: `Switch` on `o`, `Unpack`, `Drop` of the side not taken, `TailApply`
  of the other to `o′, k`.
- `Std.Parse.%elim`: `Switch` on the operation, `Unpack`, **seven `Drop`s** (the clauses not
  taken), `TailApply` of the one taken to `x, k`.
- `Main.runTick/lambda150`, `Tick`'s fused clause: four parameters (`u, k, jump, s`), `s + 1`,
  `TailApply` of `jump`.

### 1.3 One operation's route, step by step

**A fused state handler (`runFrom`, `Tick`).** The loop's `STEP_STATE_CALL`
(`native_abi::sw_eff_step`) applies `call` to `o, k, jump, s` **[read]**:

1. `sw_apply_prepare` on the `handlePlus` partial application: the fast path for a held head
   given at least its arity copies the two held values (two reference-count increments) and
   leaves `jump, s` as an over-application's rest.
2. `handlePlus` runs: switch, unpack `L o′`, drop `forward` (a decrement), tail-apply `fl o′ k`.
3. `sw_apply_prepare` on the `%elim` partial application: copies all n held clauses (n
   increments).
4. `%elim` runs: switch, unpack, n − 1 drops (decrements), tail-apply `cᵢ x k`.
5. The clause is a four-parameter closure given two arguments: `sw_apply_prepare`'s general path
   (it collects the arguments into a vector) builds a **new partial application** holding `x, k`.
6. The over-application's rest, `jump, s`, is applied to that partial application:
   `sw_apply_prepare` again, copying `x, k`, then freeing the partial application.
7. The clause body runs; its `jump v s′` is an apply of `JumpK`, which builds a `Fun::Jumped`.

Steps 1 to 6 exist only to reach the clause. SW-2493 §3.1 put all of steps 1 to 7 at 32.6% of
`Tick`'s 5,680 instructions, **1,850 [measured, from shares, ±30%]**, and counted six
`sw_apply_prepare` calls per operation, three of them on partial applications **[measured]**.
Widening the ability to eight operations costs **470 more [measured]** (6,144 against 5,674):
steps 3 and 4 copy and drop seven more clauses, about fifteen reference-count operations.

**An unfused fold (`optional`'s `stop`, any handler at a non-empty row).** The loop's `STEP_CALL`
applies `call` to `o, k`: steps 1 to 4 as above, with no over-application; the clause takes
exactly `x, k`, so steps 5 and 6 don't happen.

**A forward skipped by stage B** never reaches `call`: the loop reads the fold's forwards table
first (`effect::forwarded`) and hands the operation on (§3).

### 1.4 Why it copies

The partial applications belong to the handler, which every resumption of it shares, so they are
never unique when applied, and `sw_apply_prepare` must clone what they hold rather than move it
**[read]**. The callee then owns its arguments and drops the ones it doesn't use. The copying is
the eval/apply calling convention doing its job on a value that happens to be a dispatch table.
Nothing in it is wrong; the dispatch table is simply the wrong representation for a handler that
the lowering can see whole.

## 2. The design

### 2.1 The rewrite

Wherever the lowering meets the step shape

```text
handlePlus [5 implicit] (A.%elim [implicit…] c₁ … cₙ) forward
```

(the shape `fusion.rs`, `clauses.rs` and stage B already recognise, told apart by erasure masks,
not by how the application is marked), it lowers instead the **dispatch**

```text
o k => case o of
  L o′ => case o′ of          -- A's operations, in declaration order
    op₁ x => c₁ x k           -- β-reduced when c₁ is a literal lambda: body₁[x, k]
    …
    opₙ x => cₙ x k
  R o′ => forward o′ k        -- β-reduced when forward is a literal lambda
```

This is `handlePlus fl fr` η-expanded to its arity and its two equations inlined, then `%elim`
inlined at `fl o′ k` and each literal clause β-reduced. Every clause and the forward occurs once
in the result, so nothing is duplicated: the dispatch is the clauses' code moved into one body.

- **Built from the definitions, not from knowledge of `Plus`.** The two case trees are
  `handlePlus`'s and `A.%elim`'s own run bodies, inlined with the helper `fusion::inline` already
  uses for lifted `match`es. A change to either definition changes the dispatch with it.
- **Captures.** The dispatch closure captures the union of what the clauses and the forward
  read, each variable once. Those are the values the clause closures and partial applications
  hold today, and they live exactly as long (as long as the handler), so no lifetime changes.
- **What isn't a literal lambda** (a clause or forward that some earlier pass made into a
  variable or an application) is bound by a `let` outside the dispatch, so it is still computed
  once, at handler start, and its arm applies it: `opᵢ x => cᵢ x k`. The rewrite never fails; it
  only inlines less.
- **The lowered result** is one `Expr::Closure` of a lambda with two parameters, whose body is two
  `Expr::Match`es. The lowering already lowers case trees inside expressions (`Lowering::case`;
  fusion relies on it for inlined `match`es), so no new IR node is needed.

### 2.2 Fused state handlers: the dispatch takes all four arguments

After fusion every clause is `x k jump s => body′`, and the loop always applies `call` to four
values (`STEP_STATE_CALL`; the machine's `eff_call` for `Handler::State`). The rewrite then
η-expands the dispatch over the two extra parameters:

```text
o k jump s => case o of
  L o′ => case o′ of
    opᵢ x => body′ᵢ[x, k, jump, s]
  R o′ => forward o′ k jump s
```

so a route is one exact-arity apply of a closure: no over-application, no partial application of
the clause (steps 5 and 6 of §1.3 disappear with steps 1 to 4). The η-expansion delays nothing
observable: the generated code between `o, k` and `jump, s` is pure and total (fusion relies on
the same fact to η-expand clauses), and the loop never applies a step's partial result twice. At
the closed empty row the `R` arm is unreachable (`NoOp` has no constructors), as it is today.

An unfused fold whose clauses return a function of a state (`labelWholeFrom`, open-row `IO`
handlers) is not η-expanded: the loop gives its step two arguments, and its arms return the
clause's function of the state as today, one closure in place of today's one partial application.

### 2.3 Where it runs

In `Lowering`, at the point an application spine headed by `handlePlus` with its two runtime
arguments is lowered: that covers the fold natives' `call` argument, `fused.call`, and the steps
that reach the library's `foldCompD` (a divergence-indexed generic body, such as `Fail`'s
handlers) or `foldD` (a partial handler) as an opaque function value. Stage B's
`Classifier::reperforms` and stage A's census read the original term before it is lowered, so
their recognisers are untouched. A new module beside `fusion.rs`
(`crates/rt/src/dispatch.rs`) holds the rewrite and its unit tests.

### 2.4 What a route and a start cost afterwards

| | today | with the dispatch |
|---|---|---|
| fused state route | 3 partial-application applies (2 + n copies, n − 1 drops), 1 partial application built and freed through the general path, 2 dispatch bodies, then the clause | 1 closure apply (exact arity, fast path), 2 switches, the clause |
| fold route | 2 partial-application applies (2 + n copies, n − 1 drops), 2 dispatch bodies, then the clause | 1 closure apply, 2 switches, the clause |
| handler start (`optional`) | 10 closures (9 with no captures) and 2 partial applications | 2 closures: the dispatch (capturing `start`) and the return clause |

The unpacking of `L o′` and of the operation's argument is the same work in both columns.

### 2.5 The machine and native code

Both run the lowered IR (`crates/rt/src/code.rs` for the machine; `crates/native`'s Cranelift
bodies), so stage 1 changes no runtime code: `Handler`, `sw_eff_step`, `sw_apply_prepare`,
`rt_loop` and the machine's loop are as they are. Both runtimes see the same new closure, so the
allocation-trace agreement test (`effect_examples_agree_with_the_machine`) compares like with like.

### 2.6 JavaScript

`crates/js` lowers terms itself and doesn't lower case trees inside expressions (fusion.rs says so;
it supplies no `match` bodies to fusion). Its costs are also different: a partial application in
JS is a closure over its values by reference (`uncurried_call`), so nothing is copied per
operation; the per-operation cost is a few calls that the engine can inline, and the per-start
cost is n + 2 small closures. A JS dispatch would be an emitted `switch` in a closure, with each
clause's body as a nested function: a day's work for an unmeasured gain on a backend outside the
comparison. **Recommendation: leave JS on today's lowering**, as D3410 left it for operations in
place. Its output doesn't change, so the differential tests still check it against the others,
and the playground runs the native runtime compiled to WebAssembly, which gets the dispatch.

### 2.7 Alternatives considered

- **Change the elaborator** to emit a dispatch (a `handleWith` built-in, or the dispatch as a
  term). It changes every handler's kernel term and hash, the kernel spec, and `Std.Parse`'s
  proofs about `optionalFrom` and friends, for nothing the lowering can't do. Rejected.
- **A runtime clause table:** keep n clause closures in a vector, indexed by tag at a route. It
  removes the copies and the partial applications per route but keeps n + 1 closures per start,
  and needs a new `Handler` field and runtime code in both runtimes. The dispatch is simpler and
  saves more.
- **Move instead of copy** when a partial application is unique. A handler's step never is
  (every resumption shares the handler), so this would never fire here.
- **Inline `handlePlus` and `%elim` generically** (an IR inliner for small known functions). The
  partial applications are values held by a handler, not calls at a known site, so a general
  inliner wouldn't see them; the rewrite is that inliner specialised to the one place it matters.

## 3. Forwarding handlers

**Stage B's skip is unchanged.** A forwarding clause (`optional`'s `span`: `k (Parse.span
passes)`) or a recognised generated forward is skipped by the loop before `call` is applied: the
loop reads the fold's forwards table (`effect::forwarded`) and hands on `Call o′ r`. That path
never touches the dispatch, so its cost (1.43 to 2.07 K per level, SW-2493 §3.3: the eager
resumption, a loop left and entered, two more loop steps) is neither better nor worse. Its
remaining costs are R7's and SW-2493's option 5's (fields moved, not copied, out of a unique
resumption), not this note's.

**The skipped clauses' arms stay in the dispatch.** They are reached only when `forwarded` can't
rebuild the operation (`Err` back), which keeps the fallback correct and costs only code size.
The forwards table could become per-tag metadata beside the dispatch instead of a text argument,
but reading it is a few byte loads; not worth a change on its own.

**A forward as a direct jump past the handler.** Three readings, and the answer to each:

1. *Don't call the clause:* that is stage B, built.
2. *Don't enter this fold's loop at all:* the operation would go from the perform straight to
   the next handler out. That needs the perform to know which handler will fold its result,
   which is operations in place's lookup and consumer link (operations-in-place.md §2.2, fact 3:
   a computation is a value, so where it is made isn't always where it is handled). It can't be
   decided locally at one handler, so it isn't part of this design. What the dispatch adds there
   is the per-tag class next to the code: an entry stack could keep "dispatch closure + one class
   byte per operation" instead of digging clause values out of a partial application.
3. *Return the forwarded `Call` from the dispatch arm:* an unskipped Forward clause already does
   exactly that through `bind (Call O DoneK) k`, which R4 turns into `Call O k`. No separate work.

**The generated forward** becomes the dispatch's `R` arm, inlined when it is a literal lambda, so
a handler start no longer builds its closure (`optional/lambda37` today).

## 4. Interactions

### 4.1 R1-R3 (built)

Independent. They removed runtime objects on the loop's side of a route (resumption, pending
cell, skip `Call`); the dispatch removes generated-code work on the clause's side.

### 4.2 R4, SW-2464 (`bind (Call o DoneK) k` is `Call o k`; awaiting D3437)

Independent and additive: R4 acts in `bind`, at the perform; the dispatch acts at the route. They
touch different files (`effect.rs`'s bind leaf against `lower.rs`), so they can be built side by
side. R4 changes effect and step counts; the dispatch changes only machine step counts (§5).

### 4.3 R5, SW-2465 (no resumption for a state handler that can't use `k`)

R5 needs to know that a fused handler's step never mentions `k`. Today that is a per-clause walk
in `clauses.rs`. With the dispatch it is one fact about one lambda: parameter `k` (slot 1) is
never read in the dispatch body, which the lowering's frame already knows. So the dispatch makes
R5's test simpler, and R5's `Erased` for `k` costs the dispatch nothing. If R5 lands first it
keeps its own test; if the dispatch lands first, R5 should use the dispatch's. Sequence R5 after
stage 1, or accept a small merge.

### 4.4 R7, options 4 to 7 of SW-2493

- **R7 (rebuilt forwarded operations) and option 5 (cheaper forwards):** forwards; untouched (§3).
- **Option 4 (capture-free lambdas built once):** overlaps at handler start. If option 4 lands
  first, a start's nine capture-free clause closures already cost nothing, and the dispatch's
  start saving falls from 1.5-1.9 K to about 0.4-0.6 K (the two partial applications); conversely
  a dispatch with no captures (`runFrom`'s, a handler over constants) becomes a constant under
  option 4. Measure each alone; don't add their estimates.
- **Option 6 (a jump without an object):** the dispatch makes it simple. In a fused dispatch the
  `jump` parameter is the runtime's `JumpK` by construction, and fusion only ever puts it in tail
  position applied to two values, so the lowering can compile `jump v s′` as returning the pair
  (written to the context, with a marker result) rather than as an apply that allocates a
  `Fun::Jumped` for `sw_state_step` to take apart. That is stage 3 (§7). Without the dispatch the
  `jump` is a parameter of each separately applied clause closure and the same reasoning has to be
  made per clause, through the partial applications.
- **Option 7 (a smaller `State`):** unrelated.

### 4.5 Operations in place (D3430; reopening is SW-2493's open question)

- **Not redundant.** The dispatch takes 1.0-1.7 K off an operation that costs 6.8-9.2 K at
  `runFrom`; the floor's other 4-5 K (the perform's cells, the `Bind`, three loop steps, the
  resumption, `Done`, the continuation's apply) is untouched. Running in place removes those.
- **It makes in place cheaper and simpler.** In place calls the target's clause from the perform
  with an `InPlaceK` for `k` (operations-in-place.md §2.5). With the dispatch that call is
  `dispatch o InPlaceK jump s`: one exact-arity call. Without it, the call goes through the same
  three partial applications as today, and in place's residual per operation keeps this note's
  1.0-1.7 K, which is why SW-2493 §7.1 gives in place's saving as 4 K at the low end (today's
  dispatch) and 6 K at the high end (this one). An in-place entry (§2.1 there) could hold the
  dispatch and a class byte per operation instead of each clause's value.
- **So:** if D3430 is reopened, do this first (smaller, low risk, and its per-route saving carries
  over to in place's direct call); if it stays closed, this stands alone.

## 5. What stays identical, and what changes

| | changes? |
|---|---|
| Results, output, error messages | no |
| Kernel terms, content hashes, proofs, std sources, the elaborator's output | no: the rewrite is in `crates/rt`'s lowering, after checking |
| The check cache | no format or key change: entries hold elaboration results and are keyed by the compiler build's fingerprint, which any compiler change already moves |
| Effect counts (`EffectCounts`: loop steps, pushes, pops, routes, resumes, binds, jumps, forwards) | no: the loop does exactly what it did |
| The effect runtime's objects (`Made`: resumptions, cells, `Jumped`, handlers) | no |
| Closures and partial applications built, `sw_apply_prepare` calls | fewer (the point) |
| **Machine steps** (frames entered) | **fewer: two per route (`handlePlus`'s and `%elim`'s frames).** Where a step limit applies it is reached later, never sooner. Matt's to confirm (§8), as D3412 and D3437 did for stage B and R4 |
| Allocation traces | change, identically in the machine and native code |
| IR snapshots, `--pc-map` and profiles | change: lowering snapshots that contain a handler are regenerated; a profile attributes all of a handler's clauses to one lambda (named after the handler, `…/dispatch`, so `dev/profile_top.py` groups stay readable) |
| JavaScript | no (§2.6) |

## 6. Estimates

**Per route, `Tick` (one clause), [estimated from measured shares]:** of §1.3's 1,850 (±30%), what
stays is the clause and its `JumpK` apply and `Jumped` (about 450-500, from SW-2493's per-object
and per-apply costs) plus the new closure apply (about 250-330, one `sw_apply_prepare` fast path).
That leaves **0.6 to 1.4 K saved (central 1.0 K)**. An itemised count of steps 1 to 6 (three
fast-path applies at about 300, one general-path apply with a vector at about 400, about twelve
reference-count operations, two short bodies) gives about 1.5 K before the new apply, the upper
part of that range.

**Per route at `runFrom` (eight clauses):** the same plus the measured width, 0.47 K: **1.0 to
1.7 K (central 1.4 K)**.

**Per fold route** (`optional`'s `stop`; no clause partial application): steps 1 to 4 and the
width less the new apply: **0.6 to 1.1 K**.

**Per handler start** (`optional`, `attempt`): eight capture-free closures fewer at 159 each
**[measured, SW-2493 §7.4]**, 1.27 K, plus two partial applications at about 200-300 each
**[estimated]**: **1.5 to 1.9 K**.

**The programs** (counts from SW-2493 §5, full size; routes split as state routes = routed less
`stop`s, which route to `optional`):

| | count | unit | expressions G | count | scan G |
|---|---:|---:|---:|---:|---:|
| state routes (`runFrom`) | 13.55 M | 1.0-1.7 K | 13.6-23.0 | 22.43 M | 22.4-38.1 |
| fold routes (`stop` at `optional`) | 1.41 M | 0.6-1.1 K | 0.8-1.6 | 3.82 M | 2.3-4.2 |
| handler starts | 4.75 M | 1.5-1.9 K | 7.1-9.0 | 4.10 M | 6.2-7.8 |
| **total** | | | **21.5-33.6 (9.0-14.1% of 237.75)** | | **30.9-50.1 (11.1-17.9% of 279.33)** |

Central: about **-11.5% on expressions and -14.5% on scan**, a little above SW-2493 §7.2's -9 to
-12% and -11 to -14%, because that estimate folded the eight-clause width into its 0.9-1.2 K per
route and didn't count the fused clause's partial application (step 5).

**Others, rougher:** `bridge` (6.69 M routes and 1.20 M starts in effect-runtime-allocation.md
§4.1, of 102.1 G after R3): 8.5 to 13.7 G, **about 8-13%**. `matcher` (1.15 M routes,
`labelWhole`'s unfused clauses gain only steps 1-4): about 1-2%. Programs without handlers:
nothing. All of these are **[estimated]**; none was built.

The saving in G doesn't depend on R4 or R5 (different work), so as those land it becomes a larger
share of a smaller total. Option 4 (capture-free closures as constants) overlaps the start row
(§4.4).

## 7. Staged plan

Each stage is one lane, measured alone before and after on the same machine, with builds made the
same way (lane worktree, kache: effect-runtime-allocation.md §4.1 found a 3% offset between kache
and non-kache builds of the same source). The rule, as D3435's and effect-runtime-allocation.md's:
**kept if it delivers at least 60% of its central prediction in instructions and no comparison
program is over 1% slower**; otherwise not merged, and this note is corrected first.

| Stage | What | Predicted | Go/no-go |
|---|---|---|---|
| 1a | **Spike: the rewrite** (§2.1-2.3), measured on SW-2493's scratch loops (`Ops.sw`, kept in that lane's scratchpad; its shapes are in SW-2493 §9). Opus, about 2 h | `tick` 5,683 → 4,300-5,100 per operation; `eight` − `tick` 470 → under 100; an `optional` round (`optLoop`, 23,446) −3.5 to −5.3 K (its start plus `mark` and `next` at `runFrom`) | go if `tick` ≤ 5,080 (60% of the central 1.0 K) and `eight` − `tick` ≤ 100; else stop and report what the profile shows |
| 1b | **The same, finished:** unit tests, snapshots, both runtimes' agreement, `bench:compare` on expressions, scan, matcher, bridge | −11.5% / −14.5% (central) | kept at −6.9% expressions and −8.7% scan; nothing over 1% slower |
| 2 (optional) | **The loop calls the dispatch directly:** the handler keeps the closure's code pointer, resolved once at start, and `rt_loop` (and the machine's loop) calls it at `STEP_CALL`/`STEP_STATE_CALL` instead of going through `sw_apply_prepare`. Opus (`rt_loop`'s Cranelift), about 1.5 h | 0.2-0.35 K per route: expressions 3.0-5.2 G (1.3-2.2%), scan 5.3-9.2 G (1.9-3.3%) | 60% of central |
| 3 (optional) | **A jump as a return** (§4.4, SW-2493's option 6 on the dispatch): `jump v s′` in a fused dispatch writes the pair to the context and returns a marker; `sw_state_step` reads it; no `JumpK` apply, no `Jumped`. Opus, about 2 h | 0.4-0.55 K per state route (SW-2493 §7.6): −2.3 to −3.1% / −3.2 to −4.4%; less if R5's recycled `Jumped` lands first | 60% of central |

Stage 1a and 1b are one lane with a stop after 1a's measurement (minutes, on the scratch loops,
before any test or snapshot work). Stage 1 can run beside R4 (different files); R5 after stage 1
or with a small merge (§4.3); stage 3 after R5's decision, since both remove the `Jumped`.

**Tests for stage 1** (targeted, as CLAUDE.md's budget asks): new unit tests in
`crates/rt/src/dispatch.rs` lowering a one-operation and an eight-operation handler (one closure,
no `PartialApp` of `handlePlus`), a fused state handler (four parameters), a handler whose clauses
capture different variables (the union, once each), a handler under `foldCompD` and under `foldD`,
and a step whose clause isn't a literal lambda (the `let` fallback); `task test:one --
state_handlers_run_as_a_loop_where_they_fit`; the effect examples' run lines against the
reference evaluator and `effect_examples_agree_with_the_machine`; regenerated lowering snapshots;
`effect-forwarding.sw` (stage B still skips). Multi-shot and stored resumptions (`Each.collect`)
need no new test: the handler object and its resumptions are as they were.

## Prior art (SW-2525)

SW-2525, 9 Nov 2026, Opus, paper lane (nothing built or run). The question: how do other
implementations of effect handlers get from a performed operation to the right clause, what does
that cost per operation and per handler start, and is §2's rewrite standard? Resumption
allocation is out of scope: effect-runtime-allocation.md's Sources section and §2.7 already cover
it (Xie and Leijen 2021, Sivaramakrishnan et al. 2021). Labels: **[lit]** a paper or official
document, named; **[read]** source code, with repository, commit or tag and file (the commit
hashes are in the references below); **[inferred]** my reading of what that code costs, not
measured; **[from memory]** not re-checked for this note.

### Verdict

**This is standard practice, built with a technique that has other names; it is not new.** Two
things are being compared.

1. **The end state: a handler is one function that matches on the operation and runs the clause
   body in the matching arm.** OCaml 5.3's compiler emits exactly this for `effect` cases, with
   reperform as the fallthrough. Eff's OCaml runtime keeps a handler's operation clauses as one
   function of the effect. In fused-effects a handler's `alg` is a case on `L`/`R`, then on the
   operation, with the forward in the `R` arm: our `handlePlus` then `%elim`, already inlined.
   In `eff` a handler is a single function of the operation. Effekt and Koka keep one code entry
   per operation instead: a static table of code pointers (Effekt) or a record of clause
   closures (Koka), indexed by the operation. In every case a route costs one indirect call and
   a load or a switch, whatever the number of clauses. **None of them copies the other clauses
   on a route.** Our partial applications of `handlePlus` and `%elim` were the outlier.
2. **The way we get there: inlining two small known functions where they are partially
   applied, then β-reducing the literal clauses.** In GHC terms this is specialisation and
   inlining followed by case-of-known-constructor. GHC does it for fused-effects, and the
   library's speed depends on it (its README). Gathering the clauses' captures into one
   environment is what the closure-optimisation literature calls *closure sharing*. Effekt's
   LLVM backend does the same for a handler object: one environment for all its clauses. We
   need the rewrite only because the kernel's term for a handler is in eliminator form
   (`%elim c₁ … cₙ`), and §2.7 rightly keeps the kernel term as it is. The other compilers
   start from a surface `match` or a record and never build the partial applications.

**Prior art doesn't change the design or the D3440 recommendation** (finish stage 1b). It does
suggest one change of staging, a follow-up and a pointer for later (end of this section). No
system does better on the route *from a known handler to its clause* than one indirect call and
a switch or table load. The systems that are faster per operation get there by different
means: they don't reach a handler at run time at all (Eff's and Effekt's specialisation, GHC's
inlining of fused-effects), or they reach it without walking intermediate handlers (Koka's
evidence, `eff`'s targets vector). Both are operations-in-place territory (§4.5, D3430), and the
dispatch is what either would call.

### System by system

**OCaml 5.** A deep handler is three functions, `retc`, `exnc` and `effc`, stored in the
fiber's handler block by `caml_alloc_stack` **[read: ocaml 5.2.0 `stdlib/effect.ml` 71-88,
`runtime/fiber.c` 194-196]**. `perform` is `caml_perform` in assembly. It switches to the parent
fiber, loads the handler block's `handle_effect` and calls it with `caml_apply3` (effect,
continuation, last fiber), with no search beyond the immediate parent **[read: 5.2.0
`runtime/amd64.S` 1104-1150]**. Since 5.3 (`#12309`, `#13158`, "syntax support for deep effect
handlers") the compiler translates `match e with … | effect E x, k -> c` into `effc` as **one
function `eff k ktail => match eff with …`**, the clause bodies compiled into its arms, and
`Reperform` as the match's failure action, so an operation this handler doesn't name is passed
to the next fiber out **[read: 5.3.0 `lambda/translcore.ml` `transl_handler` 1192-1246;
`lambda/matching.ml` `for_handler` 4086-4089]**. Effects are extensible variants, so that match
is a chain of pointer comparisons against each constructor in turn, linear in the number of
clauses **[read: `matching.ml` `combine_constructor`, `Cstr_extension` case, 3200-3240]**.
Through the library API (`Effect.Deep.match_with`, the only form before 5.3), the user's
`effc` returns `Some (fun k -> …)`, so each operation also builds an option and a closure, and
a wrapper closure calls it **[read: `effect.ml` 79-88; the allocation is inferred]**. Per
operation: one continuation object (`caml_perform`'s "freshly allocated continuation"), two
stack switches, one call of `effc`, an if-chain, and per unhandled level a reperform up one
fiber. Per handler start: a fiber (a stack segment) and the three closures. **What carries
over:** the 5.3 change is the same move as ours. OCaml replaced "find a closure for this
operation, then call it" (an option and a closure per operation) with one generated function
that has the clauses inline. Our closed, numbered tags make our `Switch` cheaper than OCaml's
comparison chain.

**Koka.** A handler is a struct with one clause per operation, in the effect's declared order;
each clause is a `Clause1(fn(marker, ev, x) …)` wrapping a function **[read: koka `d23ee7cd`
`lib/std/core/hnd.kk` 63-80, 566-567]**. Evidence `Ev(htag, marker, hnd, hevv)` is found by
index in the evidence vector held in the context. The index is a constant when the effect row
is known; otherwise `kk_evv_index` searches the sorted vector **[read: `hnd.kk` 131-132, 197-203;
`lib/std/core/inline/hnd.h` 64-74; `hnd.c` 76-87]**. A perform is `@perform1(ev, select-op, x)`:
match the evidence, project the clause out of the handler with the field selector `select-op`
(a fixed offset), and call it **[read: `hnd.kk` 575-578]**. The type checker picks the clause
wrapper from the operation's kind: `fun` and `val` become `clause-tail` (run in place under the
handler's evidence vector, no resumption); `ctl` becomes `clause-control` (yield to the
handler's prompt and capture `k`); `final ctl` becomes `clause-never` **[read:
`src/Type/Infer.hs` 951-967; `hnd.kk` 651-670]**. A `clause-tail` whose body performs no
operations is simplified to `clause-tail-noop`, which skips even swapping the evidence vector:
a perform is then a field load and a direct call **[read: `src/Core/Simplify.hs` 453-455;
`hnd.kk` 666-667]**. Reference counting (Perceus) dups a field when a match binds it and the
body uses it, and nothing else, so selecting one clause out of n costs a constant few
reference-count operations, independent of n **[lit: Reinking, Xie, de Moura, Leijen, PLDI
2021, §2, from memory; inferred for this code, generated C not read]**. A clause closure with no
free variables is a static object whose dup and drop do nothing **[read: `kklib/include/kklib.h`
1390-1397]**. Per handler start: the handler struct, one closure per clause that captures
something, the `Ev`, and a new evidence vector **[inferred]**. **What carries over:** the
table-of-clauses alternative (§2.7) with its two flaws removed: selecting a clause copies only
that clause, and capture-free clauses cost nothing to build. Koka's per-operation speed comes
from evidence (no search, no walk through handlers in between) and from in-place `fun` clauses,
not from how a clause is selected.

**Effekt.** A handler is an object implementing the effect's interface, passed to its users as
a capability, so a perform is a method call on a known value with no search
**[lit: Schuster, Brachthäuser, Ostermann, ICFP 2020]**. In the LLVM backend `New` with n
clauses compiles to **one environment holding the union of the clauses' free variables plus a
static, global vtable of n code pointers**. `Invoke` takes the vtable and the environment out of
the object, loads the code pointer at the operation's index and calls it with the environment.
Each clause's code loads ("consumes") only the free variables it uses **[read: effekt
`e472427c` `effekt/shared/src/main/scala/effekt/generator/llvm/Transformer.scala` 197-238]**.
Operations are numbered by their position in the interface **[read:
`effekt/machine/Transformer.scala` 572-576]**. When the object is known where it is invoked, the
core normaliser replaces `Invoke` of a `New` by the selected operation's body, β-reduced
(subject to an inlining policy). The machine transformer treats an `Invoke` of a known object
that survives to it as an internal error ("Method call to known object should have been
reduced") **[read: `core/optimizer/Normalizer.scala` 291-300; `machine/Transformer.scala`
319-320]**. The ICFP 2020 paper goes further: for a typed subset, a staged translation leaves
"no handler-related abstractions or applications" **[lit: abstract, via the authors' page]**.
Per operation: one indirect call through a table, plus a reference-count share of the object
and of the variables the clause uses **[inferred from the code above]**. Per handler start: one
allocation, since the vtable is static. **What carries over:** this is the closest relative of
our dispatch: one shared environment captured once, and code per operation. A static table of
code pointers and our `Switch` cost about the same, since the operation's tag must be read
either way and Cranelift can lower a dense switch to a jump table. Static specialisation needs
lexically scoped handlers, which Stitchwort doesn't have (operations-in-place.md §4).

**Eff (Pretnar et al.).** The OCaml-targeting runtime represents a computation as `Value` or
`Call (eff, arg, k)`. A handler's operation clauses are **a single polymorphic function
`effect_clauses : eff -> arg -> (res -> b) -> b`**, a match on the effect, and the generic
handler applies `h.effect_clauses eff` and then the result to `arg` and the continuation
**[read: eff `b3d241a2` `ocamlHeader/ocamlHeader.ml` 1-32]**. The newer backend emits OCaml 5
handlers: one `match` with an `effect` case per clause **[read:
`src/05-backends/ocaml-handlers/translate.ml` 43-60]**. Eff's speed comes from the optimiser,
which rewrites `handle c with h` by the shape of `c`. A `Call` of an operation the handler
handles becomes the clause, β-reduced with the argument and the (handled) continuation; a
`Call` it doesn't handle stays a `Call`; handlers are pushed through `let`, `match` and `bind`.
Recursive functions are specialised to the handler around them **[read:
`src/04-optimizer/optimizer.ml` `handle_computation` 272-349, specialisation 419-517; lit:
Karachalias, Koprivec, Pretnar, Schrijvers, OOPSLA 2021, which reports that this removes most
handler overhead]**. **What carries over:** the end state of "handler known at the perform"
(next subsection, (c)). The runtime representation, one function of the effect, is our dispatch
again.

**Haskell libraries.** *fused-effects:* effects are combined with `data (f :+: g) = L … | R …`.
A carrier's `alg` matches on `L Get`, `L (Put s)` and `R other`, the last threading the
operation to the next carrier. The strict state carrier is literally
`StateC $ \s -> case sig of L Get -> …; L (Put s) -> …; R other -> thread …` **[read:
fused-effects `3f2d942d` `src/Control/Effect/Sum.hs` 25-27;
`src/Control/Carrier/State/Strict.hs` 122-127]**: our fused state dispatch (§2.2), down to the
state parameter. `send` is `alg … (inj sig) …` **[read: `src/Control/Algebra.hs` 138-140]**, and
the README credits its speed ("approximately on par with `mtl`") to GHC inlining the carriers'
instances **[lit: README, "Fusion"]**. Once specialised, case-of-known-constructor removes the
`L`/`R` and the operation at the perform site. *polysemy:* a `Union` holds an index (`ElemOf`)
and the operation, and each interpreter's `decomp` tests whether the index is 0, otherwise
decrements it and forwards **[read: polysemy `f0e312d2` `src/Polysemy/Internal/Union.hs` 65-70,
150-174, 280-285]**. That is `handlePlus`'s `L`/`R` test with an integer for the nesting, and
the interpreter the user writes is again one function over the operation. *eff (Alexis King):*
a `Handler eff` is one function of the operation. All handlers in scope are cached in an
immutable "targets vector" indexed by the effect's position in the row, so `send` is "a
constant-time operation, regardless of the number of effects": index, then call. The vector is
rebuilt at each `handle` and when a continuation is restored **[read: eff `8c4df4bf`
`eff/src/Control/Effect/Internal.hs` 340-386, 397-398, 537-538]**. Control operations use the
delimited-continuation primops of GHC proposal #313 **[lit: eff README]**. Its README makes the
point that matters for us: libraries that rely on specialisation degrade in real programs,
where "GHC compiles most effect-polymorphic code via dictionary passing, not specialization"
**[lit: eff README, line 9]**. *Freer monads* (Kiselyov and Ishii 2015) use the same
open-union index **[from memory]**. **What carries over:** our `Plus`/`L`/`R` encoding is
fused-effects' and polysemy's. Their compiled best case is our dispatch, produced by GHC's
general inliner; we get it with a rule at the one place it applies. `eff`'s caution matches §2's
choice to rewrite at the handler (always possible) rather than to depend on specialising
perform sites (only sometimes possible).

**Others.** *Multicore OCaml*, before 5.0, had the same `effect` syntax and representation as
5.3 **[from memory]**. *Links* (generalised continuations) and *Frank* look up clauses by
operation label at run time in interpreters; neither is a performance design
(operations-in-place.md §4) **[from memory]**. *Lean* has no handlers: `EStateM` is a
state-passing function, inlined, so an "operation" is a call **[from memory]**: fusion.rs's end
state, not a dispatch technique. *Defunctionalisation* (Reynolds 1972) and MLton's
flow-directed closure conversion (Cejtin, Jagannathan, Weeks, ESOP 2000) replace a call of an
unknown function by a switch on a tag over known code **[from memory]**. Our dispatch is
already that form: the operation's constructor is the tag, and the clauses are the known
code. *Closure sharing* (Keep, Hearn, Dybvig, "Optimizing Closures in O(0) Time", Scheme
Workshop 2012) merges closures that live equally long into one shared closure **[from
memory]**. Our n clause closures and the forward, all owned by the handler, are exactly that
case.

### At a glance

| System | Operation to clause | Per route, beyond the call | Per handler start |
|---|---|---|---|
| Stitchwort before (§1.3) | 2-3 partial-application applies, then the clause | n + 2 copies, n − 1 drops, a partial application built (fused) | n + 1 closures, 2 partial applications |
| **Stitchwort dispatch** (§2, measured below) | one closure apply, 2 switches | the closure's reference, the captures the arm reads | 2 closures (dispatch, return) |
| OCaml 5.3 syntax | `caml_apply3` of `effc`, an if-chain | continuation object, 2 stack switches | a fiber, 3 closures |
| OCaml `Effect.Deep` API | as above, plus a call of the returned closure | also an option and a closure | a fiber, 3 closures, a wrapper |
| Koka | evidence at an index, field load, call | ~2-3 dups/drops, constant in n [inferred] | struct, a closure per capturing clause, `Ev`, evidence vector |
| Effekt (LLVM) | vtable load at the operation's index, call | share of the object and the used variables | 1 object (vtable static) |
| Eff, optimised | none when the handler is known: clause inlined | — | — |
| fused-effects, specialised | none: case-of-known-constructor at the perform site | — | — (carrier is a newtype) |
| `eff` | targets vector at an index, call | — | targets vector rebuilt |

### What prior art suggests, costed for us

**(a) A clause table indexed without copying** (Koka's record, Effekt's vtable). Two versions:

- *Separate clause closures in a table*, selected by tag. This was §2.7's "runtime clause
  table". It is cheap per route in Koka only because Perceus copies the one field it takes and
  capture-free closures are static. With our runtime it needs: a new `Handler` field and table
  code in both runtimes; n + 1 closures per start (until SW-2493's option 4 makes capture-free
  ones constants); and for the fused case a clause applied to `x, k, jump, s` at its own arity,
  so no saving over the dispatch. **Worse than the dispatch on starts, no better per route.
  §2.7's rejection stands.**
- *One shared environment and a static code table* (Effekt). This is the dispatch with a jump
  table in place of the `Switch`: captures held once, one allocation per start. Our lowering
  already gets most of it, since Cranelift chooses jump tables for dense switches. A real
  per-operation entry point would only pay off with stage 2 (the loop calling the code
  directly): the handler could keep one code pointer per tag and skip the switch on `o′`. That
  is worth a few instructions per route against stage 2's 0.2-0.35 K. **Not worth a stage;
  note it in stage 2's lane as an option.**

**(b) Borrowing the handler** (Perceus binds only the fields that are used; Lean's borrowed
parameters; Koka's `^` annotation). After the rewrite our route already copies only what the
taken arm reads. Entering a closure takes a new reference to it as `env` and drops it later
**[read: `crates/rt/src/native_abi.rs`, `sw_apply_prepare`'s doc comment]**, and the arm's body
loads its captures. What borrowing would add is: no increment and decrement of the dispatch
closure per route, and none for captures the arm only reads. That is borrow-inference.md §4.5's
follow-up ("`Apply` borrowing its function value"), not part of that note's B1-B3, since closures
and the effect loop stay owned there (§4.5, §4.6). At about 30 instructions per reference-count
operation (§1.3's 470 for about fifteen), it is roughly 60-100 instructions per route, about 2-3%
of `tick`'s 3,458 after the rewrite **[estimated]**. **Independent of the dispatch and not a
reason to wait for it.** The effect loop's applies of `call` are the place to try it first,
since the loop owns the handler for the whole route. Listed under "Tickets to file", item 6.

**(c) Specialising a known handler where an operation is performed** (Eff's optimiser, Effekt's
normaliser and staging, fused-effects through GHC). This is the biggest win in the literature:
the route disappears, along with the `Call`, the loop step and the resumption. It needs the
handler to be known statically at the perform. Here a computation is a value, and handlers are
dynamic and found by row (operations-in-place.md §2.2, fact 3; §4 on Effekt). Today that holds
only where fusion.rs and specialisation already see a handler and its body together. So it is a
compiler project of its own, closer to SW-2135's specialisation than to this note. **It doesn't
compete with the dispatch:** Eff's rule "handle (Call op x k) with h ⇒ clause_op x k′" needs the
clause body as a term selected by operation. That is exactly what the dispatch's arms are, so
the dispatch is the natural input for it.

**(d) In-place tail-resumptive clauses** (Koka's `clause-tail` and `-noop`, `libhandler`,
`eff`). This is operations in place (operations-in-place.md, D3430 closed its stages C-D). §4.5
already explains why the dispatch helps it: the in-place call is `dispatch o InPlaceK jump s`.
Prior art adds one data point. Koka spends the effort to pick the cheapest clause wrapper by
static analysis (`clause-tail-noop` when the clause performs nothing), the same kind of
per-clause class that fusion.rs and stage B compute. Nothing changes here.

**(e) Reaching the handler without walking the handlers in between** (Koka's evidence index,
`eff`'s targets vector). Not a dispatch question. The stage 1a table below sharpens it, though:
after the rewrite a `Tick` route costs 3,458 instructions and each forwarding handler in between
still adds about 2.1 K. A parser under two `optional`s spends more on getting past them than on
the operation itself. Koka's measured result is that ten unused handlers in between cost
nothing (Xie and Leijen 2021 §5, as quoted in operations-in-place.md §4). This is the cost
D3430's in-place design addressed. The dispatch makes the comparison sharper; it doesn't change
it.

### What this changes

- **Design:** nothing. §2's end state is the one used by OCaml 5.3, Eff's runtime,
  fused-effects (after GHC) and `eff`, and with a jump table in place of a switch, by Effekt.
  §2.7's alternatives hold up against the literature.
- **Staging:** one addition. Stage 2's lane should consider, besides calling the closure's code
  directly, Effekt's per-operation entry (a code pointer per tag beside the handler, skipping
  the switch on `o′`), and keep it only if it measures above noise. The borrowed apply of (b)
  goes to borrow-inference's follow-up list, not into this plan.
- **D3440's recommendation:** unchanged (§8, decision 1: yes). Stage 1a's measured −24.5% and
  −29.1% came from removing a cost no other system pays. Nothing in prior art suggests a better
  end state for the route from a handler to its clause. The bigger wins in the literature are
  different projects ((c), (e)), and the dispatch is the form each of them would call.

### Uncertainties

- Koka's per-route and per-start costs are inferred from `hnd.kk` and the Perceus rules, not
  from generated C. Effekt's are read from the LLVM generator, not from a compiled program. No
  system was benchmarked here; the comparison is of structure, not instruction counts.
- Eff's and Effekt's papers were checked through their abstracts and the authors' pages and
  code, not read in full; claims about their optimisations rest on the code cited.
- Multicore OCaml's pre-5.0 representation, Links, Frank, Lean, MLton, Reynolds, Keep et al. and
  Kiselyov and Ishii are from memory.
- (b)'s 60-100 instructions per route is a rule of thumb from §1.3's measured width, not a
  count of the reference-count operations left in the dispatch.

### References

Papers (also see effect-runtime-allocation.md "Sources" and operations-in-place.md §4):

- K. C. Sivaramakrishnan, Stephen Dolan, Leo White, Tom Kelly, Sadiq Jaffer, Anil Madhavapeddy,
  "Retrofitting Effect Handlers onto OCaml", PLDI 2021,
  [arXiv:2104.00250](https://arxiv.org/abs/2104.00250).
- Ningning Xie, Jonathan Brachthäuser, Daniel Hillerström, Philipp Schuster, Daan Leijen,
  "Effect Handlers, Evidently", ICFP 2020; Ningning Xie, Daan Leijen, "Generalized Evidence
  Passing for Effect Handlers", ICFP 2021
  ([PDF](https://www.microsoft.com/en-us/research/uploads/prod/2021/08/genev-icfp21.pdf)).
- Alex Reinking, Ningning Xie, Leonardo de Moura, Daan Leijen, "Perceus: Garbage Free Reference
  Counting with Reuse", PLDI 2021.
- Philipp Schuster, Jonathan Immanuel Brachthäuser, Klaus Ostermann, "Compiling Effect Handlers
  in Capability-Passing Style", ICFP 2020, doi:10.1145/3408975
  ([page](https://pl.cs.uni-tuebingen.de/publications/schuster20capability/)).
- Georgios Karachalias, Filip Koprivec, Matija Pretnar, Tom Schrijvers, "Efficient Compilation
  of Algebraic Effect Handlers", OOPSLA 2021, doi:10.1145/3485479
  ([SPLASH page](https://2021.splashcon.org/details/splash-2021-oopsla/6/Efficient-Compilation-of-Algebraic-Effect-Handlers)).
- Oleg Kiselyov, Hiromi Ishii, "Freer Monads, More Extensible Effects", Haskell 2015 [from
  memory].
- John C. Reynolds, "Definitional Interpreters for Higher-Order Programming Languages", 1972;
  Henry Cejtin, Suresh Jagannathan, Stephen Weeks, "Flow-Directed Closure Conversion for Typed
  Languages", ESOP 2000; Andrew W. Keep, Alex Hearn, R. Kent Dybvig, "Optimizing Closures in O(0)
  Time", Scheme Workshop 2012 [all from memory].
- GHC proposal #313, delimited continuation primops
  ([PR](https://github.com/ghc-proposals/ghc-proposals/pull/313)).

Source code (paths relative to each repository's root):

- OCaml, tag `5.2.0`: `stdlib/effect.ml`, `runtime/amd64.S`, `runtime/fiber.c`. Tag `5.3.0`:
  `lambda/translcore.ml` (`transl_handler`), `lambda/matching.ml` (`for_handler`,
  `combine_constructor`), `Changes` (#12309, #13158).
- Koka (`koka-lang/koka`), commit `d23ee7cd73737c1da7a7a5fa837a2806facc3d6b` (27 Oct 2026):
  `lib/std/core/hnd.kk`, `lib/std/core/inline/hnd.h`, `lib/std/core/inline/hnd.c`,
  `src/Type/Infer.hs`, `src/Core/Simplify.hs`, `kklib/include/kklib.h`.
- Effekt (`effekt-lang/effekt`), commit `e472427c094a88187a9156f338139d084c4adce8`:
  `effekt/shared/src/main/scala/effekt/core/optimizer/Normalizer.scala`,
  `…/effekt/machine/Transformer.scala`, `…/effekt/generator/llvm/Transformer.scala`.
- Eff (`matijapretnar/eff`), commit `b3d241a26d9f67b09fe8fa37e4afb8f29d50a683`:
  `ocamlHeader/ocamlHeader.ml`, `src/04-optimizer/optimizer.ml`,
  `src/05-backends/ocaml-handlers/translate.ml`.
- fused-effects, commit `3f2d942d701238173923cc066e583ecb91fbdcaf`: `README.md`,
  `src/Control/Algebra.hs`, `src/Control/Effect/Sum.hs`,
  `src/Control/Carrier/State/Strict.hs`.
- polysemy, commit `f0e312d203129f50171e686e100c30fb8bf12455`:
  `src/Polysemy/Internal/Union.hs`.
- eff (`lexi-lambda/eff`), commit `8c4df4bf54faf22456354be18095b14825be5e85`: `README.md`,
  `eff/src/Control/Effect/Internal.hs`.

## 8. Decisions for Matt

For the orchestrator to number.

1. **Build compiled handler dispatch, stage 1, with its measurement stop?** Nothing a user sees
   changes; about 11-15% fewer instructions on the two parsers (estimated), something for every
   program that handles effects, and it is what operations in place would call if reopened.
   **Recommendation: yes, Opus, from this note; stages 2 and 3 only after stage 1's numbers.**
   Prior art (SW-2525, above) leaves this unchanged: the end state is the one OCaml 5.3, Eff,
   fused-effects, `eff` and Effekt use, and no system has a cheaper route from a handler to its
   clause.
2. **May it lower the machine's step counts** (frames entered: two fewer per operation answered),
   so a step limit is reached later, never sooner? Effect counts and results don't change.
   **Recommendation: yes, the same rule as D3412 and D3437.**
3. **Leave the JavaScript backend on today's lowering?** JS copies nothing per operation, so its
   gain would be small and is unmeasured; its output doesn't change; the playground uses the
   native runtime. **Recommendation: leave it, as D3410 did for operations in place.**

## 9. Uncertainties, and what I didn't do

- **Nothing was built or run.** The per-route saving rests on SW-2493's time shares (±30%) and on
  an itemised count; stage 1a's scratch measurement is the first check, and is cheap.
- **Step 5 (the fused clause's partial application through the general path)** is read from the
  bytecode (`Tick.%elim`'s `TailApply` of the clause with two arguments, the clause having four
  parameters) and from `sw_apply_prepare`'s paths, not counted: SW-2493's six applies per
  operation may count it among its three partial applications. The call counts' `ApplyKind`
  histogram on `tick` before and after settles it.
- **Frame size:** the dispatch's frame holds the slots of every arm. If the lowering doesn't reuse
  slots between arms, an eight-clause handler's frame is the sum of its clauses' frames; harmless
  in the machine (frames on the heap), and Cranelift allocates registers per arm, but worth a
  look in 1b.
- **`bridge` and `matcher`** are estimated from stage 0's counts, not SW-2493's model.
- **Not traced:** the divergence-indexed and partial forward variants' arms (they are inlined or
  applied like the plain one, but their bodies weren't read in detail); `translate` handlers,
  which have no clauses and aren't affected.
- **Not covered:** a per-handler dispatch for `Each`'s multi-shot clauses beyond what the general
  rewrite gives (it applies to them unchanged; their cost is elsewhere).

## Tickets to file

1. **Compiled handler dispatch, stage 1** (§7, 1a then 1b): the rewrite in a new
   `crates/rt/src/dispatch.rs`, applied in `lower.rs`; stop after 1a's scratch measurement. Opus,
   2-3 h. Waits for decision 1 (and 2 for the step counts).
2. **Stage 2: the loop calls the dispatch directly.** Opus, 1.5 h. After 1, only if 1 is kept.
3. **Stage 3: a fused dispatch's `jump` as a return** (supersedes SW-2493's option 6 if filed
   separately). Opus, 2 h. After 1 and the R5 decision.
4. **R5's `k` test from the dispatch** (§4.3): a note on SW-2465, not a ticket of its own.
5. **Stage 2's lane also tries a per-operation entry** (prior art (a), Effekt's vtable): a note
   on ticket 2, not a ticket of its own.
6. **The effect loop borrows the handler's `call` when it applies it** (prior art (b);
   borrow-inference.md §10's "`Apply` borrowing its function value", narrowed to the loop):
   about 60-100 instructions a route **[estimated]**. Backlog, after borrow-inference's B1.

## Stage 1a measurement (SW-2507)

SW-2507, 9 Nov 2026, Opus, spike on branch `lane/SW-2507` (not for merging). **Go**: `tick` falls
by 2.2 K per operation (5,671 → 3,458), more than twice §6's central 1.0 K and above its high end,
and the eight-operation ability costs 17 more than `tick` (470 before). On the comparison
programs: **expressions −24.5%, scan −29.1%** in instructions, about twice §6's central estimate.

### The prototype

`crates/rt/src/dispatch.rs`, called from `Lowerer::apply_def` whenever `handlePlus` is applied to
everything but `o` and `k` and its left argument is a saturated-but-two call of a definition (the
ability's `%elim`). It builds the term `o k [jump s] => <handlePlus's case tree>` with
`handlePlus`'s parameters replaced by its arguments, and in each arm that is then a call of the
`%elim`, that call replaced by `%elim`'s case tree with its parameters replaced in turn (the
extra `jump s` pushed into the arms). Each clause and the forward occurs once, in its arm, so the
lowering's `beta` turns `(x k jump s => body) x′ k jump s` into `let`s: no clause closure exists.
A clause or forward that isn't a lambda or a variable is bound by a `let` outside the closure.
A fused state handler's step is told by a flag set while `fused.call` is lowered; it gets the four
parameters. The `--pc-map` dump shows the intended shape **[read]**: `Main.runTick/lambda105` is
one four-parameter closure, `Switch` on `o`, `Unpack`, `Unpack` of the operation, `Nat.add`,
`TailApply` of `jump`; `Std.Parse.optional/lambda24` (a handler start) builds 2 closures where it
built 10 and 2 partial applications.

It covers every `handlePlus` step the lowering meets (fused or not, at any row, in std or the
program). It doesn't cover: unit tests, snapshots, the machine-agreement test beyond `test:lane
AREA=rt`, the divergence-indexed and partial forward variants beyond what the general path gives
(not read), naming the closure `…/dispatch` for profiles, the frame-size question (§9). It is
turned off by `SW_NO_DISPATCH=1` in the compiler's environment, which is how "before" was measured
with the same binary.

### Results

Native, `measure.sh` (I(300000) − I(0)) / 300000, same compiler build with and without
`SW_NO_DISPATCH` **[measured]** (`tick` was 5,686 with the unmodified branch build, matching
SW-2493's 5,683):

| loop | ability, handlers between | before | after | saved |
|---|---|---:|---:|---:|
| `tick x 0` | Tick (1 op), none | 5,671 | 3,458 | 2,213 |
| `tick x 1` | Tick, 1 forwarding (`fwdTick`) | 7,834 | 5,603 | 2,231 |
| `tick x 2` | Tick, 2 forwarding | 9,757 | 7,522 | 2,235 |
| `eight x 0` | Eight (8 ops), none | 6,149 | 3,474 | 2,675 |
| `mark optional 0` | Parse (8 ops) at `runFrom` | 6,802 | 4,355 | 2,447 |
| `mark optional 1` | Parse, under 1 `optional` | 8,983 | 6,497 | 2,486 |
| `mark optional 2` | Parse, under 2 `optional`s | 10,980 | 8,544 | 2,436 |
| `mark attempt 1` | Parse, under 1 `attempt` | 8,983 | 6,498 | 2,485 |
| `mark labelWhole 1` | Parse, under `labelWhole` (unfused fold) | 15,973 | 12,212 | 3,761 |
| `next optional 0` | Parse `next` | 8,930 | 6,255 | 2,675 |
| `note optional 0` | Parse `note` | 8,543 | 5,805 | 2,738 |
| `opt optional 0` | an `optional` round (start + `next`) | 23,506 | 13,798 | 9,708 |
| `fail optional 0` | a failing `optional` round | 42,193 | 25,674 | 16,519 |

`eight` − `tick`: 478 before, **17 after** (go needs ≤ 100). Repeats of a loop vary by
about ±15 (mostly I(0)). Every run's printed result was the same
before and after (twelve loops, small and full N). The forwarding levels cost what they did
(`tick` 2,163 → 2,145 and 1,923 → 1,919 per level; `mark` under `optional` about 2.1 K both): stage
B's skip is untouched, as §3 says.

**Why more than predicted** (call counts, `call-counts` runtime, `tick x 0` and `opt optional 0`
at 100,000 **[measured]**): per `tick` operation `sw_apply_prepare` falls from 6 calls to 2 (the 3
partial applications and the clause closure are gone; what's left is `DoneK` and `JumpK`), and
the one apply-cache miss sent to `sw_apply_prepare` per operation is gone: the loop's apply of the
dispatch takes the cache's code path. So the new closure apply §6 charged 250-330 for costs much
less, and steps 1-6 cost more than the itemised 1.5 K. Per `optional` round: closures built 14 →
6, partial applications 2 → 0, `sw_apply_prepare` 13 → 5.

**One thing worse, to look at in 1b:** `sw_cell_new` rises by one per route (`tick`: 1 → 2 per
operation; `opt`: 8 → 11 per round) and `sw_drop_words` by one. The net is still the table above,
but something that was reused (a freed cell taken by the next allocation, probably the `L o′`
injection or the operation, which `handlePlus` and `%elim` unpacked with their arguments owned)
is now freed later or by the out-of-line drop. Finding it may give a little more.

### Comparison programs

The prototype ran both correctly (`bench:instructions` checks every output against
`expected.txt`). `task bench:instructions -- expressions scan --runs 3`, first with
`SW_NO_DISPATCH=1 … --save sw2507-off`, then `--against sw2507-off`, same `target/bench` build
**[measured]**:

| program | before (median) | after (median) | change | §6 predicted (central, range) |
|---|---:|---:|---:|---|
| expressions | 235.80 G | 177.99 G | **−24.5%** | −11.5% (−9.0 to −14.1%) |
| scan | 263.47 G | 186.92 G | **−29.1%** | −14.5% (−11.1 to −17.9%) |

Spreads 0.01-0.08%. About twice the central prediction on both, consistent with the scratch loops
(per state route 2.2-2.7 K against 1.4 K; per `optional` round 9.7 K against 3.5-5.3 K). Only
instructions were measured, not time; 1b's `bench:compare` should confirm the time follows, and
look at `matcher` and `bridge`, which weren't run here.

### Revised estimate for stage 1b

The prototype is about 200 lines with the wiring; what 1b adds is §7's test list (the six
`dispatch.rs` unit tests, `state_handlers_run_as_a_loop_where_they_fit`, the effect examples'
agreement, `effect-forwarding.sw`), regenerated lowering snapshots, profile naming, the extra cell
above, and `bench:compare` on the four programs. **Estimate: Opus, 2 to 3 h** (as §7 had for the
whole of stage 1, now with 1a done), most of it snapshots and the agreement tests. The `--pc-map`
shapes and the `rt` lane passing suggest no correctness surprises, but the full tiers haven't run.

## Stage 1b results (SW-2511)

SW-2511, 9 Nov 2026, Opus, branch `lane/SW-2511`: the spike finished. Two commits on top of the
cherry-picked spike: the dispatch itself, and a general `Unpack` change that the dispatch made
worth doing (below), measured separately so it can be kept or dropped on its own.

### What changed beyond the spike

- **Shape of the rewrite.** `Dispatch::rewrite` returns the clauses it binds outside the closure
  and the closure separately (`Step`), so the lowering marks the dispatch's own lambda; a fused
  state handler's step is rewritten where fusion produces it (`rewrite_term` on `fused.call`),
  not through a flag that the next `apply_def` consumed.
- **A guard instead of a debug assertion.** The parameters' values are substituted into
  `handlePlus`'s and `%elim`'s case trees; only a variable may be a scrutinee
  (`Term::instantiate` only `debug_assert`s it). The rewrite now checks every parameter the tree
  matches on is given a variable, and otherwise leaves the step on the general path. With today's
  definitions it always is (`o` and the unpacked operation).
- **Profile names.** `ir::Lambda` has a `dispatch` flag (codec format 2 → 3): the printed IR says
  `λN dispatch`, and native symbols are `Owner/dispatchN#code` (`dev/profile_top.py`'s doc says
  so; `--focus Owner` still covers it).
- **`SW_NO_DISPATCH` is gone**; no test needed it.
- **The divergence-indexed and partial forwards** are handled, not left on the general path. Every
  forward the elaborator makes (`effects.rs`, `handle`) is a literal `o k => …` whatever its
  variant (`callD` for a row with a divergence index, `bindD (lift …)` for a partial carrier,
  `lowerIn` for a bare row), so it is β-reduced into the `R` arm like the plain one. The steps
  given to `foldD` and `foldCompD` as values are dispatch closures too (test below).
- **Frame size: the largest arm's, not the sum.** The arms of a lowered `match` reuse each other's
  slots (`Lowerer::mark`/`leave`). Measured on an eight-operation handler whose clauses bind up to
  three locals: 6 slots (two parameters, `o′`, three locals) **[measured]**, where a sum over the
  arms would be about 20 **[estimated]**. Nothing to fix.

### The extra cell and out-of-line drop per route

Found: `Tick.%elim` passed the operation's argument to the clause even when the clause ignored it,
so its `Unpack` of `tick ()` took every field, and native code freed the emptied cell inline into
the cell cache. In the dispatch the clause is inlined, the unused `x` is never bound, and an
`Unpack` that takes only some of a unique cell's fields frees it out of line (`sw_drop_words`),
outside the cache, so the next allocation missed it (`sw_cell_new`). Any `match` arm that ignores a
field of a unique cell paid the same, in any program (`| Cons _ rest => …`).

Fix (second commit): `Unpack` lists every field, the unused ones with register `NO_REG`. A unique
cell drops them (inline reference counts) and the emptied cell is freed inline into the cache, or
kept as a reuse token without `sw_empty_cell`; a shared cell skips them, as before. The machine and
the traced helper (`sw_unpack`) drop them in field order before the cell, which is the order the
cell's own drop used, so allocation traces don't change. On `tick`: `sw_drop_words` 3 → 2 and
`sw_cell_new` 2 → 1 per operation, as before the dispatch **[measured, call-counts runtime]**.

### Measurements

Instructions, `task bench:instructions -- … --runs 3`, same machine, `target/bench` builds: before
on the branch's base (`2cce80c5b`), dispatch alone (first commit), and both **[measured]**:

| program | before | dispatch | change | + `Unpack` | change |
|---|---:|---:|---:|---:|---:|
| expressions | 210.20 G | 160.13 G | −23.82% | 156.70 G | **−25.45%** |
| scan | 238.60 G | 167.85 G | −29.65% | 166.04 G | **−30.41%** |
| bridge | 77.88 G | 62.08 G | −20.29% | 61.36 G | **−21.22%** |
| disk | 60.50 G | 53.28 G | −11.93% | 52.16 G | **−13.79%** |
| matcher | 60.56 G | 58.11 G | −4.05% | 58.21 G | **−3.87%** |
| binary-trees | 20.55 G | 20.54 G | −0.03% | 20.54 G | −0.03% |
| mapops | 12.67 G | 12.66 G | −0.07% | 12.61 G | −0.42% |
| geomean | | | −13.56% | | **−14.38%** |

Spreads 0.00-0.27%. Stage 1b's bar (§7: −6.9% expressions, −8.7% scan, nothing over 1% slower) is
cleared about three times over. `binary-trees` and `mapops` handle no effects. `bridge` and `disk`
are the non-parser effectful programs (state and `IO` handlers); `matcher` routes few operations
(§6 guessed 1-2%).

`task bench:aoc`, all 55 days, every answer checked **[measured]**: geomean **−9.99%** with the
dispatch alone (36 days moved over 3%), **−11.04%** with both (38 days). 22 days fell by more than
10%, the largest 2021/03 −30.6%, 2024/03 −29.8%, 2024/02 −27.1%, 2020/03 −26.8%; the most any day
rose is 2021/17 +0.24% (and 2024/04 +0.05%). Wall time geomean −9.9% (noisy; under 0.3 s for most
days). The `Unpack` change alone (both against dispatch-only) is −1.16% geomean, from −9.8%
(2025/06) to +2.25% (2021/06) and +1.92% (2021/16); not chased.

`tick`'s loop at 300,000 operations, whole-program instructions / N **[measured, includes start-up]**:
5,721 before, 3,542 with the dispatch, 3,340 with both.

### Machine steps

Frames entered fall by two per route, as §5 said (D3440 allowed it): on the machine, `tick`'s
300,000 operations entered 1,500,003 bodies before (`handlePlus`, `Tick.%elim` and the clause each
300,000 times) and 900,002 after **[measured, `stitchwort run --profile`]**. Effect counts, results
and allocation traces in both runtimes are unchanged (the tests below).

### Tests

New in `crates/rt/tests/it/dispatch.rs`, each lowering a program, checking its IR and running it on
the machine: a fused state handler (one closure of four parameters, no captures); eight operations
at `{IO}` (one closure of two, captures `base` and `step` once each, frame 6 slots, forward inlined
in the `R` arm); handlers given to `foldD` and `foldCompD` (with the `callD` forward), at a partial
and a total row; and a clause that isn't a lambda (bound outside, the closure reads it). No
`handlePlus` or `%elim` is applied anywhere in their IR (their definitions are still lowered, since
reachability is computed on the terms before the rewrite; dead code, not called).

Run: `test:lane` rt (66), native (70), js (14); `test:one` effect/handler/resum (80, including
`effect_examples_agree_with_the_machine`, `…_with_rebuilds_checked`, `n4::handler_traces_are_the_same`
and `state_handlers_run_as_a_loop_where_they_fit`); `every_example_lowers` and
`every_shape_runs_at_a_million_elements` (3); the library hash tests (14), unchanged. No snapshot
changed: no lowering snapshot contains a handler, and JS is untouched.

### Not done

- `handlePlus` and each `%elim` are still lowered as globals though nothing calls them: a little
  code size, no run time.
- Stages 2 and 3 (§7) are unchanged by these numbers; with routes now cheaper, their share is
  larger.
