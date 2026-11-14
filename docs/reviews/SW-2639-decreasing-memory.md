# Why a deep `decreasing` recursion uses so much memory while checking

**Ticket:** SW-2639 (fuzz_elab seed 0x25a5, case 4273). **Written by:** Opus, 10 Nov 2026,
from the findings of the Sonnet and Opus lanes on this ticket, plus new hand-written
experiments (below). **Checked against:** `main` at `4a617cdb8`. Measurements use the release
CLI of the main checkout, `check --no-cache`, peak memory from `/usr/bin/time -l`. Each number is
marked **measured** or **estimated**.

## In short

- **The problem.** Checking a proof that makes Stitchwort unfold a `decreasing` function a
  million levels deep takes 3.3 GB of memory before it stops with a clear "recursed too deeply"
  error. The same recursion without `decreasing` takes a seventh of that.
- **The cause.** Each level of a `decreasing` function carries a small proof that it still has
  enough fuel, and that proof is built *from the previous level's proof*. So every level's proof
  stays alive until the recursion ends: a chain of about 3 KB per level.
- **The fix recommended.** Change what the compiler generates for `decreasing` so each level
  checks its fuel afresh with one number comparison, instead of building on the last level's
  proof. Nothing chains, the kernel doesn't change, programs run exactly as before. In a
  hand-written model of the change, memory per level fell from 3.0 KB to 0.8 KB (**measured**).
- **Not recommended:** a memory cap on each check (memory use differs between native and the
  browser, so the same file could pass on one and fail on the other), or leaving it.

**D3474** (number to be confirmed by the orchestrator): change `decreasing`'s generated fuel
helper so that each recursive call decides its bound afresh (`Nat.leq` on the measure and the
fuel) instead of chaining `Nat.leTrans` onto the previous level's proof? It changes the hash of
every `decreasing` definition and nothing a user writes or sees. **[rec: yes, as an ordinary Opus
lane, not urgent: no real program has hit it]**

## 1. The problem

The fuzzer found this definition:

```
def innerN (x: Nat): Nat
    decreasing x
:=
  match x with
    | Zero => 1
    | Succ m => innerN m [decreasing := omega]
```

and asked the checker whether `Succ (innerN 2^128) = Succ (innerN 0)` holds by `rfl`. To answer,
the checker works out `innerN 2^128` step by step, which would take 2^128 levels. It stops
correctly with `E-RESOURCE` ("recursed more deeply than allowed") at the evaluator's limit of
2,000,000 frames, which is 1,000,000 levels, since each level uses two frames. The answer is
right; the cost of reaching it isn't.

| Case (release, `--no-cache`) | Time | Peak memory |
|---|---|---|
| `innerN 2^128`, with `decreasing` | 4.8 s | 3.31 GB |
| the same recursion without `decreasing` (structural) | 0.83 s | 466 MB |
| `innerN 200000`, with `decreasing` (succeeds) | 3.1 s | 744 MB |
| the same, without `decreasing` | 0.32 s | 147 MB |

All **measured** by the earlier lanes. Memory grows in a straight line with depth: about 3.3 KB
per level with `decreasing`, against about 0.2 KB without.

On a laptop, 3.3 GB is slow but survivable. In the browser it isn't: WebAssembly gives a page at
most 4 GB, and browsers often less, so the playground would crash with out-of-memory instead of
showing the error.

## 2. The cause

A `decreasing` function is compiled to a helper that counts down a fuel number `k`, with a proof
`h` that the measure is below the fuel (`crates/elab/src/decreasing.rs`, the module comment, and
`docs/proposals/well-founded-recursion.md`, option B). The kernel only sees ordinary structural
recursion on `k`. Each recursive call `f y` becomes:

```
f.%go k y (Nat.leTrans (Succ (m y)) (m x) k p h)
```

where `p` is the user's proof that the measure went down (`m y < m x`, here from `omega`) and
`h` is this level's `m x < Succ k`. The new proof `Nat.leTrans … p h` *contains* `h`. Since
SW-281, a theorem call stays folded (it isn't computed until something takes it apart), so this
is exactly what's kept: a call node holding `p` and `h`. Level 1,000,000's proof holds level
999,999's, which holds level 999,998's, and so on. Nothing can be freed until the whole
recursion finishes.

**What each link weighs** (from the Opus lane's heap profile, **measured**): the frames
themselves are small, about 192 bytes each with their memo cell. The weight is the chain, about
3 KB per level:

- the `Nat.leTrans` call, 5 arguments, and the `Omega.prove` call behind `p`, 6 arguments. Each
  argument list overflows its inline space and is moved to the heap at a capacity of 8, about
  640 bytes each;
- the omega certificate behind `p` (the numbers and constructors that justify the step), rebuilt
  at every level, about 880 bytes, most of it the same at every level.

**What was tried and didn't reach the goal** (the Opus lane):

- shrinking the memo cell (boxing its kept value): 3.31 to 3.22 GB, reverted;
- right-sized argument lists and sharing the unchanging parts of the certificate: estimated to
  reach about 2 KB per level at best, because the chain itself remains;
- not keeping frames for unshared unfoldings: the recursion then becomes a loop that runs on to
  the 10^10-step budget while the chain keeps growing. Worse;
- unfolding lazily: the comparison needs the result's outermost constructor, which is at the
  bottom of the recursion, so laziness doesn't help; lazy proof arguments would still chain
  through closures (about 800 bytes per level, estimated) and would be a large kernel change.

So shrinking the links can't fix it. Either the chain goes, or a limit stops it sooner.

## 3. The options

### Option 1: a memory cap per check

Stop any one declaration's check with `E-RESOURCE` once it has used, say, 1 GiB.

- **How it would be measured.** A counting wrapper around the memory allocator, adding and
  subtracting each allocation's size. It works the same way in both builds: on native as a
  global allocator, in WebAssembly the same wrapper (the page's own memory size can't be used,
  since WebAssembly memory never shrinks). It costs a little on every allocation (an estimated
  1–3% of checking time).
- **What the error would say.** "Checking `t` used more than 1 GiB of memory; this usually means
  `rfl` or a type is computing something very large. Prove it step by step, or compute less in
  the statement." with the same `E-RESOURCE` code as the frame and step limits.
- **What it would do here.** `innerN 2^128` would stop at about 300,000 levels, in about 1.5 s
  (estimated from the 3.3 KB per level above).
- **Why not.** The frame and step limits are counts, so a file passes or fails the same way
  everywhere. Bytes aren't: pointers are 8 bytes on native and 4 in WebAssembly, so the same
  values take about half the memory in the browser, and allocator rounding differs too. A check
  near the cap could pass in the playground and fail on the command line, and a change to a
  data structure's layout could change which proofs are accepted. A deterministic stand-in
  (counting value nodes the evaluator allocates) avoids that, but needs a counter at every
  allocation site in `value.rs`, and it still only treats the symptom: the chain would still
  cost 3 KB per level up to the cap.

### Option 2: a `decreasing` encoding whose proofs don't chain (recommended)

**Is there one?** The bound each level needs is "`m y` is below the fuel that's left". The fuel
left depends on the whole history of the recursion, not on `y`, so any proof of it built by
reasoning has to start from the previous level's proof. That is why the chain looked
unavoidable. But the bound can also be *checked*: the fuel and the measure are both numbers
there, and the kernel compares numbers natively. A proof obtained by checking mentions only the
two numbers, never the previous level.

So the generated recursive call becomes:

```
match found: Nat.leq (Succ (m y)) k with
  | True  => f.%go k y found                 -- found: m y < k, nothing older in it
  | False => (impossible: p and h together prove Nat.leq (Succ (m y)) k = True)
```

`a < b` is already `Nat.leq (Succ a) b = True` (`docs/core.md`, the arithmetic lemmas), so
`found` is exactly the proof `f.%go` needs, and at run time it's `rfl`. The previous proof `h`
and the user's proof `p` appear only in the impossible branch, which is never taken, so they are
dropped as soon as the comparison returns. Each level holds its own fuel, its own `y` and a
constant-size `rfl`.

**Measured on a hand-written model.** I wrote the helper both ways for the same recursion as
`innerN`, with the user's proof from `omega` computed and passed in at each level, as the real
generated code does (files kept outside the repo; the shape is above):

| 200,000 levels, `rfl` to 1 | Time | Peak memory | Per level |
|---|---|---|---|
| empty file (baseline) | 0.20 s | 80 MB | |
| structural recursion, no proof | 0.28 s | 119 MB | 0.2 KB |
| today's chained shape, `omega` proof | 1.43 s | 671 MB | 3.0 KB |
| fresh check at each level, `omega` proof | 1.72 s | 251 MB | 0.86 KB |
| 400,000 levels, chained | 2.56 s | 1,280 MB | 3.0 KB |
| 400,000 levels, fresh check | 3.40 s | 400 MB | 0.80 KB |

All **measured**. Memory per level falls by about 3.5 times; time is about the same (slightly
higher in the model, because it adds a helper of its own; the real `f.%step` exists already).
With `2^128` in the hand-written model, which has no frame limit to stop it, the chained shape
was at 2.6 GB and still growing when stopped at 60 s, and the fresh-check shape stayed at 85 MB
for the whole 60 s (**measured**).

**What it should do for the fuzz case.** The frame limit still stops `innerN 2^128` at
1,000,000 levels, so the error is unchanged, but at an estimated 0.8–1.2 GB instead of 3.3 GB
(**estimated**: the model's 0.8 KB per level plus the real encoding's second frame). The same
saving applies to every `rfl` or type that computes through a `decreasing` function, at any
depth.

**What changes.**

- Only the generator in `crates/elab/src/decreasing.rs`: `f.%go`'s recursive call (`rec_lam`,
  `glue`), and the generated proofs that go through it (`f.%irrel`, by induction on the fuel,
  gains a case on the comparison whose `False` side is dismissed by the same argument; `f.unfold`
  follows from `%irrel` as now). The lexicographic form already decides `m1 y < m1 x` at each
  call (`lex_parts`), so the generator has done this kind of case before.
- **The kernel doesn't change**, so it can't make anything unsound: a mistake in the generator
  gives a refused definition, never a wrong one.
- **Running programs doesn't change**: `stitchwort run`, tests and JS already run `f.%step`
  directly, with the fuel erased.
- **Hashes** of every `decreasing` definition change, and the hash snapshots move with them
  (migration cost, D2303).
- **Cost while checking**: one native comparison per level. The measure `m y` is already
  computed at each level today, as an argument of the `Nat.leTrans` call, since the evaluator
  computes arguments eagerly (**inferred** from SW-281's notes; worth confirming with a step
  count when it's built).

**Encodings considered and rejected.**

- **Accessibility, built once (Lean's way).** Each level's evidence would be the previous one's
  function applied to `p`; with a native `accLt` it would compute to a fresh closed value, so no
  chain. But the kernel refuses to take apart a proof to produce data (`E-PROP-ELIM`), so it
  needs a kernel change, which the well-founded-recursion note already rejected (its option A).
- **Proofs erased because they're irrelevant.** Stage 1 of proof irrelevance (SW-93) skips
  *inert* proof arguments when comparing, but the evaluator still computes and keeps them, and
  `h` isn't inert anyway (it's passed to `Nat.leTrans`, which takes its proofs apart in its
  impossible cases; **inferred**). Erasing proofs while evaluating would put placeholders into
  values that the elaborator may read back into terms. Much larger, and riskier.
- **Fuel equal to the measure.** The kernel needs the fuel to drop by exactly one each step, and
  a measure can drop by any amount. Restarting from `f y` at each call (as the runtimes do) isn't
  structural, so the kernel can't check it.
- **Thunked proofs** (SW-281's option 1). Still a chain, through closures (about 800 bytes per
  level, estimated by the Opus lane).

**One further step, not part of this.** The user's proof `p` is still computed at every level
and then thrown away (in the model, the `omega` proof accounts for 0.6 s of the 1.43 s: 0.82 s with a one-line proof instead, **measured**). Passing it
unevaluated would save time, not memory, and is SW-281's option 1 again. Only worth doing if
`rfl` through `decreasing` shows up as slow in practice.

### Option 3: leave it

The checker already gives the right error, and in four seconds. No real program recurses a
million levels inside a check: no AoC day is known to have hit it (**not checked** across all days), and big inputs go through `test` and `run`, which don't use the fuel at all. The
cost of leaving it: the fuzzer will keep finding variants of this, the playground can crash on
them, and every `rfl` through `decreasing` keeps paying about 3 KB per level.

## 4. Recommendation

**Option 2.** It removes the cause rather than capping the symptom, keeps every limit a
deterministic count, leaves the kernel and running programs alone, and in a measured model cuts
memory per level from 3.0 to 0.8 KB. It is a contained generator change: an estimated half day
for an Opus lane (the generated proofs are the delicate part). It isn't urgent, so it can wait
behind work with visible benefit.

Not option 1: bytes aren't the same on native and in WebAssembly, so a cap would make acceptance
depend on where a file is checked.

**D3474:** change `decreasing`'s generated fuel helper so each recursive call decides its bound
afresh, instead of chaining onto the previous level's proof? **[rec: yes, as an ordinary Opus
lane at normal priority; no memory cap]**

## 5. Parked speed findings

Found by the Opus lane's heap profile. Each would make checking through `decreasing` a little
faster; with option 2 built they no longer affect peak memory, since the values they waste are
freed at once. Parked with the rest of the speed work (D3465).

1. **Argument lists spill at capacity 8.** A call with 5 or 6 arguments (`Nat.leTrans`,
   `Omega.prove`) overflows its inline space and is moved to a heap list of capacity 8, about
   640 bytes each, where an exact-size list would need about half.
2. **Closed certificate values are rebuilt at every level.** `omega`'s certificate is mostly
   closed terms (constants and constructors that don't mention any variable), about 880 bytes,
   evaluated afresh every time `p` is computed. Evaluating closed terms once and sharing the
   value would save the allocations and the steps.
