# SW-3311 / SW-3307 review: one settle retry per body, and settling every type parameter

Reviewer: Opus, 15 Nov 2026. Branch `lane/SW-3311`: 9d9c98ee3 (SW-3311) and
149fa067d (SW-3307), against `main` at c09af4e56. Probes ran on two binaries:

- **BR**: the worktree's release binary, built from the branch head.
- **MAIN**: the main checkout's release binary, which has SW-3305's
  per-call retry.

The probe files are in the review's scratch folder (`sw3311-review/`):

- `w1`–`w4.sw`, each with an `…ok.sw` twin that writes `[t := Nat]`:
  bodies that warn, lift lambdas, have local definitions and holes, and
  pass only through the retry.
- `s.sw`: settling in signatures.
- `h.sw`: SW-3307's error heuristic.
- `l.sw` and `lbad.sw`: non-Parse generic lemmas.
- `a.sw` and `b.sw`: places where knowing `t` early might matter.
- `q.sw`, `v1.sw`, `v2.sw`: `goal --at`.
- `genf.sh`: deep failing chains.
- `probe-pending.patch`: the S1 fix I tried.

The worktree is back to the branch head, and its binary was rebuilt from
it.

## Verdict

**Merge both commits after M1, a small fix.** S1's one-liner is worth
taking in the same pass.

SW-3311 delivers what it claims, for bodies:

- p1b, p2 and p2c are all accepted.
- The failing nested chain is linear in steps.
- A failing body costs at most two elaborations. In practice it costs
  less than MAIN, because MAIN retried per call (reads12: 40.5M steps
  against 56.4M; a broken 2020 day 2 `runsPieces`: 3.6M against 6.8M).
- Restoring state by hand works in every probe: no duplicated or missing
  warnings, goals, branch errors or navigation entries, and the hover
  index matches the unsettled twin exactly.

There are two problems:

- **Signatures aren't retried (M1).** Settling still runs there, so a
  signature that MAIN accepts is now rejected.
- **A stale probe can panic (S1).** `goal --at` panics on retried bodies,
  on MAIN too. SW-3311 restores the probe's steps but not its pending
  context.

SW-3307 is sound and its speed gain stands. Its "a more particular error
beats a type mismatch" rule has a realistic counterexample (S2). A rule
by source position chooses correctly in every case I have. The S3 labels
help in e1 but add noise in the common case (S3).

## Must-fix

**M1. Settling still runs in signatures, which have no retry, so programs
that MAIN accepts are rejected.** `s.sw`:

```
def Wrap (p: Ph Char 0): Prop := 0 = 0
theorem s1: Wrap (ph natSrc 0) := rfl
def s2 (h: Wrap (ph natSrc 0)): Nat := 0
```

- **MAIN:** checks the file. Its per-call retry ran everywhere.
- **BR:** E-TYPE-MISMATCH at `natSrc` in both signatures ("expected
  `() → {Src Char} ?0`").

This needs the same rare shape as p1b, a proof argument whose type
matches only by unfolding, but it is a regression against MAIN and
against the commit's "by construction" claim. The cheapest fix is to set
`no_settling` while signatures (and any other elaboration outside
`with_local_retries`) are elaborated. Settling exists for the speed of
proof bodies, and types are small. Wrapping signature elaboration in
`settle_retried` would also work, but it has more state to put back.
Either way, add `s.sw` as an accept example.

## Should-fix

**S1. `goal --at` (the editor's goal-at-point) panics on a body that
passed through a retry.**

- **Reproducers:** p1b.sw:11:53, w1.sw:11:98, w2.sw:13:62, w3.sw:11:71.
- **Where:** `MetaStore::solution` panics, index out of bounds, from
  `flush_probe`.
- **Not new:** MAIN panics on the same positions, from SW-3305's
  `Snapshot` restores.
- **The LSP** catches the panic, so this is a broken answer rather than a
  crash.

Cause: `goals.probe.pending`, the context of the smallest expression
around the probed position, holds a `Value` with the attempt's
metavariables. Two things fail to clear it:

- `settle_retried` calls `drop_steps_since(0)` but leaves `pending`
  alone. The next attempt's `clear_metas` then prints it against a store
  that has been reset. Even without a panic, `note_probed` mixes the
  stale `ty` and `found` into the new answer when the spans are equal.
- `undo::Snapshot` doesn't save or restore `pending` either. Its module
  doc lists "a probe's steps", but not the pending context. That is why
  w2.sw (a local definition, so `local_retries` loops) still panics with
  the one-liner: an undone plan attempt inside the first iteration leaves
  a stale `pending`.

Fix, in two parts:

1. In `settle_retried`, add `goals.probe.pending = None` next to
   `drop_steps_since(0)`. That is `probe-pending.patch`. With it, p1b, w1
   and w3 answer correctly, for example `expected () → {Src Nat} Nat`.
2. In `undo::Snapshot`, take and restore `probe.pending` (clone the
   `Option`).

Part 1 belongs in this lane. Part 2 could be its own small ticket, since
it is older than this work.

**S2. SW-3307's rule (`settled_error_first`: a non-mismatch error without
settling beats a settled type mismatch) blames the wrong argument in a
realistic shape.** `h.sw`:

```
theorem lam2 ∀ (p: () → {Src t} a) (f: t → Nat) (n: Nat): Pt t n := rfl   -- Pt uses t
theorem h2: Pt Rec 0 := lam2 natSrc (r => r.count) 0
```

- **MAIN** (and BR's settled attempt) blames `natSrc`: "expected
  `() → {Src Rec} ?0`". That is the slip.
- **BR** gives the unsettled attempt's "`Nat` has no field or function
  `count`" at the lambda. It is caused by the wrong parser, so it sends
  the reader to correct code.

The Parse version is a wrong parser followed by a `readsMap` or
`runsBind` lambda that reads a field.

A rule by source position chooses correctly in every case I have:

> Give the error that comes first in the source. On a tie, or when one
> contains the other, give the settled one.

| Case | Settled error | Unsettled error | Rule picks |
|---|---|---|---|
| reads-nested-binds-unknown-field | `rfl`, line 50 | the field, line 49 | unsettled, correct |
| h2 | `natSrc` | the lambda | settled, correct |
| e1, g8, m5 | first | later | settled, as now |
| g2, r1 | inside | the whole call | settled, as now |

Elaboration runs mostly left to right, so an error triggered later is
more often a consequence of an earlier wrong inference. Keep the
open-goals exception as it is. Recommendation: change. It's a message
choice, so the orchestrator's call; worth a small ticket if not done in
this lane.

**S3. The two S3 labels help in e1 but add noise to the common
wrong-argument error, which SW-3307 now makes common outside Parse.**

`lbad.sw` m5 passes `(3: Nat)` where the goal is about `Int`:

```
theorem m5 (h: (3: Int) ∈ [3]): (3: Int) ∈ List.append [3] [] := List.memAppendLeft (3: Nat) [3] [] h
```

- **BR's primary error** is right: "expected `Int`, but this has type
  `Nat`" at `(3: Nat)`. MAIN blamed `h` with an unfolded type.
- **The added labels.** BR then adds "`a` was taken from this call's
  expected type" over the whole call, and "without type arguments taken
  from expected types, the error is here instead: expected `3 = 3 ∨
  Void`, but this has type `3 ∈ [3]`" at `h`. That second message is
  obscure, and it marks a correct argument.
- **g8** (`settle-from-expected-wrong-row`) is the same: it marks the
  correct `5`.
- **Rendering.** Three overlapping labels on one line draw as
  `──┬┬───┬`, which is hard to read.

Recommendations, all the orchestrator's call:

- **Keep where `t` came from, as a plain Note with the value:** "`a` was
  taken as `Int` from the expected type `3 ∈ List.append [3] []`". That
  carries most of e1's value: it explains why `{Src Char}` is expected
  and invites unfolding the goal.
- **Drop the "error is here instead" label**, or show it only when the
  unsettled error's position comes *before* the settled one (S2's rule).
  When it comes after, it is usually a consequence (g8, m5), not a second
  slip. e1 then loses its pointer to `True`. That is a fair price, since
  e1 needs a goal head that ignores its type parameter, which no std or
  AoC code has.
- If the label is kept, reword it without the internal term: "if `t`
  isn't taken from the expected type, checking fails here instead: …".

**The open-goals exception: keep.** In settle-from-expected-retried and
w3, the body is unfinished, not wrong, and showing the goal is right.

**The settled error by default: keep.** It is the better error in g2, g8,
r1, m5 and h1.

## Nits

**N1.** In `lib.rs`, `settled_error_first` and `settle_note` were
inserted between `mentions_ability`'s doc comment and the function. The
two lines "Whether a row in `expr` mentions ability `name`…" now open
`settled_error_first`'s doc, and `mentions_ability` has none. Move them
back.

**N2.** When both attempts fail and the settled error is given, the
navigation types, goals and probe are the unsettled attempt's. So in e1
the editor's goal at `natSrc` says `expected () → {Src Nat} Nat`, while
the error says it expected `{Src Char}`. That is acceptable, but worth
one sentence in `settle_retried`'s doc. The alternative is to keep the
first attempt's presentation data and drop the second's, which costs
more bookkeeping.

**N3.** `reads-weaken-over-map-implicits` no longer exercises SW-1528's
"`p` wasn't worked out" note at the call. Check that another reject
example still covers that note, or add one, for example a
`readsWeaken` whose first proof leaves `p` open for a reason other than
the value type.

**N4.** `Decl::settled` collects calls from speculative attempts that
were later undone. That only causes a retry that wasn't needed, and the
"innermost settled call around `e`" lookup could pick an undone call's
span. Harmless; one line in the field's doc would do.

**N5.** `preadmit` admits a local definition from the settled attempt,
which the unsettled attempt then reuses. That's sound, since such a
definition checked on its own and is kernel-checked. Its elaborated
term may differ from what an unsettled elaboration would give, so a hash
could depend on whether the body needed the retry. That only matters for
bodies with local definitions that fail with settling, which today means
none. No action.

## Questions from the brief

**1. State left behind or lost.**

- **Restored correctly:**
  - warnings, including lambdas' (w1: W-REDUNDANT and W-LAMBDA-SHADOW
    once each);
  - goals (w3, w4: each once, also with a local definition and a hole in
    it);
  - branch errors;
  - `failed_mentioned` and `stuck_on_goal`;
  - navigation types. The `--index` refs for w1–w4 are identical to the
    `[t := Nat]` twins, apart from the two refs `[t := Nat]` adds.
- **Lifted helpers** are drafts admitted only by `lift` at the end of a
  successful `body_term`, or by `preadmit`. A body that fails in
  `body_term` leaves none. One whose `finish` fails after `lift` would
  keep its admitted helpers, but that path already exists in
  `local_retries`, and settling failures happen in `body_term`.
- **Cache:** the per-declaration cache stores only the outcome, so
  there's nothing to undo there.
- **Lost:** the probe's pending context (S1), which panics.
- **Nesting:** `with_local_retries` never nests, so `drop_*_since(0)`
  can't clear an outer body's state.

**2. Soundness and wrong rejections.**

- **Accepting wrongly:** nothing. The final comparison and the kernel are
  unchanged.
- **Rejecting what MAIN accepts:** signatures (M1).
- **In bodies,** the second attempt is the pre-SW-3282 checker, so BR
  accepts at least everything that checker accepts.
- **A theoretical gap:** a body that needs settling in one place and is
  hurt by it in another. MAIN would rescue it per call, while BR falls
  back to unsettled everywhere. I looked for a place where settling is
  needed and found none: a dot call on `t`, a constructor, a literal, a
  `match` on a `Char` or an `Option`, and arithmetic all check unsettled
  (`a.sw`, `b.sw`).

**3. Error choices.**

- The settled error by default: keep.
- The open-goals exception: keep.
- SW-3307's rule: change to source order (S2).
- The S3 labels: shrink to a provenance note, and drop or gate the second
  label (S3).

**4. SW-3307.**

- **Hash moves:** accepted as migration cost.
- **reads-weaken-over-map-implicits:** better. The old error was at the
  whole call, with "`p` wasn't worked out" and four notes, and writing
  `p` wouldn't have fixed the proof. The new one points at the map's
  proof and says its spec differs from `Written` at
  `value = { numbers = numbers }` against the `SepBy` conjunction. That
  is the real problem, since `h => h` bridges nothing. The expected side
  still prints unfolded (`∀ (state …)`), which is older than this work.
- **Non-Parse generic lemmas** (`l.sw`): every correct use checks on both
  binaries. The probes were membership lemmas over `List.append` with
  `Int`, `Nat` and a type alias, `subsequenceRefl`, `memRangeFromIntro`,
  and `memUniqueDecEq` with an instance argument. My `l5` fails on both,
  which is my probe's mistake.
- **Errors in `lbad.sw`:** identical on both binaries, except m5. There
  BR's primary error is better (at `(3: Nat)` rather than at `h`), but it
  carries the S3 labels.
- **Reach:** `List.Mem` is a definition, so every `x ∈ xs` lemma is now
  settled. That is broader than Parse and explains the
  `combinationsMem` and `Pair.instFinite` hash moves. Overmind's rolling
  std and AoC checks are the right net for it.

**5. Cost.**

- **Failing deep chain** (`genf.sh`, elaboration time):

  | depth | failing | correct |
  |---|---|---|
  | 200 | 55 ms | |
  | 400 | 212 ms | 99 ms |
  | 800 | 853 ms | 354 ms |

  MAIN at depth 400 takes 16.3 s, and I stopped its run at depth 800
  after two minutes. Steps grow linearly (107k, 214k, 428k). The
  time's quadratic factor shows on the correct chain too, so it isn't
  the retry's.
- **reads12** (reads-nested-binds-unknown-field): 2.46 s and 40.5M steps
  on BR, against 3.53 s and 56.4M on MAIN.
- **2020 day 2 `runsPieces`** with a slip in the middle (`runsText ":"`):
  0.25 s and 3.6M steps on BR, against 0.46 s and 6.8M on MAIN. The
  error is the same on both.
- **Worst case:** a body whose settled attempt fails only at the very
  end, as in reads12, so it costs about twice one elaboration. Even that
  is cheaper than MAIN here. I found nothing pathological for the editor.
