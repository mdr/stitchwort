# SW-4485 review: `cases` gaps (records of proofs, plain implications, `and_side`)

Reviewed: commit 9966d3540 (merged as b48634dc9), diffed against its first
parent. Paper review (SW-4509, Opus): code read, nothing built or run.

**Verdict: no findings of substance.** The terms have the right shape, every
new loop is bounded, and the error paths are clean. What follows is a few
small things: two places where the code and docs say slightly different
things, one narrow behaviour change, and some repeated work that could be
cached. None blocks; the first three are cheap to fix.

## What was checked

- **Term shapes and implicits.**
  - `and_side` (crates/elab/src/cases.rs:1573) builds
    `Std.Bool.andLeft {a} {b} h` / `andRight {a} {b} h`, nesting outward
    along the path. `Bool.andLeft ∀ [a b: Bool] (h: (a ∧ b) = True): a = True`
    (crates/elab/src/std/Bool/Bool.sw:26) takes exactly two implicits and one
    explicit, which matches. At each level the implicits are the sides
    `and_sides` gave for the *unfolded* test, while the inner proof's type
    is the parent side as written (a folded call). The kernel joins the two
    by unfolding, as it already does for `auto::take_apart`'s
    `And.left`/`And.right`.
  - The goal is matched by `conv(side, target)`, so the final type
    `side = True` agrees with the goal `target = True` up to conversion.
  - `goal_parts` (cases.rs:1654) evaluates field types in the same
    environment `facts.rs` uses for records of proofs (params, then `Refl`
    for earlier fields; facts.rs:445 and :743). `is_record_of_proofs`
    requires no indices, one constructor and non-dependent `Prop` fields,
    so `Term::ctor(d, 0, proofs)` has the same shape as `byFacts`' record
    proof (facts.rs:772).
  - `apply_to_part` applies only explicit, non-dependent binders, so the
    application `h g1 g2 …` is well formed. Each given is shifted by the
    number of lets, as before.
- **Bounds.**
  - `and_side` decrements its budget once per `&&` taken apart, and each
    `&&` pushes two stack entries. So at most 2·256 + (number of
    hypotheses) nodes are forced, with at most 512 `conv`s.
  - The premise loop takes one premise per explicit Π of the hypothesis's
    type. A `Prop`-valued definition that unfolded forever couldn't pass
    the termination checker, so the loop ends.
  - The record recursion shares `MAX_CONJUNCTS_DEPTH` (16) with the
    conjunction case. All the work runs under the run's evaluation budget
    (`STEPS`).
- **Error paths.** `cx.e.named("Std.Bool.andLeft")` returns `None` when std's
  Bool isn't in scope. It also returns `None` when the name is still
  `Global::Unchecked`, as inside `Std.Bool` itself or in modules checked
  before it. The `let … else` then returns `Ok(None)`, so `cases` carries on
  to its other closers, and nothing reaches the kernel.
  `membership.rs:101` uses the same pattern for `Std.Set`.
- **Hashes.** `and_side` runs only when the parts were cut and no part
  matched, and the record and plain-premise paths only where nothing closed
  before. So a theorem's proof can change only where, before this commit,
  a later step closed a case that the new code now closes earlier. That
  later step was `t` in `cases then t`, `by_parts`, a split, or, for
  `close_by_hypotheses`, `rewrite repeatedly`'s next step and the walk's
  leaf. The lane re-ran the hash_stability prelude and `cases` examples and
  found them unchanged. Projects (aoc, rogue, fmt) have no hash snapshots.
  I accept this residual risk; it isn't a finding.

## Findings, ranked

### 1. The cut flag is set at the depth bound even when nothing is left (low)

Where: crates/elab/src/auto.rs:622.

`take_apart` sets `*cut = true` as soon as `depth > MAX_PART_DEPTH`, before
it checks whether the part at that depth is a conjunction or a test fact.
A plain part at depth 9 (an atom such as `x ≤ y`, reached through eight
`∧`s or readings) counts as "cut". The `MAX_READS` path (auto.rs:651) is
right: it checks `test_fact` first. The docs say otherwise. The doc on
`hypothesis_parts_cut` says "with something left", `Parts` says "with
test facts left unread", and docs/syntax.md (the "Closing a case" bullet)
says "with something left".

Why it matters: correctness is unaffected, since the flag only enables
`and_side`, which can only find proofs. But `and_side` then also runs,
up to its 256-`&&` budget, on contexts that weren't cut. That is wasted
work, plus the small hash risk above, in more places than the docs claim.

Fix: at the depth bound, set `cut` only if the forced `ty` is `And` or
`test_fact(ty)` is `Some`. That costs one `force`, which the next line does
anyway. Or reword the three docs to "stopped at a bound".

### 2. `and_side`'s work is repeated on every failed lookup (low)

Where: `Parts::find` (cases.rs:1548–1557) calls `and_side` afresh on every
miss once `cut` is set.

The parts are computed once per `Parts`, but the `&&` walk isn't. It
repeats:

- in `by_parts_at`, for each part of a conjunction or record goal;
- in `apply_to_part` → `proof_in_scope`, for each premise of each
  implication;
- in `by_hypothesis_part`, at every case node (up to 64 + 256 cases);
- in `rewrite repeatedly`'s `try_close` and the walk's leaf, through
  `close_by_hypotheses`.

Each walk can force 512 nodes and make 512 `conv`s.

Why it matters: the doc1Shape figure (0.46 s) shows it is fine in the
measured case, and the run's `STEPS` budget caps the worst case. But a
large conjunction goal over a cut context pays 256 × (number of parts).
Records widen this: a record of proofs with *w* fields nested *k* deep is
*w^k* leaves, where a conjunction is 2^k. A record that refers to itself
(`{ a: R, b: R }`) hits the depth bound of 16 at 2^16 leaves. That is
pathological, and it existed already for `∧`, but each leaf's miss now
also walks the `&&`s.

Fix: in `Parts`, collect the `&&` leaves lazily, once, as (side value,
path) pairs within the 256 budget. `find` then only runs `conv` over that
list and builds the proof for the match. That makes the forcing and
unfolding happen once per `Parts` and leaves the behaviour the same.

### 3. Multi-premise application drops the partial fact (low, behaviour change)

Where: cases.rs:2643–2660.

Before, `f: a → b → c` with `x: a` added `f x : b → c`. Now, when `y: b`
is also in scope, it adds only `f x y : c`. Suppose the case needed
`b → c` itself, for example as one part of a conjunction goal
`(b → c) ∧ d` that `by_parts` closes by a hypothesis. The old code closed
that case and the new one doesn't. The `known` check also now compares
only the last fact.

Why it matters: it's narrow (a `Π` part inside a conjunction goal, with
the later premise in scope), and nothing in the repo is known to hit it.
But it is a case `cases` closed before and no longer closes, the kind of
narrowing D3688 asks to flag. It concerns a tactic's reach, not a proved
tool's scope, so it isn't Matt's decision. The orchestrator can decide
whether it's worth the fix.

Fix: add each intermediate application too (`f x`, then `f x y`), skipping
any that are already known. Or stop at the first premise whenever the
remaining type is itself wanted. The first is simpler and costs one let
per premise, only on the path that already adds lets.

### 4. The `and_side` budget is shared across hypotheses, and runs out with `return` (very low)

Where: cases.rs:1603.

When the budget reaches 0, `and_side` returns `None` for the whole
search. One long `&&` hypothesis (over 256) that doesn't contain the goal
therefore hides every later hypothesis in `visible` order (latest first).

Why it matters: probably never in practice. It is a deliberate global
bound, but the doc on `AND_SIDES` ("over all the hypotheses") is the only
hint.

Fix: none needed. Optionally, give each hypothesis its own share, or say
in the doc that the latest hypotheses are searched first.

### 5. `goal_parts` duplicates the record-field evaluation in facts.rs (nit)

Where: cases.rs:1654–1670, a third copy of facts.rs:445–450 and :743–748.

Fix: add a `facts::record_field_types(cx, d, args) -> Vec<Value>` helper
and call it from all three. This is a small consolidation ticket.

### 6. Looking up `Std.Bool.andLeft` by its written name (nit)

Where: cases.rs:1577–1582.

`named` resolves the name through the current file's scope. A project that
declared its own `Std.Bool.andLeft` with another type would get a kernel
error instead of an E-CASES. That is far-fetched; the `Std.Set` lookup
does the same.

Fix (optional): register `Bool.andLeft` and `Bool.andRight` as builtins,
as `And.left`/`And.right` are (`Builtin::AndLeft`), or check the found
def's arity.

## Docs

- **docs/guide/10-proofs.md**, the "cases-parts" paragraph (line ~390):
  accurate. "Closed part by part" holds only when each part closes by
  computing, by a hypothesis or by a part of one; the docs/syntax.md bullet
  says so, and the guide's brevity is fine. "Applies each implication once,
  never one to what another gave; a chain of them is `byFacts`" matches
  `apply_to_part`.
- **"When `cases` is slow to fail"** (line 471): the numbers match the code
  (`CASES` 64, `THRIFTY_CASES` 256, `STEPS` 20,000,000). The advice is
  sound.
- **docs/syntax.md**, the "Closing a case" bullet: the bounds quoted (eight
  levels, 64 test facts) match `MAX_PART_DEPTH` and `MAX_READS`. "With
  something left" overstates the depth case (finding 1).
- **docs/syntax.md**, the "Implications whose premise holds" bullet: it
  matches the code, including the `f: a → b`, `g: b → c` non-chaining
  example. It doesn't mention finding 3's dropped partial fact. That needs
  no doc change if finding 3 is fixed.
- **examples/accept/cases-implication-plain.sw** says implications are not
  chained, but no reject example pins that down. A
  `cases-implication-not-chained` reject example would keep the "never
  chained" promise from drifting. Optional.

## Suggested tickets

- Findings 1 and 2 together: tighten the depth-bound `cut` and collect the
  `&&` leaves once per `Parts` (Sonnet, small).
- Finding 3: keep the partial applications in `apply_to_part` (Sonnet,
  small, with an accept example `(b → c) ∧ d`).
- Finding 5: share the record-field types helper between facts.rs and
  cases.rs (DeepSeek, mechanical).
