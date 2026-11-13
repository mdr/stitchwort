# SW-3059 review: `auto` and `cases` on the reader (Bool as proposition stage 5)

Independent Opus review of `lane/SW-3059` at 68d0a3410 (`git diff
main...HEAD`), 13 Nov 2026. Read-only: no builds or tests were run, so every
behaviour claim below comes from reading the code, and is marked "likely"
where it hasn't been confirmed by a run.

**Verdict:** I found no soundness problem. Every term this lane builds is
checked again by the kernel, and the proof terms for read parts reuse the
`.read` constructions that are already tested (`Found::forward`,
`refutes`, the decision steps). One medium finding is a completeness gap in
`from_rules` that users will hit. The other findings are low. The branch
can be merged once M1 is fixed or filed.

## What was checked

- **Proof terms for each part.** `take_apart` (auto.rs:578) builds
  `And.left/right {p} {q} proof` as before. It reads a part with
  `hypothesis_reads` (reading.rs:1301), which gives one of:
  - `found.forward(h)`, either `Iff.forward (r args) h` or the decision's
    `sound`/`refute`;
  - `refutes(h)` for a leaf at `False`, typed `¬(e = True)`, which is
    `Bool.falseNotTrue (Eq.trans (Eq.sym h) t)` under a binder. The shifts
    are correct.

  Both polarities go through the same code `.read` uses. Each layer re-reads
  the *part's* type: a reading's statement is folded (`statement` runs under
  `folded`), so `(p && inRange 1 x 9) = True` reads its right side through
  `inRange`'s own reading. The new readings.rs test covers this in both glue
  modes. Nested layers are bounded by `MAX_PART_DEPTH` (8). Unfolding is
  bounded per read by `UNFOLD_LIMIT` (8), and the number of reads by
  `MAX_READS` (64).
- **Unknowns.** `cases`' `by_hypothesis_part` (cases.rs:733) compares with
  `conv`, so it solves nothing. `auto`'s `from_hypothesis_parts` uses
  `unify` inside `attempt` (an undo transaction), as `from_conjuncts` did,
  so the risk of solving a metavariable in a hypothesis or the goal is
  unchanged. Readings only add more candidate types. In `from_rules`, every
  binder metavariable must be solved before a term is returned (auto.rs:713
  loop). An unknown that is not a proposition makes the rule fail rather
  than be guessed (auto.rs:692). Failed attempts are rolled back. Nothing
  leaks.
- **Termination and cost.** `from_rules` never recurses. Its cost is
  O(Π-facts × (≤ 8 binders + premises × facts)) unifications, and the inner
  search runs only after a rule's conclusion has unified with the goal.
  Parts per hypothesis are bounded by the depth-8 binary tree, as before.
  See L1 for where the bounded work is repeated.
- **Ordering.** `hypothesis_parts` puts conjunction parts first (a stable
  sort on `read`). `from_rules` runs after `by_contradiction`. So an `auto`
  proof that succeeded before keeps its term. `cases` *does* change terms:
  the part closer runs before the split. This is deliberate, and it shows as
  the `cases-bool` and `cases-argument` hash changes (smaller proofs).
- **Check cache and gluing.** Nothing new feeds the cache key. Readings come
  from declarations, which are already hashed, and glue is already in
  `Options::cache_key()` (SW-1156). `Obligation::written` is threaded
  through all three places that rebuild a `Ctx` (auto.rs:169, 234, 249;
  check.rs:4173). `as_written` guards a misaligned written type with `conv`
  (reading.rs:166), so a stale entry reads nothing instead of reading the
  wrong thing.
- **A reading that fails to check.** `Read::Pending` gives nothing, so
  `auto` and `cases` don't fail because of a hypothesis they didn't need.
  That is the right choice (see L4 for the message).
- **The proposal's §11 note and the docs.** Accurate, with the gaps listed
  under L5.

## Findings

### High

None.

### Medium

**M1. `from_rules` peels every `Π`, including those inside `¬` and `≠`, so
a rule whose conclusion is a negation never applies** (auto.rs:669).

`apply_rule` loops `while let Value::Pi(..) = force(ty)`. `force` unfolds
the glued call `Not p` to `p → Empty`. Take the rule
`h: ∀ (x: Nat) => x ∈ xs → x ≠ 0`:

1. The loop peels `x`, then `x ∈ xs`, then the `x = 0` inside `≠`.
2. The conclusion it is left with is `Empty`.
3. That never unifies with the goal `y ≠ 0`, which `prove` has also forced
   to a `Π`.

**Failure scenario:** in `def f (xs: List Nat) (y: Nat) (m: y ∈ xs) (h: ∀ (x:
Nat) => x ∈ xs → x ≠ 0): Nat := 10 / y`, the division's `[auto: y ≠ 0]`
gives E-AUTO-STUCK. This is the motivating `all` pattern with the most
common side condition. The same happens to any rule concluding in `→`,
`¬` or a `∀`.

**Fix:** before peeling each binder, try `unify(ty, goal)` on the current
`ty` (in an `attempt`). Accept the first arity that matches and whose
remaining unknowns pass the premise check, or stop peeling once the
remaining type has as many leading `Π`s as the goal. Add an example with a
`≠` conclusion.

A related limit that the docs should state: a rule's conclusion is not
read. `xs.all (x => x != 0) = True` reads as `∀ x, x ∈ xs → (x != 0) =
True`, and that conclusion is a test fact. Against a goal `y ≠ 0` it
likely fails even after the fix, because nothing reads `(y != 0) = True`
as `y ≠ 0`. `x < 5` works only because the `Prop` `<` and the test fact
coincide. One option is to read a rule's conclusion when it is a test
fact, through `hypothesis_reads` one layer, after instantiation. Another
is to document the limit. Either should be a follow-up ticket, not a
blocker.

### Low

**L1. The parts are computed eagerly at every `cases` node**
(cases.rs:733, 350). `by_hypothesis_part` runs `hypothesis_parts` over all
visible hypotheses at every node, after the exact match fails. That
includes building `refutes` and `Iff.forward` terms that are never used,
and the split equations that a node adds (`b = False`) each count as a
read. With many splits, that is up to 64 reads per node, times the node
budget.

`auto` likewise builds every part before it tries a single unification.
Each part's work is bounded, so this is a constant factor, not a blow-up.
The cost shows mostly in large `cases` proofs.

**Suggestion:** match lazily, building a part's term only when its type
converts, or cache the parts per node for the hypotheses that the split
didn't touch. Measure first (profile-before-optimising).

**L2. With gluing off, the sides of a hypothesis written as `∧` are read
unfolded** (auto.rs:613-617). Only depth 1 goes through
`term_as_written`. In `h: (inRange 1 x 9 = True) ∧ q`, the left side's
type comes from the unglued `And` arguments, so with `STITCHWORT_GLUE=0`
it reads as `1 ≤ x ∧ x ≤ 9`, not `InRange 1 x 9`, and a goal
`InRange 1 x 9` fails unglued but succeeds glued.

The §11 note already admits the same for `match e:` equations. As a
result, `examples/accept/auto-readings.sw`'s `whenWanted` and `checked`
likely fail with `STITCHWORT_GLUE=0`. No tier runs examples unglued today
(I found no `STITCHWORT_GLUE` in the Taskfile or the flake), so this is
divergence of the comparison switch only.

**Either:** take the sides' written types from the written `∧` term, or
record the limitation in syntax.md's "Which reading", which currently says
the reading "doesn't depend on whether calls are kept folded".

**L3. Whether an older test fact is seen depends on how many test facts
come after it** (auto.rs:609). `MAX_READS` counts every test fact visited,
latest first. That includes leaves at `True`, which give nothing (`b =
True` from a split or a `match`). In a context with more than 64 later
test facts, an older `h: (a && b) = True` is silently ignored, and adding
an unrelated `if` can make an `auto` call fail.

The limit is documented, and 64 is generous. The suggestion is to count
only reads that gave something, or to count leaves at a lower weight.

**L4. A reading that failed to check is skipped with no note**
(reading.rs:1308). `auto` then reports E-AUTO-STUCK with nothing pointing
at the broken reading, while `.read` on the same fact would report the
pending error. The module already has an error, so this matters little.
`waiting_note`-style plumbing could add "`f`'s reading failed to check"
when the goal is what that reading would have given.

**L5. Docs and tests.**
- syntax.md:2041 and the §11 note should say that `from_rules` neither
  reads a conclusion nor matches a conclusion that is `¬`/`→`. Today
  only the second follows from the code, and only until M1 is fixed.
- Nothing covers:
  - a stuck decision's part at `False` (`Decidable.refute`), as in
    `[auto eq: DecEq k] … (h: (a == b) = False)` closing `a ≠ b` by
    `auto`;
  - a `Pending` reading staying quiet;
  - the 64 and 8 limits;
  - `from_rules` declining a rule whose unknown is not a proposition.

  One small accept example and one reject example would pin these.
- The §11 note says "for `e = False` with no reading `¬e`". The term
  is `¬(e = True)`. That is the same thing under "a `Bool` as a
  proposition", and it is the existing convention, so this is fine.

**L6. Elaboration paths that depend on `auto` failing.** Ordering keeps
the terms of `auto` proofs that already succeeded. But an `auto` that used
to fail and now succeeds can change an elaboration choice that tries
`auto` speculatively: `&&`'s fallback to the proposition reading, and
`if a && b` deciding whether a branch takes the proof. The lane couldn't
check `aoc/`, std or rogue. **The verifier should run the hash snapshots
and the project hash checks over std, `aoc/` and rogue for this batch**,
not only the changed examples.

## The lane's open question: should `from_rules` apply `∀` hypotheses as written?

The code already does this: `from_rules` takes every hypothesis
(auto.rs:637), and `auto-readings.sw`'s `given` relies on it. My view is
**yes, keep it**, for three reasons:

- **It is uniform.** §9's point is that a test fact is just another
  spelling of its proposition. If `auto` applied `xs.all p = True` but not
  the `∀` it reads as, `.read`-ing a fact into a `let` would make `auto`
  weaker, which is backwards.
- **It is predictable.** The rule is applied once, its premises must be
  matched exactly, and an unknown that is not a proposition is never
  guessed. It can't loop or search, and the reject example shows the
  boundary.
- **It is sound and cheap.** The kernel checks the term, and the extra
  work happens only on the path that was about to fail.

The one surprise is that the set of hypotheses `auto` can *use* grows to
include function-typed hypotheses. That could matter for speculative
elaboration (L6), so the verifier's hash checks should confirm it.

With M1 fixed, written `∀` facts become more useful than read ones,
because their conclusions are propositions rather than test facts. That
is another reason to file reading a rule's conclusion as the follow-up.
