# SW-4665 (every theorem sealed): Fable review

Reviewed: `git diff main...lane/SW-4665` (commits 13d20b913, 9f593d934), 23 Nov 2026.
Branch release binary built in the worktree; main's release binary used for comparison.

## Verdict

**Merge.** No soundness finding, and nothing that needs fixing before the merge. The
kernel change is three small edits on top of the opaque-definition mechanism, and each
only shrinks what unfolds. Six low findings follow, two of them already on `main`.

The soundness set passes against the branch binary
(`examples::soundness_examples_fail_for_the_expected_reason`, 1 passed, 3.2 s).

## Why the kernel part is sound

- `push_def` sets `opaque: theorem`; `declare_def` and `admit_trusted_def` both go
  through it, and `assume` clears it (no body, so nothing to hide). `mark_opaque` only
  ever sets the flag. Nothing else writes it.
- Every reader of a body in `value.rs` goes through `body_seen`/`hidden`
  (`unfold_now`, `is_folded`, `folded_call`, `opens_by_tree`, the over-applied folded
  head); `case_tree` is only reached after `unfold_now`'s `hidden` test or for a native.
  The reference evaluator tests `hidden` at the same two places.
- `hidden(g, t)` is false only while a program runs or when `t` is in the transparency
  set. `transparency` refuses a theorem in a list and filters theorem group-mates out of
  the closure, and every set is built there, so no set holds a theorem. A theorem's own
  group has no bodies while it is checked.
- So a theorem's call is neutral everywhere outside a running program. That removes
  equalities and adds none; the "no escape" rule still holds, as a theorem with a list is
  opaque.
- A kept unfolding (`Value::Call`) records the transparency set it was computed under
  (`value.rs` 307, 337), so nothing computed in one set is reused in another.

## Findings

| # | Severity | Confidence | What | Size |
|---|---|---|---|---|
| 1 | low | high | The theorem half of the folding machinery is now dead, and `docs/core.md` still describes it as live | M |
| 2 | low | high | `docs/core.md` rule 6 says a proof change "can't break another declaration"; two routes remain, one unmentioned there | S |
| 3 | low | high | The "proof is sealed" note also appears where unsealing would not have helped | S |
| 4 | low | medium | `Std.Prop.irrel` is found by name and applied with three explicit arguments, whatever its signature | S |
| 5 | low (on `main` too) | high | In a declaration with an `unfolding` list, the body does not unfold its own local `def` or lifted `match` | M |
| 6 | low (on `main` too) | high | `E-UNKNOWN-NAME` says "`dep` has no equations" when it has two | S |

### 1. Dead theorem folding, and a stale spec paragraph

`value.rs` `folds` is `(def.fold || def.theorem) && !program_running()`. A theorem is now
hidden whenever no program runs, and `hidden` is tested first, so the `def.theorem` half
never decides anything: `folded_call`, `Frame::Unfolding` for theorems, the over-applied
head rule of SW-4642 for theorems, and `STITCHWORT_THEOREM_UNFOLDS` are unreachable for a
theorem.

`docs/core.md`, "Theorems stay folded too", got a leading sentence saying so, but the rest
still reads as current: "the kernel accepts `J m b (viaCase 0 h) ≡ J m b h` this way" is
now false for a theorem `viaCase`. The leading sentence says the rest applies "where its
body is visible", which is nowhere.

Related test gap: `examples/accept/proof-call-against-unfolding.sw` was the example for
SW-4642's path (a call folded by name, compared unfolded). Its lemmas are now `def`s,
which don't fold by name, so it tests ordinary unfolding. The path still serves
dictionaries and `Quot.lift` leaves; I did not check whether another test covers it
there.

Recommend: a follow-up lane (Opus, kernel) that removes the theorem case from `folds`
and what only it reaches, rewrites the paragraph and the G12 row, and adds a dictionary
or `Quot.lift` example for the over-applied folded head if none exists.

### 2. Rule 6 overstates encapsulation

Rule 6 says "changing a proof can't break another declaration". The next paragraph
correctly documents the inert marks as an exception (question 1: yes, accurate; repro
below). A second route is not mentioned: content hashes still cover proofs, so a changed
std proof moves a native's pin (`E-BUILTIN` until repinned, as this lane's three Float
pins show) and every dependent's cache key. That is stage 2 (interface-only hashes).

Repro of the inert leak, `review/r1.sw` in the lane's scratch folder:

```
theorem ignores ∀ (n: Nat) (p: n = n): 0 = 0 := byComputing
theorem uses ∀ (n: Nat) (p: n = n): n = n := p
theorem leakI ∀ (n x: Nat) (p q: n = n):
    J (y e => Nat) x (ignores n p) = J (y e => Nat) x (ignores n q) := byComputing   -- accepted
theorem leakU ∀ (n x: Nat) (p q: n = n):
    J (y e => Nat) x (uses n p) = J (y e => Nat) x (uses n q) := byComputing         -- E-REFL
```

`leakI` is accepted only because `ignores`'s sealed proof doesn't use `p`.

Recommend: in rule 6, "apart from the inert marks (below) and, until stage 2, hashes".

Two smaller elaborator readers of a theorem's body remain, neither affecting what is
accepted by the kernel: `opaque::declined_holding` reads a declined theorem's body to
choose a `rewrite` note, and `matching::same_shifted` (SW-4661, known).

### 3. The sealed note where sealing isn't the cause

`declined_in` names a theorem whenever it heads the proof of a `J` or projection. In

```
theorem e3 ∀ (a b n: Nat) (h: (a = b) ∧ (b = 0)): pick a b n = n := pick.eq.ifTrue a b n h
```

the mismatch carries "Note: `And.left` is a theorem: its proof is sealed, so only its
statement is used", but the `J` is stuck on the variable `h`; an unsealed `And.left`
would be stuck too. True, but it points the reader at the wrong cause. The opaque-`def`
note has the same imprecision. Recommend: leave for now, or give the note only when the
theorem's arguments are closed.

### 4. `Prop.irrel` by name

`equations.rs` `branch_lib` looks up `Std.Prop.irrel` and `Uniq::Irrel` applies it to
`(p, h, h')` all explicit. `DecEq.uniqueEq` beside it reads its binders' implicitness
from the type. If std's signature changes, the generator builds an ill-typed proof; I
did not trace whether that surfaces as a skipped equation or an internal error. A user's
own `Prop.irrel` doesn't interfere (checked: a file declaring a different
`Prop.irrel` still gets the equation from std's).

### 5. Owner doesn't unfold its own helpers (on `main` too)

`docs/core.md`: "a `match` or local definition lifted from a body with a list is opaque
with the same list, and the body unfolds the ones admitted before it". Not so here, on
both binaries (`review/u3.sw`):

```
opaque def two: Nat := 2
theorem t1 ∀ (n: Nat) (b: Bool): (two + n = 2 + n) ∧ (b = b) unfolding two :=
  def helper (m: Nat): Nat := two + m
  let first: helper n = 2 + n := byComputing     -- E-REFL
  ...
```

The note says "add `unfolding t1.helper` after this declaration's signature", which
doesn't parse (`unfolding g.loc` is `E-PARSE`). The same file's `t2` shows it for a
lifted `match`. Not caused by this lane; file a ticket.

### 6. "has no equations" (on `main` too)

For `def dep … := if h: … then (match … with | MkDep => …) else 0`, naming
`dep.eq.ifTrue` gives "`dep` has no equations", while `stitchwort doc dep` lists
`dep.eq.ifTrue.mkDep` and `dep.eq.ifFalse`. The message should say the name isn't one of
them and list them. `doc` also prints the first as `MkDep = MkDep → dep n = …` with no
guard hypothesis shown, which I did not investigate.

## The brief's questions

1. **Routes by which a theorem's body reaches another declaration.** For what the kernel
   accepts: only the inert marks, documented accurately. Probed and sealed: a theorem
   group-mate of an unfolded opaque `def` (`q1.sw`: `viaGroup … unfolding f` stays stuck
   on `t 0`), an arity-0 theorem, a local theorem from outside and from its owner, the
   check-cache replay (`s2.sw`: checked with the cache, then a new declaration added;
   the replayed theorem is sealed), `assume` (no body). Generated `.eq`/`.unfold`
   theorems are theorems and sealed. Not accept/reject: hashes (finding 2) and two
   message or search readers.
2. **`E-UNFOLDING-THEOREM`.** Covers short, namespace-qualified and `Std.`-qualified
   names, any position in the list, on a theorem and on an `opaque def`. A local theorem
   can't be named at all. The elaborator reports a theorem group-mate as
   `E-UNFOLDING-THEOREM` where the kernel alone would say `E-UNFOLDING-GROUP`; harmless.
   I found nothing it refuses that should be accepted: generated lists hold only opaque
   `def`s (`opaque_unfold` skips theorems, `opaque_helper_admitted` now does).
3. **`Uniq::Irrel`.** The statement is right: `f args = branch[h]` for the caller's `h`,
   proved by `J` along `Prop.irrel p h' h`. It is not misleading, but it is weaker than a
   reader may expect: `useAnd a b n = J (x e => Nat) n h.left`, whose right side never
   computes. Asking for `= n` now gives `E-TYPE-MISMATCH` (with finding 3's note) in
   place of `E-NO-EQUATION`. Without std's `Prop.irrel` the old refusal remains.
4. **Hashes.** No collision. A declaration hashes `"def"`, the theorem flag, then
   opacity. A theorem and an otherwise identical `opaque def` differ in the flag. A
   theorem with a list writes `"opaque"`, a count of at least one and the hashes; one
   without writes nothing; there is no written empty list.
5. **Float pins.** Confirmed as far as kernel terms show: `STITCHWORT_DUMP_KERNEL` output
   is byte-identical on main and the branch for `Float.neg`, `negFrom`, `abs`, `sub`,
   `add`, `make`, `isNaN`, `nan`, `flipSignBits`, `clearSignBits`, `isValid`, `ofBits`
   and `Model.addBits`. `flipValid`, `clearValid` and `flipValidFrom` are identical at
   top level too, so the change is deeper in their lifted helpers' proofs. The three
   pins that moved are exactly the ones that reach those two theorems; `Float.add`
   didn't.
6. **`docs/core.md`.** Accurate on the rule, the closure, `assume`, the cache replay and
   the hash. Two corrections: findings 1 and 2.

## For Matt's awareness (inside D3722, no decision needed)

Sealing reaches ordinary-looking code through std's projection lemmas, which are
theorems. Accepted on main, refused on the branch:

```
def pick (a b n: Nat): Nat := if h: (a = b) ∧ (b = 0) then J (x e => Nat) n h.left else 0
theorem concrete: pick 0 0 5 = 5 := byComputing        -- E-REFL: stuck on `And.left`
```

and (`u2.sw`) a `test` of a function that casts along a lemma passes while `byComputing`
on the same closed call fails. Both are the class D3722 accepted and rule K restores.

## Not checked

- Whole std, `aoc/`, `games/rogue` and `tools/fmt` checks, the pin tests and
  `test:hashes` (the verifier's and Overmind's).
- The 150 hash snapshots line by line: I checked that every changed line is a hash and
  that added and removed counts differ only for the edited examples.
- The lifted helpers below `Float.flipValid`/`clearValid` term by term.
- Whether a failed `Prop.irrel` proof is a skip or an internal error (finding 4).

## Tickets to file

- Remove the dead theorem folding and rewrite the spec paragraph; cover the over-applied
  folded head with a dictionary or `Quot.lift` example (Opus, 60 min). Findings 1, 2.
- Body with an `unfolding` list doesn't unfold its own helpers; the note suggests a
  clause that can't be written (Opus, 60 min). Finding 5.
- Sealed note only where the theorem's proof would have computed; `Prop.irrel` binders
  read from its type; "has no equations" message (Sonnet, 45 min). Findings 3, 4, 6.
