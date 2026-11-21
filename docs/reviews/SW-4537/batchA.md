# SW-4537 batch A: the parser strata (SW-4538)

Opus port lane, 21 November 2026, against `main` at `c93be57a0` (the drawn theorems unchanged
since `110e3e3fc`). Files: [`BatchA.lean`](BatchA.lean), [`BatchA.v`](BatchA.v),
[`batchA.csv`](batchA.csv) (`count_ports.py`, the `pilot.csv` format). Both files compile with
the commands in the note's §5 (Lean 4.35.0; Rocq 9.1.1, Stdlib 9.0.0) **[measured]**: no errors,
no warnings, no `sorry`/`admit`/`Admitted`.

## Per theorem

Lines, statement + proof **[measured, `count_ports.py`]**:

| Theorem | Stratum | Stitchwort | Lean | Rocq |
|---|---|---|---|---|
| `readsBlockResult` | walk 2 | 3 + 13 = 16 | 3 + 19 = 22 | 2 + 10 = 12 |
| `followsParenAtom` | two-run 1 | 10 + 1 = 11 | 8 + 8 = 16 | 7 + 6 = 13 |
| `followsListPatternStep` | two-run 2 | 9 + 8 = 17 | 9 + 6 = 15 | 8 + 6 = 14 |
| `runsBlockOneLine` | readback 1 | 10 + 23 = 33 | 8 + 4 = 12 | 7 + 6 = 13 |
| `openWithin` | readback 2 | 4 + 1 = 5 | 4 + 2 = 6 | 4 + 1 = 5 |
| `unaryHung` | readback 3 | 11 + 145 = 156 | 11 + 66 = 77 | 5 + 57 = 62 |
| `runsWalkHere` | readback 4 | 3 + 9 = 12 | 3 + 3 = 6 | 2 + 4 = 6 |
| **Total** | | **50 + 200 = 250** | **46 + 108 = 154** | **35 + 90 = 125** |

Non-blank characters, statement + proof **[measured]**:

| Theorem | Stitchwort | Lean | Rocq |
|---|---|---|---|
| `readsBlockResult` | 184 + 623 | 178 + 465 | 173 + 433 |
| `followsParenAtom` | 603 + 77 | 536 + 284 | 509 + 307 |
| `followsListPatternStep` | 552 + 329 | 494 + 208 | 474 + 199 |
| `runsBlockOneLine` | 464 + 406 | 419 + 181 | 363 + 186 |
| `openWithin` | 153 + 79 | 154 + 61 | 148 + 62 |
| `unaryHung` | 330 + 4,980 | 330 + 3,189 | 337 + 2,696 |
| `runsWalkHere` | 120 + 127 | 111 + 74 | 106 + 100 |
| **Total** | **2,406 + 6,621 = 9,027** | **2,222 + 4,462 = 6,684** | **2,110 + 3,983 = 6,093** |

On these seven, by lines: Lean 0.62, Rocq 0.50 of Stitchwort; by characters 0.74 and 0.67.
`unaryHung` carries most of it (156 of 250 lines). Per theorem the ratio runs from 0.36
(`runsBlockOneLine`, Lean) to 1.45 (`followsParenAtom`, Lean). These are the batch's own
figures, not an estimate: stage 2 weights them.

Support, non-blank non-comment lines of definitions and axioms in each theorem's section,
uncounted **[measured]**:

| Section | Lean | Rocq |
|---|---|---|
| shared parser prelude | 73 | 43 |
| `readsBlockResult` | 39 | 31 |
| `followsParenAtom` | 37 | 30 |
| `followsListPatternStep` | 39 | 32 (includes `forall2Rev`, std's `List.all2Reverse`, which the Lean prelude has) |
| `runsBlockOneLine` | 38 | 31 |
| `openWithin` | 20 | 13 |
| `unaryHung` | 234 | 186 |
| `runsWalkHere` | 4 | 3 |

`unaryHung`'s support is under the 300-line rule in both, so nothing was set aside on that count.

## Time

Agent clock time, reading included **[measured, `date` at milestones, rounded]**: reading the
note, the theorems and std's `Parse` definitions about 3 minutes; the prelude about 2; the six
short theorems about 5 in both systems together (under a minute each, compile-fix loops
included); `unaryHung` about 9 (reading its definitions and 16 named lemmas 2, Lean 3, Rocq 4).
Whole batch about 17 minutes to two compiling files. No theorem came near the 45-minute rule.

## Set-asides and reserves

None. No reserve was used.

## Mathlib

No `mathlib:` notes. Nothing here wanted it: the proofs are monad runs, case splits, list
equalities and a little arithmetic (`omega`/`lia` on `nest`).

## The prelude

Shared by all seven, uncounted (rule 9). Both systems: the parser is a function from the mark to
`Except String (α × Mark)` (Lean, with a `Monad` instance so `do` works) or `string + A * Mark`
(Rocq, with `bind`/`ret` and a `do` notation, as the pilot). `ReadsAt`, `ReadsIn`, `Gives`,
`Mark.Alike`, `Follows`, `RunsFrom`, `Runs`; `mark`, `left`, `fatal`; std's `followsDone`
(`followsPure`), `followsThen` (`followsBind`), `followsLeft`, and `All2` with its reverse lemma,
all proved. Lean adds five `@[simp]` run lemmas (`pure_run`, `bind_run`, `mark_run`, `left_run`,
`fatal_run`), all `rfl`: they are what makes `simp [defs, ran]` close a run. With core's
`StateT` instead, `simp` turned binds into `<$>` and stalled on `pure = Except.ok`
**[measured, a scratch test]**, so the pilot's StateT style would have needed a longer simp set
per theorem.

Cut from std: the state is the mark alone (`furthest`, `expected`, `messages` only shape error
reports); the mark's `left` and the `Honest` bookkeeping are dropped, as in the pilot. One
consequence: `block` reads its fuel as `rest.length + 1` where std reads `left + 1`; equal under
`Honest`, and the proof only passes the number to `runsBlockLinesOneLine`.

## What made a comparison unfair, either way

- **`byWalking` has no port (against the ports).** `followsParenAtom` is one line in Stitchwort
  (`byWalking [lemmas]`) and 8 in Lean, 6 in Rocq, the only theorem here where both ports are
  longer. Rule 9 allows a monad tactic written once in the prelude; I didn't write one, since
  only two of the seven theorems would use it. A Lean `macro` or Rocq `Ltac` doing
  `apply followsBind; [apply lemma | intros ? ? <-]` over a hint list would take
  `followsParenAtom` to about 2 proof lines and `followsListPatternStep` to about 4
  **[estimated]**. Stage 2 may want to count the two-run stratum with and without that.
- **Dropping `Honest` (for the ports).** Stitchwort's proofs of `runsBlockOneLine` and
  `runsWalkHere` thread `state starts honest` and offsets through std lemmas
  (`runsFromBindAt`, `runsLook`, `runsSame`); the ports run the function directly. Much of
  `runsBlockOneLine`'s 23-to-4 gap is that. The pilot made the same cut.
- **Opaque definitions (neutral to slightly for the ports).** Rule 5: functions used only
  through named lemmas are axioms (`peekIn`, `stops`, `openHead`, `bounds`, the Base relations,
  …). The lemma axioms are true of the real functions; consistency rests on the real
  definitions being a model, which they are, up to the cut-down `Tok`.
- **Cut-down `Expr` in `unaryHung` (slightly for the ports).** Four constructors kept (`Atom`,
  `App`, `Infix`, `Prefix`); Stitchwort's catch-all branches cover about twenty. The ports'
  catch-alls (`try discriminate`, `| _ =>`) would be the same length with the full type, so the
  count is unchanged, but `cases` would make more goals.
- **Rocq's packed statements.** Rocq's statement lines are lower mostly because its users put
  several binders a line (`unaryHung`: 5 lines against 11); characters are level across all
  three (330, 330, 337).
- **Forced renames (rule 3).** Rocq: `rest` (a binder) to `rst`, since `rest` is the mark's
  field; `unary` (a hypothesis) to `isUnary`, since `unary` is the function. Lean kept every
  name.
- **`readsBlockResult`'s Lean proof is longer than Stitchwort's** (19 against 13): Lean's
  `match` on the list plus `rcases` on `BlockRead` spends lines on the two impossible
  disjuncts, which Stitchwort closes with `arithmetic` one-liners. Rocq does it in 10 with
  `try discriminate` and a three-way destruct pattern. An idiomatic but not golfed Lean proof;
  `simp_all`/`omega` could merge a few lines.
- **Recursion.** `unaryHung` calls itself one level down. Lean: the theorem recurses with
  `termination_by depth`; Rocq: `Fixpoint … {struct depth}` proved by tactics, checked at
  `Qed`. Neither needed an induction principle or a duplicated base case.
