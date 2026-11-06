# Proposal: a `match` on a decision and an `if` that tests its `Bool`

**Status:** draft 1, 6 November 2026. Ticket SW-1694 (from SW-1688), started
under D2518. Nothing built. Open decisions: D2525 to D2527
([§5](#5-decisions-for-matt)). Code references were read at `e0f9d7809`; no
program was run for this note (D2518: read and write only), so everything
about behaviour is read from the source and the SW-1688 commit, not
measured.

## 1. The problem

2021 day 18 has a function with an `if` on a comparison:

```
def split: Number → Option Number
  | Regular value => if 10 ≤ value then Some (Pair (Regular (value / 2)) (Regular ((value + 1) / 2))) else None
  | Pair _ _ => None
```

(`aoc/src/Aoc/Year2021/Day18/Day18.sw:66`). Its proofs used to split on that
`if` by matching on the comparison's *decision*, the value that says yes or no
and carries the proof:

```
  | Regular value, split2, some =>
    match Nat.decLessThan 9 value with
      | Yes _ => rewrite <- Option.someInjective some in omega
      | No _ => Void.exfalso (Option.noneNotSome split2 some)
```

In the `No` arm the hypothesis `some: split (Regular value) = Some split2`
should read `None = Some split2`. Since total division (SW-1640) it doesn't:
it still holds the whole `if`, and the arm fails with `E-TYPE-MISMATCH`
(SW-1688). Nothing in the proof changed. What changed is how the `if` in
`split` is compiled:

- An `if` on a proposition (`10 ≤ value`) is first elaborated with its
  decision, `Decidable.elim (Nat.decLessThan 9 value) (_ => …) (_ => …)`, so
  that the branches can use the proof (`check.rs:5131`, `decided_if`,
  `check.rs:5291`).
- If neither branch uses the proof, `unused_proof_if` (`check.rs:5192`)
  rewrites it as a plain `Bool` test, `Bool.ifThenElse (Nat.leq 10 value) …`:
  the term an `if` on a `Bool` gives, so lemmas stated with a `Bool` test
  (`filter (x => x < k)`) match. For the standard comparisons the `Bool` is the
  comparison itself, not `Decidable.toBool` of the decision
  (`Decision::into_bool` and `comparison`, `bind.rs:184`, `bind.rs:212`;
  SW-206 item 4).

Before SW-1640, `/` took an `auto` proof that the divisor isn't zero, and that
search found its proof under the `if`, so the branches counted as using it and
the `if` kept its decision form. Now they don't, and it becomes a `Bool` test.

A `match` on an expression replaces that expression, by its computed form,
wherever it occurs in the goal and the hypotheses (`matching.rs:10-19`). The
decision `Nat.decLessThan 9 value` computes to `Bool.decTrue (Nat.leq 10
value)` (`Decidable.sw:135`). The old `Decidable.elim` form held exactly that
term; the new `Bool.ifThenElse (Nat.leq 10 value) …` holds only the `Bool`
inside it. So the `match` finds nothing and refines nothing. No warning says
so: `W-MATCH-NOT-FOUND` is given only for a named `match`
(`matching.rs:1509`, the `s.name.is_none()` test), and these were unnamed.

SW-1688 changed the three proofs to match on the `Bool` instead (`match
Nat.leq 10 value with | True … | False …`), and added
`examples/accept/match-bool-if-division.sw`.

**The trap in general.** Whether a proof's `match` on a decision refines an
`if` depends on whether the `if`'s branches use its proof. That is decided far
from the proof, inside the definition, and can change with an edit that has
nothing to do with the proof (dropping an `xs[i]` bound, a library change like
SW-1640).

**The idiom that doesn't have the trap already exists.** A `match` on the
*proposition*, `match h: 10 ≤ value with | True => … | False => …`, is matched
as the `Bool` the `if` reads (`matching.rs:489`, SW-206 item 5), here `Nat.leq
10 value`, and where a decision computes to `Bool.decTrue b` it is matched as
`b` (`matching.rs:505`, `tested_bool` at `matching.rs:571`, D1073). That `b`
occurs in both forms of the `if`: as the `Bool` test, and inside
`Bool.decTrue b` in the decision form, where `Bool.decTrue True` computes to
`Yes rfl` and the `if` computes on. So matching on the condition refines the
`if` whichever way it was compiled. `h: Nat.leq 10 value = True` is the same
proposition as `10 ≤ value` by computation (`Nat.LessEq` is `Nat.leq m n =
True`, `Data.sw:69`), so it can be used as the proof (the example's `big`) and
`omega` reads it. syntax.md already teaches this as the way to split on an
`if` (`docs/syntax.md:1984-1994`), and the proving guide says "a proof follows
a program's `if` by matching on its `Bool`" (`docs/proving-guide.md:366-367`).
Neither says that a match on the *decision* can silently miss.

### How many proofs match on a decision

A grep for `match … Nat.dec…`/`Int.dec…`/`Bool.dec…` in `aoc/`, `std/` and
`examples/` finds about 45 (`grep -rn "match [^w]*\(Nat\|Int\|Ord\|Float\|Bool\)\.dec"`).
The trap concerns only the decisions that compute to `Bool.decTrue b`
(`Nat`, `Int` and `Float` `<` and `≤`, `Ord.byKey`): `Nat.decEq` and the other
`=` decisions are not shortened by `comparison`, so their `Bool` form is
`Decidable.toBool d`, which still holds `d`. That leaves about 30 matches on
`Nat.decLessThan` or `Nat.decLessEq`. Read by hand, they fall in two groups:

- **Case splits for evidence** (most): the arms use the proof and nothing is
  refined, e.g. `sumByPositive` (`aoc/.../Day14/Proofs/Spread.sw:16`),
  `cellSomeInside` (`aoc/.../Day13/Proofs/Picture.sw:57`), 2021 day 11's
  `Parts.sw` and `Cascade.sw`, `Graph/Search.sw:680`.
- **Splitting an `if`** whose branches use the proof, so it is in decision
  form: 2021 day 16's `readGroups` (`decreasing reader.length`, the recursive
  call needs the comparison), matched in `Fields.sw`, `Complete.sw` and
  `Sound.sw` (about ten matches). These hold today, and break the way day 18
  did if a change ever stops the branches using the proof.

All of them check today (the SW-1682 lane's run over every `aoc/` namespace
found no failure but day 18's). So this is about a trap for new proofs and a
latent one in day 16, not about breakage on `main`.

## 2. The options

### (a) Leave the elaborator; document the idiom; warn precisely

Say in syntax.md (beside the D1073 paragraph, `docs/syntax.md:1994`) and in
the proving guide (`docs/proving-guide.md:366`): to split on an `if`, match
on its condition (`match h: 10 ≤ value with | True | False`), which works
whichever form the `if` takes; a match on the decision (`Yes`/`No`) gives
evidence and refines only an `if` whose branches use the proof.

Add a warning for exactly the day 18 shape, say `W-MATCH-DECISION-IF`:
the scrutinee is a decision whose computed form is `Bool.decTrue b` (a sibling
of `tested_bool`); that form occurs in neither the goal nor a hypothesis; and
`b` does occur there as the condition of a `Bool.ifThenElse`. The test is
specific enough to give for unnamed `match`es too. The message names the
hypothesis or goal and the fix:

```
warning[W-MATCH-DECISION-IF]: this `match` on a decision doesn't refine the `if` in `some`
  looked for `Bool.decTrue (Nat.leq 10 value)`
  note: the `if` tests the `Bool` `Nat.leq 10 value` directly, since its branches don't use the proof
  note: match on the condition instead: `match h: 10 ≤ value with | True => … | False => …`
```

As `W-MATCH-NOT-FOUND` does, it should be given also when the arms fail
(`docs/proving-guide.md:372-376`), which is where the user needs it.

- **Soundness:** unchanged; nothing new is elaborated.
- **Proofs that check today:** unchanged. The warning could fire on a
  passing proof that matches a decision for its evidence while a hypothesis
  holds an unrelated `if` on the same comparison. I expect few or none; a lane
  can count them on the days it touches, and the fix is one line.
- **Cost:** small. Detection in `matching.rs` beside `not_found`, where the
  normal forms and the copied hypotheses are already at hand; one reject
  example; two doc paragraphs. About two hours on Sonnet.
- **Learning it:** from the docs, and at the moment it matters from the
  warning, which says what to write.

### (b) Match a `Bool.decTrue b` decision as `b`

Extend D1073 from propositions to decisions: when a decision scrutinee
computes to `Bool.decTrue b`, the `match` generalises `b` and translates the
arms: `Yes p` becomes the `True` arm with `p` bound to the equation `b =
True`, `No r` the `False` arm with `r` built from `b = False`
(`r := h => Bool.falseNotTrue (Eq.trans (Eq.sym e) h)`). `p`'s declared type,
`9 < value`, is `b = True` by computation, since `Bool.decTrue b: Decidable
(b = True)` and the decision has type `Decidable (9 < value)`. A decision form
`if` is refined too, as `Bool.decTrue True` computes to `Yes rfl`.

It can't be done as "generalise both the decision and `b`": the occurrence
test refuses a scrutinee that is part of another (`matching.rs:960-967`), and
the decision's type mentions `b`. Hence the translation.

The catch is in which occurrences of `b` get replaced. The generalisation
replaces every one, and a comparison *proposition* contains `b` once
computed: `spot.y < height dots` is `Nat.leq (Succ spot.y) (height dots) =
True`. So in `cellSomeInside` (`Picture.sw:57`), whose goal is `spot.y <
height dots ∧ …`, the `Yes inY` arm's goal would become `True = True ∧ …`, and
`Both inY inX` would no longer check. Two restrictions:

- **(b1) always:** breaks proofs like `cellSomeInside`, which check today.
- **(b2) only when the decision itself is found nowhere and `b` is found:**
  still breaks `cellSomeInside` (the decision isn't in its goal, `b` is).

So (b) as stated changes proofs that check today, and those failures would be
`E-TYPE-MISMATCH`es in arms that nobody touched.

- **Soundness:** fine; the result is an ordinary `match` on a `Bool`, with
  proofs built from its equation, all checked by the kernel.
- **Cost:** medium (Opus, most of a day): the arm translation in
  `matching::lifted` (`matching.rs:454`), named matches (`d: Nat.decLessThan …
  = Yes p` needs a small std lemma, `Bool.decTrue b = Yes e` for `e: b = True`,
  by cases on `b`; proofs inside `Yes`/`No` are compared irrelevantly,
  `docs/core.md:240`), sub-patterns limited to variables and `_`, and the
  stage 2 as-written search (`matching/as_written.rs`), whose check 2 would
  need to agree with the new target.
- **Learning it:** nothing to learn when it works; when it breaks a goal as
  above, it is a surprise that's hard to trace.

### (c) Keep the decision form of an `if` that a proof matches on

Make `unused_proof_if` keep `Decidable.elim` when some proof later matches on
the decision. Not possible locally: `split` is elaborated, checked, hashed and
cached before and apart from its proofs (often in another file), and its term
is its meaning to the kernel and to every other proof. A definition's term
can't depend on its future readers. The global version, "always keep the
decision form for comparisons", undoes SW-206 item 4: `if` and a `Bool`
argument (`filter (x => x < k)`) would stop giving the same term, and the
proofs that match on the `Bool` today (`match h: a <= b`, AoC 2025 days 2 and
3, `docs/syntax.md:1994`) would stop refining. Rejected.

### (d) Others

- **(d1) A `Bool` form that keeps the decision.** Have `unused_proof_if` write
  `Decidable.toBool (Nat.decLessThan 9 value)` instead of `Nat.leq 10 value`.
  A decision match would then find it, but `toBool (Bool.decTrue b)` is not
  `b` by computation when `b` is stuck, so lemmas and `match`es stated with
  the comparison as a `Bool` stop matching. That's the reason for SW-206
  item 4; rejected for the same reason as (c).
- **(d2) A kernel rule `toBool (decTrue b) ≡ b`.** Would make (d1) harmless,
  but it is a new conversion rule in the kernel for one convenience. Out of
  proportion; rejected.
- **(d3) (b) restricted to `if` conditions.** Generalise `b` only where it is
  the condition of a `Bool.ifThenElse` (in the computed goal and hypothesis
  types), leaving every other `b`, including those inside comparison
  propositions, as it is. The motive abstracts just those positions, so it is
  always well typed (`b` and the new variable are independent elsewhere), and
  those are exactly the positions where the decision form had
  `Decidable.elim (Bool.decTrue b)`. That gives back what the `match` did
  before SW-1640, and `cellSomeInside`'s goal is left alone. It needs a second
  mode for the occurrence test (it replaces all occurrences today,
  `matching.rs:1767`) and the arm translation of (b). As-written search would
  be switched off for this mode at first. Soundness as (b). Cost: (b) plus the
  new mode, about a day on Opus. Proofs that check today: only those that
  match a decision while a hypothesis holds a `Bool` `if` on it and use that
  hypothesis unrefined; I found none by reading, and a whole-AoC run would
  confirm (that needs Matt's OK).

## 3. Comparison

| | Kernel | Proofs that check today | Cost | How users learn it |
|---|---|---|---|---|
| (a) docs + warning | unchanged | unchanged (rare new warning) | ~2 h, Sonnet | docs; the warning names the fix |
| (b1)/(b2) match as `b` | unchanged, all checked | some break (`cellSomeInside`) | ~1 day, Opus | nothing, until it breaks a goal |
| (c) keep decision form | n/a | many break | n/a | rejected |
| (d1)/(d2) | (d2) changes it | many break / n/a | n/a | rejected |
| (d3) `if` conditions only | unchanged, all checked | expected none, to be measured | ~1 day, Opus | nothing to learn |

## 4. Recommendation

Do (a) now. The idiom that never has the trap, `match h: <condition> with |
True | False`, already exists and is already what syntax.md and the proving
guide teach for splitting an `if`; what's missing is saying that a decision
match can miss, and a warning that turns the silent miss into a one-line fix.

Don't build (b). Hold (d3) in the backlog: it removes the trap rather than
explaining it, but at the cost of a second occurrence-test mode in a part of
the elaborator that has had three stages of work this week
(`matching/as_written.rs`). Revisit it if the warning turns up often in new
AoC days, or when 2021 day 16's `readGroups` matches are next edited.
Day 16 and the other existing decision matches don't need migrating: they
check, and the warning would say if one stops.

## 5. Decisions for Matt

- **D2525:** Take option (a): document that a `match` on a decision refines
  only an `if` whose branches use its proof, point to `match h: <condition>
  with | True | False` as the way to split an `if`, and add a warning
  (`W-MATCH-DECISION-IF`) for the day 18 shape, given for unnamed `match`es
  too? **[rec: yes]**
- **D2526:** Reject (b) (match every `Bool.decTrue b` decision as `b`), since
  it would rewrite comparison propositions in goals and break proofs such as
  2021 day 13's `cellSomeInside`; and reject (c), (d1), (d2)? **[rec: yes]**
- **D2527:** File (d3) (refine only `if` conditions) as a backlog ticket, to
  reconsider if the D2525 warning fires often in new proofs, rather than
  building it now? **[rec: yes, backlog]**
