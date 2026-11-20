# SW-4341 review: a guard's hypotheses in the form it is written (D3699)

Ticket SW-4343, Opus paper review of `lane/SW-4341` (commit e8d090bf1),
20 Nov 2026. Read only: no builds or tests run.

**Verdict: merge after fixes** (two should-fix items, both small: one doc
paragraph, one example). No blockers. Soundness is not at stake: every
changed term still goes through `kernel::declare_def`, and a refusal there
becomes an equation skip, not an accepted theorem.

## What the change does, as read

- `guard_terms` now also returns `written_bool`: true for
  `Condition::Bool` and `Condition::Conjunction`, false for
  `Condition::Decided` and `if h: P` (equations.rs:4859-4869). It is set by
  which `Condition` variant `logic::condition` produced, so by how the guard
  is written, not by looking at the elaborated `Bool`.
- `probe_row` looks for a decided proposition behind the `Bool` only when
  `!written_bool` (equations.rs:2656), so `xs == []`, `a && b` and chains no
  longer get `prop`.
- `GuardRead::fails_as_bool` / `failed_bool` (equations.rs:940-959) give
  the one rule for how a failed condition is stated. `NotGuard`
  (equations.rs:4708-4725) gives the same terms as before for every
  `GuardRead`; only which guards have `prop` set has changed. `Overlap` with
  a guarded row now ends `c[σ] = False` where `fails_as_bool`, else
  `… → P → Void` as before (equations.rs:4775-4795).
- The eqK walk (equations.rs:7320-7340): a Bool overlap's hypothesis
  applied to the values here is the `= False` fact, used like `NotGuard`'s
  (`ite_step` for `Bool.ifThenElse`, `normal_void` for `Decidable.elim`).
- `induct.rs` `refute`: a Bool tail is not a premise (`premise = 0`); the
  clash path wraps its `Void` in `exfalso [c = False]`. `refute_guard`
  with a tail: no `h` binder, the base of the `J` chain is the split's fact
  itself, and each motive's body is the tail, not `tail → Void`.

## 1. Soundness and trust

No new trusted path. All eqK terms go through `declare_equation` →
`kernel::declare_def` (equations.rs:3379); `f.induct` likewise. A wrong
term built by any of the new branches makes the kernel refuse it, reported
as an equation skip ("the kernel refused the generated proof",
equations.rs:2541-2551). Nothing bypasses the check.

## 2. Statements and index arithmetic

**eqK and induct agree.** Both are built from the same `GuardRead`: the
statement through `fails_as_bool`/`failed_bool`, the induct split's facts
through `guard_side`. I checked each fact against the statement:

- `!dec`, Bool written: the split is `Bool.inspect c`; the `no` fact is
  `Var(0): c = False` = `failed_bool(c)` (dec false → `c = False`).
- `dec` with `bool_test` (`if h:` over `b = X`, or an `unfolded`
  comparison whose proof the arm uses): the split is `inspect b`; the
  failing side's `h` is `b = notX` = `failed_bool` (via `bool_test`).
- `prop` set: `refute d h` (and `notNotOf` for `¬Q`), the old forms,
  unchanged.

Examples that pass an induct case's hypothesis to a lemma stated as eqK
states it confirm this for the Bool tail: `leafNotComma` in
match-induct-guarded-overlap-several.sw (two guarded rows, `vars` 2 and 3),
and `fwdPairOfNotArm` in tools/fmt/src/Syntax/SettleBareProofs.sw.

**`c[σ]`.** Unchanged: `jmap(cond, at, vars.len())` maps the earlier
row's variables to the hypothesis's `∀` variables, and `failed_bool`
wraps the mapped term. `bool_test` on the mapped term sees the same `Eq`
shape. In `NotGuard`, `remap` with `solved` substitutes as before.

**refute_guard (induct.rs:3058-3231).** With a tail, `premise = 0`:

- `top = depth + vars + eqs`: the lambdas bind exactly the variables and
  equations (`names` is `top - depth`). One too many would give the proof
  an extra `Pi` and break every Bool partial overlap
  (`countPairs.induct`, `three.induct`, `withoutR.induct`).
- `fact.shift(top + premise - at)`: with a tail the base sits at `top`, no
  `h` lambda; with a premise it sits under `h`, at `top + 1`, as the old
  `top_old + 1 - at` did (`top_old` had the `+1`). Off by one with a tail,
  the fact would read the last equation's binder instead of the split's
  `h`; the kernel would refuse every example above.
- `stated_at = depth + vars + eqs`: the tail's depth (under the `Pi`s) and
  the old `binders[vars + eqs]`'s depth (the old `top - 1`). Same value
  for both forms.
- `eq = Var(top - 1 - (depth + vars + e))`: equation `e`'s level under
  `top` binders, right whether or not the premise binder is there.
- Final: `lams(names, proof)` with a tail; `proof (Var 0)` with a premise.

For the proposition path, `skipSame.induct` (`if h: x = y`, partial
overlap) keeps its hash in the snapshot, so the rewritten arithmetic gives
the very same term there; `countSame.induct` (new) covers the `!dec`
proposition path.

**refute's clash path (induct.rs:2920-3040).** `Var(eqs - 1 - e + premise)`
and `inner = vars + eqs + premise` are the old formulas; with `premise = 0`
they are the ones non-guarded overlaps have always used (e.g.
`explode.eq3`'s two-equation `notArm2` in aoc Day 18). The only new thing
is `exfalso [tail] void`, with `tail` at `depth + inner`, the body's
depth. Right.

**Which examples hit which new branch**

| Branch | Examples |
|---|---|
| `NotGuard` as `c = False` for `==`/`&&` (prop no longer set) | pattern-guard-equations (`emptyOrOne`, `between`, `countSome`), pattern-guard-forms, text-patterns-prefix, or-pattern-binding, chained-comparisons (`guarded`) |
| `Overlap` ending `c[σ] = False`, eqK walk `!dec` (`ite_step` on the applied hypothesis) | pattern-guard-forms (`countPairs.eq3`), match-induct-guarded-overlap (`withoutR.eq3`), -several (`three.eq3`, `eq4`), pattern-guards snapshot (`twoColumns`, `sized`) |
| `refute`, Bool tail, clash + `exfalso` | `countPairs.induct` (leaf `[h]`), `withoutR.induct`, `three.induct` |
| `refute_guard`, tail | the same three `induct`s, at the leaves where the guard was tested and failed |
| `refute_guard`, premise (arithmetic rewritten) | `skipSame.induct` (hash unchanged), `countSame.induct` |
| eqK walk `dec` path, Bool overlap (`normal_void` on an applied overlap hypothesis) | **none** (see S2) |
| `refute_guard` tail where the fact is `inspect b`'s `b = notX` (`dec` guard) | **none** (see S2) |
| `refute_guard` tail with two or more equations, condition using variables from more than one | **none** (see S2) |

## 3. Scope (D3688)

Not a narrowing. No driver, grammar or alphabet change; no new refusal in
code that reaches users (the early lookup in `refute` (induct.rs:2930)
fails only where the `Overlap` hypothesis itself could not have been built,
equations.rs:4779). No top theorem gains a condition: the eqK/induct
hypotheses change form, `c = True` instead of `P` (`.read` goes between
them); they are no weaker. The proofs that changed are the proofs that
used the old forms: examples, and `tools/fmt` Settle proofs, where
`fwdPairOfNotArm`/`notArmOfFwdPair` (internal lemmas, not acceptance
theorems) change their hypothesis or conclusion to the equivalent `= False`
and `guardOfPair` is removed as no longer needed. `betweenInside` and
`countSomeStep` keep their old statements and are proved from the new
forms, which shows the two forms are equivalent.

The `&&` guard whose proof the arm uses (`Decidable.elim` on `P ∧ Q`)
gets exactly the terms it got before (`dec`, no `bool_test` →
`fails_as_bool` false → `¬(P ∧ Q)`, overlap `… → P ∧ Q → Void`). Being
unchanged, it is not a narrowing. syntax.md:2421 and pattern-guards.md
(D3699 paragraph) say so honestly; the proving guide and guide ch. 10 don't
mention it (N2).

## 4. Bool or proposition: decided by how it is written

`written_bool` follows the `Condition` variant, and `logic::condition`
tries a `Bool` check first (logic.rs:254-292). So:

- a `Bool`-valued call (`isComma a`), `!b`, `a || b`, `xs == []`, `a == b`
  on a type with only `DecEq` (`==` checks as a `Bool`): all `Bool` →
  `c = True` / `c = False`. Before, `==` on a decided type and `&&` were
  read back as propositions by `decided_view`; that was the point of D3699.
- `n != 3` / `n ≠ 3`, `x = y`, `xs = []`: `Condition::Decided` →
  proposition (pattern-guard-equations `skipThree`, `emptyOrTwo`,
  pattern-guard-forms `countSame` confirm; `countBig`'s hash is unchanged).
- `x != 0 && x > 1` (propositions inside `&&`): `Conjunction` → `Bool`,
  as decided (`&&` is the `Bool` operator; `countSome`).

No misclassification found. One corner: `condition`'s fallback (a
proposition nothing decides, with placeholders drafted) re-checks as a
`Bool` and so is `written_bool`; that is a `Bool` reading of what was
written, so it fits the rule.

## Findings

### S1 (should-fix, docs). syntax.md:2150 still says a guard's equations read the chain as `∧`

"Where a proposition is wanted (a statement, a hypothesis, the fact an
`if` or a guard learns, a guard's equations) the middle is put back …, so
goals read `lo ≤ f x ∧ f x ≤ hi`". A guard `| k if 3 <= twice k < 9`
(chained-comparisons.sw:42) is written as a `Bool`, so `guarded.eq1` now
takes `(3 <= twice k && twice k < 9) = True` (the middle put back by
`quote_folded`, equations.rs:4851-4855); the snapshot hashes for
`guarded.eq1`/`eq2` changed with it. Drop "a guard's equations" from that
list, or add: a guard's equations state the chain as the `Bool` with the
middle put back, `(lo <= f x && f x <= hi) = True`.

### S2 (should-fix, test). Three new term-building paths are untested by any example

The kernel would refuse a wrong term, so the risk is losing an equation or
`f.induct` that used to be generated, not unsoundness. But these paths
were rewritten and nothing exercises them:

1. The eqK walk's `dec` path with a Bool partial overlap
   (equations.rs:7428-7440, `normal_void` on `overlap_applied`), and
   `refute_guard`'s tail where the fact is `inspect b`'s `h: b = notX`
   (induct.rs:3660-3685 then 3156). Before this change those cases went
   through `refutes`.
2. `refute_guard`'s tail with two equations and a condition that uses
   variables from both (`from_x` for an earlier equation in the motive).

A short addition to examples/accept/pattern-guard-forms.sw covers both,
for example:

```
-- A comparison whose proof the arm uses, over a partial overlap.
def firstFits (limit: Nat): List Nat → Nat
  | [x, _, ..rest] if h: x <= limit => x + firstFits limit rest
  | [_, ..rest] => firstFits limit rest
  | [] => 0

theorem firstFitsLe ∀ (limit: Nat) (xs: List Nat): firstFits limit xs ≤ xs.sum :=
  match induct (firstFits limit xs) with …

-- Two columns, both partial, the condition using one variable from each.
def pairUp: List Nat → List Nat → Nat
  | [_, b, ..xs], [c, ..ys] if b == c => 1 + pairUp xs ys
  | [_, ..xs], ys => pairUp xs ys
  | [], _ => 0
```

with a `match induct` proof over each and one theorem applying the
`notArm2` of the induct case to `f.eq2` (as `leafNotComma` does). If
`if h: x <= limit` doesn't elaborate to the `b = True` form, use an arm
that uses the comparison's proof without naming it (the `unfolded` case,
e.g. `if i < xs.length => xs.getLt i`).

### N1 (note, docs). `if h: P` over a `Bool` test fails as `= False`, not `¬P`

syntax.md:2421, pattern-guards.md (the D3699 paragraph) and
proving-guide.md:588-589 list `if h: P` among the proposition forms that
keep `P` / `¬P` / `… → P → Void`. Where `P` elaborates to `b = X`
(`bool_test` matches), `fails_as_bool` is true: `NotGuard` is `b = notX`
(as before this change) and a partial overlap now ends `… → b = notX`
(before: `… → b = X → Void`). Consistent and arguably right (it is a `Bool`
test), but the docs should say "`if h: P` keeps `P`, except a `P` that is a
`Bool` test `b = True`, which fails as `b = False`".

### N2 (note, docs). The `&&`-with-used-proof exception is missing in two places

docs/proving-guide.md:586-590 and docs/guide/10-proofs.md:549 state the
rule without the exception that syntax.md:2421 and pattern-guards.md give
(`if i < n && 0 < i => xs.getLt i` still states `P ∧ Q` and `¬(P ∧ Q)`).
One clause each.

### N3 (note, robustness). An unexpected `normal = None` builds an ill-typed term instead of skipping

equations.rs:7440: in the `dec` path, when the hypothesis is a Bool
overlap's `= False` (`refutes` is `None`) but `normal` is `None` (the
tree's `Decidable.elim` proposition isn't `b = X`, or `bool_equation`
fails for an `unfolded` row), `(None, None) => hyp (Var 0)` applies an
equation as a function. `fails_as_bool` requires `bool_test` of the
recorded condition, so this should not happen; if it does, the kernel
refuses and the equation is skipped with a kernel message rather than a
clear reason. Suggest: when `fails_as_bool` and `normal` is `None`,
`skip("an arm's condition is a `Bool` test in its statement but not where
the definition tests it")`.

### N4 (note, docs). match-induct-friction.md §1 still says `n != 3` changes

docs/proposals/match-induct-friction.md:159-160 and :365 say a guard `n
!= 3` would give `(n != 3) = True`; the lane found `!=` is the
proposition operator, so it keeps `n ≠ 3`. A line under §1 saying so, or
a pointer to the D3699 paragraph in pattern-guards.md, would stop a reader
of the note from expecting the wrong form.

## Verdict

Merge after fixes: S1 (one sentence in syntax.md) and S2 (one example
covering the `dec` Bool overlap and a two-equation Bool tail). N1, N2 and
N4 are one-line doc edits worth doing in the same fix; N3 can be filed.
