# What a catch-all arm can use of the literals above it

**Status:** design note, 15 November 2026 (SW-3318; the finding is from
catch-all-goals.md's probes). B and A are built (SW-3335, `literal_facts.rs`;
the open question in §4 B is settled: an `auto` obligation solved after the
declaration still sees the arm's marks, but its helper must be lifted, so
`Elaborator::lift` solves a declaration's obligations before lifting even
when it has no `match` helper of its own). The recommendation adds a
step to `auto` and a line to goals, with no new syntax and no change to
existing terms or hashes, so it is the orchestrator's call, not a question
for Matt. The kernel option (C) would need Matt's review if it is ever
wanted.

Claims are marked **[source]** (read at `0c43a1af5`), **[measured]** (the
main checkout's release binary, built 07:34 today; probes `p1.sw` to
`p4.sw` in the lane's scratchpad, quoted below) or **[recalled]** (other
languages, from their documentation, not re-run here).

## In plain words

**The problem.** In a proof's catch-all arm after number, character or text
patterns (`| 5 => … | m => ?`), the goal shows `m: Nat ⊢ …` and nothing
says `m ≠ 5`. The arm does know it, but only as a fact that makes
computation go (another match on `5` takes its `_` arm), not as a
hypothesis. A proof that needs `m ≠ 5` as a value (to pass to a lemma, say)
has to know a trick: transport along the equation into a match,
`h => J (y _ => match y with | 5 => Void | _ => Unit) Trivial h`.
`byDecision` and `Nat.equalFalse m 5 rfl` both fail.

**The change.** Teach `auto` that trick: a goal `x ≠ lit` (a number,
character or text literal, or a constructor tree of them) is tried by that
transport, which the kernel accepts exactly when the catch-all knows the
fact. And show the facts in the catch-all's goal, as `m ≠ 5` lines under
the context, with a note that `auto` uses them.

**What it should do.** `hf m byDecision` (or any `[auto]` argument) proves
`m ≠ 5`, `d ≠ 'k'` and `t ≠ "ab"` in the catch-alls where the four-line
`J` term is needed today [estimated; the `J` term itself is measured to
check in all three]. No term, hash or kernel rule changes for existing
code: the new step runs only where `auto` would otherwise fail.

## 1. What the elaborated catch-all knows [source]

A number column compiles to the kernel's own `NumCase(x, [(k, b)…], d)`,
not to a decidable-equality chain and not to `Succ` peeling
(`check_tree`'s `Tree::NumCase`, `crates/elab/src/lib.rs`;
number-patterns.md). In the default `d`, the variable's value is replaced,
in the context and the goal, by the same variable marked *apart* from the
arms' numbers: `Head::Var(x, Apart{5})` (literal-match-facts.md, D1306).
The kernel's `check_num_case` does the same. The mark is used in one place,
evaluation: a `NumCase` on `k + x` takes its default when each arm's number
is below `k` or minus `k` is in `x`'s set.

So there is **no proof term** of `x ≠ 5` anywhere in the elaborated
catch-all. The fact exists only as a mark on a value, and read-back drops
marks, so terms and hashes don't mention it. It is not `n = Succ (Succ …)`
shaped either: literal-match-facts.md's "no shapes" rule says apart from
`0` isn't `Succ` of anything.

Characters and texts go through the same path. `'k'` is `MkChar 107 _`, so
a character column splits the `MkChar` wrapper (a constructor case) and
then does a `NumCase` on the code: the catch-all's mark is on `code✝`.
A text pattern is `MkText` around a list of those, split character by
character (a trie), so a text catch-all is checked at several leaves (five
for `"ab"`), each with marks on the codes it tested. The fact `t ≠ "ab"`
holds at every leaf, for a different reason at each.

## 2. Probes [measured]

| Probe | Body of the catch-all | Result |
|---|---|---|
| `a1`: `n = 5 ∨ n ≠ 5`, `\| 5 => … \| m => ?` | `?` | `m: Nat ⊢ m = 5 ∨ m ≠ 5`: no fact shown |
| `a7`: the same with `match e: n` | `?` | adds `n: Nat`, `e: n = m`: no fact either |
| `a4` | `Inr byDecision` | `E-AUTO-STUCK`, "can't decide `n ≠ 5` here" |
| `a5` | `Inr (Nat.equalFalse m 5 rfl)` | `E-REFL`: `m.equal 5` doesn't compute (`Nat.equal` is a `Zero`/`Succ` tree; marks don't help it) |
| `a3` | `h => Bool.falseNotTrue (Eq.cong isFive h)`, `isFive` a match on `5` | checks |
| `a6` | `h => J (y q => match y with \| 5 => Void \| _ => Unit) Trivial h` | checks, no helper definition |
| `a8` | `hf m (that J term)`, `hf: ∀ k, k ≠ 5 → f k = 0` | checks: the fact passed to a lemma |
| `c2`: `Char`, after `'k'` | the same `J` term with `'k'` | checks |
| `t2`: `Text`, after `"ab"` | the same `J` term with `"ab"` | checks at all five leaves |
| `t3` | `Inr byDecision` | `E-AUTO-STUCK`, "can't decide `MkText ['a', MkChar code✝ valid✝, ..tail✝] ≠ "ab"`" |

So the fact is derivable today, without changing any term the elaborator
makes: the transport works because the motive's own match meets the marked
variable and takes its `_` arm. What's missing is that nothing shows it
and nothing writes it for the user.

## 3. How others do it [recalled]

- **Lean 4.** `match h : n with | 5 => … | m => …` gives `h : n = m` in the
  second arm and no `n ≠ 5`: `match` alone adds no overlap facts. The
  `split` tactic on a goal containing such a match does, as a hypothesis
  `x✝ : n = 5 → False` (inaccessible, but `simp_all`, `omega` and
  `contradiction` use it), and so do the equation lemmas of a definition
  by match (`f.eq_2 : ∀ n, (n = 5 → False) → f n = …`). Literal patterns
  compile to `decEq` tests, so the facts are proofs already in the term.
- **Agda, Idris 2.** A catch-all clause gets nothing; to know `n ≢ 5`, one
  matches on `n ≟ 5` with `with` and takes the `no ¬p` branch.

Stitchwort already does more than either inside the arm: its catch-all
computes with the fact, which Lean's `match` doesn't. What Lean's `split`
adds over us is the fact as a usable (if unnamed) hypothesis.

## 4. Options

**A. Show the facts in the goal (display only).** Under the context, one
line per literal the arm is known to differ from: `m ≠ 5`, `d ≠ 'k'`,
`t ≠ "ab"`, in the arm-as-written view (SW-3317), so the scrutinee is shown
by the user's name. Taken from the case tree, not from the earlier rows: an
earlier arm with a guard (`| 5 if b =>`) gives no fact, and one over several
columns (`| (5, 'x') =>`) gives `¬(n = 5 ∧ c = 'x')` at best, so it's left
out. A line is shown only when the transport for it would check at every
leaf of the arm. On its own, A shows a fact the user still can't use
without the trick. Cost: goals.rs and arm_display.rs, about 2 hours.

**B. `auto` proves `x ≠ lit` by transport (recommended, with A).** A new
`auto` step, tried after the existing ones fail and before the
contradiction closer: for a goal `a ≠ b` where `b` (or `a`) is a closed
literal value, elaborate `h => J (y _ => match y with | b => Void | _ =>
Unit) Trivial h` and keep it if it checks. Then:

- the user refers to the fact through `auto`: `byDecision` where `m ≠ 5`
  is wanted, an `[auto ne: k ≠ 5]` parameter on a lemma, or the decision
  steps that already ask `auto` for their side conditions;
- it works for numbers, characters and texts [measured, as the `J` term],
  and should for `Int` literals within a sign and literals nested in
  constructors [estimated];
- existing proofs keep their terms, since the step runs only where `auto`
  failed before; a proof that uses it gets the `J` term inline, an ordinary
  term the kernel re-checks.

The note under the goal's facts says so: "known from the arms above; `auto`
proves these". To check while building: that an `auto` obligation in a
catch-all is solved with the leaf's context (its marked values), since
obligations are solved after the declaration is elaborated. Cost: about 3
hours with A's line, Sonnet, with an Opus review (it is near the match
compiler, and the proof is checked per leaf).

**C. Make `Nat.equal` compute on marked variables (a kernel rule).** Extend
the evaluation rule: `Nat.equal (k + x) n` is `False` when `x` is apart
from `n - k` (and the symmetric case). Then `m == 5` is `False` in the
catch-all, so `byDecision`, `Nat.equalFalse m 5 rfl`, `if m == 5` in a
program the proof steps through, and `Char`/`Text` equality (built on
`Nat.equal` of codes) all compute. Sound by literal-match-facts.md's
argument: a marked variable is none of its numbers. But it changes what the
kernel accepts (docs/core.md, Matt's review, the oracle tests), for a gain
B mostly gives: what C adds is programs that test `==` instead of
matching. Worth reconsidering if a proof of that kind turns up.

**D. Name the fact (new syntax).** For example `| m (ne: m ≠ 5) =>`, or
`match h: n` giving the catch-all `h` as the facts. The elaborator would
bind the transport term under the name. It changes what users write, and
neither Lean's `match` nor Agda does it. With B, `byDecision` at the use
does the same job in one word, so D isn't needed now.

## 5. Recommendation

**B with A.** It makes the fact visible where the user looks for it and
usable with a word they already know, for numbers, characters and texts
alike, with no syntax, no kernel rule and no change to existing terms or
hashes. Since it adds no syntax, it is the orchestrator's call; there is no
question for Matt. C is a kernel change and D is new syntax; both would
need Matt and neither is needed for the probes above.

Suggested ticket: "A catch-all after literal patterns: `auto` proves `x ≠
lit` by transport through a match on `lit`; goals list the facts (`m ≠ 5`)
known from guard-free single-column literal arms above; examples/goals
snapshot and an accept example for `Nat`, `Char`, `Text`" (Sonnet, est.
3 h; Opus review). The user-visible language guide and syntax.md paragraph
on number patterns ("the facts aren't hypotheses with names: a proof that
needs `n ≠ 3` as a value proves it as usual") change with it.
