# SW-4488 review: `byFacts` stage 1a

Opus paper review (SW-4489, 21 Nov 2026) of `lane/SW-4488` (bac6cb40e,
3cb9620d2, 4b80a0942, 08a0d29d1) against docs/proposals/closer.md stage 1
and docs/reviews/SW-4483-byfacts-in-context.md §4–§5. Every reproducer
below was run with the lane's release binary
(`.claude/worktrees/SW-4488/target/release/stitchwort check --no-cache`).
Line numbers are in `crates/elab/src/facts.rs` unless another file is named.

## Summary

The soundness picture is good. Every term goes through the elaborator's
checks and then the kernel. No probe made a false statement check. The
bugs found below produce ill-typed terms that end in an error. None
produces a wrong proof. The cases.rs refactor is a verbatim extraction.
The formatter changes touch only proof bodies and one test.

Three things should be fixed before merge:

- a de Bruijn shift bug in constructor equations;
- `--expand-facts` writing text that doesn't check under `cases then`;
- a part-depth limit that makes `byFacts` weaker than `cases` on long `&&`
  chains, the formatter's case.

The remaining findings are about order dependence, slow failures and the
error message.

## Must fix before merge

### 1. Nested constructor equations: wrong variable in the term

`take_equation_apart` (l. 514–517) shifts the k-th field's proof by `k`.
That assumes each earlier part added exactly one `let`. But `self.add` on
an earlier part may take it apart further: a nested constructor equation,
or a test-fact reading. Each such step binds more lets, so the proof
points at the wrong variable.

```
theorem pairNested ∀ (f: Nat → Nat) (a b x y: Nat) (e: (Some a, x) = (Some b, y)) (h: f x = 0): f y = 0 := byFacts
```

gives `E-TYPE-MISMATCH: expected (Option Nat, Nat), but this has type
Nat`. The same file with `(a, x) = (b, y)` checks.

The fix: record `cx.level()` when `field_equations` is called, and shift
each proof by `cx.level() - that` at its `define`. Add `pairNested` to
`facts-forms.sw`.

### 2. `--expand-facts` under `cases then` writes a proof that doesn't check

`take_facts_expansions` (l. 1676–1686) keeps the last expansion for each
span. A `byFacts` checked once per case of `cases then byFacts` can find
a different term in each case.

```
theorem splitB ∀ (b: Bool) (g: Bool → Prop) (p q: Prop) (x: p) (y: q) (t: p → g True) (f: q → g False): g b := cases then byFacts
```

This checks. `--expand-facts` rewrites it to `cases then t x`, which fails
with `expected g False, but this has type g True`. That breaks bar 4
("every `byFacts` in the pilot expands to a term that checks").
`--expand-repeatedly` already handles the same case.

Do what `--expand-repeatedly` does: when one span was recorded with
different texts, leave the call as it is and list it. Add a CLI test with
`splitB`.

### 3. `MAX_PART_DEPTH = 12` cuts long `∧` and `&&` chains, so `byFacts` is weaker than `cases`

`add` stops taking a fact apart at depth 12 (l. 327). Each conjunct of a
right-nested chain costs one level. Each conjunct of a test fact costs
two: `.read`, then `.right`.

- `(h: p0 ∧ … ∧ p15): p15 := byFacts` fails.
- With `(h: (b0 && … && b9) = True)`, `byFacts` closes `b4 = True` but
  not `b6`, `b7` or `b9`. `cases` closes all four.

Long `&&` predicates are the formatter's case, which closer.md's bars
target (SW-4483 §5: 2,808 lines of `Bool.andLeft (Bool.andRight …)`).

Taking a fact apart always terminates, since each part is a strict
subterm. A reading that reads as itself is already caught by the `conv`
dedupe (l. 312–318). So bound the total number of parts (say 1,000, and
say so in `E-FACTS` when it is hit), not the depth. Add a 20-conjunct
`&&` probe to `facts-probes.sw`.

## Should fix

### 4. A premise with an unknown takes the nearest fact, with no backtracking: the result depends on fact order

`apply` (l. 1040–1050) fixes a premise's unknown with the first fact that
unifies, in reverse order of when facts were added. `witness`
(l. 919–929) does the same. If that choice makes a later premise fail,
no other fact is tried.

```
theorem orderA ∀ (p q: Nat → Prop) (r: Prop) (step: ∀ (x: Nat) => p x → q x → r) (h1: p 1) (hq: q 1) (h2: p 2): r := byFacts
theorem orderB ∀ (p q: Nat → Prop) (r: Prop) (step: ∀ (x: Nat) => p x → q x → r) (h2: p 2) (hq: q 1) (h1: p 1): r := byFacts
```

`orderB` checks. `orderA` fails, and its error doesn't say why (the
premise `q 2` was never closed).

The search is deterministic, but adding an unrelated hypothesis can break
a working proof. The order isn't documented: docs/syntax.md says only "a
premise with a fact in scope".

This is not guessing: only facts fix unknowns. But it is committing to
one fact among several. Backtrack over the facts that fit, each try
counted as an attempt. That keeps SW-4483 §4.2's rule (only a fact fixes
an unknown) and makes success independent of order. Only the term chosen
would still depend on it. Then document "nearest first".

### 5. Substitution is blocked by facts it moved, and builds an ill-typed motive when the goal mentions a dependent fact

`substitution`'s `blocked` loop (l. 1229–1238) treats any level that is
neither in `self.facts` nor a `let` as a variable needing its own copy.
A hypothesis already moved by an earlier substitution has left
`self.facts`, so it blocks every later substitution of a variable it
mentions:

```
theorem movedBlocks ∀ (f: Nat → Nat → Nat → Nat) (x y a b: Nat) (e1: a = b) (k: f a b y = 1) (e2: x = y) (h: f x a 0 = 0): f y b 0 = 0 := byFacts
```

This fails with `left open: f x b 0 = 0`. Without the irrelevant `k`, it
checks.

The loop also skips facts entirely. So when the goal mentions a fact
whose type mentions `x`, the motive `z q => G[z]` is ill-typed:

```
theorem depMotive3 ∀ (n m: Nat) (h: n < 5) (e: m = n) (pr: (k: Nat) → k < 5 → Prop) (w: ∀ (p: m < 5) => pr m p): pr n h := byFacts
```

gives `E-TYPE-MISMATCH: expected z ≤ 4, but this has type n < 5`. A
sibling, `depMotive2`, shows `left open: pr m h`: a goal that doesn't
type-check.

The fix: decide by "is a fact" (`is_fact`), not by membership in
`self.facts`. Block `x` when the goal, or a fact being moved, mentions a
variable whose type mentions `x`.

### 6. The substitution budget is shared and never given back

`self.substitutions` (l. 1115) grows on every substitution, including
those inside premise proofs that fail and are undone. `part` restores
`facts` (l. 769–772) but not the counter. After 16, no part can
substitute again.

```
theorem few  ∀ (g q r: Nat → Prop) (a b: Nat) (good: q a → g a) (hq: q b) (e: a = b) (s1 … s8:  ∀ (x: Nat) => r x → g x): g a := byFacts
theorem many ∀ (g q r: Nat → Prop) (a b: Nat) (good: q a → g a) (hq: q b) (e: a = b) (s1 … s17: ∀ (x: Nat) => r x → g x): g a := byFacts
```

`few` checks. `many` fails without reaching the attempt limit, and
nothing in the error says why.

Restore the counter with the facts, or count substitutions as attempts.
Either way, say in `E-FACTS` when a limit stopped it.

### 7. Failures can be slow: the attempt limit bounds attempts, not their cost

At every node, phase 2 re-runs work that is never counted:

- `direct` (l. 792–842): a `conv` against each fact, two more against each
  equation fact (the flipped check), and `by_contradiction` over all
  facts;
- `arithmetic` on each arithmetic node, uncounted (l. 883–889);
- no memo: the same failing part is searched again at each depth and for
  each candidate.

Measured, each a failure:

| File | `byFacts` | Comparison |
|---|---|---|
| 60 equation facts, 60 `p i = True` facts and the 7 loops of `facts-attempt-limit.sw` (`stress.sw`) | 97 ms | `cases` 24 ms; without the loops 2.4 ms |
| 10 comparisons, 7 facts `∀ x => x + 2 * x > e + d → g x → g x` (`slowFail3`): 7 attempts, 7 failing `arithmetic` calls | 22 ms | `arithmetic` alone 1 ms |

SW-4483 §4.7 and G4 ask for failure under 5 ms. The reject examples meet
it, but these show what `cases then byFacts` will meet in large contexts.

Fixes:

- check contradiction once per fact set in phase 1, as specified (it
  doesn't depend on the part), not at each node;
- count `arithmetic` calls as attempts, or allow one per distinct part;
- memoise failed (part, depth) within a call;
- prune a premise that is `conv` to the goal of an ancestor node. That
  ends `g x → g x` loops at once, and also stops terms like
  `s3 a (s3 a (good …))`, which `withLoops3` writes today.

### 8. "Two facts that refute each other" covers only constructor and Bool clashes

`direct` uses `cases::by_contradiction`, which finds two constructors
that differ, or `e = True` beside `e = False`. Each of these fails:

```
theorem notOther ∀ (a: Prop) (h: a) (k: ¬a) (g: Nat → Prop): g 0 := byFacts
theorem voidFact ∀ (v: Void) (g: Nat → Prop): g 0 := byFacts
theorem natClash ∀ (n: Nat) (h: n = 2) (k: n = 3) (g: Nat → Prop): g 0 := byFacts
theorem contra ∀ (n: Nat) (h: n < 3) (k: 5 ≤ n) (g: Nat → Prop): g n := byFacts
```

`notVoid` (`h: a`, `k: ¬a` ⊢ `Void`) does check.

The cheap general rule: when a part isn't `Void`, also try to prove
`Void` from the facts (phase 2 applies `k`; `arithmetic` refutes
comparisons), then eliminate. With the memo of finding 7, this costs
little. `a` beside `¬a` is the first case a reader expects. At minimum,
document which contradictions are found.

### 9. `E-FACTS` falls short of SW-4483 §4.5

- It doesn't name the premise that failed. In `facts-missing-fact.sw` it
  lists `f: a → c` but not that `a` wasn't found; §4.5 asks for "the
  first premise of each that nothing closed".
- A part from a constructor equation's field shows a blank name, because
  `UNWRITTEN` is printed by `plain`, l. 1286. `pairNestedFirst` shows
  `  : a = b` and `rewrite <-   at e: …`. Print something like
  `(a field of e)`.
- After a substitution, the part shown is the substituted one
  (`movedBlocks`: `f x b 0 = 0`, which is not what the user wrote), and it
  can be ill-typed (finding 5).
- A stop by the substitution or part limit isn't reported (finding 6).

### 10. `then t` and `then ?` see the substituted goal

A part left open after the substitution retry goes to `then t` in its
substituted form (l. 767–774):

```
theorem thenSubst ∀ (f: Nat → Nat) (a b: Nat) (e: a = b) (k: f a = 1): f b = 1 ∧ f a + 1 = f a + 1 ∧ (f b = 2 ∨ f a = 1) := byFacts then ?
```

shows `⊢ f a = 2 ∨ f a = 1`. The `then t` a user writes then depends on
which equations the search used. Hand `then t`, and `E-FACTS`, the part
as it was before the retry, and keep the substitution only when it closes
the part.

### 11. In an argument, `byFacts` is a parse error that doesn't say what to do

`Both byFacts y` gives `E-PARSE: expected the end of the declaration,
but found byFacts`, as `byWalking` does. `Both cases y` and
`Both arithmetic k` check. The rule is documented ("In an argument,
bracket it: `Both (byFacts) h`"), but the message should say so. Add a
note to the parse error for both words.

### 12. Attempts used aren't in `--timings`

SW-4483 §4.7 asks that the attempts used be printed, so that proofs near
the limit can be seen. This is a small addition beside the existing
tables.

### 13. Document the limits as built

docs/syntax.md and the proving guide should say:

- the nearest fact is taken for an unknown (or, after finding 4, that the
  facts are tried in order);
- which contradictions are found;
- the part, substitution and attempt limits;
- that `then t` gets the substituted part (or not, after finding 10);
- that the time bound is a count of attempts, whose cost grows with the
  facts in scope.

The proving guide's "fails within its 200 attempts (2.4 ms …)" reads as a
time bound, which finding 7 shows it isn't.

## Notes

### 14. Soundness, terms and the kernel

The term forms are all ones the kernel already has:

- `let`s;
- `Exists.elim` (its result unified with the goal);
- `J` with a motive `z q => G[z]` based at `t`, along `back: t = x`, for
  the goal;
- `J` based at `x`, along `fwd: x = t`, for each moved fact;
- `Eq.flipped`;
- `Bool.andIntro`;
- constructors;
- accessors or `Proj`;
- applications.

I checked the `J` directions and the shifts of `fwd` (l. 1170) and of
listed items (l. 871); they are right. No kernel change, and no existing
hash moved. Eliminating an `∃` into data is refused, if badly:
`def pick (n: Nat) (h: ∃ (k: Nat) => k > n): Nat := byFacts then n` gives
`E-UNIVERSE`. Better: refuse a goal that isn't a proposition up front,
with `E-FACTS`.

### 15. Phase 1 can't loop

- The part depth bounds it (and so would a part count, finding 3).
- Substitution is bounded by its budget.
- Re-entry from `part` substitutes only while `substitution` finds an
  equation whose variable is mentioned. The equation used leaves the
  facts, so each round removes one.

Phase 1 loses nothing it shouldn't, apart from findings 3 and 5: the
fact is kept beside its parts.

### 16. The `cases.rs` refactor

`field_proof` is the old loop body moved out verbatim. It reads
`cx.level()` at the same point as before, so `take_apart` is unchanged.
`field_equations` is new and used only by `byFacts`.

### 17. The self-hosted formatter

- Token.sw adds `KwByFacts`.
- GoodItemProofs.sw (l. 414, 541) and LexReadsProofs.sw (l. 298) add a
  case to the match in the proof bodies of `wordKindFixed`,
  `wordKindNotNumeral` and `wordKindPlain`. Their statements are
  unchanged.
- No top theorem, acceptance theorem or `MustAccept` file changed.
- Slice1.sw gains a test that `byFacts` is refused.

What it refuses now that it accepted before: `byFacts` as a name, or as
a field name (`type R = { byFacts: Nat }`). The Rust parser refuses the
same, since the word is reserved, so the formatters agree. Nothing on
`main` uses the word. This follows from the language change Matt
approved in D3708 (closer.md lane 1a: "the self-hosted formatter refuses
the new word until a slice reaches it"). It is not a narrowing under
D3688, but the orchestrator may want to mention it in one line.

### 18. Expanded text in another file

`Std.Bool.andIntro`, `Witness`, `match … with | Witness …`,
`rewrite <- e at h` and `arithmetic [h.left, h.right]` all check again
in a file of their own. That covers the probes and `band.sw`. Nothing
tests them in a project namespace with an explicit import list, which is
the lane's own concern. Add one CLI test there.

Calls left unexpanded are fine in principle: `then t` and field
equations. But the CLI doesn't list them, as `--expand-repeatedly` does,
so a user can't tell a call left alone from one not reached.

Expansions are also recorded for a `byFacts` whose declaration then
fails (`depMotive3` prints "expanded 1 byFacts call").

### 19. Listed terms are elaborated before the goal's `∀` is introduced

A term in the brackets can't use a name that the goal's own `∀` binds. It
can only use the declaration's parameters. Fine for stage 1, but
document it.

### 20. Tests to add with the fixes

- Accept examples:
  - `pairNested`;
  - a 20-conjunct `&&` chain;
  - `orderA`;
  - `movedBlocks`;
  - `notOther`.
- A CLI test for expansion under `cases then`.
- Reject examples:
  - an `∃` goal that no fact fixes (the "no witness is invented" promise
    has no reject example today);
  - `byFacts` with no known goal (`no_goal`).
- A goals example of `then ?` after a substitution.

## The lane's decisions

The lane's list wasn't on the ticket, so these are the ones the brief
names, and the ones visible in the code.

| Decision | View |
|---|---|
| Recognised only where an expression starts (a reserved word, like `byWalking`) | Agree: `byFacts [x]` as an argument would clash with a list argument. Improve the message (finding 11) |
| `then t` tried on each open part | Agree. Give it the part as written (finding 10) |
| Lazy substitution (after the search fails, then retry) | Agree for speed when it isn't needed. But it doubles the cost of a failure, and leaks into `then t` and `E-FACTS` (findings 7, 10) |
| 200 attempts | Agree on the number. Count `arithmetic` too, and memoise, so that the count bounds time (finding 7) |
| Contradiction expands to `cases` | Acceptable. It is `cases`' own closer, so `cases` closes the same goal. An explicit term would be better where there is one, since expansion exists to remove searches |
| A premise's unknown fixed by the nearest fact, no backtracking | Disagree: order-dependent (finding 4) |
| Part depth 12 | Disagree: cuts the formatter's chains (finding 3) |
| 16 substitutions in all | Disagree: shared across failed branches (finding 6) |
| Only hypotheses whose names aren't shadowed | Agree: the expanded text has to name them |
| Field-equation parts never expanded | Agree for stage 1. List them (finding 18) |
| Depth 3 | Agree (SW-4483 §4.2) |
| `arithmetic` not tried on a variable's statement | Agree |
