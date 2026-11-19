# Proving guide for agent lanes

This page is for an AI agent proving theorems in Stitchwort: AoC proofs, the
roguelike's, std's. It holds the rules a proof lane follows, the workflow
that works, which tool fits which goal, what the common errors usually mean,
and the performance traps. Every rule comes from something our own lanes ran
into ([agentic-proving.md](research/agentic-proving.md) §5, `aoc/NOTES-2024.md`,
`games/rogue/PROOFS.md`, `games/rogue/NOTES.md`). The skill file of card C21 in
that note is the model: in that paper, a short list of rules and pitfalls
took one model's shortcuts (`assume`s left in proofs) from 18 to 0.

The reference for every construct is [syntax.md](syntax.md). Where this page
and syntax.md disagree, syntax.md wins; fix this page.

## 1. Rules

These aren't style. A lane that breaks one has to say so in its report.

1. **Never weaken a statement to make a proof go through.** Don't change the
   conclusion, don't add a hypothesis, don't narrow a type. If a hypothesis
   really is needed, add it, and list it in the report under "Not proved",
   with why the statement is false or out of reach without it. Our lanes did
   this every time (8 cases, all disclosed: agentic-proving.md §5 J). For example, AoC day 8
   proves part 2 only for antennas on the map, and says why that's needed:
   antennas at rows 100 and 101 below a 1 by 1 map would break it (aoc/NOTES-2024.md:2090–2096).
   Day 19 states that every theorem takes `Striped patterns`
   (aoc/NOTES-2024.md:6042); day 21 that `part1Correct` and `part2Correct`
   assume `Optimal` (aoc/NOTES-2024.md:7016).
2. **Prove against a spec written in the problem's own words**, kept apart
   from the program. The AoC days have `Spec/Spec.sw`, which reads like the
   puzzle (`aoc/src/Aoc/Year2024/Day06/Spec/Spec.sw` quotes it: "If there is
   something directly in front of you, turn right 90 degrees"). The proofs
   then say the program computes what the spec says. A spec copied from the
   program proves nothing. On day 4 the spec caught a bug that a test had
   recorded as correct (aoc/NOTES-2024.md:803–822). A spec bug is reported
   as a bug, not modelled around.
3. **Run `stitchwort audit` on the namespaces you touched before reporting,
   and read every line** ([workflow.md](workflow.md#how-a-proof-lane-finishes),
   [syntax.md](syntax.md#auditing-theorems-stitchwort-audit)). `✗` is a
   failure: fix it or list it under "Not proved". `!` is a warning: read the
   statement and decide whether its hypotheses contradict each other. For a
   vacuity warning (random inputs never met the hypotheses), add a closed
   witness theorem that applies it to arguments for every hypothesis
   (`theorem fooExample: … := foo 3 byComputing`); the warning becomes a pass
   and `--verbose` names the witness. Quote the summary line in the report.
4. **No new `opaque` definition just to get past a check.** `opaque` is
   honest when it stops the checker computing something it should only name
   (§6 below). It doesn't make anything true, but it changes what later
   proofs can see. Each new `opaque def` gets a comment saying why
   (as `games/rogue/src/Rogue/Random.sw:11–14` has for `lcg`), and a line in
   the report.
5. **Report "not proved" honestly.** Unfinished (`?`), proved only under an
   added hypothesis, proved for a different statement, or only tested: each
   is "Not proved", with what's missing. "Tested on the examples" is not
   proved. "No counterexample found" is not proved.
6. **Break the program once, and check the proofs fail.** Change a `<=` to
   `<`, or drop a step; the proofs about it should stop checking, often with
   a counterexample. Our lanes did this by hand on 17 days, for example
   aoc/NOTES-2024.md:1772–1774 ("Changing the program's `last <= target` to
   `last < target` makes `canMakeReaches` fail with a counterexample").
   Put the program back afterwards.

### Writing statements (Matt, 4 Nov 2026)

Statements are read by people deciding what was proved, so write them as
statements. Use the operators, not the prefix forms: `a ∧ b`, `a ∨ b`,
`¬p`, `a ↔ b`, `x ≠ y`, `∀ (x: T) => p`, `∃ (x: T) => p`, rather than
`And a b`, `Or a b`, `Not p`, `Iff a b`, `Not (x = y)` or `Exists (x => p)`.
They are the same terms (same hashes), so proofs that take them apart with
`Inl`, `Both` and so on don't change.

A `Bool` where a proposition is expected means `b = True`
(docs/syntax.md, "A `Bool` as a proposition"), so state a test's fact
bare: `(h: xs.any p)`, `isSmall m ∧ isSmall n`, `¬a`. State facts with
`∧`; write `(a && b) = True` only for a fact a program hands you and you
mean to `rewrite` with, since that is the term an `if a && b` or a
`match h: a && b` gives (D3486). Keep `= True` on a side of `=`, and write
`b = False` as it is. A `False` in a statement is the `Bool`, so a goal
`False` is really `False = True`, which has no proof; for a proposition
with no proof, write `Void`.

Tests and statements (docs/guide/10-proofs.md, "Tests and
propositions"): take a fact about a test apart with the patterns of the
statement it reads as (`| Both a b`, `| Inl a`, `| { low, high }` for a
record reading), take a part with `h.left`, and write `.read` where the
whole fact is wanted as its statement (`h.read`, `(h.read x m).right`).
Build a fact with the statement's constructors (`Both a b`, `Inr hb`, a
record literal). Don't write a helper that converts a test to its
statement, or a `= True ↔` lemma, where a pattern or `.read` does it; `auto`
and `cases` already use the test facts in scope as what they read as, and
apply a `∀` once. A new test with a statement of its own gets a
`@[reading]` theorem beside it.

Build, open and project `∃` and `∧` proofs with tuples (D3631,
docs/syntax.md, "Proof tuples"): `(7, big, square)` proves `∃ (n: Nat) =>
n > 2 ∧ n * n = 49`, one part per binder and per conjunct, and is the same
term as `Witness 7 (Both big square)`. Open a hypothesis or a lemma's result
with a pattern `let`, `let (n, _, square) := lemma xs`, rather than a
one-arm `match`: in a proof it is that `match`, and it refines the goal.
Use the same tuple in `match` arms, lambda parameters, clause lambdas and
arms; `_` skips a part, and a last part names the rest of the chain
(`(x, a, rest)` gives `rest: B ∧ C`). For one part of a `∧`, write
`h.left` or `h.right`; deeper than that, a pattern `let` with `_`s reads
better than `h.right.right.left`. Write `Witness` and `Both` only where a
function is wanted (`hs.map (Witness x)`). An `∃` tuple needs its goal
known, so give a `let` the type if nothing else does. Records stay records:
a proposition with named parts is opened with `{ seen, .. }`.

A theorem puts every variable before the colon, as a parameter
(`theorem plusZero ∀ (n: Nat): n + 0 = n`), and a proof by cases is a `match`
on them: `theorem timesOne ∀ (n: Nat): n * 1 = n := match n with | Zero => …
| Succ k => …` (D3470). The `∀` right after the name is how a theorem's header
reads as "for all"; it is cosmetic (the same term and hash), `stitchwort fmt`
writes it on every theorem with explicit parameters, and it stays off a header
with only implicit ones (D3472). Premises the proof names are parameters too
(`(h: x < y)`), not a `→` after the colon (D3471). This is the house style
for theorems; a `def` keeps its arms and its `→`. `stitchwort sweep
theorem-binders` converts old-style theorems; `check` warns (`W-THEOREM-FORALL`) on a theorem whose statement still starts with `∀` after the colon, and the editor's quick fix "Move ∀ variables before the colon" converts it. Likewise `W-ARROW-FORALL` on a statement written `(x: T) → P` for `∀ (x: T) => P` (D3462), with the quick fix "Write ∀ instead of ->".

Write "for all" as `∀` in a quantified hypothesis and where a quantifier is
part of the statement itself, after the colon: `(all: ∀ (x: a) => x ∈ xs →
p x)`, `theorem t (p: Nat → Prop): (∀ (n: Nat) => p n) → p 0` (D3458). It is
the same term as `(x: T) → p`, so it's applied and introduced as before
(`all x mem`, `n => …`). A function type that isn't a proposition stays an
arrow, `(n: Nat) → Vec Nat n`. Goals print a quantified proposition with `∀` too, including one whose
result is a hypothesis's predicate applied to arguments (`∀ (x: a) => p x`,
with `p: a → Prop`). Messages, which have no types for the variables, show
that as `(x: a) → p x`. Write an ability row's result type
without parentheses: `{Fail} List Nat`, not `{Fail} (List Nat)` (D2307).
After a row whose first ability starts lowercase (`{e}`, `{e, f}`) or an
empty row `{}`, keep the brackets around a result that starts with a section,
a prefix operator, `match`, `if`, `include` or the like (`{e} (.f)`,
`{e} (-x) * y`): without them the row reads as a record joined to what
follows. An application or an atom needs none (`{e} f x`), and a row that
starts with an ability (`{IO | e}`, `{Fail, e}`) never reads as a record.
Build and match lists with brackets: `[x, ..xs]` and `[a, b, ..rest]`,
not `Cons x xs` (D2324); `Cons` stays only where it's used as a function
(`t => Cons t rs`, `fold Cons`). A rest before an append and an append
around a bracketed list are the same term to the checker: they compute to the
same list, so a motive may rely on either form.

```stitchwort
theorem same (x: Nat) (xs ys: List Nat):
    [x, ..xs ++ ys] = [x, ..xs] ++ ys := byComputing
```

Values that a lemma's own hypotheses or result determine go in square
brackets, as implicit parameters, so no caller writes `_` for them (D2422).
`Bool.andRight` is stated `[a: Bool] [b: Bool] (h: (a ∧ b) = True): b = True`
and called `Bool.andRight settled`, not `Bool.andRight _ _ settled`: the
checker reads `a` and `b` off the type of `settled`. Keep a parameter
explicit when callers have to supply it:

- it is not fixed by a later explicit argument or by the expected type
  (`List.distinctRange a b`, whose statement only mentions them);
- it is a function or predicate the hypothesis's type can't recover, such as
  the `p` of `List.memFilter xs p x` (higher-order unification guesses wrong
  and the error shows up far from the call);
- the lemma is passed as a function value (`List.all2Weaken rowWritten`),
  since implicit parameters are filled in where the name is used and the
  value then no longer has the function type expected.

When one call does need a value of an implicit parameter, name it:
`Bool.andLeft [a := Set.contains a key] [b := Set.contains b key]
(rewrite … in held)`.

A chain `a && b && c` nests to the right, `a && (b && c)`, so `Bool.andLeft`
gives `a = True` and `Bool.andRight` gives `(b && c) = True`, not `b = True`.
To reach `b`, take the right part first: `Bool.andLeft (Bool.andRight held)`,
and `c` is `Bool.andRight (Bool.andRight held)`.

Two kinds of lemma keep their parameters and binder kinds, because the
compiler applies them itself. Congruence lemmas (`FCong`, `FCongMem`,
`FCongRange`) have the parameters of `F`: `rewrite` and `decreasing` check
that shape and build explicit applications (`Option.mapCong` stays
`(x: Option a) → (f1: a → b) → (f2: a → b) → …`). And a lemma that
`crates/elab/src/omega.rs` or `Decidable.elimEq`'s users build calls to
changes only together with the code that builds them.

### A statement that spells out a match

A theorem statement that spells out a `match` is checked as any `match` is,
with the theorem's parameters, including its hypotheses, in scope, so a
hypothesis that rules out one of the arms makes that arm `W-UNREACHABLE`
("this case can't happen: here `selected` is `None = Some value`"). It still
checks, but the warning is right: the arm can never be reached, and std's
`the_library_has_no_unreachable_arms` test fails on it. Hold the match in a
small helper definition, where no hypothesis is in scope, and state the
theorem about the helper (as `Parse.oneValue` does for `Parse.runsOneStep` in
`crates/elab/src/std/Parse/Runs.sw`):

```
-- warns W-UNREACHABLE on `| None`: `selected` rules that arm out
theorem selectedIsValue ∀ (chosen: Option Nat) (value: Nat) (selected: chosen = Some value):
    (match chosen with
      | Some value => value
      | None => 0) = value :=
  rewrite selected then byComputing

-- no warning: the match is in a definition, out of `selected`'s scope
def oneValue (chosen: Option Nat): Nat :=
  match chosen with
    | Some value => value
    | None => 0

theorem selectedIsValueViaHelper ∀ (chosen: Option Nat) (value: Nat) (selected: chosen = Some value):
    oneValue chosen = value :=
  rewrite selected then byComputing
```

A statement that spells out a Prop-valued `match` (`match t with | A => x = 1
| B => True`) can also fail with `E-AUTO-NONE` when `auto` needs a proof of
it: the match is checked where it is written, and the same match written again
is a different helper, so hold it in a helper definition and state the
theorem, its hypotheses and the lemmas about the helper, as above.

## 2. Workflow

1. **State it with `?` first, and read the goal.** Write the statement with
   `?` as its proof, then `stitchwort check`. The checker carries on past
   `?` and prints what goes there:

   ```
   theorem lengthAppend ∀ (xs: List Nat) (ys: List Nat): List.length (List.append xs ys) = List.length xs + List.length ys :=
     match xs with
       | Nil => byComputing
       | Cons x rest => ?
   ```

   ```
   [GOAL] Goal: in `lengthAppend`
      │                      ╰── ys: List Nat
      │                          x: Nat
      │                          rest: List Nat
      │                          ⊢ Succ (List.length (List.append rest ys)) = List.length rest + List.length ys + 1
   ```

   Goals are shown as written: a call stays a call until it can take a
   step at once, and then it is shown after that step. Here
   `List.length (List.append (Cons x rest) ys)` matches on its `Cons` at
   once, so it shows as `Succ (…)`, while `List.length rest` stays as it
   is (§3 says what `rewrite` and `match` search). A declaration with a `?` is
   unfinished, not wrong: later declarations can use it by its type, so you
   can state lemmas with `?`, use them in the main theorem, and prove them
   afterwards. But `check` fails while any `?` is open, and so does `audit`
   ([syntax.md](syntax.md#goals-)). `check --index -` gives the same goals
   as JSON.
2. **Search for counterexamples early**, before spending time on a proof:
   `stitchwort check --counterexamples --verbose NAMESPACE`. It tries up to
   10,000 inputs per theorem, proved or not. The verdicts, as printed
   (run on a scratch file):

   ```
     ✗ subAdd       counterexample: a = 0, b = 1
     ! vacuous      gave up: the hypotheses held in 0 of 10000 cases (if they contradict each other, the theorem is vacuous)
     ~ addSub       none in 10000 cases (sizes up to 98; evidence, not a proof)
     - sortedShort  gave up (hypotheses true in 526 of 10000 cases)
   searched 4 theorems for counterexamples: 1 false, 1 with none found, 2 gave up (1 with the hypotheses true in no case), 0 inconclusive, 0 not applicable
   ```

   - `✗` **counterexample**: the statement is false. Fix the statement (or
     the program), not the proof.
   - `!` **hypotheses held in no case**: `theorem vacuous (n: Nat) (h: n + 1 = 0): n = 42 := arithmetic`
     checks, and proves nothing. Printed even without `--verbose` when the
     proof checked. Narrow hypotheses (a list of exactly 50 elements) can
     also hold in no case; read the statement and say which it is.
   - `~` **none found**: evidence, not proof. **Weak evidence** is a `~`
     whose hypotheses held only for small inputs, and it can hide a false
     statement. This one is false (an increasing list of 6 elements), yet
     the search found nothing (`examples/goals/counterexample-weak-evidence.sw`):

     ```
       ~ shortIncreasing  none in 10000 cases (evidence, not a proof), but the hypotheses held only for inputs of up to 5 constructors of the 40 made: weak evidence, unless they allow no larger ones
     ```

   - `-` **gave up** (the hypotheses held in under 1 case in 10),
     **inconclusive** (out of steps), **not applicable** (a function
     parameter, an indexed type, `Exists`, …): the search says nothing
     either way.

   A failing proof, or a `?`, also gets a counterexample note when the
   search finds one ("this statement is false; a counterexample: …").
3. **Small lemmas.** A lemma over any `keep` function, then instantiated,
   checks where the same fact about the real, large function blows up
   (aoc/NOTES-2024.md:1497–1500). A lemma stated for any list that has a
   property, instantiated once at the end, avoided a 130,321-element list
   being computed (aoc/NOTES-2024.md:7290–7298). One fact per lemma also
   makes `arithmetic [lemma …]` and `cases then t` easy to feed.
4. **`stitchwort test` for programs.** Tests are run-time checks of closed
   `Bool` expressions, not proofs. Use them for parsers, examples and the
   puzzle answers; prove the rest. Results are cached; `--no-cache` runs
   them again.
5. **The check cache.** `check`, `test` and `run` reuse checked
   namespaces from `.stitchwort/cache` in the project folder, keyed by the
   source, its dependencies and the compiler. A warm check of a proof
   namespace takes about 0.25 s, a cold one seconds (agentic-proving.md §6).
   Hits are trusted without the kernel checking them again
   ([check-cache.md](proposals/check-cache.md), stage 3). Use `--no-cache`
   to time a check, and if you suspect a stale answer.
   **The loop for one theorem in a big namespace (SW-4197).** The cache is
   per namespace, so editing any theorem makes `check NAMESPACE` check the
   whole namespace again. Measured with a release build, warm (tools/fmt,
   19 Nov 2026): a one-line edit in `Syntax.ReadBackHungApp` (7 theorems,
   661 lines) costs 14 to 15 s to `check`; `check --only
   Syntax.ReadBackHungApp.appAnyHung` costs 1.8 to 5 s for the theorem
   alone, about 1.4 s of it loading the namespace's 17 dependencies from
   the cache. A warm, unedited check is 0.6 to 0.9 s. So while editing a
   theorem, run `stitchwort check --only NAMESPACE.theorem` (the output
   says how many theorems were NOT checked), and run the plain `check
   NAMESPACE` once at the end (and before the report), since only that
   checks every theorem. Two limits: `--only` checks the theorems it
   names and those they use, so it doesn't see what a later theorem in
   the file breaks; and after editing a namespace, checking a namespace
   that uses it (`--only Down.thm`) still checks the edited one in full
   (22 s for `ReadBackHungFull` after an edit in `ReadBackHungApp`),
   because only the namespaces you name are pruned. Naming the edited one
   too (`check --only Down.thm Up`) prunes both, but saves nothing when
   `Down.thm` needs all of `Up`'s theorems (it did, 23 s). Edit and check
   the theorem in its own namespace, and check downstream ones at the end.
6. **Work in a scratch file** for experiments (a lemma's shape, an error you
   don't understand), outside the repo or in the scratchpad, checked with
   `stitchwort check file.sw` (file mode: only `Std` is visible).
7. **Comment sparingly, with one exception: the proof idea** (D3657, Matt,
   16 Nov 2026). A theorem's statement is usually its doc: give it a `--|`
   doc only to say which part of the spec it covers or why a hypothesis is
   needed. Inside a proof, a `--` note is for what the proof can't show, such
   as why a lemma is stated more generally or why a definition is `opaque`
   (§1, rule 4). Don't narrate the steps
   ([syntax.md](syntax.md#what-to-write)). The exception: a theorem whose
   proof runs over about 15 lines ends its doc with the **proof idea**, one
   or two sentences naming the induction, the key lemma or the invariant
   (a sketch of the shape, not a real theorem):

   ```
   --| The first row of the region after reading the bits is their value: by
   --| induction on the bits, where each letter halves the region and the
   --| first row gains the bit's value.
   theorem regionFirstRow …
   ```

   A proof is hard to make read as itself; the idea says which proof it is,
   so a reader can follow the detail, and a repair can check that the plan
   still holds. It names the plan, not the steps: "by induction on `xs`;
   the cons case uses `lengthAppend`" is an idea, "rewrite with `addComm`,
   then …" is narration.
8. **State, don't chain** (D3656, Matt, 16 Nov 2026). Every fact a proof
   passes through should be on the page where a reader, or an agent
   repairing the proof, can see it. Two parts:
   - A chain of two or more equalities is a `calc`, one line per step, not
     `Eq.trans a (Eq.trans b c)` or `(a.trans b).trans c`. `check` warns
     (`W-PROOF-CHAIN`) on `trans` nested two deep, however it is laid out, and the fix is
     the `calc`: the intermediate terms are the ones the nest left out. A
     single `Eq.trans a b` is fine.
   - A `rewrite` run of more than about three rules, or one whose result a
     later step depends on, passes through a typed `let` (or an ascription)
     that states the fact reached: `let reached: a + b = b + a := rewrite …`,
     then the rest. A change to a rule then breaks at the stated fact, with
     a goal to compare, not three steps later.

   Existing proofs move over when they are next touched, not in a sweep.
9. **Name or leave out a lemma's arguments** (extends D2367 to proofs). An
   argument that unification fixes is `_`, or implicit in the lemma's
   statement: `Nat.addComm _ b`, not the whole term again. A lemma call with
   more than about four arguments left explicit names them,
   `lemma (tree := later) (rest := k) h`, so a reordered parameter
   fails at its name, and a reader can tell which argument is which.

## 3. Tools, and when each fits

Import what you use: std's theorems live in namespaces that need an import
(`import Std (Nat)` for `Nat.modLt`; without it, `E-UNKNOWN-NAME` says so).

| Goal | Tool |
|---|---|
| Both sides compute to the same value | `byComputing` |
| Finitely many cases, each closed by computation, a hypothesis or arithmetic | `cases` |
| Linear arithmetic on `Nat`/`Int` from facts in scope | `arithmetic`, `arithmetic [facts]` |
| An equation of polynomials | `algebra`, `algebra [h]` |
| A closed decidable proposition | `byDecision` |
| A `Bool` property of every value of a finite type, more than 64 cases | `Finite.check` |
| Replace one side of an equation inside the goal | `rewrite` |
| Rewrite with several equations until none fits, then close | `rewrite repeatedly [rules]` |
| A chain of `=`, `<=`, `<` steps | `calc` |
| Induction | recursion in the theorem (structural, or `decreasing`) |
| Induction over a nested type (`List T` inside `T`) | `T.induct`, `T.inductMem`, `T.size` |

- **`byComputing`** proves `a = b` only when both sides compute to the same value.
  `+` recurses on its first argument, so `1 + c` computes to `Succ c` and
  `c + 1` doesn't (aoc/NOTES-2024.md:824–836). A goal stuck on a variable
  needs a `match`, `cases` or a lemma.
- **`cases`** finds what the goal is stuck on (a variable or call of a type
  with two or more constructors), splits it as a `match` would, and closes
  each case by computation, a contradictory hypothesis, a hypothesis of the
  goal's type, `arithmetic`, or by running the goal's decision procedure (as
  `byDecision` does). It introduces a goal's leading binders itself
  (`theorem t: (x: Bool) → P x := cases`). When nothing is stuck and nothing
  closes it, it falls back to splitting a variable the goal mentions, the
  one that makes the fewest cases. `cases then t` tries `t` in every case
  first, and splits the condition of an `if` the goal shows before what it
  is stuck on inside definitions, so each case's goal keeps the calls `t`
  names. A hypothesis `h: Some x = Some y` (any one constructor on both
  sides) gives `x = y`, and `cases` then replaces `y` by `x` in the goal and
  the hypotheses, so `f x = f y` needs no `rewrite` or `Eq.cong`; in
  `cases then t`, `t` may still name `y`. Inside a `cases then …`
  continuation a constructor's fields have hygienic names (shown as
  `record✝`) that a proof can't write, so `match` on the constructor first
  to name them. `cases then (lemma inner)` doesn't refine `inner` in the
  lemma's type: bind the lemma's result with a `let` first (`let step :=
  lemma inner`), and `cases` refines `step`'s type. An equation with no variable side (`f x =
  f y`) is only kept as a fact, not rewritten with. An `Int` `==` that a test depends on (`if x + 1 == y then …`) is
  split as one `Bool`, true or false, and `arithmetic` reads it in each case;
  `cases` doesn't take the `Int` apart into `OfNat` and `NegSucc`. At most
  **64 cases** (or 20 million evaluation steps), then `E-CASES-BUDGET`. It doesn't do
  induction (`List`, `Nat`). Examples: `examples/accept/cases-*.sw`.
- **`arithmetic`** proves `<=`, `<`, `=` on `Nat` and `Int` (and contradictions)
  from every arithmetic fact in scope: parameters, pattern variables, a
  plain `if`'s condition and a `match`'s equation in a `decreasing`
  definition (neither needs a name), and `let`s. Pass other facts as
  `arithmetic [lemma a b]`. It knows `-`, `max`, `min`, multiplication by a literal, and `x / k`
  by a literal only by its two bounds (`(x / k) * k ≤ x ≤ (x / k) * k + k -
  1`); `x * y`, `x % k`, `List.length xs` and calls are atoms it knows
  nothing about. It reads a hypothesis `x ∈ a ..< b` (or `..=`) as `a ≤ x` and
  `x < b`, and proves such a goal from the bounds. It doesn't know what `% 2` is: pass `Nat.divModEq` and
  `Nat.modLess` for each (aoc/NOTES-2024.md:7304–7311). Its failure
  message's model "may not be a real counterexample". Division is total
  (`x / 0 = 0`, `x % 0 = x`, as in Lean), so `Nat.divModEq` and most
  remainder lemmas (`Nat.modMod`, `Nat.modAddMul`, `Nat.mulModMod`) hold for
  every divisor and take no hypothesis; the few that are false at 0
  (`Nat.modLess`, `Nat.modLt`, `Nat.divAddMul`, `Int.modNatLt`) ask for
  `d ≠ 0`.
- **`auto`** isn't a proof term: it is the compiler filling an `[auto h: P]`
  argument, from evidence given by name, a hypothesis in scope of exactly
  that type, or a decision procedure (DESIGN.md "`auto` and `Decidable`").
  Its search stops after 8 levels of nested decisions; past that, pass the
  proof (`d.sound byComputing`), as the roguelike did for its 7th key
  (games/rogue/PROOFS.md:192). An `if h: …` puts `h` in scope for `auto`.
- **A decision is a record**, `{ holds: Bool, sound: holds = True → p,
  complete: p → holds = True }` (D3483, SW-2746). Build one test first,
  `{ holds = Nat.equal m n, sound = …, complete = … }`, so that `==`
  computes to the test, or with `Decidable.yes h` and `Decidable.no r`
  (`import Std (Decidable)`). To split on one, write `if h: p then … else
  …`: `h` is the proof of `p` in the first branch and its refutation in the
  second, and nothing in the goal is rewritten. To refine a goal or
  hypothesis that has an `if` on `p`, match on the test: `match e: x < y
  with | True => … | False => …`, where `e` is the proof in the `True` arm.
  A hypothesis `e: (x == y) = False` becomes `x ≠ y` with
  `DecEq.soundFalse x y e` (or `Decidable.refute d e`), and `e: … = True`
  becomes `x = y` with `DecEq.sound e` (or `d.sound e`). `d.holds` is the
  `Bool` a decision stands for. A goal that holds the decision itself (the
  `if h:` of a program whose branch uses `h`) splits by a `match` on the
  record, `| { holds = True, sound = s, complete = _ } => … s byComputing …`, or,
  when that is refused (`E-MATCH-MOTIVE`: the decision computes to its
  fields), by a `match` on what its test waits for (`match h: cave.height
  with | Zero | Succ _`; `aoc/src/Aoc/Year2021/Day15/Proofs/Levels.sw`).
- **`byDecision`** (`import Std (byDecision)`) is Lean's `by decide`: it
  proves a closed proposition by running its decision procedure. False is
  `E-AUTO-FALSE`; stuck on a variable is `E-AUTO-STUCK`, so split the
  variable with `cases` or use `Finite.check`.
- **`Finite.check p byComputing x`** proves `p x = True` for every `x` of a finite
  type by computing `p` on each value of `Finite.all`. Put several variables
  in one record or pair. It is the way past `cases`' 64 cases: 2^10 values
  take about 0.1 s, 2^16 about 12 s (`examples/accept/finite-check.sw`).
  Data types without recursion or `Nat` fields get `Finite` derived.
- **`rewrite repeatedly [rules]`** (docs/syntax.md, "`rewrite repeatedly`")
  is for a goal that needs the same few lemmas in several places, in an
  order you would otherwise work out by hand: `List.appendAssoc` and
  `List.filterAppend` across a list of pieces, or a printer lemma and the
  recursive call in each arm. Reach for `byComputing` first (what computes
  needs no rule), then one `rewrite` where one step does it, then
  `rewrite repeatedly`. List lemmas with their arguments left open, unless
  `match` or `cases` has computed the goal past the lemma's left side as
  written: then give the arguments (`wordsSnoc comment [" ", ..out]`), or the
  search compares by computing, which is slow for large terms and may not
  find it. A rule that fits its own result (`Nat.addComm`) is refused; use
  `algebra`. After `then`, state what is left (`then (t: P)`) or close with
  `arithmetic` or `cases` (W-REWRITE-REPEATEDLY-UNSTATED).
- **`rewrite p then t`** replaces `p`'s left side by its right side in the
  goal and checks `t` against the result; `rewrite <- p`, `rewrite p at h`.
  It needs a known goal (`E-REWRITE-NO-GOAL` otherwise). It replaces every
  occurrence of the first instance it matches. It looks for the left side
  in the goal *as written* first (the form goals are printed in, calls kept,
  so `rewrite isSafeCorrect _` finds `isSafe { levels = xs }` and the next
  goal keeps `isSafe`), and uses that when no copy of the left side is
  left hidden inside a call; otherwise, and when it finds nothing, in the
  goal *as it computes*, so a rule can still rewrite inside a definition.
  When both find nothing, a call the goal shows that steps at once (an
  argument is known: `(printer.write " ").words`) is still found, with the
  rule's open arguments solved from the call's. Arithmetic the goal already
  unfolded is not there to find (8 items in agentic-proving.md §5 E). Give
  the rule its arguments when you can (§6). Inside a function argument it
  goes through the call's congruence lemma (`List.mapCong`, …). A rule for
  `/` also rewrites the `/` inside `x % 2`, since `%` computes to
  `x - x / 2 * 2`: rewrite the `%` rule first (SW-976 item 4, AoC 2021
  day 16 notes).
- **`match e:` and `cases`** look for `e` the same way: in the goal and
  the hypotheses *as written* first, comparing up to computation, so
  `xs.map (f a)` finds the goal's `xs.map (y => f a y)` and the arms keep
  the goal's calls (`double a`, not `a + a`). They keep that only when it
  replaces everything the search *as it computes* would; otherwise (a copy
  of `e` inside a definition the goal mentions, or an `e` that computes
  to a constructor) they replace what that search finds, and the arms'
  goals hold no calls (`examples/accept/match-as-written.sw`).
- **`calc`** chains steps `_ = e := proof`, `_ <= e`, `_ < e`; a step with
  no proof is `byComputing`. Use it when `rewrite` picks the wrong occurrence, or
  to say exactly which form you want.
- **Induction is recursion.** A theorem that calls itself on a smaller
  argument is a proof by induction; the recursive call is the induction
  hypothesis. For other measures, `decreasing e` (or `decreasing (m1, m2)`)
  after the type: each recursive call needs a proof that the measure went
  down, from `auto` (a guard `if next < n` in scope) or `[decreasing :=
  proof]`. `f.unfold x` is a `decreasing` definition's own equation, for
  `rewrite f.unfold x then …`; on unknown arguments `f x` doesn't unfold by
  itself.
- **Arms have equations.** Every `def` with arms gets `f.eq1`, `f.eq2`, …
  (one for each arm, in the order written): the call on that arm's patterns
  equals its body. An arm an earlier arm overlaps takes a hypothesis for
  each overlap (`notArm1: x ≠ 3`). `stitchwort doc f` lists them, with `[stuck]` on the ones
  to use and the reason for any it couldn't make. Prefer one to `f.unfold`
  plus a hand-written `match`, or to a helper lemma that restates a step.
  They help where `f`'s call is stuck: on a variable (`rewrite f.eq3 x h1 h2
  in …`, the hypotheses proved by `omega` or `rfl`), and in `decreasing` and
  `opaque` definitions. A call with constructors already computes, so
  `rewrite f.eq2 then …` there is `E-REWRITE-NOTHING`: let `byComputing` or `cases`
  compute it. Adding an arm renumbers the ones after it, and a name that no
  longer exists is `E-UNKNOWN-NAME` pointing at `doc`.
- **Nested types**: for `type Packet = | Number (value: Nat) | Packets (items: List Packet)`,
  the compiler generates `Packet.size`, `Packet.induct` (the `Packets` case
  gets `List.All motive items`) and `Packet.inductMem` (every member `q`
  with `List.Mem q items`). `decreasing Packet.size p` with `items.attach`
  makes recursion through the list need no proof
  (`examples/accept/nested-data-induction.sw`).
- **Hypotheses are ordinary values.** Pass them on, take them apart with
  a tuple pattern (`let (x, a, b) := h`), `match`, `.left`, `.right`;
  `Void.impossible` from a contradiction.

## 4. Common errors and what they usually mean

Each was run on the example named; the output is quoted, shortened.

- **`E-CANNOT-INFER`**: a type isn't known yet where it's needed, usually a
  lambda's parameter or a record literal before what fixes it
  (15 items in agentic-proving.md §5 D). Annotate it.

  ```
  [E-CANNOT-INFER] Error: can't tell what `p` is, so can't look up `.name`
    Note: … annotate it, as in `(p: Person) => p.name`, or write the function's full name
  ```
  (`examples/reject/dot-cannot-infer.sw`.) `E-UNSOLVED` ("can't work out an
  implicit argument") is the same problem for an implicit: give it with
  `f [x := …]`.
- **`E-REFL`**: the two sides don't compute to the same value. Usually the
  goal is stuck on a variable (needs a `match`, `cases`, or a lemma such as
  `Nat.addComm`), or the statement is false; check the counterexample note.

  ```
  [E-REFL] Error: `byComputing` can't prove this
    │ theorem plusComm (n: Nat) (m: Nat): n + m = m + n := byComputing
    │                                                       ╰─── `n + m` and `m + n` aren't equal
    │ Note: `byComputing` proves `a = b` only when both sides compute to the same value
  ```
  (`examples/reject/plus-comm-by-rfl.sw`.)
- **`E-CASES`**: a case nothing closed. The notes give that case's
  hypotheses, its goal, and often a counterexample, which usually means the
  statement is false:

  ```
  [E-CASES] Error: `cases` couldn't close the case it reached by the splits a = True, (n <= 2) = False
    Note 1: h: n ≤ 3
    Note 2: goal: False = True
    Note 5: this statement is false; a counterexample: a = True, n = 3
  ```
  (`examples/reject/cases-open-case.sw`.) If it's true, give the case's
  proof with `cases then t`.
- **`E-CASES-BUDGET`**: more than 64 cases, or more than 20 million
  evaluation steps (a goal holding a large computation, such as a whole
  drawn map; state the fact about one row or cell instead and prove that).
  The note says what it split,
  and, when every variable is finite, points at `Finite.check`
  (`examples/reject/cases-budget.sw`). Otherwise prove a fact that decides
  several cases at once and pass it with `cases then t`, or `match` by hand.
  A record type with many fields can exhaust the budget without an
  interesting case: `cases` falls back to splitting each field, and 11
  fields of a few values each multiply past 64 cases. Match on the
  constructor first (`match r with | Row a b … => cases`), then use `cases`
  on the one field that matters.
  The same error comes sooner when a case grows too large to split: a
  goal and hypotheses that, written out in full, have more than a million
  parts (`examples/reject/cases-split-too-large.sw`).
- **`E-ARITHMETIC`**: the facts don't give the goal. "an integer model …
  satisfies the facts" names values for the atoms; often a fact is missing
  (pass it in `arithmetic […]`) or an atom hides arithmetic (`x % 2`, `x / 2`,
  a call). With a counterexample note, the statement is false
  (`examples/reject/omega-integer-model.sw`). Very large coefficients fail
  differently: near 2^160 they are "too large" for the search, and a chain
  near 2^106 runs it out of budget, so keep coefficients under about 2^110.
  State small lemmas that eliminate one variable per call instead of one
  `arithmetic` over the whole chain.
- **`E-MATCH-MOTIVE`**: generalising a `match`'s scrutinee makes the type
  ill-formed, because something else in the type depends on it. The note
  says the fix: a top-level helper with a written signature
  (`examples/reject/match-bad-motive.sw`).
- **`E-REWRITE-*`**:
  - `E-REWRITE-NOTHING`: the left side isn't in the goal as written, nor as it computes. The
    notes show the goal "as written" and "as it computes", and say when the
    goal already holds by computing (`examples/reject/rewrite-nothing.sw`).
    When the note says the goal already computed past the rule, a side with
    no variables has folded to a literal: close that step with `byComputing`,
    or use `J` with an explicit motive. The elaborator also folds closed
    constants in a type annotation (`Float.Model.pow2 1074` becomes its
    value), so a rule about `pow2 1074` can silently find nothing there;
    `J` with the motive written out works.
    A `match c: e` refines the hypotheses that mention `e` as well as the
    goal, so inside its arm a hypothesis already has the branch's form: use
    it as it is rather than rewriting it
    (`examples/reject/rewrite-refined-by-match.sw`). A proof follows a
    program's `if` by matching on its `Bool` (its condition), or on the
    comparison's decision when the arms need its proofs; also for `if a && b`: one
    `match e: a && b with` refines the goal, and `arithmetic` reads `e` as
    `a ∧ b` or `¬(a ∧ b)` (`examples/accept/match-if-and.sw`). Usually the goal
    unfolded the definition first: rewrite with a lemma about the unfolded
    form, or state the step with `calc`.
  - `W-MATCH-NOT-FOUND`: a `match h: e` whose `e` is in neither the goal nor
    a hypothesis (as they compute) refines nothing, so each arm has the goal
    unchanged. It is given when the arms don't use `h`, and also when they
    fail to check, so that the arms' errors (an unsolved `?42`, an unfolded
    parser run) are read beside the cause. The note shows the goal as the
    search saw it; write `e` as that shows it. (A function argument written
    `f x` where the goal has `y => f x y` is found as written, unless the
    occurrence is only inside a call.) Day 12's `% 90` against the program's
    `% 45` is this (`examples/reject/match-not-found-arm-fails.sw`).
    An unnamed `match` is given it too, but only when its arms fail: it
    is often a case split for the arms' own sake (SW-1721,
    `examples/reject/match-not-found-unnamed.sw`).
  - `E-REWRITE-MOTIVE`: replacing the term makes the goal ill-typed, usually
    because an `auto` proof (the `i < xs.length` in `xs.getLt i`) is about
    it. Rewrite a larger term (`xs.getLt i`), or use `calc`
    (`examples/reject/rewrite-motive-auto.sw`).
  - `E-REWRITE-PREMISE`: the rule matched but its premise (`x ≤ n`) isn't a
    hypothesis and `arithmetic` can't prove it; give it in the rule
    (`examples/reject/rewrite-premise-unproved.sw`).
  - `E-REWRITE-NO-GOAL`: no expected type; ascribe it, `(rewrite p then t: a = b)`,
    or use `rewrite p at h`.
  - `E-REWRITE-BUDGET`: the comparisons were too expensive. That says
    nothing about whether the occurrence is there; use a more specific rule
    or `calc`.
  - `W-REWRITE-UNCONFIRMED`, `W-MATCH-UNCONFIRMED`: the search over what
    the goal computes to ran out (the goal is too large unfolded, or the
    budget went), where the `rewrite` or `match` used to fail with
    `E-RESOURCE` or `E-REWRITE-BUDGET`, so the term was replaced only where
    the goal and hypotheses show it, without checking for copies inside
    calls. The proof is still checked in full: a copy left inside a call
    makes a later step fail (the body, an arm) with its own error, never
    makes a wrong proof check (`examples/accept/as-written-unconfirmed.sw`,
    `examples/reject/as-written-unconfirmed-copy.sw`). To get the full
    search back, make the large argument a variable.
- **`E-AUTO-NONE`, `E-AUTO-FALSE`, `E-AUTO-STUCK`**: no decision procedure
  (or one not yet checked, `examples/reject/auto-waiting.sw`); the
  proposition is false (`examples/reject/auto-membership-absent.sw`); it's
  stuck on a value not known here:

  ```
  [E-AUTO-STUCK] Error: can't decide `(b || not b) = True` here
    ╰── it involves values that aren't known here, and computing it doesn't settle it
    Note: establish it first, with `if h: … then … else …`
  ```
- **`E-TERMINATION`**: a recursive call isn't on a piece of an argument.
  Add `decreasing e`, or recurse on the pattern's own variable:

  ```
  [E-TERMINATION] Error: can't show that `half` terminates
    ╰── this recursive call might not terminate: the 1st argument, `predecessor n`, isn't seen as smaller
  ```
  (`examples/reject/non-structural.sw`.) When the recursion follows a value
  that isn't a part of an argument (halving a number, walking a graph), a
  depth limit makes it total and provable: an extra `fuel: Nat` argument,
  decreased at each call, failing (or returning a default) when it runs out.
  **`E-DECREASING`** is the same with
  `decreasing`: the message shows the goal (`n - step < n`) and what's in
  scope; give `[decreasing := …]` or guard with `if … then`
  (`examples/reject/decreasing-missing-proof.sw`). A later call's decrease
  can't come from an earlier recursive call's result: the checker knows the
  arguments' parts, not facts about the function's own result. Take the
  result apart and guard the next call (`| Succ k => if h: k < n then f k
  else …`), or carry the bound in an argument (SW-976 item 6, AoC 2021 day
  16's decoder; it used the run-time guard).

  ```stitchwort
  def throughResult (n: Nat): Nat
      decreasing n
  :=
    if one: 1 < n then
      match throughResult (n - 1) with
        | Zero => 0
        | Succ k => if h: k < n then throughResult k else 0
    else 0
  ```
- **`E-RESOURCE`** ("ran out of resources"): not a type error and not a
  failed test; the checker gave up within its limits. In proofs it usually
  means a definition is being computed in full, on a big literal or on
  unknown arguments. Run on a scratch file
  (`theorem countBig: count 10000000 = 10000000 := byComputing`, with `count` a
  recursive copy of the identity):

  ```
  [E-RESOURCE] Error: ran out of resources: it recursed more deeply than allowed
    │ theorem countBig: count 10000000 = 10000000 := byComputing
    │                       ╰─────────────────────── while checking this
    │ Note 1: this isn't a type error or a failed test: there's no answer within the limits
    │ Note 2: it happened while checking `countBig`
    │ Note 3: it ran out while unfolding `count`
  ```
  The last note names the definition being unfolded (for "a value was too
  large to write out" too, unless it is the standard library's); when it
  doesn't, find it by replacing parts with `?`. Then see §6. Other forms:
  "a value was too large to show" (aoc/NOTES-2024.md:1479–1485). A `match`
  that runs out on a call given a number also says so: "`outer` is called
  here with the number `12`, so it is computed in full: make the number a
  variable, stating a lemma for any `n`, and use the lemma with `12`"
  (`examples/reject/as-written-unconfirmed-slow-check.sw`).
  A check can take minutes before it runs out (its limit is 10 billion
  evaluation steps). While it runs, `stitchwort check` says which
  declaration it is on and what it is unfolding, after 250 million steps
  (about 7 s) and each time the steps double:

  ```
  note: still checking `Main.t`: over 250,000,000 evaluation steps so far, unfolding `countdown` (it stops at 10,000,000,000)
  ``` Two of the roguelike's
  three failures in one proof were this (games/rogue/PROOFS.md:216–226).
  A `rewrite` or `match` whose goal (or a hypothesis) is too large once its
  calls are computed, on a call with a large literal such as
  `settle plan 1000`, no longer fails this way when the term is shown in the
  goal: it is rewritten or refined where it is shown, with
  `W-REWRITE-UNCONFIRMED` or `W-MATCH-UNCONFIRMED` (below). Where it
  isn't shown, it is still `E-RESOURCE`: state the lemma for any `limit`
  and instantiate it (AoC 2020 day 11's `settledExactly`).
- **`E-TYPE-MISMATCH` with a computed type**: the expected type is shown as
  it computes, which can look unlike what you wrote: `lcg seed < 2147483648`
  is expected as `… % 2147483648 ≤ 2147483647`, and `Nat.modLt _ _` with
  holes then doesn't match. Give the lemma its arguments
  (`Nat.modLt (seed * 1103515245 + 12345) 2147483648` checks).
- **`expected Float.isValid N`**: a local equation about a float constant
  in scope (`pv: Float.Model.pow2 1074 = …`, or one about `units` of a
  literal) can make the checker fill a
  float literal's validity proof with `pv`, giving `expected Float.isValid N`.
  Inline the step with `byComputing` instead of keeping the local equation
  (bug SW-3887).

When a message hid the real problem (22 items in agentic-proving.md §5 C), say so in the
report: messages get fixed from those reports.

## 5. Finding lemmas

Std has about 2,500 theorems (`grep -rhoE "^theorem [A-Za-z.]+"
crates/elab/src/std | wc -l` counts 2496). Our lanes twice rewrote lemmas
std already had, and found others only by grepping (aoc/NOTES-2024.md:373,
7934–7937). Search by type before writing a lemma: `stitchwort search`
finds std's and the project's theorems (and functions) by the shape of their
statement, and says what to import
([syntax.md](syntax.md#lemma-search-stitchwort-search)):

```
stitchwort search 'List.length ((_: List _) ++ _) = _'   # a statement's shape
stitchwort search '⊢ Not (Less = Greater)'              # conclusions only
stitchwort search '(?a: Nat) ≤ ?b → ?b ≤ ?c → ?a ≤ ?c'  # ?x: the same term each time
stitchwort search --rewrite 'List.map (List.map _ _) _' # equations and Iffs to rewrite with
stitchwort search 'Nat → List _ → List _' --definitions # a function by its type
```

**To find out what a function does, run `stitchwort doc NAME` before reading
its source** (`stitchwort doc List.filterMap`, `stitchwort doc Shape.scale` in
a project). It prints the header with its parameter names, the doc, the tests
and `…Example` theorems named after it (the quickest way to see how it is
called and what it returns), and its theorems, the rewrite rules first, with
the command that lists all. `stitchwort doc Option` or `stitchwort doc
Aoc.Year2024.Day06` lists a namespace's declarations with their summaries.
`--theorems 0` skips the check, so it is instant
([syntax.md](syntax.md#what-a-declaration-does-stitchwort-doc)). `stitchwort
search '"filterMap"'` ranks the declaration with that name first, then the
theorems that merely contain it.

**See the goal at any point with `stitchwort goal --at FILE:LINE[:COL]`.**
You don't need a `?` there: it prints the names in scope and `⊢` the goal at
that point of a finished or half-written proof (`expected T` in program
code). On a step it gives the goal before and after: put the point on each
rule of a `rewrite` chain in turn, on an arm's pattern, or on a `calc` line's
`_`, to follow the proof without editing the file; on an expression that
fails, it gives the goal it had to prove. `--json` gives the same for a
script (`context.step` has `before`, `after` and `rule`). Exit 2 means
nothing was checked there (a comment); a file of a project is read in the
project from any folder, taking about as long as `check` of the file
([syntax.md](syntax.md#the-goal-at-a-point-stitchwort-goal---at)).

**At a `?`, run `stitchwort search --at FILE:LINE` before writing a proof by
hand.** It lists the lemmas that close the goal there, as proofs to paste,
each checked by the kernel (`exact`, `withHypotheses`, `afterObligations`),
then those that apply leaving smaller goals, then rewrites with the goal each
leaves ([syntax.md](syntax.md#what-closes-this--stitchwort-search---at)):

```
stitchwort search --at proofs.sw:42        # the goal `?` on line 42
stitchwort search --at proofs.sw --goal 2  # the file's second goal
stitchwort search --at src/Aoc/Year2024/Day06/Proofs/Loops.sw:120  # in AoC
stitchwort search --at src/Rogue/Proofs/Reach.sw --goal 1          # in the roguelike
```

Read its `applicable` results as next steps (`Nat.leOfEq a c ?` leaves
`a = c`). **In AoC and the roguelike, put a `?` where the proof goes and
run `search --at` on the file** (from any folder: the project is found from
the file's). It reads the goal in the file's namespace with its imports,
searches std and the project (not the theorem itself or what uses it), and
checks each closing proof pasted into the file. A project lemma the file
doesn't import comes as its full name (`Aoc.Year2024.Day23.Proofs.firstOfTwo a b`), with
the import that would shorten it. A warm check cache makes it about 2 s a goal (more where the namespace
takes long to check); in the AoC benchmark (search.md, "As built (stage 2b)")
it found the lemma the proof used for 11 of 28 one-lemma proofs (most misses
needed the goal's own definition unfolded first: try `rewrite` with its
equation, or a `stitchwort search` pattern on the unfolded form). Since stage
3, on 29 goals the AoC 2021 lanes met, it closes the goal with what the proof
used, or offers that as a step, for 27 (search.md, "As built (SW-993, stage 3
follow-ups)").

Paste a goal as it is printed (its lowercase variables become named holes).
Read `relation` first: an `instance` result's statement fits the pattern as
it stands; a `generalisation` or `commonInstance` one only fits once your
holes or its variables take some structure. A `relaxed pass` means nothing
naming everything the pattern names matched: read those results as weaker.
Grep is still the way to search by name, or by text a pattern can't say.
Std's theorems are top-level with their full name, in
`crates/elab/src/std/<Namespace>/*.sw`:

```
# by name: std names lemmas after what they're about (lengthAppend, modLess, addComm)
grep -rn "^theorem List\.length" crates/elab/src/std
grep -rnE "^theorem Nat\.[a-z]*[Mm]od" crates/elab/src/std

# by the shape of the conclusion (statements can run over several lines: add -A2)
grep -rnE "^theorem .*List\.length \(List\.append" crates/elab/src/std
grep -rn -A2 "^theorem Set\.contains" crates/elab/src/std

# a function's congruence lemmas (for rewrite and decreasing inside a callback)
grep -rn "^theorem List\.[A-Za-z]*Cong\b" crates/elab/src/std
```

Then check how it's stated (argument order, implicit arguments, `[auto]`
premises) before using it. `Nat.addComm`, `Nat.addZero`, `Nat.modLess`,
`Nat.divModEq` and `List.lengthAppend` are the ones lanes reach for most.
If std lacks a lemma you needed, prove it in your namespace and list it in
the report as a std candidate (agentic-proving.md §5 A, about 40 items, is the largest category).

### Checking, auditing and testing a std lemma

Std is a folder of files (`crates/elab/src/std`), not a project, so the
commands that name a project's namespaces take a different form
([testing.md](testing.md#editing-the-standard-library), SW-2863). The
checkout's library is found from the binary, so they run from any folder;
`--std-dir DIR` names another copy.

- **Check the file** a lemma is in, with its path relative to the library:
  `stitchwort check --std Float/Theory.sw` (or `Std.Float.Theory`, or a
  folder, `Float`). It checks that file in full, proof bodies included, and
  the files it needs:

  ```
  checked 1 standard library file
  ```

  The cache is `.stitchwort/cache` in the current folder, as for `check`.

- **Audit a lemma by its full name**, from any folder, including a project's:
  `stitchwort audit Std.Float.Theory.absBelowOf`. With no findings it prints
  the summary alone (rule 3 asks for that line in the report); `--verbose`
  adds a line per theorem, with its axioms and search result:

  ```
  audited 1 theorem: 0 failed, 0 with warnings, 1 passed
  ```

- **Test a `test` block.** `check` checks the block's statement but doesn't
  run it, and a library file has no project to name, so copy the test into a
  scratch `.sw` file with an import of what it uses, and run
  `stitchwort test FILE`:

  ```
  import Std (Float, Int, Nat)

  test "abs" := Float.abs (-2.0) == 2.0
  ```

  ```
    ✓ abs  ran
  1 test(s): 1 passed, 0 failed (0 from the cache)
  ```

  `--only NAME` runs one test of the file. Tests are runtime checks of
  closed `Bool` expressions, not proofs.

## 6. Performance pitfalls

Checking compares terms by computing them. On unknown arguments, a cheap
program can be an enormous term.

- **Constants that unfold.** `(seed * 1103515245 + 12345) % 2147483648` on
  an unknown `seed`: `+` computes on both sides, and `%` would count the
  12345 down while checking (games/rogue/src/Rogue/Random.sw:11–14). The
  roguelike made `lcg` opaque for that reason. Whether it bites depends on
  the comparison: on a scratch file, `lcg seed < 2147483648` with `lcg`
  transparent checked in under a second. Watch any definition with a `%`
  or `/` by a large literal (`% 2147483648`, `% 16777216`) that proofs
  mention, and time the check.
- **A field read inside a lambda is a call.** `cave.height` is
  `cave.rows.length`, computed again whenever the lambda runs; hoist it into
  a `let` outside. In AoC 2021 day 15's run, moving `cave.height` out of the
  `level` lambda took the day from 31.7 s to 17.6 s (the AoC 2021 day 15
  notes, `aoc/NOTES-2021.md:3676`), and the proofs didn't change. Nothing
  warns about it, and hoisting by the compiler is parked (SW-1814).
- **Big normal forms.** A definition that is the whole search
  (`reachable`, day 18), a 130,321-element closed list (day 22), or a
  generator run under a handler (roguelike) is computed in full when a
  comparison isn't written identically: 10 s, more than 100 s, and
  `E-RESOURCE` respectively (aoc/NOTES-2024.md:5922–5924, 7272–7284;
  games/rogue/NOTES.md:283–305). Split the statement so the big term is a
  variable (§2, item 3), compare by name, or make it opaque.
- **A statement with no parameters is computed when it is declared.**
  `theorem t: countdown 0 100000000 = countdown 0 100000000 := byComputing` runs
  the whole loop before the proof is looked at (minutes; at 1,000,000
  steps, 1.2 s): the kernel evaluates a closed statement in full. Give the
  theorem a parameter (state it for any count, as days usually do) or name
  the big value with a definition, and the call stays folded. Kept as is
  for now (D2448); the design and a patch that removes the cost are in
  [glued-closed-types.md](proposals/glued-closed-types.md).
- **Leave rules no open arguments you could give.** On a scratch file with
  an opaque `lcg`, `rewrite lcg.unfold then …` took 25 s to check, and
  `rewrite lcg.unfold seed then …` and `unfolding lcg` took 0.2 s each (run
  30 Oct 2026; which step took the time wasn't established).
  `STITCHWORT_REWRITE_METRICS=1` prints what each `rewrite` did.
- **When `opaque` is honest.** Make a definition opaque when its proofs
  need its *name* and its *properties*, not its computation: a hash, a
  random generator, a search whose result is described by a spec. Then:
  `rewrite f.unfold x then …` takes one step into it; `unfolding f` after a
  theorem's type opens it for that theorem only
  ([syntax.md](syntax.md#opaque-definitions)). It is honest when the
  comment says why and the report mentions it. It is not honest when it
  hides a definition so that a goal "can't be computed" into something
  false-looking: opacity never makes a false statement provable, but it can
  make a proof depend on a property you then never prove. If proofs need
  to unfold it everywhere, it shouldn't be opaque.
- **State facts about a `{Fail}` function through a named wrapper.**
  `Fail.toResult (() => x.traverse on) = Ok …` written inline is elaborated
  wrongly: the thunk's computation is wrapped as a value, so the right side
  comes out `Ok (Done …)`. Define a small wrapper,
  `def runExpr (on: Steps) (input: Expr): Result (Expr) Text :=
  Fail.toResult (() => input.traverse on)`, and state the facts about
  `runExpr`; that is how `exprOk` is stated just below it in
  `tools/fmt/src/Fmt/Walk.sw`. `tools/fmt/src/Fmt/MeaningProofs.sw` keeps
  its inline `Fail.toResult` statement against a named pure result
  (`declBindersAgree`, with `dropDeclBindersPure`).
- **A `{Fail}` step that never fails.** A step declared `{Fail}` whose body
  never fails won't evaluate under `Fail.toResult`, and `cases` hits its
  64-case budget on it; declare the step pure (no `{Fail}`). `mergeHeader`
  and `mergeBinding` in `tools/fmt/src/Fmt/Passes.sw` are pure for this
  reason.
- **Time it.** `time stitchwort check --no-cache NAMESPACE`. A proof
  namespace taking several seconds cold has something unfolding; halving
  the file (or replacing proofs with `?`) finds it. On day 23 one 100-line
  theorem took 16 s; split into lemmas, 2 s (aoc/NOTES-2024.md:7689).
  `stitchwort check --no-cache --timings NAMESPACE` prints, after the
  check, a table per namespace (a cached one is marked `(cached)`) and one
  of the declarations checked: elaboration, kernel and total milliseconds,
  evaluation steps and term nodes, slowest first, the 20 slowest by default
  (`--timings=50` for 50, `--timings=all` for every one; std's own
  declarations are in the table too). The theorem at the top is the one to
  split. A namespace the cache answers for has no rows, so add
  `--no-cache`.

## 7. The report

A proof lane's report says, in this order:

- what is proved, each theorem in plain words;
- **Not proved**: unfinished theorems, hypotheses added (each, with why),
  what's only tested;
- the `stitchwort audit` summary line, and what each `!` turned out to be;
- that breaking the program made the proofs fail (which change, which
  theorem);
- new `opaque` definitions and why;
- friction: missing std lemmas, misleading messages, slow checks, with
  file:line, so they can become tickets.
