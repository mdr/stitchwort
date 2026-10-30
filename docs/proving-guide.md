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
   antennas at rows -100 and -99 would break it (aoc/NOTES-2024.md:2090–2096).
   Day 19 states that every theorem takes `Striped patterns`
   (aoc/NOTES-2024.md:6019); day 21 that `part1Correct` and `part2Correct`
   assume `Optimal` (aoc/NOTES-2024.md:6988).
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
   statement and decide whether its hypotheses contradict each other. Quote
   the summary line in the report.
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

## 2. Workflow

1. **State it with `?` first, and read the goal.** Write the statement with
   `?` as its proof, then `stitchwort check`. The checker carries on past
   `?` and prints what goes there:

   ```
   theorem lengthAppend (xs: List Nat) (ys: List Nat): List.length (List.append xs ys) = List.length xs + List.length ys :=
     match xs with
       | Nil => rfl
       | Cons x rest => ?
   ```

   ```
   [GOAL] Goal: in `lengthAppend`
      │                      ╰── ys: List Nat
      │                          x: Nat
      │                          rest: List Nat
      │                          ⊢ Succ (List.length (List.append rest ys)) = List.length rest + List.length ys + 1
   ```

   Goals are shown computed, not as written. A declaration with a `?` is
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
   - `!` **hypotheses held in no case**: `theorem vacuous (n: Nat) (h: n + 1 = 0): n = 42 := omega`
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
   being computed (aoc/NOTES-2024.md:7265–7272). One fact per lemma also
   makes `omega [lemma …]` and `cases in t` easy to feed.
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
6. **Work in a scratch file** for experiments (a lemma's shape, an error you
   don't understand), outside the repo or in the scratchpad, checked with
   `stitchwort check file.sw` (file mode: only `Std` is visible).

## 3. Tools, and when each fits

Import what you use: std's theorems live in namespaces that need an import
(`import Std (Nat)` for `Nat.modLt`; without it, `E-UNKNOWN-NAME` says so).

| Goal | Tool |
|---|---|
| Both sides compute to the same value | `rfl` |
| Finitely many cases, each closed by computation, a hypothesis or arithmetic | `cases` |
| Linear arithmetic on `Nat`/`Int` from facts in scope | `omega`, `omega [facts]` |
| An equation of polynomials | `ring`, `ring [h]` |
| A closed decidable proposition | `byDecision` |
| A `Bool` property of every value of a finite type, more than 64 cases | `Finite.check` |
| Replace one side of an equation inside the goal | `rewrite` |
| A chain of `=`, `<=`, `<` steps | `calc` |
| Induction | recursion in the theorem (structural, or `decreasing`) |
| Induction over a nested type (`List T` inside `T`) | `T.induct`, `T.inductMem`, `T.size` |

- **`rfl`** proves `a = b` only when both sides compute to the same value.
  `+` recurses on its first argument, so `1 + c` computes to `Succ c` and
  `c + 1` doesn't (aoc/NOTES-2024.md:824–836). A goal stuck on a variable
  needs a `match`, `cases` or a lemma.
- **`cases`** finds what the goal is stuck on (a variable or call of a type
  with two or more constructors), splits it as a `match` would, and closes
  each case by computation, a contradictory hypothesis, a hypothesis of the
  goal's type, `omega`, or by running the goal's decision procedure (as
  `byDecision` does). It introduces a goal's leading binders itself
  (`theorem t: (x: Bool) → P x := cases`). When nothing is stuck and nothing
  closes it, it falls back to splitting a variable the goal mentions, the
  one that makes the fewest cases. `cases in t` tries `t` in every case
  first. At most **64 cases**, then `E-CASES-BUDGET`. It doesn't do
  induction (`List`, `Nat`). Examples: `examples/accept/cases-*.sw`.
- **`omega`** proves `<=`, `<`, `=` on `Nat` and `Int` (and contradictions)
  from every arithmetic fact in scope: parameters, pattern variables, `if
  h:` and `match e:` equations, `let`s. Pass other facts as `omega [lemma a
  b]`. It knows `-`, `max`, `min`, multiplication by a literal; `x * y`,
  `x / 2`, `x % k`, `List.length xs` and calls are atoms it knows nothing
  about. It doesn't know what `% 2` is: pass `Nat.divModEq` and
  `Nat.modLess` for each (aoc/NOTES-2024.md:7276–7284). Its failure
  message's model "may not be a real counterexample".
- **`auto`** isn't a proof term: it is the compiler filling an `[auto h: P]`
  argument, from evidence given by name, a hypothesis in scope of exactly
  that type, or a decision procedure (DESIGN.md "`auto` and `Decidable`").
  Its search stops after 8 levels of nested decisions; past that, pass the
  proof (`Decidable.fromYes …`), as the roguelike did for its 7th key
  (games/rogue/PROOFS.md:192). An `if h: …` puts `h` in scope for `auto`.
- **`byDecision`** (`import Std (byDecision)`) is Lean's `by decide`: it
  proves a closed proposition by running its decision procedure. False is
  `E-AUTO-FALSE`; stuck on a variable is `E-AUTO-STUCK`, so split the
  variable with `cases` or use `Finite.check`.
- **`Finite.check p rfl x`** proves `p x = True` for every `x` of a finite
  type by computing `p` on each value of `Finite.all`. Put several variables
  in one record or pair. It is the way past `cases`' 64 cases: 2^10 values
  take about 0.1 s, 2^16 about 12 s (`examples/accept/finite-check.sw`).
  Data types without recursion or `Nat` fields get `Finite` derived.
- **`rewrite p in t`** replaces `p`'s left side by its right side in the
  goal and checks `t` against the result; `rewrite <- p`, `rewrite p at h`.
  It needs a known goal (`E-REWRITE-NO-GOAL` otherwise). It replaces every
  occurrence of the first instance it matches. It looks for the left side
  in the goal *as it computes*, so a definition the goal already unfolded
  isn't there to find (8 items in agentic-proving.md §5 E). Give the rule its arguments
  when you can (§6). Inside a function argument it goes through the
  call's congruence lemma (`List.mapCong`, …).
- **`calc`** chains steps `_ = e := proof`, `_ <= e`, `_ < e`; a step with
  no proof is `rfl`. Use it when `rewrite` picks the wrong occurrence, or
  to say exactly which form you want.
- **Induction is recursion.** A theorem that calls itself on a smaller
  argument is a proof by induction; the recursive call is the induction
  hypothesis. For other measures, `decreasing e` (or `decreasing (m1, m2)`)
  after the type: each recursive call needs a proof that the measure went
  down, from `auto` (a guard `if h: next < n` in scope) or `[decreasing :=
  proof]`. `f.unfold x` is a `decreasing` definition's own equation, for
  `rewrite f.unfold x in …`; on unknown arguments `f x` doesn't unfold by
  itself.
- **Nested types**: for `type Packet = | Number (value: Nat) | Packets (items: List Packet)`,
  the compiler generates `Packet.size`, `Packet.induct` (the `Packets` case
  gets `List.All motive items`) and `Packet.inductMem` (every member `q`
  with `List.Mem q items`). `decreasing Packet.size p` with `items.attach`
  makes recursion through the list need no proof
  (`examples/accept/nested-data-induction.sw`).
- **Hypotheses are ordinary values.** Pass them on, take them apart with
  `match`, `And.left`, `And.right`; `Void.exfalso` from a contradiction.

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
  [E-REFL] Error: `rfl` can't prove this
    │ theorem plusComm (n: Nat) (m: Nat): n + m = m + n := rfl
    │                                                       ╰─── `n + m` and `m + n` aren't equal
    │ Note: `rfl` proves `a = b` only when both sides compute to the same value
  ```
  (`examples/reject/plus-comm-by-rfl.sw`.)
- **`E-CASES`**: a case nothing closed. The notes give that case's
  hypotheses, its goal, and often a counterexample, which usually means the
  statement is false:

  ```
  [E-CASES] Error: `cases` can't close the case a = True, (n <= 2) = False
    Note 1: h: n ≤ 3
    Note 2: goal: False = True
    Note 5: this statement is false; a counterexample: a = True, n = 3
  ```
  (`examples/reject/cases-open-case.sw`.) If it's true, give the case's
  proof with `cases in t`.
- **`E-CASES-BUDGET`**: more than 64 cases. The note says what it split,
  and, when every variable is finite, points at `Finite.check`
  (`examples/reject/cases-budget.sw`). Otherwise prove a fact that decides
  several cases at once and pass it with `cases in t`, or `match` by hand.
- **`E-OMEGA`**: the facts don't give the goal. "an integer model …
  satisfies the facts" names values for the atoms; often a fact is missing
  (pass it in `omega […]`) or an atom hides arithmetic (`x % 2`, `x / 2`,
  a call). With a counterexample note, the statement is false
  (`examples/reject/omega-integer-model.sw`).
- **`E-MATCH-MOTIVE`**: generalising a `match`'s scrutinee makes the type
  ill-formed, because something else in the type depends on it. The note
  says the fix: a top-level helper with a written signature
  (`examples/reject/match-bad-motive.sw`).
- **`E-REWRITE-*`**:
  - `E-REWRITE-NOTHING`: the left side isn't in the goal as it computes. The
    notes show the goal "as written" and "as it computes", and say when the
    goal already holds by computing (`examples/reject/rewrite-nothing.sw`).
    Usually the goal unfolded the definition first: rewrite with a lemma
    about the unfolded form, or state the step with `calc`.
  - `E-REWRITE-MOTIVE`: replacing the term makes the goal ill-typed, usually
    because an `auto` proof (the `d != 0` in `x % d`) is about it. Rewrite a
    larger term (`x % d`), or use `calc` (`examples/reject/rewrite-motive-auto.sw`).
  - `E-REWRITE-PREMISE`: the rule matched but its premise (`x ≤ n`) isn't a
    hypothesis and `omega` can't prove it; give it in the rule
    (`examples/reject/rewrite-premise-unproved.sw`).
  - `E-REWRITE-NO-GOAL`: no expected type; ascribe it, `(rewrite p in t: a = b)`,
    or use `rewrite p at h`.
  - `E-REWRITE-BUDGET`: the comparisons were too expensive. That says
    nothing about whether the occurrence is there; use a more specific rule
    or `calc`.
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
  (`examples/reject/non-structural.sw`.) **`E-DECREASING`** is the same with
  `decreasing`: the message shows the goal (`n - step < n`) and what's in
  scope; give `[decreasing := …]` or guard with `if h: … then`
  (`examples/reject/decreasing-missing-proof.sw`).
- **`E-RESOURCE`** ("ran out of resources"): not a type error and not a
  failed test; the checker gave up within its limits. In proofs it usually
  means a definition is being computed in full, on a big literal or on
  unknown arguments. Run on a scratch file
  (`theorem countBig: count 10000000 = 10000000 := rfl`, with `count` a
  recursive copy of the identity):

  ```
  [E-RESOURCE] Error: ran out of resources: it recursed more deeply than allowed
    │ theorem countBig: count 10000000 = 10000000 := rfl
    │                       ╰─────────────────────── while checking this
    │ Note 1: this isn't a type error or a failed test: there's no answer within the limits
    │ Note 2: it happened while checking `countBig`
    │ Note 3: it ran out while unfolding `count`
  ```
  The last note names the definition being unfolded; when it doesn't, find
  it by replacing parts with `?`. Then see §6. Other forms: "a value was
  too large to show" (aoc/NOTES-2024.md:1479–1485). Two of the roguelike's
  three failures in one proof were this (games/rogue/PROOFS.md:216–226).
- **`E-TYPE-MISMATCH` with a computed type**: the expected type is shown as
  it computes, which can look unlike what you wrote: `lcg seed < 2147483648`
  is expected as `… % 2147483648 ≤ 2147483647`, and `Nat.modLt _ _` with
  holes then doesn't match. Give the lemma its arguments
  (`Nat.modLt (seed * 1103515245 + 12345) 2147483648` checks).

When a message hid the real problem (22 items in agentic-proving.md §5 C), say so in the
report: messages get fixed from those reports.

## 5. Finding lemmas

Std has about 2,300 theorems (`grep -rhoE "^theorem [A-Za-z.]+"
crates/elab/src/std | wc -l` counts 2282). Our lanes twice rewrote lemmas
std already had, and found others only by grepping (aoc/NOTES-2024.md:373,
7906–7907). Until `stitchwort search` exists (SW-915), grep before writing a
lemma. Std's theorems are top-level with their full name, in
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
- **Big normal forms.** A definition that is the whole search
  (`reachable`, day 18), a 130,321-element closed list (day 22), or a
  generator run under a handler (roguelike) is computed in full when a
  comparison isn't written identically: 10 s, more than 100 s, and
  `E-RESOURCE` respectively (aoc/NOTES-2024.md:5821–5826, 7254–7272;
  games/rogue/NOTES.md:283–305). Split the statement so the big term is a
  variable (§2, item 3), compare by name, or make it opaque.
- **Leave rules no open arguments you could give.** On a scratch file with
  an opaque `lcg`, `rewrite lcg.unfold in …` took 25 s to check, and
  `rewrite lcg.unfold seed in …` and `unfolding lcg` took 0.2 s each (run
  30 Oct 2026; which step took the time wasn't established).
  `STITCHWORT_REWRITE_METRICS=1` prints what each `rewrite` did.
- **When `opaque` is honest.** Make a definition opaque when its proofs
  need its *name* and its *properties*, not its computation: a hash, a
  random generator, a search whose result is described by a spec. Then:
  `rewrite f.unfold x in …` takes one step into it; `unfolding f` after a
  theorem's type opens it for that theorem only
  ([syntax.md](syntax.md#opaque-definitions)). It is honest when the
  comment says why and the report mentions it. It is not honest when it
  hides a definition so that a goal "can't be computed" into something
  false-looking: opacity never makes a false statement provable, but it can
  make a proof depend on a property you then never prove. If proofs need
  to unfold it everywhere, it shouldn't be opaque.
- **Time it.** `time stitchwort check --no-cache NAMESPACE`. A proof
  namespace taking several seconds cold has something unfolding; halving
  the file (or replacing proofs with `?`) finds it. On day 23 one 100-line
  theorem took 16 s; split into lemmas, 2 s (aoc/NOTES-2024.md:7661–7662).

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
