# Proposal: rewriting one chosen occurrence (`rewrite p within …`)

**Status:** draft 1, 7 November 2026, for Matt's decisions D2860 to D2864 ([§8](#8-decisions)).
Ticket SW-2011, split from SW-758 (2024 day 11's findings). Theme Q of
[aoc-friction-synthesis.md](../research/aoc-friction-synthesis.md) (ranked 10th, "Rewriting one
occurrence"). Written against `main` at `f65648d40`. Nothing was run for this note: it is read
only (the shared machine was checking proofs).

Related: [calc-rewrite.md](calc-rewrite.md) §4 (prior art) and §9 stage 3, which deferred
"choosing occurrences" with "`calc` with an explicit step covers this";
[rewrite-hypothesis.md](rewrite-hypothesis.md) (`at h`, whose parsing this copies);
[goal-as-written.md](goal-as-written.md) and [bounded-readback.md](bounded-readback.md) §4.1
(D2542: searches act on what is visible), staged in
[bounded-readback-remaining.md](bounded-readback-remaining.md) as 6a (SW-1839) and 6b (SW-1840);
[code-review-elab-tactics.md](../reviews/code-review-elab-tactics.md) F7 (four copies of the
find, abstract and transport machinery).

Labels: **[checked]** read in this repository at the place given; **[cited]** read in the note
named; **[inferred]** my reasoning, not run.

## 0. Summary

**The problem.** `rewrite p` replaces *every* place where `p`'s left side appears. Sometimes you
want only one of them. In 2025 day 2 the goal is

```
Nat.pow 10 (k - 1) ≤ Nat.fromDigits (List.take (Nat.digits x).toList k)
```

and the fact to hand is about `List.length (List.take … k)` where the goal has the first `k`.
`rewrite <- repBlockLength …` turns *both* `k`s into the length, including the one inside
`List.take … k`, and the proof no longer fits. The day's author wrote "There is no workaround but
`J`", with the whole goal restated by hand as a motive (`aoc/src/Aoc/Year2025/Day02/Proofs/
Repeated.sw:259` **[checked]**). 2024 day 11 hit the same thing (`Split.sw:36`, an `Eq.cong` with
the goal restated). Two more days hit a different form of it, a copy hidden inside what `%`
computes to, and one day hit the opposite (wanted every copy, got one).

**The change.** One new clause on a rule: `within` and a pattern, where `_` stands for anything.

```
rewrite <- repBlockLength x k n hn hq within Nat.pow 10 _ in
  Nat.fromDigitsHeadBound …
```

Only the occurrences inside a part of the goal that looks like `Nat.pow 10 _` are replaced. The
pattern is matched against the goal as it is printed, so what you read in the error is what you
point at. No numbers to count. This is SSReflect's `rewrite [in pattern]H` (§3.2).

Two smaller pieces go with it: the hidden-copy days need nothing new once stage 6a lands (it
makes `rewrite` act on what is visible), and the "every copy" day needs a note on the failure
that follows, saying which other instances the rule left alone.

**What it should do.** The two `J`/`Eq.cong` workarounds become one-line `rewrite`s; the error
when a `rewrite` replaced too much says what it replaced and points at `within`; and `rewrite`
without `within` behaves exactly as before. We'd know by converting the two AoC proofs (stage
3) and by the new accept and reject examples.

## 1. The problem: what the days hit

The synthesis lists four days (2021 day 16; 2024 days 4 and 11; 2025) **[cited:
aoc-friction-synthesis.md theme Q, §5 item 7]**. Read in their own notes, they are three
different problems:

| Kind | Day | What happened | Source |
|---|---|---|---|
| **A. A copy hidden inside a call** | 2021 day 16 | `rewrite halfOfDouble acc bit, parityOfDouble acc bit` failed: the first rule also rewrote the `/ 2` inside the `% 2`, which computes to `x - x / 2 * 2`. Workaround: the `%` rule first. | NOTES-2021.md:4079–4083; `crates/elab/src/std/Nat/Bits.sw:439` |
| | 2024 day 11 | `rewrite splitLeft …, splitRight …`: same, `stone % place` computes to `stone - stone / place * place`. Workaround: `%` first. | NOTES-2024.md:3218–3229 |
| | 2025 day 1 | `rewrite Nat.divOne n, Nat.divOne (Succ n)`: the first rule had rewritten both (pain point 7). | aoc-2025.md:2425–2430 |
| **B. Two visible copies, one wanted** | 2024 day 11 | `rewrite <- rightHalfLength stone even` rewrote `half` inside `drop half` as well as the exponent. Workaround: `Eq.cong` with the goal restated. | NOTES-2024.md:3207–3217; `aoc/src/Aoc/Year2024/Day11/Proofs/Split.sw:30`, `:36–41` |
| | 2025 day 2 | `k` in `pow 10 (k - 1)` and in `take k ds`: `rewrite` changes both. "There is no workaround but `J`." | aoc-2025.md:2394–2399; `Repeated.sw:257–263` |
| **C. Every instance wanted, one rewritten** | 2024 day 4 | `rewrite <- List.getOrGet rows _ []` rewrote `List.get rows r` but not `List.get rows (1 + r)` and the other two: the `_` is fixed by the first match. Writing the rule four times worked. The cost was a misleading note. | NOTES-2024.md:900–911 |

**A** is not a choice the user wants to make: in the goal as printed there is one `/ 2`, and it is
the one they meant. **B** is a real choice between two visible places. **C** is the reverse of B,
and its cost was the message, not the missing feature.

### 1.1 Why A happens today

`rewrite` first searches the goal as written (calls kept, `quote_folded`), but keeps that result
only if no copy of the left side is hidden inside a call (`hidden_copy`,
`crates/elab/src/rewrite/as_written.rs:390–416` **[checked]**). `x % 2` hides an `x / 2`, so
the as-written result is thrown away and the unfolded search runs, which replaces both
(`rewrite.rs:739–805` **[checked]**). That completeness check is exactly what D2542 removes:
"`rewrite` … use[s] the as-written occurrences whenever there are any, with no completeness
check" **[cited: bounded-readback.md, "Decided"]**. Stage 6a (SW-1839) builds it. After 6a,
`rewrite halfOfDouble acc bit` replaces only the visible `/ 2`, and all three kind-A days work in
the order first written. **[inferred from the note and the code; 6a's own tests should include
one of them, see §7]**

### 1.2 Why B and C happen

The occurrence search (`Search::visit`, `rewrite.rs:1316–1356` **[checked]**) walks the goal in
pre-order and replaces every candidate that passes the key, binder, type and unification tests.
There is no filter on *where* a candidate is. A rule with unknowns (`_`, or arguments left off)
has them solved by the first match, and later candidates are compared with the solved left side
(`rewrite.rs:1254–1256` and `:1431–1438`, "Read back again after each match, so … later copies match by syntax"
**[checked]**). That's B and C. `docs/syntax.md` says so: "Every matching occurrence is replaced.
There is no way to pick one; use `calc`" and "The first match fixes the rule's open arguments"
(`docs/syntax.md`, `rewrite`, "What will surprise you" **[checked]**).

The reject example for C exists (`examples/reject/rewrite-first-instance.sw`), and its message
says nothing about the instance left behind: the E-REFL notes show the goal after rewriting and no
more (`crates/cli/tests/running/snapshots/running__examples__reject__rewrite-first-instance.snap`
**[checked]**).

## 2. What works today

1. **`J` or `Eq.cong` with the goal restated** (both B days). Correct, long, and you restate the
   whole goal with a variable at the place you mean. 2025's `repAbove` is four lines of motive and
   arguments for what is one rewrite.
2. **Widen the rule with `Eq.cong`.** `rewrite <- Eq.cong (t => Nat.pow 10 (t - 1)) (repBlockLength
   x k n hn hq) in …` has the left side `Nat.pow 10 (k - 1)`, which occurs once. The AoC code
   already uses `rewrite <- Eq.cong Pair.fst same` (`aoc/src/Aoc/Common/GridGraph.sw:37`
   **[checked]**), but with a named function; with a lambda, whether the lambda's parameter type is
   inferred in a rule is not something I checked (SW-741 lists `Eq.cong (x => 4*x) h` as a
   problem once). **[inferred]** Nobody on the B days found this, and it still restates the
   context between the pattern's head and the occurrence (`t - 1`), with no `_` for the parts in
   between.
3. **`calc`** with the intermediate form written out, as syntax.md advises. Fine for one step,
   but it restates the goal too.
4. **Order the rules** (kind A): the `%` rule first. Works, but you have to know why.
5. **Write the rule once per instance** (kind C). Works; the problem was finding out.

## 3. How other systems do it

### 3.1 Numbers: Lean's `nth_rewrite` and `occs`, Rocq's `at n`, Arend's `{i}`

Lean 4 has `rw (occs := .pos [2]) [h]` **[cited: calc-rewrite.md §4.1, from the Lean reference]**
and Mathlib's `nth_rewrite 2 [h]`. Rocq has `rewrite H at 2`, counting copies of the first matched
instance **[cited: calc-rewrite.md §4.5]**. Arend's `rewrite {2} p t` **[cited: calc-rewrite.md
§4.8]**. SSReflect has `rewrite {2}H` too. All number the occurrences in the system's own
traversal of the elaborated term, which the user can't see; in Lean the usual advice when
`nth_rewrite` picks the wrong one is to try the next number, and numbers shift when the goal is
edited above the point. **[inferred: general Lean experience, not a cited source]**

### 3.2 Patterns: SSReflect's contextual patterns

SSReflect writes the place, not a number: `rewrite [in X + _]H` rewrites only inside subterms
matching `X + _`, and `rewrite [X in _ + X]H` names the exact position with a variable. The
pattern is matched against the goal; its `_` are wildcards. **[inferred: from memory of the
SSReflect manual; I did not reopen it for this note]** This is the form this note recommends, in
its first (`in`) shape only.

### 3.3 Focus: Lean's `conv`

`conv in pattern => rw [h]` focuses on the first subterm matching the pattern; `conv => enter [2,
1]; rw [h]` navigates by argument positions. **[cited: NOTES-2024.md:3216, linking the Lean
book's `conv` chapter]** `conv` is a sub-language (navigation, `ext` under binders, its own
tactics); Stitchwort is term-mode, with no tactic state to focus. `conv in pattern` alone is the
same idea as SSReflect's `[in pattern]`.

### 3.4 Hiding: Rocq's `set`, Lean's `set`/`generalize`

`set x := e` replaces occurrences of `e` with a local definition, which `rewrite` then doesn't
see. In Stitchwort a `let` in the proof doesn't change the goal (the goal comes from the
signature), so this needs a new goal-changing form, `generalize`-like, with its own motive. More
machinery than a filter on the existing search, for the same result. **[inferred]**

## 4. Options

| | Option | Covers | Cost | Against it |
|---|---|---|---|---|
| 0 | Document the `Eq.cong` widening; nothing new | B (if lambdas work in rules) | 20 min | Still restates the context; nobody found it; no `_` |
| 1 | **Occurrence numbers**, `rewrite p (occurrence := 2)` | B | ~60 min | Counts positions you can't see (§5); breaks when the goal changes; `at n` would clash with `at h` |
| 2 | **`within pattern`** on a rule | A (before 6a), B | ~90 min with docs | One new contextual word; pattern can't separate two identical siblings |
| 3 | `within X in pattern` (SSReflect's named position) | A, B, and identical siblings | Option 2 + ~45 min | More syntax than any day needed |
| 4 | `conv`-style focus | everything | days | A sub-language for a term-mode system |
| 5 | `set`/`generalize` to hide copies | B | ~2 h | A goal-changing form with its own motive |
| 6 | An explicit motive, `rewrite p as (t => …)` | B | ~45 min | That's `J`; it restates the goal |

C is covered by none of them, and needs none: it needs a note (§6.4).

**Recommendation: option 2**, with the note for C, and nothing new for A beyond 6a.

Why 2 over 1: the pattern says *where* in the problem's terms (`Nat.pow 10 _`: "the exponent"),
survives edits elsewhere in the goal, is matched in the same term the error prints (§5), and needs
no rule for counting hidden positions. Both B days are one pattern each. Why 2 over 0: `_` skips
the parts you'd otherwise restate, it reads as intent rather than a trick, and the error can list
what the pattern matched. Why not 3 yet: no day had two identical siblings (`f k + f k`, wanting
one); 2's syntax leaves room for it (`within X in …`) without changing what 2 means.

What it rules out: nothing. Numbers could still be added later on top of the same filter.

## 5. Which goal the occurrences are counted in

This is the subtle part, so in plain terms first: the goal Stitchwort prints is not always the
goal `rewrite` searches. Today, if the as-written search is thrown away (§1.1), the search runs
over the goal fully computed, where `x % 2` is `x - x / 2 * 2`, `List.range n` may show as
`List.rangeFrom 0 n`, and a call you can see may be gone. Anything that counts occurrences in that
term counts things the user can't see.

**For `within`:** the pattern is matched only against the goal read back *as written*
(`quote_folded`, from the goal value unforced, as `as_written::search` does at
`rewrite/as_written.rs:294` **[checked]**). That is the same read-back every `rewrite` message
uses to show the goal (`shown`, `rewrite.rs:1745–1755` **[checked]**). So the pattern is matched
against the text in the error, modulo the printer's sugar (`x % 2` for `Nat.mod x 2`, `xs.drop n`
for `List.drop xs n`), which the pattern is elaborated through too, since you write it in the same
surface syntax. A `within` rule never falls back to the computed goal: if the pattern matches
nothing as written, it is an error (§6.3), not a search somewhere else. Limits fail, they don't
choose (D2543).

One gap: a definition's inner `match`, lifted to a `%match` helper, is printed as its body
(SW-1469, open) but held as a helper call, so a pattern written as that `match` won't match it.
**[inferred from the synthesis's gap B]** That is a printing gap, not a `within` one: the pattern
for the call (`f _`) works.

**Inside a matched instance**, the rule's occurrences are found by the same pre-order search as
today, over the same as-written term, with today's tests (key, no bound variable, type,
unification). A copy of the left side hidden inside a call *within* the pattern instance is left
alone: that's D2542's rule, applied early. No completeness check, no "today's instance".

**If numbers were wanted** (option 1, not recommended): they would have to count over the same
as-written term, in pre-order, which is left to right in the printed text for prefix calls,
operators and method calls (all store their arguments in reading order), *but* would have to skip
what the printer hides: implicit arguments, instance dictionaries, and proof arguments such as
`/`'s `d ≠ 0`, which D2549 shows is where a visible-looking `d` also hides
(`bounded-readback.md`, D2549 **[cited]**). And before 6a, the computed-goal fallback would number
a different term: the same `rewrite p (occurrence := 2)` would mean different places depending on
which path ran. That is the main reason not to number.

### 5.1 How this interacts with stages 6a and 6b

- **Before 6a.** `within` uses only the folded search that `replace_occurrences_as(…, folded =
  true, …)` already provides (`rewrite.rs:1079–1110` **[checked]**), with no `hidden_copy` check
  and no `todays_instance`. So a `within` rule already follows D2542. A rule without `within` is
  unchanged. In that window `within` is also a workaround for kind A: `rewrite halfOfDouble acc
  bit within _ / 2` matches only the visible `/` (the one inside `%` is inside a `Nat.mod` call in
  the as-written term). **[inferred]**
- **6a** (SW-1839) removes the completeness check, today's instance and the unconfirmed paths from
  the plain search. A `within` rule is unaffected, since it never used them; kind A then needs no
  `within`. 6a's lane should keep `within`'s branch on the same folded search it moves to, which
  is a merge, not a design change. Whichever lands second takes the conflict in
  `rewrite_once` (`rewrite.rs:686–805`). That's my sequencing call: `within` doesn't wait for 6a.
- **6b** (SW-1840) is `match`, `cases` and the transport. `within` is `rewrite`-only and doesn't
  touch them. Once F7's single abstract-and-transport module exists, the pattern filter becomes a
  parameter of the shared occurrence search, and `match … within` would cost little; not proposed
  until a day needs it.
- **Stage R** (`rewrite f`, D1433: a rule naming a definition is one step of it) composes:
  `rewrite f within …` unfolds `f` only inside the pattern. Nothing to design. **[inferred]**

## 6. The design

### 6.1 Syntax

```
rewrite p within P in t
rewrite <- p within P, q in t          -- `within` belongs to its rule
rewrite p within P at h in t           -- the pattern is matched in h's type
```

`P` is an expression in which `_` matches anything. `within` is a contextual word, like `at`: not
reserved (`Position.within` is a function in `aoc/src/Aoc/Common/Grid.sw:97` **[checked]**), and
special only where a rule can end, by the same parser rule as `at` (`ends_rewrite_rule`,
`crates/syntax/src/parser.rs:782–790`; `rewrite_body`, `:3266–3305` **[checked]**). A rule that
applies a function to a variable named `within` puts it in brackets, as with `at`. The pattern
ends at `,`, `at`, `in` or the end of the `rewrite`.

### 6.2 Meaning

For one rule with `within P`:

1. Elaborate `P` by inference, in the rewrite's context, each `_` an unknown of the pattern's own.
2. Read the goal (or `h`'s type) back as written. Walk it in pre-order. A subterm is a **pattern
   instance** if it has `P`'s head and number of arguments (the same `key` test the rule uses,
   `rewrite.rs:1529`) and unifies with `P`, solving only the pattern's unknowns. The unification
   is undone after each test, so each instance is matched afresh: `within Nat.pow 10 _` covers
   `Nat.pow 10 a` and `Nat.pow 10 b` both. Instances don't nest: the walk doesn't look for another
   instance inside one.
3. Inside each instance, find the rule's occurrences as today (§1.2), the rule's own unknowns
   solved by the first occurrence in the first instance, as now.
4. Abstract those occurrences, check the motive, round-trip and build the `J`, all unchanged
   (`rewrite.rs:1138–1176`).

Occurrences inside functions passed as arguments (the `under` path, `crates/elab/src/rewrite/
under.rs`) are not searched when `within` is given, in this version: an instance that mentions a
variable bound inside the goal is skipped, as a plain occurrence is today. If that leaves nothing,
the error says so (§6.3). No day needed it.

Implementation sketch: a `within: Option<Pattern>` on `Search`, and a wrapper hook for
`replace_with` (`crates/elab/src/lift.rs:333`) that, on a pattern instance, runs the rule's
`visit` over the instance (a `replace_with` starting at the current binder depth: today's
`go_replace` takes `under`, so it is a one-function addition) and returns the result, so the walk
doesn't descend twice. Pattern unknowns sit below `rule_metas` or are tracked separately so the
"one way" check (`rewrite.rs:1422–1430`) doesn't count them as foreign. **[inferred, a sketch for
the lane]**

### 6.3 Errors

- **The pattern matches nothing:** `E-REWRITE-WITHIN`, "`within Nat.pow 10 _` matched nothing in
  the goal", with the goal as written in a note. If the pattern matches somewhere only inside a
  function argument, a second note says `within` doesn't look there yet.
- **The pattern matches, the rule doesn't inside it:** `E-REWRITE-NOTHING` as today, with a note
  listing the instances found ("inside `Nat.pow 10 (k - 1)` and 1 more"), in pre-order, which is
  the order they appear in the printed goal.

Both get reject examples and snapshots.

### 6.4 The notes for kinds B and C (no `within` used)

When a `rewrite` is followed by a failure that the rewrite plausibly caused (E-REFL at the end of
the chain, or the body's E-TYPE-MISMATCH), add a note:

- **B:** if the rule replaced two or more occurrences: "`rewrite <- rightHalfLength stone even`
  replaced 3 occurrences of `stone.digitCount / 2`: in `List.take …`, in `Nat.pow 10 …` and in
  `List.drop …`; to rewrite some of them, `within` a pattern for that part".
- **C:** if the rule had unknowns, and other instances of its unsolved left side remain in the new
  goal: "`rewrite h` fixed `n := 1` at its first match; `f 2` is another instance it left: write
  the rule again for it (`rewrite h, h`)". That is
  `examples/reject/rewrite-first-instance.sw`'s snapshot gaining a note.

Both ride on 6a's E-REFL note, which already records each rewrite's left side as it runs and
searches for leftovers only on the error path (`bounded-readback.md` §4.1, "E-REFL's note"
**[cited]**; SW-1723, absorbed by 6a **[cited: bounded-readback-remaining.md:577]**). So this
stage comes after 6a.

No "every instance" form (`rewrite all`, Lean's `simp only`): D2541 rules out a `simp`, the
workaround is a repetition, and the day's cost was the message. If another day needs four or more
copies, revisit (D2862).

### 6.5 What it costs

- Parser: one contextual word and a field on `RewriteRule` (`crates/syntax/src/ast.rs:261`).
- Elaboration: the pattern filter in `Search`, one branch in `rewrite_once`, one in `rewrite_at`.
  No kernel change: the output is the same `J`, checked as today.
- Docs: syntax.md's `rewrite` section (a table row, the "What will surprise you" line replaced),
  the proofs chapter of the guide (`docs/guide/10-proofs.md`) with a checked example, and the
  accept and reject examples. A feature-tour page isn't needed: it's a proof convenience, not
  something a newcomer meets first.
- It adds one more caller to F7's copies (the folded search); it adds no copy.

## 7. What it should do, and how we'd know

- `examples/accept/rewrite-within.sw`: the 2025 shape (`k` in two places, `within Nat.pow 10 _`),
  the 2024 shape (three copies, the middle one), `within` with `at h`, and a pattern whose `_`
  differ between instances.
- `examples/reject/rewrite-within-nothing.sw` (`E-REWRITE-WITHIN`) and
  `rewrite-within-nothing-inside.sw` (`E-REWRITE-NOTHING` with the instances note).
- Converted: `repAbove` (`Repeated.sw:257–263`) from `J` to `rewrite … within`, and
  `recombineHalves` and `rightHalfSmall` (`Split.sw:26–41`) from `Eq.cong`/`ltCongRight` to
  `rewrite`. Their days' tests pass.
- 6a's lane adds the kind-A check: `Nat.toBitsFold`'s step (`Bits.sw:439`) checks with the rules
  in the order first written. (6a's brief, not a new ticket.)
- `rewrite-first-instance.sw`'s snapshot gains the C note.

## 8. Decisions

- **D2860: add `within P` to a `rewrite` rule, replacing only the occurrences inside parts of the
  goal that match the pattern `P` (`_` for anything), matched in the goal as printed?** [rec: yes,
  because it turns both kind-B days' `J`/`Eq.cong` into one-line rewrites, says where in the
  problem's terms, and changes nothing for rules without it]
- **D2861: no occurrence numbers (no `nth_rewrite`, `at 2` or `(occurrence := n)`) for now?** [rec:
  yes, because numbers count positions the printed goal hides (implicit, instance and proof
  arguments), would mean different places before 6a depending on which search ran, and break when
  the goal changes; `within` covers every day]
- **D2862: for "the `_` matched only one instance" (2024 day 4), a note on the failure that
  follows, and no "rewrite every instance" form?** [rec: yes, because the day's cost was the
  misleading message, repeating the rule works, and D2541 rules out `simp`; revisit if a day needs
  four or more copies again]
- **D2863: the word is `within`, contextual like `at` (not reserved)?** [rec: yes, because `in`
  and `at` are taken by the body and the hypothesis, `within` reads as English at the call site,
  and `Position.within` in AoC stays legal]
- **D2864: a pattern's `_` are wildcards matched afresh at each instance, unlike a rule's `_`,
  which the first match fixes?** [rec: yes, because a pattern says where to look, not which term
  to replace; `within Nat.pow 10 _` meaning "every power of 10" is what both days need, and the
  difference is one line in syntax.md]

Not questions (mine to decide, stated): `within` doesn't wait for 6a (§5.1); no `under`-path
support in the first version (§6.2); the notes of §6.4 come after 6a because they share its E-REFL
machinery; SSReflect's named position (option 3) is left out until a day needs it.

## 9. Tickets to file

In order. The first can start now; the second waits for SW-1839 (6a).

1. **`rewrite p within P`** (§6.1–6.3, §6.5). Opus (a `rewrite` change: core language under
   D2506). 90 min. Parser word and AST field; the pattern filter in `Search`; `within` with `at h`;
   `E-REWRITE-WITHIN` and the instances note; syntax.md (`rewrite` table row and the "What will
   surprise you" line), `docs/guide/10-proofs.md` with a checked example, accept and reject
   examples. Tests: `task test:one -- rewrite` (the rewrite examples and their snapshots), the
   parser's `rewrite` unit tests, `task snap:hashes NAME=rewrite-within` and the
   `hash_stability` test for the new examples, and the guide example check for the proofs
   chapter. Absorbs SW-758's "rewrite occurrence selection" item.
2. **Notes for a `rewrite` that replaced too much or too little** (§6.4). Sonnet. 60 min. After
   SW-1839, on its E-REFL note. Tests: the snapshots of `rewrite-first-instance.sw` and of a new
   reject example for the B note; `task test:one -- rewrite`.
3. **Convert the two kind-B proofs** to `within` (§7): `Aoc.Year2025.Day02` `repAbove`, and
   `Aoc.Year2024.Day11` `recombineHalves` and `rightHalfSmall`. DeepSeek (mechanical, with the
   exact lines given). 30 min. After 1. Tests: those two days' tests only (`task test:one --` each
   day), and `stitchwort fmt` on the files.

Also, for the orchestrator: add to SW-1839's brief "check `Nat.toBitsFold`'s step
(`Bits.sw:439`) with `halfOfDoubleBit` first" (kind A, §7), and drop the occurrence item from
SW-758's title once ticket 1 is filed.

## 10. What this note did not do

- Ran nothing. The claims about 6a fixing kind A, and about the `Eq.cong` widening with a lambda
  working today, are inferred; ticket 1's lane can check the second in a minute.
- Did not reopen the SSReflect or Lean manuals: §3's details for them are from memory or from
  calc-rewrite.md's citations, as labelled.
- Did not design `within` for `match`, `cases` or the transport (§5.1), or under binders (§6.2).
