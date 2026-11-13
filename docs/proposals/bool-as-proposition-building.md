# Building a test fact from a proof of its reading (D3549a, SW-3087)

**Status:** built (SW-3087, 13 Nov 2026; see "As built" at the end).
Design addendum to [bool-as-proposition.md](bool-as-proposition.md)
§6.6, 13 November 2026, for D3549a (Matt, 13 Nov 2026: yes, once the reader
gaps are closed). Read-only analysis on `main` at `66ebcc00a`, plus
SW-3121 (step 2c), which landed while it was written. It follows the
risk analysis in [SW-3105-silent-read.md](../reviews/SW-3105-silent-read.md)
(Fable) and the counts in [SW-3101-measure.md](../reviews/SW-3101-measure.md).
D3550 (keep `.read` explicit for now) is assumed throughout: only the build
direction is implicit here.

Labels, as in the parent note: **[checked]** = run through today's release
binary (probe files `b1.sw` to `b7.sw`, in this lane's scratchpad
`sw3087/`); **[read]** = read in the source at the line given;
**[measured]** = counted with `grep` over `crates/elab/src/std`, `aoc/src`
and `games`; **[inferred]**; **[estimated]**.

## 0. In plain words

**The problem.** A program's facts are tests: `xs.contains x = True`. Where
a lemma or a definition wants such a fact, and you have a proof of what it
means (`m: x ∈ xs`), you have to wrap the proof in a helper:
`(List.memContains xs x).backward m`, `Bool.falseOfNotTrue _ (e => omega)`,
`DecEq.trueOfNe ne`. About 85 such wrappers are left in std and AoC
**[SW-3101]**. Constructors already do this (`Both a b` where `(p && q) =
True` is wanted, §6.6); a plain proof or a lambda doesn't, and gets a type
mismatch with no hint **[checked: `b1`, `b5`, `b7`]**.

**The change.** Where a test fact is expected and the term you give proves
the fact's reading, the compiler builds the fact for you:

```
theorem fromMem (x: Nat) (xs: List Nat) (m: x ∈ xs): xs.contains x := m
let e0: Nat.equal m 0 = False := e => omega          -- e: m = 0
let unequal: ((a + a != number): Bool) = True := same => differ (omega)
List.allOfAll _ map.cells (List.allOfMem _ map.cells (entry inCells => …))
  becomes  entry inCells => …                          -- against a `cells.all …` fact
```

It does this the careful way SW-3105 recommends: only after the declaration
has **failed** with exactly that mismatch, by checking the declaration again
with the build at that place. So a program that checks today can't change
meaning: the new step never runs for it.

**What it should do.** About 55 to 70 helper uses go **[estimated from the
per-helper counts in §5.3]**, mostly `Bool.falseOfNotTrue` (35 uses
**[measured]**) and `List.memContains … .backward` (25 **[measured]**, about
half of them in positions a build can reach). The cost is one extra check of
each declaration per built site, on the first check only (the cache keeps
the result).

## 1. What the user writes, and what it means

A **test fact** is `e = True` or `e = False` for a `Bool` `e` (the `Bool` on
the right; `True = e` isn't one, `reading.rs:260` **[read]**). Where one is
**expected**, a term is accepted if its type is one of the fact's
**candidates**, and the compiler wraps it in the reading's `backward`:

1. **The reading, one layer at a time.** The fact's reading (§5.4), then,
   while that reading is itself a test fact, its reading, and so on (at most
   8; this is the chain constructors already follow, `read_through`,
   `reading.rs:1073` **[read]**). The first layer whose proposition the
   term's type is wins.
2. **For `e = False` only, the plain meaning `¬(e = True)`** (as `.read`
   gives `¬e` for a leaf, §6.8). It comes after the readings, so a test with
   a negative reading builds from that first.

A **lambda** (which has no type of its own until checked) takes the first
candidate that is a function type: a `≠`, `∉`, `¬` or `∀` reading, else the
plain `¬(e = True)`. Its binders get that candidate's types.

| Given | Where expected | Candidate used | Today's helper, real use |
|---|---|---|---|
| `m: x ∈ xs` | `xs.contains x = True` | reading | `(List.memContains region.plots plot).backward member`, `aoc/src/Aoc/Year2024/Day12/Proofs/Sides.sw:116` (typed `let`), `:188` (argument) |
| `ne: a ≠ b` (or `same => …`) | `((a != b): Bool) = True` | second layer: `not` reads as `(a == b) = False`, which reads as `a ≠ b` | `DecEq.trueOfNe (same => differ (omega))`, `aoc/src/Aoc/Year2020/Day09/Proofs/Window.sw:16`; `Year2020/Day20/Proofs/Corners.sw:33` inside `Both` |
| `h: a ≠ b` | `(a == b) = False` | reading (via the decision, step 2b) | `DecEq.falseOfNe`, `std/Decidable/Decidable.sw:33`; its one use is a `rewrite` rule (`:42`), which keeps it |
| `same: a = b` at `Nat` | `(a == b) = True` | reading | `equalOf`, `aoc/src/Aoc/Common/Proofs/Grid.sw:30`, used at `:33`, `:36` |
| a `∀` lambda `x m => …` | `xs.all p = True` | reading `∀ x => x ∈ xs → p x` | `List.allOfAll _ map.cells (List.allOfMem _ map.cells (entry inCells => …))`, `aoc/src/Aoc/Year2021/Day09/Proofs/Part1.sw:35`, `:48` |
| `h: n < m` | `(m <= n) = False` | reading `Nat.leqReadsFalse` | `Nat.leqFalseOfLess`, `std/Nat/Arith.sw:527`, `std/Nat/Digits.sw:222`, `Common/Proofs/Range.sw:62` |
| `e => omega` | `Nat.equal m 0 = False` | reading `m ≠ 0`, so `e: m = 0` | `Bool.falseOfNotTrue (Nat.equal m 0) (e => omega)`, `std/Float/Float.sw:430`, `:457`–`:476` |
| `h: ¬(a ≤ b)` | `Nat.leq a b = False` | plain `¬(e = True)` | `Bool.falseOfNotTrue (Nat.leq a b) h`, `std/Nat/Arith.sw:93` |
| `wallHeld => …` | `world.isWall p = False` (a leaf) | plain `¬(e = True)` | five in one theorem, `aoc/src/Aoc/Year2024/Day15/Proofs/Widen.sw:48`–`:76` |

Today each row is `E-TYPE-MISMATCH` **[checked: `b1`–`b3`, `b5`–`b7`;
`b4b` for `!=`]**.

**The equation case is a build.** `(x == y) = True` from `same: x = y` (at
`Nat`, or any type with `DecEq`) is built, because `x = y` is the fact's
reading (D3549a's own wording covers it). It can't be confused with the
fact itself: `same` is an equation at `Nat` and the fact is one at `Bool`,
so they never unify, and the build only happens after they have failed to.
A given equation that *does* fit as the fact (an equation between `Bool`s
that unifies, or one whose type is still an unknown) is taken as the fact,
as today, and nothing is built. `rfl` and `Refl` never build (the rule of
§6.1): against `(b == b) = True` they mean the equation, and `DecEq.refl b`
stays (114 uses **[measured]**).

**What is not built**, each an error as today:

- **A proof of a whole compound.** `k: x ∈ xs ∧ x < 3` against
  `(xs.contains x && x < 3) = True`: the `&&` layer's reading is
  `xs.contains x = True ∧ x < 3 = True`, which isn't `k`'s type, and the
  next layer is not looked at because the reading isn't a test fact. `Both
  m k'` builds it part by part (the constructor reads `&&`, then each part
  is a build of its own). One step, at one place.
- **Where nothing expects a test fact**: an untyped `let`, a `rewrite`
  rule, `Eq.sym (…)`, `Eq.trans`. About half of the `memContains.backward`
  uses are of this kind (13 of 25 **[measured]**) and keep the helper.
- **A term written `h.read`.** Read and then built would convert between two
  tests with the same reading, a silent `simp` (SW-3105 §4.4). The build
  refuses a term whose head is a written `.read`.
- **A cons-unfolded `all`.** Since SW-3121, `[d, ..more].all p` reads as `p
  d ∧ more.all p` (step 2c), so a `∀` lambda doesn't build it; `Both` does.

## 2. The mechanism: repair after failure (form R)

### 2.1 The term

For a candidate at layer *k*, the term is the reading's `backward` applied
*k* times, innermost first: `Iff.backward (r₁ args) (… (Iff.backward (rₖ
args) p))`, the same terms `step_proof` writes for constructors
(`reading.rs:1078` **[read]**), and for a decision `d.complete p`. For the
plain candidate, `Bool.falseOfNotTrue e p`. The kernel checks all of it.

### 2.2 The trigger

The first check of a declaration is exactly today's. When an
`E-TYPE-MISMATCH` is made (`Ctx::mismatch`, `check.rs:1086`, or the lambda
error, `check.rs:4851` **[read]**), it gets a structured field, `build:
Some(span)` (as `Diagnostic.import` carries a quick fix's import,
`crates/syntax/src/diagnostic.rs:51` **[read]**), if all hold:

1. the expected type, as written (`expected_as_written`), is a test fact,
   and neither its test's head nor the found type is blocked on an unknown;
2. a candidate (§1) fits: the found type is convertible with it, or unifies
   with it with everything solved taken back (as `read_note` does today,
   `reading.rs:1735`–`:1743` **[read]**); for a lambda, a candidate is a
   function type;
3. the term isn't a written `.read`, `rfl` or `Refl` (as built: a bare
   `rfl` never gets here; see "As built").

This is computed when the error is made, with the same unify-and-undo the
`.read` note already does in the first check, so the first check is
unchanged. It's skipped at once (one look at the expected type) unless the
expected type is a test fact.

### 2.3 The retry

`with_local_retries` (`crates/elab/src/lib.rs:2687` **[read]**) already
re-runs a declaration's body from clean state (unknowns cleared) when it
can make progress. It gets one more reason to: the body failed with an
error whose `build` field names a span not yet in the declaration's
**build set**. The span is added and the loop goes round. In the rounds
after, at a span in the set:

- `compare` (`check.rs:6074`), after everything it tries today has failed
  and before it makes the error, builds from the first candidate that fits;
- the lambda arm checks the lambda against its candidate and builds.

A span in the set is a permission, not an instruction: the plain check is
still tried first, so a span reached again in another way (a fall-back
path, a second elaboration of the same argument) where the term fits as it
is gets no build.

**Bounds.** A span is added once, so a declaration with *k* built sites is
checked *k* + 1 times (errors come one at a time). The densest real
declaration has 5 (`widenSeparate`, Day 15 `Widen.sw` **[read]**). The set
is capped at 8; past it the error is reported as today, with a note that
says so. A failure whose span is already in the set, or that has no
`build` field, ends the loop and is reported.

**Where the loop sits.** Inside `with_local_retries`, so it runs after the
body's own fall-backs and before the declaration's. Its five callers
(`lib.rs:1556` tests, `:2676` definitions and theorems, `partial.rs:491`,
`decreasing.rs:1424`, `defaults.rs:267`) must not themselves fall back on a
mismatch; the one I read that falls back at all, a test's `Bool`-then-
partial retry, does so only on `E-PARTIAL` (`lib.rs:1592` **[read]**). The
implementation lane confirms the other four, or moves the loop out to
`group` (`lib.rs:2751`), which re-runs a whole mutual group per round.

**Postponed comparisons.** When `compare` is stuck on an unknown it places
the term as it is and queues the comparison (`queue.rs:1036`, SW-3105
§2.3). If that fails later, nothing can be inserted. In the first version
such failures carry no `build` field (no wasted round); a placeholder, as
`DecideTerm` does (`check.rs:6010`), can follow if real code needs it.

### 2.4 Why it can't change a program that checks today

The retry runs only for a declaration whose check has failed, and the first
check runs exactly as now (the field is computed after the mismatch, with
its unification undone, as the `.read` note's already is). A declaration
that checks today never reaches the retry, so its term, type and hash are
the same. A declaration that failed today may now check; its dependants
that failed because of it (`E-FAILED-DEPENDENCY`) may then check too. That
is the whole change.

The constructors' building (§6.6, `check.rs:5044`, `:5074` **[read]**) is
untouched: it is a direct step, shipped with stage 2, and it composes with
this one: `Both m k` against `(xs.contains x && x < 3) = True` reads `&&`,
checks `m` against `xs.contains x = True`, fails, and the retry builds `m`.

## 3. The hazards from SW-3105, in this direction

- **The flip, mirrored (`x13.sw`).** `{ c | why = m }` with `c: Checked
  (xs.contains x = True)` and `m: x ∈ xs` checks today by changing the
  record's parameter, `records.rs:1182`'s fall-back **[checked again: still
  checks]**. A step in `compare` would make the update as written succeed
  and keep the old type, silently. Under form R it never fires: the
  declaration checked. The example stays as an accept test whose `let
  member: x ∈ xs := again.why` would fail if it flipped.
- **`cases in t` (`cases.rs:356`).** Only in a retry, where the proof is new
  anyway.
- **Equations.** The fact is an equation, and is used as one wherever it
  fits; a build only happens where it doesn't. The asymmetry SW-3105 §4.4
  noted (built from `a = b`, but not read back to it) is now just "building
  is implicit, reading is `.read`" (D3550).
- **Order.** `let w := if c then found else m` (`x14.sw`) is an error today
  and will check, with `w` the test fact: the second branch is checked
  against the first's type and is built. `if c then m else found`
  (`x15.sw`) stays an error asking for `.read`. That is what any `if` does
  (the first branch sets the type); it's documented with an example.
  Through a lemma, `both m k` against a test fact isn't built where `Both m
  k` is (the lemma's result is a compound, §1); the error note says to use
  `Both`.
- **Never chained.** A build never applies to a written `.read`, and
  nothing reads implicitly, so read-then-build can't happen.

**What the retry costs** **[estimated]**: one full check of the declaration
per built site, only on a check that isn't cached. The ~70 sites after the
sweep are spread over roughly 50 declarations out of thousands, so a
whole-tree `check --no-cache` should move by well under 1 %; the long-proof
case is the editor, where a declaration with 5 builds is checked 6 times on
each edit. If that shows up, the build set can be kept between edits and
tried in the second round, after an unseeded first round has failed (so
§2.4 still holds).

## 4. How it shows

- **Hover** on a built term: `m : x ∈ xs`, then "builds the test fact
  `xs.contains x` (by `List.memContains`)". The build set goes in the check
  cache's entry with the declaration, so hover survives a cached replay.
- **Goals and hypotheses**: unchanged. Inside a built lambda the binder has
  the candidate's type (`e: m = 0`), which is what the goal shows.
- **When the retry fails** with an error at or inside a built span, a note
  says so: "`m` builds the test fact `xs.contains x` here, as a proof of `x
  ∈ xs`". Otherwise the error is the retry's own, with no note: it is a real
  error of the program with the builds in.
- **When no candidate fits**, the mismatch gets a note mirroring the
  `.read` one: "this expects the test fact `xs.contains x`, which reads as
  `x ∈ xs`: a proof of that is accepted here" (today `b1`, `b5` have none
  **[checked]**). For a compound: "build it part by part with `Both`".
- **At the cap**: the error as today, plus "the compiler built 8 test facts
  in this declaration and stops there".
- No inlay hint: there is no word to show.

## 5. Tests

### 5.1 The two oracles (SW-3105 §4.6)

Both are whole-corpus runs, for the verifier or Overmind, not a lane.

1. **Programs that check are unchanged.** A switch, `STITCHWORT_BUILD=0`,
   turns the retry off (in the cache key, or run with `--no-cache`). Every
   declaration in std, AoC, the roguelike and the examples that checks with
   it off has the same type and hash with it on. True by construction; the
   run tests the construction (that the field's unify-and-undo leaks
   nothing). The example hash snapshots must not move in the
   implementation's merge, except for new examples.
2. **Deletion oracle, the build way.** SW-3111 deletes each `.read`; it
   gets a second half: replace each build helper at a position that expects
   a test fact (`Bool.falseOfNotTrue e p` → `p`, `(r …).backward p` → `p`,
   `DecEq.trueOfNe p` → `p`, `List.allOfAll _ xs (List.allOfMem _ xs f)` →
   `f`, `Nat.leqFalseOfLess a b p` → `p`, `equalOf a b p` → `p`) and check
   that one file. Allowed: an error, or a check where every declaration has
   the same type and every `def` the same hash (a theorem's proof may
   differ). This half is also the sweep's work list.

### 5.2 Examples

- `accept/build-from-reading.sw`: every row of §1's table, in a typed
  `let`, as a lemma's argument and inside `Both`/`Inl`/`Witness`; the
  two-layer `!=`; a lambda taking the reading's binder; the plain `¬(e =
  True)` for a leaf and for `Nat.leq`; five builds in one theorem.
- `accept/build-keeps-meaning.sw`: `x13.sw` (the record update keeps
  today's type) and `Eq.sym same`, `rewrite same in` on a fact used as an
  equation, each with a line that would fail if it flipped; `x14.sw`
  checking with `w` the test fact.
- `reject/build-*.sw`: a whole compound (note: use `Both`); `rfl` against
  `(b == b) = True`; `h.read` against another test with the same reading;
  `x15.sw` (asks for `.read`); nine builds in one declaration (the cap).

### 5.3 The sweep afterwards

Sonnet or DeepSeek, driven by the oracle's list:

| Helper | Uses **[measured]** | Goes **[estimated]** |
|---|---|---|
| `Bool.falseOfNotTrue` | 35 | ~30 (not in rewrite rules); where the lambda's binder becomes the reading (`Set.contains t other = False` → `other ∉ t.toList`), the body changes, often by a second build |
| `List.memContains … .backward` | 25 | ~12 (13 are rewrite rules, `Eq.sym`, untyped `let`s) |
| `List.allOfAll` with `allOfMem` | 9 | ~6 |
| `Set.containsFromListIff`/`memToList` `.backward` | 13 / 15 | few: the reading is `k ∈ (Set.fromList xs).toList`, not `k ∈ xs` |
| `DecEq.trueOfNe`, `equalOf`, `Nat.leqFalseOfLess` | 3, 3, 4 | all, and the helpers themselves |
| `Bool.orLeft`/`orRight`, `notTrue`, `notOfFalse`, `andIntro` | 2, 2, 5, 2, 4 | most (some already go with `Inl`/`Inr`/`Both` today) |

About 55 to 70 in all, against SW-3101's ~85 ± 25 %. `DecEq.refl` (114) and
`List.anyOfMem` (7, which `Witness y (Both mem q)` already replaces) are
not this design's.

## 6. Staging and estimate

1. **Implementation, Opus** **[estimated 6 to 8 h]**: candidates and the
   `build` field (reading.rs, beside `read_note`); the build set, the round
   in `with_local_retries` and the cap; the marked-span steps in `compare`
   and the lambda arm; the notes; hover and the cache entry; the switch;
   the examples; `docs/guide/` and `docs/syntax.md` (a user-visible
   feature), and §6.6 of the parent note (drop "Not built: a lambda").
   Depends on SW-3095 (`==` on `Nat` inside expressions reads as `x = y`)
   for the equation rows; the rest can go now.
2. **Oracles, Sonnet + Overmind** **[estimated 2 to 3 h of lane, plus a
   compute run]**: the switch run and SW-3111 with its build half.
3. **Sweep, Sonnet or DeepSeek** **[estimated 3 h]**: §5.3.
4. **Then D3550 again**: with the retry machinery built and the oracles
   clean, reading in form R is a small step (SW-3105 §6, "what would change
   my mind").

## 7. Calls made here, and one question for Matt

Implementation calls, open to change in the lane:

- The equation case builds (§1): `x = y` is the reading of `(x == y) =
  True`; `rfl`/`Refl` never build.
- A lambda takes the reading's binder where the reading is a function type,
  else `¬(e = True)` (so `inA => …` against `s.contains k = False` gets
  `inA: k ∈ s.toList`, the premise of `k ∉ s.toList`, not the test fact). This matches
  `.read`, which gives the same reading.
- `e = False` also builds from the plain `¬(e = True)`, after the readings.
- Lambdas go through the retry too, not a direct step like constructors:
  one mechanism, and no audit of fall-backs for them.
- Cap 8 per declaration.

**D3555 (not blocking; for after the sweep): should building get a word,
as reading has `.read`, for the places where no test fact is expected
(`rewrite` rules, `Eq.sym`, untyped `let`s)?** About 13 `memContains`
uses and a handful of others are in such places. Rec: **not now**; count
what's left after the sweep, then decide (the parent note's §6.8 already
deferred it to the counts).

## 8. Method and limits

- Probes `b1.sw`–`b7.sw` and `b4b.sw` (in
  `/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw3087/`)
  and SW-3105's `x13.sw`, each run once with `target/release/stitchwort
  check`. No build was implemented, so every statement about what it does
  is **[inferred]**.
- Read: `reading.rs` (`test_fact_in`, `for_ctor`, `for_record`, `dot_read`,
  `read_through`, `read_note`), `check.rs` (the mismatch error, the lambda
  arm), `lib.rs` (`with_local_retries`, the test loop), the
  `decreasing.rs` fall-back at `:1476` (a warning only). Not read: the
  bodies of `partial.rs:491` and `defaults.rs:267`'s callers.
- Counts are `grep` over source lines and include a few comment-free false
  hits; the "goes" column is a judgement from reading about 30 sites.

## As built (SW-3087)

`crates/elab/src/build.rs`, with the candidates in `reading::candidates`.

- **Where.** `check::compare`, after `along_match_equation` and before the
  error: in a round where the span is allowed, the build; otherwise the
  mismatch carries `Detail::build` (the span) when a candidate fits, found
  with a snapshot taken and restored. The lambda arm of `check_value`
  (a lambda against a non-function type) does the same with the first
  function-type candidate. The retry is a loop round in
  `with_local_retries` (`build::again`), before the local-definition
  retry. The other four callers (`partial.rs`, `decreasing.rs`,
  `defaults.rs`, the test loop in `lib.rs`) were read: none falls back on a
  type mismatch (the test loop only on `E-PARTIAL`), so the loop stays
  there.
- **The plain candidate** is `Decidable.toBoolOfNot (Bool.decTrue e) p`,
  both in the core, so building needs no std file loaded.
- **Notes.** A mismatch against a test fact where nothing fits gets "this
  expects the test fact …, which reads as …: a proof of that is accepted
  here" (for a compound, "build it part by part with `Both`"); a written
  `.read` that would fit gets "`.read` … isn't built back"; an error inside
  a built term gets "here, the compiler builds the test fact … from a proof
  of …"; the ninth build, the cap note. The `build` field is taken off the
  error that is reported.
- **Hover** goes with the call defaults' hover text (`nav.call_defaults`),
  which the check cache already keeps, keyed at the built term's span: it
  shows on a variable or a call's head; for a built lambda, on its first
  binder.
- **Switch.** `STITCHWORT_BUILD=0` (`Options::build`), part of the cache
  key.
- **Differs from §3.** `x14.sw` (`let w := if c then found else m`) builds
  `m` in the retry, but an `if` whose branches are proofs is then
  `E-UNIVERSE` (an `if` in a `let` with no type is checked in `Type`), as
  it is for any two proofs; so the order example isn't in
  `build-keeps-meaning.sw`. `x15.sw` is `reject/build-second-branch.sw`.
- **Postponed comparisons** carry no field, as planned (the field is set
  only in `compare`'s own error).

- **After the review** (`docs/reviews/SW-3087-review.md`):
  - A permission is the place *and* the fact expected there (shown), so a
    comparison at the same place against another fact isn't built.
  - The other failed `match` arms (`branch_errors`) are read too: every arm
    that can build is allowed in the same retry, so a `match` takes two
    checks, not one per arm. Each round starts with `branch_errors` cut
    back to its length on entry, so a failing declaration reports only the
    arms that failed in the last round (this also fixes the
    local-definition retry, which had the same leak).
  - A `.read` is recorded from its receiver to its field, so a call whose
    last argument is `h.read` isn't mistaken for one.
  - There is no `rfl`/`Refl` guard: a bare `rfl` is checked as the
    equation itself and never reaches the build, while `(rfl: b = b)`,
    given its type, is a proof of `b = b` like any other and builds.
