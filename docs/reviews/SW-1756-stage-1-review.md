# Review: bounded read-back stage 1 (SW-1746)

**Ticket:** SW-1756, an independent review of `lane/SW-1746` at `28cc45f04` (D2364: the
change generates kernel terms). **Reviewer:** Opus, 6 Nov 2026. **Against:**
`docs/proposals/bounded-readback.md` §2.5, §2.6, §6 and stage 1, D2523, D2535, D2541–D2542.
The code was read; the branch's release binary (built after the last source change) was run
on the AoC and roguelike namespaces below. Line numbers are the branch's.

## Verdict: merge

Nothing found that blocks. The kernel sites are sound, the `decide` argument holds and held
again over 53 AoC namespaces, the proofs most likely to be hit pass, and the hash moves are
the ones the change should cause. Three small follow-ups, none needed before merging:

1. **Correct the note's §2.5 table** (doc only). It lists `matching.rs:521/657/851` as output
   terms "the kernel checks" and `named.rs:895` as a binder type. They are neither: the
   `matching.rs` terms are occurrence-search targets and `named.rs:895` is a mention test
   (§5 below). The lane was right to leave them; the note should say why, so that a later
   stage doesn't "finish" stage 1 by folding them.
2. **`proof_expected` with an unknown inside a call** (`check.rs:4980`; a backlog ticket,
   low priority). See §1.
3. **Count `decide`'s steps in stage 0c's measurement** (`STITCHWORT_READBACK_METRICS`).
   See §2, "budget".

## 1. Kernel terms

A folded term and the unfolded one are convertible, and the kernel decides only up to
conversion, unglued: evaluating a folded term with gluing off unfolds every call, so the
kernel sees the same normal form. So no term can come to *mean* something else. What could
differ is whether a check *succeeds*, in three ways, which I looked for:

- **A call the kernel can't unfold.** A call (`Value::Call`) is only made for a definition
  with a body that is visible (`value.rs:1716`, `body_seen`); a hidden opaque one stays a
  neutral in both read-backs. A definition still being elaborated has no body, so there is
  no call to it. Accessor types can only mention earlier fields, and `shared_fields` decides
  which fields are shared by a syntactic `mentions` on the declared field types
  (`shared.rs:117`), so the `unused()` placeholders in `accessors` (`shared.rs:240`) can't
  appear in a folded read-back: a folded read-back mentions a subset of what the declared
  type mentions.
- **A different sort.** `check.rs:4980` asks the kernel the sort of the expected type. The
  inferred type of `f args` is `f`'s declared result, of the unfolding its body's type; they
  are convertible, and there is no cumulativity (`docs/core.md`; I checked that `def P (x:
  Nat): Type := x = 0` is E-UNIVERSE), so `Prop` stays `Prop`.
- **An unknown.** The kernel rejects `Term::Meta` (`core/src/check.rs:411`). A folded term
  keeps a call's arguments, so an unsolved unknown in an argument that the unfolding
  drops (`def Holds {A: Type} (b: Bool): Prop := b = True` at an unsolved `A`) now
  reaches the kernel, where before it vanished. At `check.rs:4980` the kernel error becomes
  `Ok(false)`: the `if` is elaborated as a data `if` rather than a proof `if`, and then fails
  (it doesn't succeed wrongly). At `rewrite.rs:1605` the folded term is only evaluated (glued)
  and bound as a value, the body is checked only when it has no unknowns, and unglued
  conversion forces the calls, so a dropped unknown vanishes there as before. I couldn't
  build a case for `check.rs:4980` that gets that far (an implicit unsolved in an expected
  type is usually an error earlier), so this is a follow-up, not a fix: if it happens, read
  back unfolded there when the folded term has an unknown.

Steps rather than meaning: the kernel now computes calls in elaborated terms (an accessor's
type, `fromYes`'s goal) that it was handed already computed. That is extra work in the
kernel's budget where the call is expensive and its normal form small, and less where the
normal form is large (the reason for the change). Nothing in the runs below hit a limit.

## 2. The `decide` argument

The argument (§2.6) is right: with gluing off, evaluation unfolds every call, so the value
`decide_unglued` gets has the same normal form as before, and the procedures are found by
unification, which is up to conversion. The cases the brief asked about:

- **Unknowns.** Both read-backs replace solved unknowns as they go (`force_solved` at each
  visit, including a call's arguments). A call whose cached unfolding was computed while an
  unknown was unsolved is re-run in the folded path, so it computes now; in the unfolded path
  its stale, stuck unfolding was read back and re-evaluated, which also computes. Unsolved
  unknowns are the same neutral in both.
- **`Chars` against `Cons`, `Nat` against `Succ`.** Both are values the same machine
  produces, glued or not; `Chars` reads back the same way in both modes (`value.rs:2154`),
  and `Succ` of a call is the one place the modes differ in shape (`value.rs:2167`), where
  unification treats `Nat(n)` and `Succ` alike. A procedure is chosen by unifying its
  conclusion, so a representation difference could only matter to a first-order shortcut,
  and none showed up.
- **Budget.** This is the real difference. The unfolded path re-evaluated a normal form
  (cheap, linear in its size, but the read-back could be huge); the folded path re-runs
  every call in the proposition unglued, even one whose unfolding was already computed. For
  `decide` on an expensive computation with a small answer that is roughly twice the work,
  in one declaration's budget. Not seen in std (the lane's run) or in my AoC run, but stage
  0c's measurement should count `decide`'s steps so it is seen if it happens.

**Run:** `STITCHWORT_DECIDE_BOTH=1 stitchwort check --no-cache` over every `Proofs`
namespace of 2025's days and 2024 days 12, 15, 23, 2021 day 12 and 2020 days 3, 4, 19, 20
(the days that use `decide` or `byDecision` by name; 53 namespaces with their dependencies):
passed, **0 differences**, 62 s. Also all of 2025's day namespaces and those days' (18), 6 s:
passed, 0 differences.

## 3. Output terms and later searches

Folded accessor types (and folded `bind_missing` types: its `pi_value`, `named.rs:735`, is
evaluated from the folded `Pi` and flows on as the partial application's type) change what a
goal shows, so a search can find something different. Under D2541–D2542 that is the intended
behaviour, and a needle only inside a call is still found by the fallback when nothing is
visible. The risk is a proof that rewrote inside an accessor's computed type while a visible
copy also existed, or that rewrites *with* an accessor (whose sides are now calls).

**How I searched.** Every record declaration in `aoc/src` and `games/` (180, one or many
lines, by a script), filtered to those with a proposition field whose type contains a call;
then every `rewrite`, `match`, `calc` or `at` line using those fields. Candidates:

- `Aoc.Common.Grid` (`nonEmpty: (firstWidth rows == 0) = False`; `rewrite mapFirstWidth …
  in grid.nonEmpty`, `Grid.sw:199`).
- `Aoc.Year2025.Day08.Proofs` (`Labelled`, `Counted`: `rewrite counted.counts`,
  `counted.labelOwn`, `inv.agree`, `inv.stored`; their sides are `ownLabels` and `labelOf`
  calls, before this change computed).
- `Aoc.Year2024.Day21.Proofs` (`Fitted`: `keyAt`, `walk`, `cheapestRoute`, `distance`).
- `Rogue.Proofs` (`Valid`, `Framed`, `OnScreen`, `Corner`: `rewrite sound.framed.rows`,
  `sound.framed.columns`, `Bounds.sw:222–234`).

**Run:** `stitchwort check --no-cache Aoc.Year2025.Day08.Proofs Aoc.Year2024.Day21.Proofs
Aoc.Common.Proofs` (8 namespaces), then `Aoc.Year2025.Day08 Aoc.Year2024.Day21 Aoc.Common`,
then `Rogue.Proofs` in `games/rogue`: **all passed**. With §2's runs, about 100 s in all.

Not covered: AoC days whose records have no proof fields but whose proofs use std accessors
whose types moved (`Fin`'s bound, `Map`/`Set`'s invariants, `Ord`'s laws, `Float.valid`).
Those are the merge tier's and stage 6's to see.

## 4. The hashes

The moves are what the change should cause, but the expected set is wider than "things
mentioning an accessor whose field type contains a call": the other sites (`fromYes`'s goal,
binder types of elaborated lambdas, record-update `let`s and annotations) change the
elaborated terms of the definitions that contain them, and those move on their own.
Spot-checked:

- `autobind-values`, `record-ext`, `eqeq-proof-fields`: only `Main.Dial.inRange` moves
  (`position ≤ highest`, a call), to the same new hash in all three.
- `if-proof-branches` (`Capped.capped`), `int-dial` (`Pos.ok`), `update-identity`
  (`Range.ok`), `extract-let-in-match` (`Above.above`): an accessor each, nothing else.
- `negative-arguments`: tests of `Float.abs`; `Float.abs` and `Float.neg` mention `x.valid`
  (`Float.isValid bits = True`, a call), `Float.sub` calls `Float.neg`, and `Float.add`
  matches on the record rather than using the accessor, so it doesn't move. That is exactly
  the three pins. `FLOAT_DATA_HASH` covers the constructor's field types, not the accessor,
  so it stays.
- `bang-arguments`, `expected-types`, `show`, `namespaces`: the derived `Finite`
  instance's `%mem`, `%complete` and `%instFinite`, through std's `Finite` and `List`
  membership, which moved.
- `lemma-on-large-normal-form`, `logic-notation`: through `Set`'s and `Map`'s definitions.
- The prelude: 731 of 5,652 names, by namespace Map 282, Set 127, Graph 118, List 66, Float
  62, Mod 23, Ord 22, the rest a few each: all reach a record or interface with a
  proposition field (Map's and Set's invariants, Ord's laws, Float's validity).

I didn't find a move that none of the sites explains.

## 5. The skipped sites

Leaving them unfolded is right:

- `matching.rs:521`, `:657`, `:851`: the scrutinee's `ty_term` is a search target, not only
  a motive type. `occurs(a_normal, &b.ty_term)` (`:969`) compares it with a scrutinee's
  normal form; `free_levels` (`:1000`) decides copying; `cannot_occur` (`:1463`) needs
  `Term::Data` at its head, which a folded type alias would hide; and `normals`' cap is its
  size. Folding it would change what `match` generalises: stage 6b's work.
- `named.rs:895` (`dependencies`): a mention test. A folded domain can mention a parameter
  its normal form drops, which would add a dependency and change how arguments are planned.
  Mentions move to the reader in stage 4.

Related, and consistent: `bind.rs:96–99` keep their unfolded read-backs for the mention
tests, and the annotation's codomain (`whole_term`, `bind.rs:99`) stays the unfolded term
that test built. Harmless; it could reuse a folded read-back when stage 4 moves mentions.

## 6. Code quality

- The comments read well and say why. `decide`'s doc now states D484's clause in D2541's
  terms and gives the `y < 10` example the right way round.
- `STITCHWORT_DECIDE_BOTH`: fine as a debug switch, documented on `decide`. Two notes. It
  reads the environment on every decision; a `OnceLock` would make it free (not needed for
  correctness). And the unfolded run's steps aren't given back by the snapshot, so with the
  switch on a decision near its budget can fail in the folded run and be reported as a
  difference: worth a line in its doc. Keep it until stage 6 measures `decide` again, then
  drop it.
- `decided` compares `Debug` strings of zonked terms: crude but adequate for a check that
  expects equality.
- The guide's new sentence (`docs/guide/10-proofs.md`) and
  `examples/reject/field-type-as-declared.sw` say what users see, and the snapshot shows
  `fits s.books s.capacity = True`.
