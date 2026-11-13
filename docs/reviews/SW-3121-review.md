# SW-3121 review: `all` / `any` of a cons read as `∧` / `∨`

Opus review (D2364: the change decides which proof terms are built from
test facts). Reviewed `git diff main...lane/SW-3121` (commit cc2665177),
without snapshot and board files.

**Verdict: merge, with two follow-ups filed.** The rule is sound: a reading
only picks which `Iff` the elaborator applies, and the kernel still checks
`Iff.forward (Bool.andReads (p d) (more.all p)) h` against `h`'s type by
conversion. It is also deterministic, and it does what the ticket asked:
41 `Bool.andLeft`/`andRight` helper calls become 8. There is a cost, though.
Three things that worked on a cons list before now fail: `.read x m`,
`Witness` on `any`, and `auto` applying the `∀` to a member. Nothing in std
or AoC that I checked used them, but the docs don't say they changed, and
the `.read` failure gives a poor error.

## What I ran

- Release CLI built in the worktree (it was already up to date).
- `examples/accept/readings-all-cons.sw`: **fails on main's binary**
  (E-NO-NAMESPACE on `.left`/`.right`, E-NO-READING on `Both` and `Inl`/`Inr`)
  and **passes on the lane's**. So the example covers what it claims.
- `check --std --no-cache` on List/Lemmas, List/SortLemmas, Set/Spec,
  Map/Map, Graph/Search, List/Distinct, Parse/Runs and Nat/Pigeonhole. These
  are the std files with the most `.read x …` uses. All pass.
- `check --no-cache` on these AoC days: 2021 Day12, 2020 Day16, 2024 Day12,
  2020 Day20, 2021 Day08 (all heavy `.read` users), and 2020 Day04 and
  2024 Day24 (edited by the lane). All pass.
- These reading examples check on the lane's binary: effect-logic-in-lambdas,
  list-toolkit, reading-decision-test, auto-readings, cases-readings,
  read-all, readings-any-all, readings-unfold-defs, readings-witness-bound,
  readings-applied-facts and bool-readings. The rejects reading-shape-argument
  and reading-overlap still give their errors.
- Edge-case files in the scratchpad, checked on both binaries (results below).
- Rough timing of 5 std files (`--no-cache`): main 8.9 s, lane 6.4 s. That
  is noise from different builds. There is no measurable cost.

## Findings

### Medium

**M1. `auto` no longer applies a cons fact's `∀` to a member in scope.**
(`crates/elab/src/reading.rs:816-824`; the behaviour that
`examples/accept/auto-readings.sw:5-6` promises.)

```
def small (x: Nat) [auto ok: x < 5]: Nat := x
def afterMatch (xs: List Nat) (h: xs.all (x => x < 5)) (x: Nat) (m: x ∈ xs): Nat := match xs with
  | [] => 0
  | [d, ..more] => small x            -- main: ok; lane: E-AUTO-STUCK `x ≤ 4`
def fromCons (d: Nat) (more: List Nat) (h: [d, ..more].all (x => x < 5)) (x: Nat) (m: x ∈ [d, ..more]): Nat := small x
                                      -- main: ok; lane: E-AUTO-STUCK
```

`auto` now sees `d < 5` and `more.all p` (a `∀` over `more`), but the
membership `x ∈ [d, ..more]` is a disjunction it doesn't split. The reverse
case gets better: `small x` with `m: x ∈ more` failed on main and works now.
A `match` on the list inside a function that relies on `auto` is a natural
pattern, so code that is fine on main can break. I found no `[auto …]`
parameter over `all`/`any` in std or AoC, and the AoC days I checked pass.
Overmind's whole-AoC and roguelike check will show whether anything else
depends on it.

Fix, as a follow-up ticket: let `auto` keep the quantifier reading of a cons
fact as well as the step. That means one lookup with `cons_step` turned off,
taking the `∀`'s facts too. The alternative is to treat the cons step as a
fallback, tried only when an `∧`/`∨` is wanted (`.left`, `.right`, `Both`,
`Inl`, `Inr`, a `Both`/`Inl` pattern) and the quantifier reading doesn't
fit. That keeps `.read`, `Witness` and `auto` working, but it is a bigger
change to how the reader dispatches, and it makes a fact's reading depend
on how it is used. I recommend the `auto`-only fix.

**M2. Three uses of cons facts that worked before now fail, and neither the
docs nor the errors say so.** (`docs/guide/10-proofs.md:742`,
`docs/proposals/bool-as-proposition.md:454`.)

| Proof on a cons list | main | lane |
|---|---|---|
| `h.read x m` with `h: [d, ..more].all p` | ok | E-NOT-A-FUNCTION "this isn't a function" |
| `[1, 2, 3].all (x => x < n)`, then `h.read 2 …` | ok | E-NOT-A-FUNCTION |
| `Witness d (Both (Inl rfl) hd)` for `[d, ..more].any p` | ok | E-NO-READING |
| `match h with \| Witness x found` for `[d, ..more].all p = False` | ok | E-NO-READING |
| `match h with \| Inl a \| Inr b` for the same `= False` fact | fails | ok (it now reads as `p d = False ∨ more.all p = False`) |

All of these follow from the design. Most need one cheap fix:

- The guide paragraph and §5.4 step 2c should say what happens at `= False`.
  `[d, ..more].all p = False` reads as `p d = False ∨ more.all p = False`, and
  `any` reads as a `∧` of `= False`s, through `Bool.andReadsFalse` and
  `orReadsFalse`. The quantifier forms `∃` and `∀` no longer apply.
- When `.read`'s result is applied to arguments and the fact read as `∧`/`∨`
  because its list is a cons, the E-NOT-A-FUNCTION error needs a note. It
  should say that `[d, ..more].all p` reads as `p d ∧ more.all p` here, and
  that the reader should use `.left`/`.right`, or the `∀` through
  `(List.allReads _ _).forward h`. As things are, the error is a puzzle
  (orchestrator: file as a small diagnostics ticket).
- Literal lists are affected too: `[1, 2, 3].all p` now reads as a chain of
  `∧`s. The docs only talk about the case tree's `[x, ..xs]`. Add a sentence.

### Low

**L1. The check matches the definition's name as a string.**
(`reading.rs:765`) `g.def(f).name().to_string() == "List.all" | "List.any"`.
It is correct today. Method calls (`xs.all p`) resolve to the same `DefId`,
and `NonEmptyList.all`, `Array.all`, `Text.all` and `Map.all` unfold to
`List.all xs.toList p`, a call, so they read as the quantifier. That is
consistent with the "named by a call" rule. `Set.all` is a fold. A user
can't define a second `List.all`. Two weaknesses:

1. A rename of `List.all` would switch the rule off silently. Only the
   example would catch it.
2. It allocates a `String` on every unfold step of every lookup. That is
   negligible beside `reading_for`'s linear scan, but it is easy to avoid.

Better: key the rule on the reading that would be found, by skipping when
`theorem` is one of the four `List.{all,any}Reads[False]`, resolved by name
once. Or add `Builtin::ListAll`/`ListAny` to the registry. Either costs one
id comparison.

**L2. The cons check looks at every argument, not the list's position.**
(`reading.rs:774-780`) Today only the list argument can be a `List` cons:
the others are the element type, a function and the row, whose `Ctor` is the
row type's. The check is correct, but it would be clearer to test the
argument at `List.all`'s list position.

**L3. A solved meta standing for the list isn't seen as a cons.**
(`reading.rs:775`) Only the test as a whole goes through `force_solved`; the
arguments don't. So `List.all ?m p` with `?m := [d, ..more]` reads as `∀`
until the meta is zonked. I couldn't trigger this. `(keep _ h).left` fails
on main and on the lane, because the `_` is never worked out, which is a
separate existing problem. Calling `force_solved` on the argument (it
follows metas only and never unfolds a call) would make the rule independent
of when metas get solved. It costs one line.

**L4. The docs don't say what `[].all p` reads as.** It still reads as the
quantifier: `∀ x ∈ [] → …` and `∃ x ∈ []`. I checked: `match h with |
Witness x found => Void.exfalso found.left` works for `[].any p`. That's
fine, but a reader of step 2c might expect `True`/`False`. Add one clause.

**L5. Example gaps.** (`examples/accept/readings-all-cons.sw`) The example
has no `= False` case and no case of a list named by a call, for example
`def ys (d) := [d, 1]` then `(ys d).all p` reads as `∀`. The doc and the
guide both claim the latter. Add both, a line each.

## Questions from the brief

- **Same fact, different readings?** Readings are deterministic, given the
  value's shape. The shape comes from the context, which is the intent:
  - A `match` (case tree) and `rewrite e at h` both make the fact a cons:
    `rewrite e at h in h.left` works on the lane.
  - A `let` keeps the literal.
  - A call such as `(ys d).all p` stays `∀`.

  `lookup` always runs folded. With gluing off, `as_written` re-evaluates the
  written type with the case tree's refinements, so both modes see the
  `Ctor`. On main the reading of a cons fact was the inconsistent one.
  Main's own error message says "`d <= 4 && more.all (x => x <= 4)` reads as
  `∀ …`": with no written type and gluing off, the value had already been
  unfolded to `&&`. The rule makes this consistent rather than less so.
- **Cached vs fresh:** the cache stores the elaborated terms, and the same
  source gives the same values, so there is no order dependence and no hash
  instability beyond the expected one-off ripple. That ripple affects proofs
  whose facts now go through `andReads` and `orReads`, including `auto` uses
  that still succeed by another route. The lane didn't repin the snapshots;
  that is the verifier's job.
- **`cases`:** `cases` on a cons `all` fact closes `d < 5` and
  `more.all p` on both binaries.
- **Performance:** one name lookup per unfold step. Nothing measurable.

## Decisions for Matt

None blocking. M1's fix (keep the quantifier reading for `auto`) is an
implementation detail, so it is the orchestrator's call.
