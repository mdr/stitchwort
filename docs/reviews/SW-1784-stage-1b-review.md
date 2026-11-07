# Review: bounded read-back stage 1b (SW-1748)

**Ticket:** SW-1784, an independent review of `lane/SW-1748` at `861f426d2` (D2364: the
change generates kernel terms). **Reviewer:** Opus, 7 Nov 2026. **Against:**
`docs/proposals/bounded-readback.md` (revision 3) §2.5 and stage 1, D2523, D2541, D2543;
the stage 1 review (`SW-1756-stage-1-review.md`); the site table
(`SW-1747-stage-0b-sites.md`). I read the code and ran the branch's release binary on the
AoC and roguelike namespaces named below. For §2 I added a throwaway dump test on the
branch, and for the main side swapped `effects.rs` back to `main`'s copy for one build.
Both were removed afterwards, and nothing else in the tree changed. Line numbers are the
branch's.

## Verdict: merge

Nothing blocks it:

- Every changed site writes a term that the kernel checks up to conversion, or is a
  fallback check.
- The round trips still do their job.
- The hash moves are explained.
- No AoC or roguelike proof that uses `Char` or `Text` equality breaks.
- The roguelike's elaborated output is byte-identical whether its dependencies come from
  the check cache or are elaborated in the same run.

Whole AoC doesn't need to run before merging. The roguelike already passed here, cold.
Leave both to the merge tier. Two follow-ups, neither needed before merging:

1. **File a ticket (core, Opus):** a call's kept unfolding doesn't record whether it was
   computed with gluing on. The folded read-back can then write an unglued unfolding (§4).
   This is the likely cause of the lane's finding, and it predates this change.
2. **Doc only:** add the lane's "left unfolded" list to the note's stage 1 text, as SW-1756
   asked for stage 1. Then no later stage will "finish" 1b by folding `field_type`,
   `move_to` or the round trips in `families.rs`, `rows.rs` and `rewrite.rs`.

## 1. The changed sites

**Kernel-checked output** (most of `effects.rs`, all of `interfaces.rs` and
`derive_induct.rs`): row and type arguments of the effect builtins, `Comp` annotations,
handler eliminator implicits, the terms instance search returns, and binder and argument
types of the generated principles. SW-1756 §1 showed that such terms are safe:

- a folded term is convertible to the unfolded one;
- a call exists only for a definition whose body is visible;
- the kernel decides with gluing off.

That argument carries over here. I looked for the one way 1b could differ from stage 1: a
folded read-back that mentions a level its unfolding drops, where that level is bound to a
placeholder (`value::unused()`). There are only two placeholder environments in the changed
files, both in `derive_induct.rs`:

- **`reindex`** (`define_field_size_mem`, line 1772). Now folded, and safe. The kept fields
  are found by `mark` over exactly the terms that are reindexed afterwards: `parts`, from
  `size_of`, now folded, and `elem_ty`, built from the same folded `elem_is`. Evaluating a
  term only reads the slots it mentions, and the re-read can't mention more. So no
  `unused` slot is reached.
- **`move_to`** (line 1253). Left unfolded, rightly. Its slots come from `pred_levels`'
  unfolded mention test, so folding only `move_to` would break that agreement. The new
  comment says so.

**The effects round trips** (`refresh` 1468, `settle_let_lambda` 1592, `comp_app` 3629). The
claim is that folded does the same job because the readers unfold as they go. I checked it
against `decode`, `decode_row_value` and `comp_parts_at`:

- Each of them calls `force` on every value it matches on: the operation type, `Plus`'s
  two arguments, `rowOp`'s argument, the `Effects` value, and the type itself.
- `force` unfolds a `Value::Call` (`needs_forcing` is true for every call). So a call
  anywhere on the path they inspect is seen through.
- The values they keep without forcing go to readers that cope with calls. Label arguments
  go to `agree`, which unifies. The result type `t`, a `CompIn`'s tail and the divergence
  index go to unification or to `div_state`, which forces.

The round trip exists to let something stuck on a since-solved unknown compute. The folded
read-back gets that the same way: `force_solved` replaces a solved unknown at each visit,
call arguments included, and each call is re-made by `eval` with an empty unfolding cache.
So a stale kept unfolding isn't carried over. A call that steps at once is forced, so, for
example, `CompIn Empty t` comes back as `t` and `comp_parts` sees the pure type.

The one difference is that the type now keeps aliases as written. In `let-pure` the result
type is `Grid`, not `List (List Nat)` (§2). Every consumer of that type forces it before
matching, as consumers of user-annotated types already must. `effects` (26 tests) and the
effects driver tests, which the lane ran, cover this path.

**The omega and ring fallbacks** (`omega.rs:3992`, `:4019`, `ring.rs:1279`):

- Each one only decides between going on and an *internal* error, after a first `unify`
  has failed. The proof term is then kernel-checked.
- The folded re-read fixes the same staleness as the unfolded one, by re-making the
  calls. Unification is up to conversion, so it succeeds where the unfolded re-read did.
- The fact props and goals carry no unknowns that the call-against-call shortcut could
  solve differently.

**The interfaces terms:**

- `attempt`'s `Head(k)` arguments keep their value beside the term, and the search
  matches on the value.
- `method_call` and `decide_eq_of` decide on `unfold_folded(found)` and `fields[index]` as
  values; only the term they return is folded.
- `decide_eq` is reached from `decide_unglued` with gluing off. There `quote_folded` is
  `quote`, except for a call kept from glued time, which it writes as the call.
- `scanned` (1388), the one interfaces site that chooses, is untouched.

## 2. The hash moves

- **Prelude:** 37 lines moved, all of them `Std.Parse` (and its tests), `Std.Text.fromListEq`
  and its match helpers, and `Std.Option.someBeqSomeExample`. All of them use `==` at `Char`
  or `Text`, or through `Option`.
- **Examples:** each of the 64 snapshots has a source with `==`, a derived `DecEq` or
  `Ord`, or `Std.Parse`, or depends on one that does. I scripted the check; it flagged four
  without a match, and by hand all four are `test … == …` on `Option Text` or a pair, or a
  derived `%decEq`.
  - A telling detail in `text-block`: `example.lines.head == Some "L68"` moves, while
    `example == "…"` doesn't. A direct `Text` dictionary was already `Text.decEq`. Only a
    composite dictionary (`Option`'s, with `Text`'s inside) used to be read back
    one step unfolded.
- **`let-pure` (`Main.countRolls`):** I dumped the term on the branch and with `main`'s
  `effects.rs`. The only difference, in three places, is the result-type implicit of
  `Effect.bind`, which is now `Main.Grid` (the alias, as declared) instead of
  `List (List Nat)`. That is exactly the intended output.
- **`abort-constant` (`Main.firstIsA`; `Main.main` depends on it):**
  - The only difference is one implicit argument of the `sigCase` in the
    `translate (sigCase sigLeft sigFromNo)` mapping. It is now `NoOp`, where `main` wrote
    `rowOp Empty`. The two are convertible: `rowOp Empty` is `NoOp` in one step.
  - Here folded gives the *more* computed term. I didn't trace which changed site makes
    the value differ: the read-backs themselves treat a stuck `rowOp` application
    alike, so it comes from one of the round trips upstream. Either way the change is
    harmless.
  - The pretty printer hides implicits, so the two terms print the same. The
    difference only shows in the `Debug` dump.

No unexplained move.

## 3. The equality dictionary change

Methods are now written as `Char.decEq x y`, where they used to be its unfolding
`Char.decEqFrom x y (Nat.decEq …)` (`Text` likewise). That change can only break a proof
whose rewrite rule or match names the unfolded form, or relies on finding it as written.

- **Grep:** `decEqFrom` appears only in std's own definitions (`Decidable.sw`, `Char.sw`,
  `Text.sw`, `Float.sw`, `Nat/Arith.sw`). It doesn't appear anywhere in `aoc/` or
  `games/rogue`.
- **Std's own lemmas** about `==` are elaborated by the same code, so both sides of a
  rewrite move together. Today's searches still look in the normal form (D2542's 6a isn't
  merged), and there the two forms are identical.
- **Run:** `stitchwort check --no-cache` on every AoC `Proofs` namespace that touches
  `Char` or `Text` equality: `sameCharEq`, `== '…'`, `== "…"`, `Text.toList`,
  `Char.toNat`. That is 2020 days 2–20, 2021 day 10, 2024 day 4 and 2025 day 6: 27
  `Proofs` namespaces. With their dependencies, 75 namespaces were checked over three runs
  (15 s, 15 s and 24 s). **All passed.**
- **Run:** the roguelike, which uses `DecEq.sound`, `soundFalse` and `refl` on
  `Position`: `Rogue.Proofs` cold (2 s), then the whole project (§4). **Passed.**

## 4. The lane's finding: cached unfoldings

With the lane's temporary instrumentation, an extra read-back inside `quote_folded` moved
twelve `Rogue.Proofs` hashes and grew two `%match3` types about 50×. The instrumentation
was an unfolded read-back of each value, both terms evaluated unglued and compared by
conversion.

**Is it in this change? No; it predates it.** My reading of the code, not reproduced:

- `force_call` (`value.rs:842`) keeps a call's unfolding in its shared `Rc<Unfolding>`
  (`Frame::Unfolded`, line 1521) whether gluing is on or off. `Unfolding::get` checks only
  the metavariable epoch, not the gluing mode.
- So a glued call that is forced with gluing off keeps an unglued unfolding, whose parts
  contain no calls. That happens whenever `decide` evaluates against the context's values
  (`auto.rs:821`), or in the instrumentation's unglued conversion.
- If the folded read-back (`value.rs:2125–2144`) meets that call later and it steps at
  once, it forces the call. It then gets the kept unglued unfolding and writes it out in
  full, not as the calls a glued unfolding would contain. That is one plausible source of
  a 50× motive.
- A second possible source: 39 of the instrumented conversions ran out of the
  declaration's budget. Any site that recovers from `E-RESOURCE` (stage 0c's list) then
  takes another path.
- Either way, the instrumentation perturbed the evaluation history within one declaration.
  This change adds more folded read-back sites, so more places could show such a
  difference, but it doesn't create the mechanism.

**Can the merged code's result depend on cache state? No:**

- Unfoldings are kept per `Value::Call`, and every call is made fresh, with an empty cache.
- No value outlives a declaration. The elaborator's `Caches` and the kernel's `EvalCaches`
  hold no `Value`s, and `glued` resets the declaration state.
- So the output depends only on the declaration's input and the binary, not on whether
  its dependencies were elaborated in this run or loaded from the check cache.

**Run:** the roguelike, branch binary:

1. A cold check into an empty `--cache-dir`.
2. The `Rogue.Proofs` entry deleted, then checked again against warm std and `Rogue`.
3. All three `ns.Rogue*` entries deleted, then checked again against warm std.

The regenerated `Rogue`, `Rogue.Proofs` and `Rogue.Tests` entries were byte-identical to
the cold run's each time.

`a_namespace_checked_alone_has_the_same_hashes` (which the lane ran, and which passed)
covers the example projects the same way.

**Still a risk for later stages:**

- Hashes and term sizes depend on the order of evaluation inside a declaration. Any
  change that adds or removes an unglued force can move them, or blow up a motive, with
  no change in meaning.
- Stage 6b (`match` motives) is the most exposed.
- Possible fixes, for the ticket in the verdict: keep only glued unfoldings, by not
  storing one when gluing is off; or tag the unfolding with the mode.
- Then rerun the lane's instrumentation: if the twelve hashes no longer move, the cause is
  confirmed.

## 5. Left unfolded, or folded, wrongly?

I found none either way.

- **`field_type`** (430): `classify` matches its head. It also becomes a binder type, so
  those binders stay in normal form. That's harmless, and they could be folded at the
  output once the classification reads a separate copy (later, not now).
- **`move_to`**: see §1.
- **The mention tests** (`effects.rs` 619, 3699, 4010, 5118; `derive_induct.rs:632`;
  `scanned`): stage 4.
- **Zonk** (`effects.rs:3986`): stage 4.
- **Message text** (4135, 4142): stage 5.
- **The round trips in `families.rs:702`, `rows.rs:250` and `rewrite.rs:588`**: they feed
  unification or a hypothesis search, so folding them could change what is solved. Left
  for stages 4 and 6a, rightly.
- **`omega`'s `same` sites** (SW-1747 item 1, the GAP): not touched. That's correct for
  this stage; they decide.

The remaining `quote(` calls in the three main files are exactly these. I grepped them.

## Tests run

All with the branch's release binary (built at `861f426d2`, no uncommitted changes):

- `stitchwort check --no-cache` on:
  - 2020 days 17 and 19 `Proofs` (8 namespaces, 15 s);
  - days 2–11 `Proofs` (32 namespaces, 15 s);
  - days 12–16, 18 and 20, 2021 day 10, 2024 day 4 and 2025 day 6 `Proofs` (35
    namespaces, 24 s).

  All passed.
- `Rogue.Proofs` cold (2 s), then the whole roguelike three ways against one cache
  directory (about 4 s each). Passed, and the entries were byte-identical (§4).
- The term dumps in §2, from a temporary ignored test (`cargo test --release -p
  stitchwort-driver`, about 30 s a build), on the branch and with `main`'s `effects.rs`.
  Removed afterwards.

Not run: whole AoC, the merge tier, `hash_stability` (the lane ran it, 9/9).
