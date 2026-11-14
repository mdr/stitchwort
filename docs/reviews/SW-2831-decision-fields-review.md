# SW-2831 review: proof terms use the decision's fields

Opus paper review (D2364: the change generates kernel terms) of `lane/SW-2831`,
commit 69d0f9df9. Read-only: nothing was built or run. Background:
`docs/proposals/decidable-record.md` §5.2.

**Verdict: merge.** No must-fix. One should-fix (a stale sentence in
`docs/syntax.md`), and one merge condition: the lane couldn't check its 12
`aoc/` edits, so the verifier's batch has to include an `aoc/` check.

## The record

`crates/elab/src/std/core/Decidable.sw:20-24`: `{ holds, sound, complete }`,
so with `Term::Proj`'s 0-based field index (`crates/core/src/term.rs:207-213`)
`holds` is 0, `sound: holds = True → p` is 1 and `complete: p → holds = True`
is 2. This matches what's already in use: `carry.rs:54` (`Proj(decidable, 1, d)`
for `sound`) and `cases.rs:1877` / `matching.rs:2157` (`Proj(decidable, 0, _)`
for `holds`). `Decidable.refute [p] (d) (e: d.holds = False): ¬p`
(`core/Decidable.sw:30-31`) has the same parameters, in the same order and
with the same implicitness, as the deleted `toBoolFalse: ∀ [p] (d) => holds d = False → ¬p`.

## (1) Field index, type, argument order, same `d`: OK

| Site | Old | New | Check |
|---|---|---|---|
| `omega.rs:1082-1084` (`prove_goal`, goal `holds d = True`) | `toBoolOf [p] d proof` | `Proj(Decidable, 2, d) proof` | `proof: p` (proved by `prove_goal` on `p`); field 2 is `p → holds = True`. OK |
| `omega.rs:1617-1619` (reader, fact `holds d = True`) | `toBoolSound [p] d proof` | `Proj(Decidable, 1, d) proof`, read as `p` | field 1 is `holds = True → p`; the type passed to `read` is the same `p` the old `lemma` returned (its codomain was `p`). OK |
| `omega.rs:1621-1623` (reader, fact `holds d = False`) | `lemma(toBoolFalse, [p, d, proof])` | `lemma(refute, [p, d, proof])` | same Pi shape, so `lemma`'s walk and the returned `¬p` are unchanged; the `notNotOf` follow-up for `!=` still sees `¬p`. OK |
| `equations.rs:1321-1338` `to_bool_lemma` | `lemmas[which] [p] d h` | 0 → `Proj 2 d h`, 1 → `toBoolOfNot [p] d h`, 2 → `Proj 1 d h`, 3 → `refute [p] d h` | 0 was `toBoolOf` (complete), 2 was `toBoolSound` (sound): indices match. Callers (`equations.rs:7199`, `7234-7236`, `7279`; `induct.rs:2236`, `2262`) are unchanged and pass the same `which`. OK |
| `omega.rs:983-988` `decision_field` | | `Proj(lib.decidable, k, quote_folded(d))` | `d` is the `BoolForm::ToBool` value, quoted with `quote_folded`, the same call `both()` used for the old lemma's argument. Not re-elaborated. OK |

The decision `d` in every site is the one the old lemma received: in omega
it's the `ToBool(p, d)` from `bool_form` (`omega.rs:888-917`: a `holds` call's
argument, `Nat.decEq x y` for `Nat.equal`, or the `Int.decEq x y` head of a
`… .0` spine); in `equations.rs` it's `Decided::One`'s `d` or, for a
conjunction, the `Decidable.and` built by `conjunction_decision`, both as
before.

What changes in the term: the old lemma took `p` explicitly (as an implicit
argument) and the kernel checked `d : Decidable p`; a projection infers `p`
from `d`'s type. Where `p` (from `bool_form`, or `Decided::prop`) and `d`'s
inferred proposition differ syntactically, the kernel now meets the
difference at the use site (`proof: p` against the field's domain, or the
stated equation against the field's codomain) by conversion, not inside the
lemma's argument check. Either way they must be convertible, so nothing that
checked before can fail now on that account. Likewise `holds d` in the goals is
`Def(Holds) d` while the fields' types mention `Proj 0 d`: the deleted lemmas'
bodies (`toBoolOf … := d.complete x`) needed the same delta step, now taken at
each use. Cost is one unfold per use; not worth measuring.

`Term::Proj` needs the type to have eta (`term.rs:207-209`); `Decidable` does
(`carry.rs` and `cases.rs` already emit and match projections of it).

## (2) `refute` for `toBoolFalse`: OK

- omega (`omega.rs:1621`) and `equations.rs`'s `which == 3`: same signature,
  see above.
- `std/List/ByKey.sw:32` `Decidable.refute (List.decMem z zs)`: partial
  application, same type `holds = False → ¬(z ∈ zs)`. OK
- `aoc/…/2025/Day07/Proofs/Distinct.sw:19`: `refute (DecEq.decide Left Right) rfl (…)`:
  same three arguments. OK
- `aoc/…/2021/Day09/Proofs/Part2.sw:105` `Decidable.refute _ closed other`:
  same statement (`closed: (height != 9) = False` gives `¬¬(height = 9)`,
  applied to `other: ¬(height = 9)`). It keeps the `_`, which now has to be
  solved against `refute`'s `d.holds` rather than `toBoolFalse`'s
  `Decidable.holds d`; see the merge condition below. NOTE

## (3) Coverage, silent degradation: OK

- `BranchLib::to_bool_lemmas` is `Some` when `Decidable` (core),
  `Std.Decidable.toBoolOfNot` and `Std.Decidable.refute` (core) resolve
  (`equations.rs:4507-4513`). Before, it needed the four `toBool*` lemmas, all
  in `std/Decidable/Decidable.sw`, where `toBoolOfNot` still is: so it is
  `Some` in exactly the same situations. The gates that depend on it (guards
  stated as the proposition at `equations.rs:2589`, conjunction guards at
  `:1259`) see no change, so no guarded equation silently falls back to its
  `Bool` statement.
- `GUARD_LEMMAS` (`module.rs:2924`) still loads `toBoolOfNot`; `refute` is
  core and always loaded, listing it is harmless.
- omega's `Lib::new` (`omega.rs:660-672`) needs `refute` and `toBoolOfNot`,
  the same file as before plus core; `LIBRARY` (`:142-146`) drops the three
  names. No omega path gives up where it used to prove.
- No path in `crates/` names a deleted lemma (`git grep` over 69d0f9df9,
  snapshots excluded). Only prose does; see (5).
- The snapshot diffs are hash lines only; no equation statement code was
  touched (the `equations.rs` diff is confined to `to_bool_lemma` and the
  `BranchLib` field), so moved hashes are proof terms and their dependants.
  E.g. `omega-bool-ne`: the `Int` cases (which go through `ToBool`) moved, the
  `Nat` ones (through `Bool.not`/`Nat.equal`) didn't, as expected.

## (4) The four `_` call sites in `aoc/`: OK, same statements

None changes a theorem's statement: each is a proof term, inside an unchanged
signature or a `let` with an unchanged type annotation.

- `aoc/src/Aoc/Common/Proofs/Grid.sw:134`: `toBoolSound _ (Bool.andLeft differ)`
  of `(directionIndex other != directionIndex direction) = True` gave
  `¬(… = …)`; `DecEq.neTrue` (`std/Decidable/Decidable.sw:33-34`) takes
  `((x != y): Bool) = True` to `x ≠ y`, the same. OK
- `aoc/src/Aoc/Year2021/Day09/Proofs/Part2.sw:108` `notNineOfOpen`: statement
  unchanged, `(height != 9) = True → height ≠ 9`; `DecEq.neTrue open` is exactly
  that. OK
- `aoc/src/Aoc/Year2024/Day08/Proofs/Part2.sw:165`: `DecEq.neTrue (Bool.andRight same)`,
  the same `≠` fact `harmonicsCorrect` took before. OK
- `aoc/src/Aoc/Year2020/Day09/Proofs/Window.sw:19`: the `let`'s type
  `((a + a != number): Bool) = True` is unchanged; the proof names the decision
  `Decidable.not (DecEq.decide (a + a) number)`, which is what `!=` elaborates
  to (the `DecEq` instance on `Nat`), and `.complete` takes `¬(a + a = number)`
  to it. If `!=` on `Nat` elaborated to a different but convertible decision
  the annotation would still check by conversion. OK

All four rely on `DecEq.neTrue`'s implicit `x`, `y` being solved from `h`'s
type, which the existing `notNineOfOpen`-style uses elsewhere already do.

**Merge condition (NOTE).** The lane may not run `aoc/` checks, and its report
lists pins and snapshots (std, examples) only. The 12 `aoc/` edits, the
`_` kept at 2021 Day09 `Part2.sw:105` in particular, have not been elaborated by
anyone. The verifier for the batch that takes SW-2831 should include an
`aoc/` check (cached is enough: the edited files are rechecked); a failure would
be local and easy to fix (name the decision, as at `Window.sw:19`).

## (5) Other

- **SHOULD-FIX: `docs/syntax.md:1956`** still says "`Decidable.toBoolSound`
  and `toBoolOf` are the same as theorems". They no longer exist; drop the
  clause (the sentence before it already names `d.sound` and `d.complete`) or
  point at `Decidable.refute` for the `False` direction.
- NOTE: `docs/proposals/omega.md:307,314` and
  `docs/proposals/pattern-guards.md:409-410` describe the generated terms with
  the old names. Proposals are records of a design, so leaving them is fine;
  a one-line "(now `d.sound`/`d.complete`/`refute`, SW-2831)" would save a
  reader a search. `aoc/NOTES-*.md` and `docs/aoc-2025.md:1074` are history:
  leave them.
- NOTE: `Decidable.toBoolOfNot` is the one bridge lemma left. Its name now
  stands alone among `d.sound`, `d.complete` and `Decidable.refute`; a
  name in the same family (e.g. `Decidable.holdsFalse`, the converse of
  `refute`) would read better. That's a user-visible name, so it's Matt's call
  and a separate ticket, not this one.
- OK: `std/List/Lemmas.sw:3036-3037`: doc comment updated to name the fields.
  `std/Decidable/Decidable.sw:1-6`: header and `toBoolOfNot`'s new doc are
  accurate.
- OK: the std and example call sites (Fin, ByKey, SortLemmas, Map/Spec,
  Nat/Divides, Text, quot-library, trip-journal) are one-for-one:
  `toBoolSound d h` to `d.sound h` and `toBoolOf d x` to `d.complete x`, with
  the same `d` written out. Elaborated by the lane through the prelude and
  example snapshots.
