# SW-3101: Bool as proposition stage 4, measure for D3549

Measured on `main` at `448f3cb8c` (13 Nov 2026), read-only, by grep, a small
classifier script, and reading the code around sites. Labels: **[measured]** =
enumerated by grep/script over every site; **[judged]** = I read the site and
decided; **[extrapolated]** = from a sample of N sites, stated.
Scope: `crates/elab/src/std`, `aoc/src`, `games/rogue/src`, `examples/accept`.

## 0. Headlines

- `.read` uses: **358** in std (145) + aoc (213), 0 in games/rogue, plus 54 in
  `examples/accept` (tests of `.read` itself; kept apart). [measured, noise such as
  `reader.read` and comments removed]
- Where §7's restricted silent crossing could have inserted it (wanted type's
  head known and not `=`, not a rewrite rule / untyped let / omega hint /
  function head): **about 45 of 358 (12 to 13 %)**, range 39 to 51.
  [every non-obvious site read: 142 candidates in std+aoc, judged one by one;
  the rest excluded by position by script, spot-checked on a 60-site sample]
  The review's estimate was "at most half of 585 `.read`s" (~290).
  About **three quarters of all `.read`s (~265) sit where no silent crossing
  could ever remove them** (rewrite rules, untyped lets, omega hints, function
  position, or a wanted `=`).
- Conversion helpers still used: **414 uses** of the 25 named helpers (plus
  `Set.memToList` 19), down from the ~1,200 in §8.4. Classified by why they
  stayed [judged on ~60 sampled sites, then extrapolated per helper]:
  (a) known reader gap about 95; (b) needs building from a proof about 85;
  (c) needs silent crossing about 50; (d) other, mostly **not swept yet or kept
  as style, where `.read`/`Both`/`h.left` work today**, about 205.
- Risk sites (§7): test facts used as equations (`rewrite same in`,
  `Eq.sym same`, `let`, `trueNotFalse`) about **390**. Under the *restricted*
  form none changes meaning, since the wanted head is `=` or unknown there.
  The real exposure is not in `.sw` code but in the elaborator's mismatch hook
  ordering (section 4).
- Recommendation: **build half: yes, later and narrowly. `.read`-insertion
  half: no (keep D3488's deferral).** Details in section 5.

## 1. `.read` uses [measured unless stated]

Raw `grep -Eo '\.read\b'`: std 152, aoc/src 250, examples 58, rogue 0.
After dropping comments and non-fact `.read` (`reader.read`, `afterLengthType.read`,
`Sized.read` in `dot-notation.sw`, Day 16 / BitReader): std 145, aoc 213 = 358;
examples 54.

Position of each site in std+aoc (script, regex on the line; ±10 %):

| Position | Sites | Crossable? |
|---|---|---|
| directly a rewrite rule (`rewrite x.read in`, `<- x.read`) | 110 | no: no expected type |
| applied, `h.read x m` (fact in function position) | 42 | no |
| untyped `let a := h.read` | 33 | no |
| `omega [h.read]` hint | 17 | no |
| typed `let` | 13 | 4 yes (`let ne: a ≠ b := same.read`), 9 wanted `=` |
| argument / constructor field / body | 143 | see below |

Of the 143 arguments and bodies (all read by hand [judged]):

| Wanted type | Sites | Restricted crossing applies? |
|---|---|---|
| head `=`, reading is an equation (`Eq.trans x.read`, `Inl e.read` for `a = b ∨ …`, lemma param `n = t * d`) | ~60 | **no, excluded by §7** (and the fact fits as an equation already; this is §7's first risk) |
| `≠` where the fact is `(a == b) = False`: lemma param `other ≠ key` | 20 | **yes**, the "`e = False` against `¬(e = True)` first" form |
| `∈`, `∉`, `Distinct`, `Equiv`, `¬∈`, `∧` of those: `missing found.read`, `Both above.read below.read` | 15 | **yes** |
| uncertain: wanted type not seen to be known at that point (implicit params, `J` motives, `rewrite … in x.read`) | 12 | maybe (counted half) |
| unclear reading or `.read.read`, tuples, wanted `=` for other reasons | ~35 | no |
| other typed `let` with `≠` | 4 | yes |

So 20 + 15 + 4 = **39 firm**, 12 uncertain, **~45 central** [judged]. The sample
check agrees: in my first 60-site systematic sample (every 7th line) 6 of the 53
real sites were crossable (11 %), which extrapolates to 41 of 358.

Examples:

- `≠` argument: `std/Graph/Search.sw:230,240,250,335,660`, `std/Map/Map.sw:684,693,741`,
  `std/Set/Spec.sw:179,273,784,791,810`,
  `aoc/.../Year2024/Day06/Proofs/Sightlines.sw:31,32`, `Loops.sw:33` (all
  `… other same.read` into `Map.getInsertOther`, `Set.containsInsertOther`, … with
  param `ne: other ≠ key`).
- typed `≠` let: `std/List/Lemmas.sw:1735,1782,1793`, `std/Set/Spec.sw:816`.
- membership: `std/List/Toolkit.sw:645` (`out c.read`), `std/Set/Spec.sw:454`
  (`Both inA outB.read`), `Year2020/Day05/Proofs/Proofs.sw:105,113`,
  `Year2024/Day24/Proofs/Complete.sw:130`, `Year2021/Day12/Proofs/Neighbours.sw:91,101`
  (inside `rewrite lookupBuilt … named.read`), `std/Map/Spec.sw:1967` (body `h.read`
  for `Map.Raw.Equiv`).
- excluded for `=` head: `std/Nat/Divides.sw:34,39`, `std/Float/Theory.sw:82,1350`,
  `Year2024/Day12/Proofs/Steps.sw:23-26`, `Year2021/Day12/Proofs/Neighbours.sw:78-82`.

`examples/accept` (54 uses): about 25 are `theorem t (h: e = True): P := h.read`
with a non-`=` `P`. They are the feature's own demonstrations and are the
positions a silent crossing would make `.read`-free; they would have to keep
`.read` as the documented spelling.

## 2. Conversion helpers still used [measured counts; classification judged]

Counts exclude comments and the helper's own declaration. `std`/`aoc`/`rogue` split.
Where the sweeps went: SW-3060 std; SW-3079 AoC 2020-21 days 1,5,6,9,10,12,16,19,20,21
and 5,8,9,11,12,14,15,16,17; SW-3092 AoC 2024 days 2,4-8,10-17,22-24 and 2025 days
2,4,7,8,9. **Not swept at all: `aoc/src/Aoc/Common` (60 uses), `games/rogue` (8), and the 2020/2024 days
outside those lists.** SW-3067's Nat/Int readings (`leqFalse`) arrived after
SW-3060, so std was not re-swept for them.

| Helper | Uses (std / aoc / rogue) | Main reason it stayed |
|---|---|---|
| `DecEq.sound` | 71 (9/60/2) | (d) not swept (Common 15, 2020/2024 leftovers); a few foundational (`Decidable.sw`, can't use a reading it proves); 1 of 15 sampled (a), tuple `==` (`Graph/Search.sw:611`) |
| `DecEq.soundFalse` | 16 (6/8/2) | (d) plus (a)/(c): `Search.sw:614` tuple `==` as a `≠` argument |
| `Nat.equalSound` | 10 (9/0/1) | (d): `core/Char.sw:44`, `core/Equality.sw:94` are the reading's own proof (foundation); `Float/Theory.sw:230` wanted `=` |
| `Bool.andLeft` / `andRight` | 79 / 79 (22+20 std, 15+17 Common) | sampled 16: (d) 11 (`let inside := Bool.andLeft safe`, `Day10 Proofs:134`, Common: `h.left`/`Both` works now), (a) 4 (`Parse/Runs.sw:1061` cons-unfolded `all`; `Day23 Part1:102` with `Set.containsFromListIff`), (c) 1 |
| `Bool.andIntro` | 25 (2/23/0) | `Both x y` builds against a known `= True` already; remaining are (d) inside `Eq.trans`/unannotated, and ~2 of 5 (b) |
| `Bool.orElim` | 10 | (d): applied to a proof built by `Eq.trans`; a `match … | Inl` on the expression would do |
| `Bool.orLeft`/`orRight` | 4 / 4 (Common) | (b): build `(a || b) = True` from a proof, `Common/Proofs/Grid.sw:37` |
| `Bool.notTrue`, `orFalseLeft`/`Right` | 4, 5, 4 | (b): build `= False` / `¬` from parts |
| `Bool.falseOfNotTrue` | 34 (20/14/0) | (b): builds `e = False` from a `¬(e = True)` proof: `Float/Float.sw:164,468,482`, `Year2024/Day15/Proofs/Part2.sw:230`, `Day24 Complete.sw:64`, `Nat/Arith.sw:110,112` (6 of 7 sampled) |
| `Nat.leqFalse` | 36 (36/0/0) | (c): `Nat.lessLe n m (Nat.leqFalse m n h)`, `SortLemmas.sw:8`, `Arith.sw:292,571`, `Omega/Sound.sw:216,301`, `List/Grid.sw:150`: wanted `<` known, fact `leq m n = False`. 6 of 7 sampled. Also (d): `.read` is shorter and works today wherever the argument is a named fact |
| `Bool.notOfFalse` | 1 | (b) |
| `List.memContains` (`.forward`/`.backward`) | 33 (8/25/0) | 85 % `.backward`: (b), building the test fact from `x ∈ xs` (`Year2024/Day12/Proofs/Fences.sw:28`, `Regions.sw:106`, `Year2020/Day14/Proofs/Decode.sw:90`, `Year2021/Day12/Proofs/Rules.sw:79`); `.forward` (c): `List/Toolkit.sw:417` |
| `List.anyTrueElim` / `anyOfMem` | 8 / 6 | (d) foundation (`List/Toolkit.sw:325` is the reading's own proof) and (b) for `anyOfMem` |
| `List.allMember` | 2 | (d) |
| `List.allToAll` / `allOfAll` | 8 / 8 | (d): `List.All p xs` is a different statement from the reading `∀ x ∈ xs, p x = True`, e.g. `Parse/Reads.sw:1577`, `Common/Proofs/GridParse.sw:36`; goes if `List.All` is defined as the reading |
| `DecEq.trueOfNe` | 3 | (b): builds `(a != b) = True` from `≠`, `Year2020/Day09/Proofs/Window.sw:16` |
| `Set.containsFromListIff` | 26 (3/23/0) | (a): `Set.contains` has no reading, 5 of 5 sampled |
| `Set.memToList` | 19 (6/13/0) | (a): same gap (not a reading, §8.4) |
| `Set.isSubsetIntro`/`Elim` | 2 / 1 | (b) |

Totals [extrapolated, from 60 sampled sites + helper-level judgement, ±25 %]:
(a) ~95, (b) ~85, (c) ~50, (d) ~205, of ~433 (414 + 19 `memToList`).
Not in this design and still large: `Bool.falseNotTrue` 159, `Bool.trueNotFalse` 74
(`Void.exfalso (Bool.falseNotTrue h)`).

## 3. What D3549's halves would each remove

- **Silent `.read` (c)**: ~50 helper uses (mainly `Nat.leqFalse`, 36, which a plain
  `h.read` already shortens today) plus the ~45 `.read` calls of section 1. About
  **95 words** of source across the whole tree.
- **Building (b)**: ~85 helper uses (`falseOfNotTrue` 34, `memContains.backward` ~28,
  `orLeft/orRight/andIntro/orFalse*/notTrue` ~20, `trueOfNe` 3). Not `.read`s: it
  removes `.backward`/`falseOfNotTrue` wrappers where the wanted type is a test fact.
- **Gaps (a)** ~95 go when readings for `Set.contains`, list/Option/record `==` and
  tuple `==`, and cons-unfolded `all`/`any` land, with no D3549 decision.
- **Sweep (d)** ~205 go with a sweep of Common, rogue and the 2020/2024 leftovers
  and std's Nat readings. That is the largest and cheapest win, and independent of D3549.

## 4. §7's risks, by real sites [measured by script, rough]

Test facts used as an equation, near their binding (`match x: e` or `(h: e = True)`):

| Use | Sites |
|---|---|
| `rewrite x in …` / `<- x` / `, x` with the fact as a rule | ~229 |
| `Eq.sym` / `Eq.trans` / `Eq.cong` with the fact | ~81 |
| `Bool.trueNotFalse (… x …)` | ~78 |
| `let a := x` alias | 3 |
| total | ~390 |

Examples: `std/Nat/Bits.sw:175` (`rewrite some in`, with `some: Nat.leq (m+n) 0 = False`),
`std/Fin/Fin.sw:127`, `std/Nat/Divides.sw:104`, `std/Nat/Arith.sw:376`.
Reading: these are all the intended use (rewriting `e` to `True` or `False`, or
`J` on a Bool equation). In the restricted form the wanted head here is `=` or
unknown, so **none of the 390 changes**. Where the restricted form does act (the
45), the fact could not have been an equation there, so no checking program
changes meaning either; the cases are errors today.

What I could not measure from `.sw`:
- the try-and-fall-back paths (`if c`, `&&` with nothing expected, comparison
  sections) live in the Rust elaborator. A hook would go in `check.rs::compare`
  (`crates/elab/src/check.rs:6063`), which already tries an effect coercion after
  `unifies_with_instances` fails and before postponement, so a head not yet forced
  would be left to the postponed path, as the note asks. Counting the
  elaborator's callers that rely on a failing `compare` would need an audit of
  `compare` and its callers (not a grep).
- elaboration-order sensitivity: of the 45 sites, the 12 uncertain ones are the
  ones that might hit it (implicit parameters unresolved, `rewrite … in x.read`).
  About 5 of 12 look order-sensitive on reading. That is a risk for the firm 39
  only if lemma applications can have metas in the parameter's head; `Map.getInsertOther … other same.read m`
  has them all explicit.

## 5. Recommendation

**(1) Building facts from proofs (accept a proof of the proposition where the test
fact is expected): worth doing, as a narrow later stage.**
- Removes ~85 helper uses, mainly `falseOfNotTrue` (34) and `.backward` of
  `memContains` (~28), and makes the `Witness`/`Both` building of §6.6 work for
  a bare variable proof, not just constructors.
- Risk is small: the wanted type is a literal `e = True`/`e = False` (only
  where `e` has a reading) and the found type is a proposition; today that is a
  type error, so no checking program changes. Deterministic: the reading is picked
  by `e`, the proof is checked against the reading's statement, wrapped in
  `r.backward`. A found type headed `=` (e.g. `x = y` where `(x == y) = True` is
  wanted) is the one ambiguity: it is meant, and is not a fall-back path anywhere.
- Cost: `E-NO-READING` wording for the leaf case, a note on mismatches, and one
  more place in `compare`. Do it after the (a) gaps, so the readings it needs exist.

**(2) Silent `.read` insertion: no. Keep the D3488 deferral.**
- It would remove ~45 `.read`s and ~50 helper uses, about 95 words of source. Three
  quarters of `.read`s are in positions it can never reach (rewrite rules, untyped
  lets, omega hints, function position, a wanted `=`); so `.read` stays the
  everyday word either way, and the guide would still have to teach it.
- Over half of what it would fix is `Nat.leqFalse` (36), `h.read` is already one
  word shorter than that and works now. The `≠` argument group (20) and the typed
  `≠` lets (4) are the only places it would be a pleasant gain, and "e = False
  against ¬(e = True) first" covers exactly those: if anything is done, do only this
  slice, as a hint on the mismatch error (a note "write `same.read`", as stage 3 did)
  instead of an insertion.
- Risk: the fall-back paths and elaboration-order dependence are real and not
  measurable here; the gain is too small to pay for an audit of `compare`'s callers.

**(3) Before either**: the biggest effect is not a language change.
- Sweep `aoc/src/Aoc/Common` (60), `games/rogue` (8), 2020/2024 leftovers, std's
  `Nat.leqFalse` (36), `Parse`/`Omega`/`Float` (~70): about 200 helper uses go with
  `.read`, `h.left` and `Both` today.
- Close the (a) gaps (~95): `Set.contains` reading, tuple and list/Option/record `==`,
  cons-unfolded `all`, and `List.All` as the reading (`allToAll`/`allOfAll`, 18).

## 6. Findings worth filing

1. Sweep the unswept areas (Common, rogue, 2020/2024 leftovers, std `Nat.leqFalse`,
   `Parse`/`Omega`/`Float`): ~200 helper uses, Sonnet, no language work.
2. `List.All` versus the reading of `all`: define `List.All p xs` as the reading's `∀`
   (or have the reader target it) so `allToAll`/`allOfAll` (18 uses) go.
3. Reading for `Set.contains` (and so `containsFromListIff` 26, `memToList` 19):
   45 uses, the largest (a) block.
4. Tuple `==` reading (`Graph/Search.sw:611,614`).
5. Optional: a mismatch note for `e = False` where `¬(e = True)` or `a ≠ b` is wanted
   ("write `same.read`"), the 24 `≠` sites.

## Method notes

- `.read` positions: `/…/scratchpad/cls.py` (regex per line, binder found by `match x:`
  or `(x: …)` up to 80 lines back); output in `cls.json`, candidate list in `cand.txt`.
- Helper counts: `helperuses.txt` (414 lines: file:line:text) from `area.sh`.
- Risk counts: `risk.py`. They count uses near the binding (60 lines) and include some
  non-test equations bound by `(h: P = True)`, so they over-count by an unknown
  few percent.
- The classification in section 2 is judged on about 60 sampled helper sites, not
  all 414; the per-helper split is an extrapolation and will move by ±25 %.
