# Record eta: the remaining stages after stage 1b

**SW-1849**, 7 November 2026. Design only: nothing was built or run. A
companion to [record-eta.md](record-eta.md), whose design (D2498 to D2505,
D2509 to D2511, D2551) it keeps. It says what stages 1 and 1b deliver, plans
the stages left, with a brief for each that can be pasted, lists the
workarounds the sweep removes, and says how the stages fit with the bounded
read-back plan ([bounded-readback-remaining.md](bounded-readback-remaining.md),
SW-1828). Its questions are D2630 to D2634 (§6).

Written against `main` at `437852b04`, after the merge of record eta
(`319c28c0c`) and before SW-1829 (the whole-AoC slowdown after that merge)
has an answer. Line numbers are that commit's. Labels: **[checked]** (read
in the code here), **[cited]** (from the ticket or review named),
**[inferred]** (my reasoning).

## Contents

1. Where things stand
2. The remaining stages
3. The sweep: what eta makes unnecessary
4. Order against the bounded read-back stages
5. Briefs
6. Questions for Matt
7. What this note did not do

## 1. Where things stand

### 1.1 What users get today (stages 1 and 1b, merged 7 Nov)

For a type **declared as a record** (`type Position = { row: Nat, column:
Nat }`), with one constructor, not recursive, in `Type`, and with at least
one field that isn't a proof (`qualifies_for_eta`, `core/src/check.rs:2255`;
D1981, D2509):

- **A record equals the record built from its own fields, by `rfl`.**
  `theorem positionEta (p: Position): p = { row = p.row, column = p.column
  } := rfl` checks (rule 1, in the kernel and the unifier). It failed with
  `E-REFL` before. **[checked: SW-1764's probes]**
- **A function that matches a record computes on an unknown record.** With
  `down` defined by `| { row, column } => { row = row + 1, column }`,
  `(down p).column = p.column := rfl` checks (rule 2). This is the commoner
  case in the friction notes. **[cited: SW-1764 §1]**
- **The unifier fills holes through fields.** `{ row = ?r, column = ?c }`
  against `p` solves `?r := p.row` and `?c := p.column`
  (`unify.rs:1632-1665`). The rule waits on a value stuck on an unsolved
  unknown, and is off inside `first_order` (`NO_ETA`, `unify.rs:2030`), as
  record-eta.md §8 asked. Two fields of the same name on two records are
  compared by their records first (`same_field_records`, `unify.rs:1683`;
  D2511). **[checked]**
- **What doesn't change:** proof-only records, records with no fields,
  recursive records, interface dictionaries (the hashed `no_eta` mark,
  kept by the check cache since SW-1768), propositions. A definition with a
  native implementation keeps its record patterns stuck on unknowns
  (`eta_held`, `core/src/value.rs:1958`; today only `Float.add`, pinned by
  `only_float_add_is_held`). Field access `p.row` is still a call of the
  accessor, which rule 2 opens to `Proj(Position, 0, p)` (record-eta.md
  §6.4, D2566 open). A field of a glued call stays a call, `(f x).i`
  (stage 1b). **[checked]**
- **One proof** was rewritten: 2021 day 13's `rewrite Point.ext … in rfl`
  is `rfl`. **[checked: the merge's diff touches no other `.sw` file
  outside `examples/`]**

### 1.2 What isn't done

| Item | Planned as | State |
|---|---|---|
| Unifier eta (record-eta.md §8) | stage 2, SW-1643 | **Mostly built in stage 1**: metavariables first, not against blocked values, off in `first_order`, proof fields through the proof task, plus D2511's same-field rule. What's missing is the elaborator-level tests records.md §7.3 and §14 asked for (a metavariable of unknown type against a record literal, before and after its type is solved; `Person` and `Pet` through the elaborator; an ill-typed comparison giving no accepted solution) and any surface example. **[checked: no `examples/accept/*eta*`, no unifier test names eta]** |
| Docs | stage 4 | **Owed since stage 1.** The guide and `docs/syntax.md` don't say that a record equals its fields' record by `rfl`, or that a match on an unknown record computes (CLAUDE.md: a user-visible feature updates both). `syntax.md:476` (`T.ext`) still reads as the only way. **[checked]** |
| `Pair`, and eta by shape | stage 3, SW-1644 | Not started. D2509 held eta to declared records "until stage 3", which departs from D2499 (eta by shape). |
| The sweep | stage 4, SW-1645 | Not started. **The records part doesn't need stage 3**: every hand-written eta lemma found (§3) is about a declared record, so it is already `rfl` on `main`. |
| D2566's measurement (accessor openings) | stage 3 | Not started. |
| The cost of rule 2 | SW-1762, bounded read-back 4c and 6b | `Rogue.Proofs` +28%, nearly all `resolveOutOfWalls` (proof term 4.6k → 106k nodes), read back unfolded through `match`'s motive. Measured again in 4c and 6b. **[cited]** |
| The whole-AoC slowdown | SW-1829 | Open: whole AoC no-cache, about 69 s before the merge, didn't finish in 6 minutes after it. Nothing below should start until it has an answer; if it reverts the merge (D2586), these stages start again from the branch, unchanged. |
| SW-1755 (`x + y` on unknown floats shows as written; trip-journal as a check) | — | **Probably done by SW-1667**: `examples/reject/float-sum-stays-a-sum.sw` pins the sum shown as a call, and `the_trip_journal_checks` runs in every tier. The orchestrator can confirm and close it. **[inferred from the merge's file list]** |

## 2. The remaining stages

In order. Each is one lane. The models follow CLAUDE.md: the kernel and the
unifier are core language (Opus, D2506); the sweep is proof clean-up
(Sonnet).

### Stage 2′: unifier tests, examples and docs (Opus, 60 min)

*Replaces SW-1643's scope (D2630).*

- **For users:** nothing newly checks: it pins down what stage 1 built, and
  tells people about it. The guide's proofs chapter shows `p = { row =
  p.row, column = p.column } := rfl` and a function on an unknown record
  computing; `docs/syntax.md`'s records section says so, and its `T.ext`
  entry says when `T.ext` is still needed (field equalities that aren't
  `rfl`).
- **Code areas:** `crates/elab/src/unify.rs` tests; `examples/accept/`,
  `examples/reject/`; `docs/guide/10-proofs.md` (or `03-data.md`'s records
  part) with a checked example; `docs/syntax.md` Records. No change to the
  rules unless a test finds a bug, in which case the lane stops and reports.
- **Must accept:** `positionEta := rfl`; `(down p).column = p.column :=
  rfl`; an implicit record argument solved through a literal (`{ row = ?r,
  column = ?c }` against `p`); a metavariable of unknown type against a
  record literal, where the type is solved later; `Box (List Nat)`'s
  `b = { value = b.value }`; a record with a proof field beside a data field
  (`c = { value = c.value, small = h }` for any `h`).
- **Must reject:** `Person` and `Pet` of one layout, through the elaborator
  (`p = asPerson q`), with the message snapshot; a proof-only record
  (`(x y: Small) → x = y`); a recursive record's eta; a `first_order` case
  where rule 1 would have paired a literal with a value of another type (a
  unit test with `NO_ETA` off shows it would accept, so the test is live);
  a unifier problem against a value stuck on an unsolved unknown waits
  rather than splitting into projections.
- **Risks:** none to soundness (tests and docs). The surface examples move
  no hash, but a new example needs `task snap:hashes` and the
  `hash_stability` test.
- **Success:** every test above shown to fail with its rule switched off
  where that's possible; guide examples checked; SW-1643 closes with this
  lane.

### Stage 4a: the record sweep (Sonnet, 60 min)

*Split from SW-1645 (D2631); can run before stage 3.*

- **For users:** none directly; AoC and the roguelike read better, and the
  proofs stop teaching readers a workaround. About 25 hand-written eta
  lemmas and their uses go (§3).
- **Code areas:** `aoc/src/Aoc/**/Proofs/`, `games/rogue/src/Rogue/Proofs/`;
  no Rust.
- **Must accept:** every namespace touched checks with `stitchwort check
  --no-cache` on that namespace, and `task audit:touched` for proof lanes.
- **Must reject:** nothing new; but each removed workaround is a live case
  only if it was needed before: the lane notes which removals were
  impossible before (the friction notes say so for most; it needn't check
  each on an old build).
- **Risks:** a lemma removed that another namespace uses (grep the name
  across `aoc/` and `games/` first); a `rewrite xEta in …` whose rewrite
  also moved something else, so the plain `rfl` fails (keep it, note it);
  goal shapes in messages (snapshots, mechanical). Small conflict risk with
  any AoC lane touching the same days' proof files.
- **Success:** the greps of §3.1 find no hand-written eta lemma for a
  declared record; the record `match`es left in proofs each have a reason
  (names used later, or a readability gain), listed in the ticket.

### Stage 3: eta by shape, `Pair` first (Opus, 180 min, Opus review)

*SW-1644 (D2499 restored; D2632, D2633).*

- **For users:** pairs behave like records. `p = (p.fst, p.snd) := rfl`; a
  function that matches a pair computes on an unknown pair, so `(swap
  p).fst = p.snd := rfl` and `swap (swap p) = p := rfl` (2020 day 1's
  friction: "`Some (b, c)` … writing `| Some (p, q) =>` computes it"); and
  any one-constructor type written with `|`, such as `type Wrapper = | Wrap
  (inner: Nat)`, gets the same.
- **What it gives eta to, beyond `Pair`** (a first list from reading, not
  exhaustive): `Text` (`MkText chars`), `Char` (`MkChar code valid`),
  `Effect.SigMap`, `Omega.Env`, `Omega.Row`, `Ring.Env`, `Ring.Mono`, and
  application types such as 2021 day 10's `FirstIllegal`. Not `And`,
  `Exists`, `Unit` (propositions) or `UnitType` (no fields). The lane's
  first step prints the kernel's own list: a test that names every std type
  that newly has eta, as `only_float_add_is_held` names the held
  definitions, so each one is a decision, not a surprise.
- **Code areas:** `core/src/check.rs` (`qualifies_for_eta` drops `&&
  data.record`); every elaborator place that treats `Pair` specially
  (`derive*.rs`, `dot.rs`, `check.rs`, `effects.rs`, `equations.rs`,
  `missing.rs`: grep `Pair`) and the generated accessors for non-record
  types (`shared.rs:accessors`); `eta_hold.rs` and
  `only_float_add_is_held` (the held set grows if a `Text` or `Char`
  native matches its constructor); hash snapshots; the JS and runtime
  back ends are unchanged (rule 2 is off while running, and `Pair` keeps
  its tag).
- **Must accept:** the `Pair` examples above; nested `((a, b), c)` on an
  unknown computing; `(?a, ?b)` against `p` solving `?a := p.fst`; a
  pattern lambda `((row, pixels)) => …` whose body is a goal about
  `row`; `w = Wrap w.inner := rfl`; `c = MkChar c.code c.valid := rfl`;
  `t = MkText t.chars := rfl`; `'L'` patterns (`MkChar 76 _`) still
  grouping as numbers on an unknown `Char` (`literal-match-facts.sw`).
- **Must reject:** `(p q: (Nat, Bool)) → p = q`; `p = (p.snd, p.fst)` at
  `(Nat, Nat)`; a `Pair` against a one-constructor `Span` of the same
  layout (kernel: `Proj(Span, 0, p)` with `p: Pair Nat Nat` refused); a
  one-constructor recursive type (`| More (head: Nat) (rest: Nat → Stream)`)
  has no eta; a one-constructor type whose only field is a proof; an
  interface dictionary still has none now that the record condition is gone
  (the `dictEta` reject, cold and warm); `?m` against `(?m.fst, x)` fails
  by the occurs check rather than looping (the unifier never expands a
  metavariable into a pair of new ones, record-eta.md §8.1).
- **Measure** (needs Matt's OK, D2633): instructions retired for whole AoC
  and the roguelike, `check --no-cache`, with stage 3 on and off (a
  temporary switch, as the prototype's `SW_NO_ETA`), each in the
  background and stopped at 6 minutes; how often rule 2 fires on `Pair`,
  `Text` and `Char` separately; and, for D2566, how much goes into opening
  accessors on unknowns (a count of accessor openings, and their share of
  instructions).
- **Risks:**
  - *Performance.* Pairs are far commoner than records: 332 uses of `fst`
    and `snd` in 84 AoC files, and every `foldLeft` with a pair
    accumulator. Rule 2 fires on each match of an unknown pair, under
    binders too, and the unfolded read-back sites bounded read-back hasn't
    reached yet expand what it computes (SW-1762's shape). SW-1829 shows
    how far a check can move: whatever its cause, stage 3 must not start
    before it is understood.
  - *`Text` and `Char`.* Rule 2 opens every std function that matches
    `MkText` (75 uses in std) on an unknown text, so goals that showed
    `t.length` could show list functions on `t.chars`, unless the
    function has a native (then the hold keeps it). This is the Float.add
    problem again (SW-1744), wider. If it shows, D2632's fallback applies.
  - *Unifier.* Rule 2 fires on unsolved metavariables (D2511), so a
    `match` on `?p` gives `?p.fst` rather than waiting, and more solutions
    come from `same_field_records`, which is lossy. Elaboration can change
    in many more places than with records. Termination: rule 1 replaces a
    comparison with smaller ones, and the unifier never expands a
    metavariable, so no new loop (Agda's #3597 came from expanding
    metavariables). A test pins the `?m` occurs case.
  - *Hashes and natives.* Terms read back with `Proj` move most hashes
    above a pair (migration cost, doesn't count). A moved std term can
    unbind a native silently: run extract's `bound_to_the_prelude` tests.
  - *Reflective tactics.* `Omega.Env`, `Ring.Env` and `Ring.Mono` get eta,
    so goals inside `omega`'s and `ring`'s reflection lemmas may compute
    further. Run the `omega` and `ring` examples.
- **Success:** the accept and reject tests pass, each shown live; std, the
  roguelike and the examples check; whole AoC within the D2507 limit, and
  its instructions at most 5% above the run with the new types' eta
  switched off (record-eta.md Q7 accepted about 5% for rule 2 on records;
  this is the same allowance again for pairs and the rest, D2633); a report on accessor
  openings that answers D2566's condition.
- **Stop points:** if the whole-AoC instructions rise more than 10%, or any
  namespace takes more than twice as long, stop and report with the per-type
  counts before fixing anything (D2632).

### Stage 4b: the pair sweep (Sonnet, 45 min)

- **For users:** none directly. The pair matches in proofs that exist only
  to compute go (§3.2), and the friction note's "pairs have no eta" lines in
  `aoc/NOTES-2020.md` get a dated "fixed by SW-1644" mark.
- **Code areas, tests, risks:** as 4a, for pair patterns.
- **Success:** each pair match left in a proof has a reason, listed.

### Stage 5 (conditional): accessor bodies as `Proj` (Opus, 60 min)

Only if stage 3's measurement shows accessor openings are a visible share
(D2566's condition). The accessor of an eta type is generated with the body
`Proj(D, i, x)` instead of a `case`, so opening it is one step that doesn't
go through rule 2; use sites stay calls.

- **Must accept:** every probe of record-eta.md §6.4's "what the mixture
  costs" table, again; `rewrite` of `p.row` in both spellings.
- **Risks:** accessor hashes move, and everything above them (migration
  cost). The update lemmas (`T.f.update.g`) and the printer cases that
  recognise accessors must still recognise them.
- **Success:** the measured share falls; nothing else changes.

## 3. The sweep: what eta makes unnecessary

### 3.1 How to find them, by reading

Each grep gives candidates. Every candidate is read, removed, and its
namespace checked; one that still needs the workaround stays, with a
comment only if the reason isn't plain.

1. **Hand-written eta lemmas:** `grep -rnE '[a-zA-Z]+Eta\b' --include='*.sw'
   aoc games crates/elab/src/std`. The lemma's statement becomes `rfl`;
   better, its uses do, and the lemma goes.
2. **`T.ext` with only `rfl` field proofs:** `grep -rnE '\.ext\b'` and read
   the arguments (`Image.ext _ _ rfl`). Those whose field proofs are all
   `rfl` become `rfl`. `T.ext` itself stays (record-eta.md Q6).
3. **Record matches whose arm is `rfl`, or which exist to compute:** `grep
   -rnE '\| *\{ *[a-z][A-Za-z]*(, *[a-z][A-Za-z]*)* *\} *=>'` in proof
   files. A one-arm `match r with | { … } => rfl` becomes `rfl`. A match
   that binds names used later can stay if the names help; if not, use
   `r.field`.
4. **Hand-written ext lemmas that duplicate `T.ext`:** the rogue's
   `positionExt` is proved through `positionEta`; it can be `Position.ext`
   or one `rewrite … in rfl`.
5. **For pairs (4b only):** `grep -rnE '\| *\([a-z_][A-Za-z0-9]*, *[a-z_][A-Za-z0-9]*\) *=>'`
   in proof files, and the `Some (p, q)`-style renamings the 2020 notes
   describe. No hand-written pair eta lemma exists (no `(p.fst, p.snd) =
   p` in the tree).

### 3.2 A first list

**Hand-written eta lemmas (stage 4a; all on declared records):**

| Where | Lemma | Uses |
|---|---|---|
| `games/rogue/src/Rogue/Proofs/Position.sw:15` | `positionEta` | `positionExt` (line 19); `Reach.sw` 114, 119, 134, 140 |
| `aoc/…/Year2024/Day06/Proofs/Part2.sw:91` | `positionEta` | line 98 (`rewrite positionEta position at …`) |
| `aoc/…/Year2025/Day02/Proofs/Templates.sw:127` | `templateEta` | line 147 (`Inl (templateEta template)`) |
| `aoc/…/Year2020/Day02/Proofs/Complete.sw:10` | `entryEta` | 43 |
| `aoc/…/Year2020/Day04/Proofs/Complete.sw:10` | `fieldEta` | 43 |
| `aoc/…/Year2020/Day05/Proofs/Complete.sw:11` | `passEta` | 38 |
| `aoc/…/Year2020/Day07/Proofs/Complete.sw` 14, 18, 22, 136 | `colourEta`, `ruleEta`, `contentEta`, `rulesEta` | 38, 55, 125, 145 |
| `aoc/…/Year2020/Day08/Proofs/Complete.sw` 14, 18 | `instructionEta`, `programEta` | 32, 46 |
| `aoc/…/Year2020/Day09/Proofs/ParseComplete.sw:15` | `dataEta` | 24 |
| `aoc/…/Year2020/Day10/Proofs/Complete.sw:15` | `bagEta` | 24 |
| `aoc/…/Year2020/Day11/Proofs/Complete.sw:57` | `layoutEta` | 76 |
| `aoc/…/Year2020/Day12/Proofs/Complete.sw:32` | `instructionEta` | 40 |
| `aoc/…/Year2020/Day13/Proofs/Complete.sw:46` | `notesEta` | 58 |

Seventeen lemmas, most proved by a one-arm record match. Several uses are
`rewrite …, xEta x in rfl` after a parse lemma (`Fail.toResultThen`), so
the `rewrite` keeps its other steps and only the eta step goes.

**`T.ext` with only `rfl` fields:** `aoc/…/Year2020/Day20/Proofs/Orientations.sw:307`
(`let eta: { rows = image.rows } = image := Image.ext _ _ rfl`). 2021 day
18's `Exploding.ext … (List.appendAssoc …) rfl rfl rfl`
(`Explode.sw:17`) has a field proof that isn't `rfl`, so it stays.

**Record matches in proofs** (39 one-line arms by grep 3; record-eta.md §1
counted 108 record patterns in all, with nested and multi-line ones). The
ones that exist to compute, from reading:

- `aoc/…/Common/Proofs/Offset.sw:55` (`offsetOf`: `match next with | { row,
  column } => rfl`; record-eta.md §11 confirmed it);
- `aoc/…/Year2020/Day17/Proofs/Boot.sw:19` (`startsPocket`: §11 confirmed);
- `aoc/…/Common/Proofs/Bits.sw:22`, `GridParse.sw:66`, `Plane.sw` 202,
  220, 224;
- `aoc/…/Year2020/Day06/Proofs/Complete.sw:29`, `Day12/Proofs/Complete.sw:56`,
  `Day14/Proofs/Complete.sw:63`;
- the arms inside the eta lemmas above (they go with the lemmas).

To read and decide: `Year2024/Day12/Proofs/Sides.sw` 185, 193, 232;
`Year2021/Day12/Proofs/Neighbours.sw` 45, 61, 78 and `Parse.sw:43`;
`Year2020/Day12/Proofs/Parts.sw` 33, 45; `Day14/Proofs/Complete.sw:21`;
`Day04/Proofs/Complete.sw:129`; `Day19/Proofs/ParseComplete.sw` 105, 155.
These bind names the arm uses; they may be there to compute, or for
readability.

**Pair matches in proofs (stage 4b; 15 by grep 5):**
`Year2025/Day08/Proofs/Sizes.sw:72`, `Year2024/Day06/Proofs/Sightlines.sw:83`,
`Year2024/Day16/Proofs/Part2.sw:135`, `Year2021/Day09/Proofs/Facts.sw:17`,
`Year2021/Day09/Proofs/Part1.sw` 24, 39, `Year2021/Day11/Proofs/Parts.sw:76`,
`Common/Proofs/GridAround.sw:39`, `Common/Proofs/GridCells.sw` 244, 287,
318, 323, `Year2020/Day07/Proofs/Part1.sw:89`, `Year2020/Day20/Proofs/Monsters.sw:198`,
`games/rogue/src/Rogue/Proofs/Bounds.sw:107`, and std's
`Parse/Reads.sw:991`. Many are inside `List.memMap`-style eliminations where
the pattern names the parts of a member; those stay unless the names go
unused.

**Docs and notes:** `aoc/NOTES-2020.md` (days 1, 17, 20), `games/rogue/PROOFS.md`
and `docs/research/aoc-2020-friction-days-10-20.md` theme K describe the
missing rule: each gets a dated line saying it's fixed (not rewritten,
since they are records of friction at the time).

## 4. Order against the bounded read-back stages

The bounded read-back plan (SW-1828 §5.1) orders 0c, 1c, R; then 4a, M;
then 4b, 4c, 5, O; then 3, 6a, 6b, 7. Its 4c (zonk) and 6b (`match`
motives) measure SW-1762's `resolveOutOfWalls`. How record eta's stages
fit:

| Record eta stage | Before / after | Why |
|---|---|---|
| **2′** tests and docs | any time after SW-1829 | Touches `unify.rs`'s tests only, and examples and docs. Moderate textual conflict with 4a and 4c (both edit `unify.rs`), so not side by side with them; otherwise free. |
| **4a** record sweep | any time after SW-1829 | `.sw` proofs only. Free of every bounded read-back stage except M (the measured proofs), which may touch the same AoC files; run them apart if they share a day. |
| **3** `Pair` and by shape | **after SW-1829 and bounded read-back 0c**; preferably after 4c; not waiting for 6b | Stage 3 multiplies rule 2's firings, and its cost runs through the unfolded read-back sites that 4a to 6b remove. 0c's metrics show which sites the extra firings reach, and are the baseline stage 3 measures against. 4c (zonk) removes the whole-solution read-back that one unsolved `?p.fst` would trigger, which pairs and D2511 make common. 6b fixes the motives (SW-1762) but is about six lanes away; stage 3's stop point catches the case where waiting for it is needed. Stage 3's hash moves conflict with every lane that regenerates snapshots: start it when few are in flight. |
| **4b** pair sweep | after 3 | Needs Pair eta. |
| **5** accessor bodies | after 3, if its measurement says so | Its measurement is stage 3's. |

The bounded read-back plan's measurements of record eta (4c's and 6b's
`resolveOutOfWalls` report) should be taken again after stage 3 merges,
since pairs will add to them: that's a line for those briefs, not a stage
here.

**SW-1829.** Its cause isn't known. If it is one of the unfolded read-back
sites, bounded read-back moves that site's stage first (its §5.1) and
stage 3 waits for it. If it is in record eta itself (rule 2's cost, the
glued projections, the hold), its fix belongs before stage 3 and may change
stage 3's brief (for example a lazier rule 2). Either way the plan here
absorbs the fix rather than duplicating it.

## 5. Briefs

Each block can be pasted. Each brief also carries CLAUDE.md's standing
lines: the worktree, time stops, no daily or full tier, `stitchwort fmt`,
`cargo fmt` and clippy, and the language guide for user-visible changes.

---

**2′. Record eta: unifier tests, surface examples and docs** (Opus, 60 min;
SW-1643, D2630)

- *Goal:* pin down the unifier eta stage 1 built (record-eta.md §8;
  `unify.rs:1632-1665`, `NO_ETA` at 2030, `same_field_records` at 1683)
  with the elaborator tests records.md §7.3 and §14 asked for, add surface
  examples, and write the docs stage 1 owed. No rule changes; if a test
  finds a bug, stop and report.
- *Tests to add:* see record-eta-remaining.md §2, stage 2′ (must accept, must
  reject). Show each live: switch its rule off locally and see it fail.
- *Docs:* `docs/guide/` (proofs chapter, or the records part of
  `03-data.md`): "a record is its fields" by `rfl`, and a function on an
  unknown record computing, with a checked example; `docs/syntax.md`'s
  Records section, and the `T.ext` entry (line 476) saying it's for field
  equalities that aren't `rfl`.
- *Run:* `task test:one --` with the new examples and unit tests,
  `record_eta`, `eta_hold`; `task snap:hashes` and `hash_stability` for the
  new examples.
- *Success:* the tests pass and were each shown live; the guide's examples
  check; no other hash moves.

---

**4a. Record eta sweep: records** (Sonnet, 60 min; SW-1645 split, D2631)

- *Goal:* remove the workarounds for the missing record eta from `aoc/` and
  `games/rogue/`, now that it's on `main`. Read
  record-eta-remaining.md §3: the greps in §3.1, the first list in §3.2.
- *Do:* delete the hand-written eta lemmas and use `rfl` (or drop the eta
  step from a `rewrite`); replace all-`rfl` `T.ext` calls with `rfl`; replace
  one-arm record matches whose arm is `rfl` with `rfl`; for the "to read and
  decide" matches, remove a match only if the proof reads as well with
  `r.field`. Grep each lemma's name across `aoc/` and `games/` before
  deleting it. Add a dated line to each friction note in §3.2's last
  paragraph.
- *Run:* `stitchwort check --no-cache` on each namespace touched, one at a
  time; `task audit:touched -- <Namespace>` for each; `stitchwort fmt` on the
  files touched. No whole-AoC run.
- *Success:* no hand-written eta lemma for a declared record is left; the
  record matches left in proofs are listed in the ticket with a reason each.

---

**3. Record eta stage 3: eta by shape, `Pair` first** (Opus, 180 min, Opus
review; SW-1644, D2499, D2632, D2633)

- *Read first:* record-eta.md §6.1 and §6.4, record-eta-remaining.md §2
  stage 3 and §4, SW-1764, SW-1829's answer.
- *Goal:* `qualifies_for_eta` (`core/src/check.rs:2255`) no longer needs
  `data.record`, so every one-constructor, non-recursive type in `Type` with
  a field that isn't a proof has eta (D2499). Pairs then behave like
  records: `p = (p.fst, p.snd) := rfl`, `swap (swap p) = p := rfl`.
- *First:* a test that names every std type that newly has eta, and update
  `only_float_add_is_held` deliberately if the held set grows (report the
  new members).
- *Then:* fix what breaks in std, the examples and the roguelike, as stage 1
  did. Tests: §2 stage 3's must-accept and must-reject lists, each shown
  live.
- *Measure (D2633):* add a temporary switch that turns the new types' eta
  off. In the background, each stopped at 6 minutes: whole AoC and the
  roguelike, `check --no-cache`, instructions retired, with the switch on
  and off. Count rule 2 firings per type (`Pair`, `Text`, `Char`, other),
  and accessor openings with their share of instructions (D2566). Remove
  the switch before the lane ends.
- *Stop and report* if whole-AoC instructions rise more than 10% over the
  switch-off run, if any namespace takes twice as long, or if more than five
  proofs in `aoc/` or the roguelike break: with the per-type counts, before
  fixing further.
- *Run also:* `record_eta`, `eta_hold`, extract's `bound_to_the_prelude`
  tests, the `omega` and `ring` examples, `literal-match-facts`,
  `task snap:hashes` and `hash_stability`.
- *Success:* as §2 stage 3; a short report of the measurements on the
  ticket, and D2566's answer from them.

---

**4b. Record eta sweep: pairs** (Sonnet, 45 min; after stage 3)

- As 4a, for §3.1's grep 5 and §3.2's pair list, and the 2020 notes' "pairs
  have no eta" lines.

---

**5. Accessor bodies as `Proj`** (Opus, 60 min; only if stage 3's
measurement meets D2566's condition)

- As record-eta.md §6.4's "the change": generate eta types' accessors with
  the body `Proj(D, i, x)`; use sites stay calls. Tests: the probes of
  §6.4's "what the mixture costs", `rewrite` both spellings, the update
  lemmas, the two printer cases. `task snap:hashes`, `hash_stability`,
  `bound_to_the_prelude`.

## 6. Questions for Matt

- **D2630: Stage 2 (unifier eta, SW-1643) is mostly built already: make it
  a short Opus lane of elaborator tests, surface examples and the guide and
  `syntax.md` text stage 1 owed, rather than a unifier change.** [rec: yes.
  Stage 1 put rule 1 in the unifier with every restriction §8 asked for, and
  D2511 added the same-field rule. What's missing is the tests records.md
  asked for, and telling users. 60 minutes, not a kernel lane.]
- **D2631: Split the sweep (SW-1645): the records part runs now, after
  SW-1829, and the pairs part after stage 3.** That amends D2505's order,
  which put the sweep last. [rec: yes. All 17 hand-written eta lemmas found
  are about declared records, which already have eta on `main`. Waiting for
  `Pair` gains nothing, and the sweep is the check that stage 1 works on
  real proofs.]
- **D2632: Stage 3 gives eta by shape to every qualifying type (D2499), not
  only `Pair`, with a stop point: if `Text`, `Char` or another type makes
  checks much slower or changes many goals, the lane stops and reports the
  per-type cost; whether to exclude a type then (which would need record-eta.md Q3's
  `no-eta` opt-out after all) is decided on those numbers.** [rec: yes. By
  shape is what D2499 decided, and the kernel condition stays a function of
  the declaration. `Text` is the one I'd watch: rule 2 opens every std
  function that matches `MkText` on an unknown text. The `no_eta` mark
  already exists, is hashed and survives the cache, so excluding a type
  later is small; but it is a user-visible attribute, so it's your call, on
  numbers.]
- **D2633: Stage 3 starts after SW-1829 is answered and bounded read-back's
  0c (metrics) has merged, preferably after 4c (zonk), without waiting for
  6b; and it may run whole AoC and the roguelike `check --no-cache` twice
  (eta on and off), in the background, stopped at 6 minutes each.** [rec:
  yes. Pairs multiply rule 2's firings, whose cost goes through the
  unfolded read-back sites those stages remove; 0c gives the baseline. 6b is
  about six lanes away, and the stop point catches the case where stage 3
  needs it. The two runs are the only way to see the cost of `Pair`, as the
  prototype's were for records; they're outside the lane test budget, so
  they need your OK.]
- **D2634: Close SW-1755 (the `x + y` must-pass example and the
  trip-journal check) as done by SW-1667, once the orchestrator has
  confirmed `float-sum-stays-a-sum`'s snapshot shows the sum as a call.**
  [rec: yes. Both parts merged with record eta.]

**D2566 (open) is unchanged by this reading:** keep `p.field` as an
accessor call and measure at stage 3 [rec: yes]. One addition for stage 3's
brief, not a change: by shape adds `Text` and `Char`, whose accessors
(`t.chars`, `c.code`) are opened often in std, so the measurement reports
accessor openings per type, and stage 5 can be limited to the types where
it pays.

Decided here, as sequencing: stage 2′ and 4a can run side by side, and
neither waits on bounded read-back; stage 5 exists only if stage 3's
numbers call for it; the sweep lanes are Sonnet (D2505).

## 7. What this note did not do

- It ran nothing: no build, no test, no measurement (the brief said so).
  The counts in §3 are greps of the tree at `437852b04`; the "to compute"
  readings are from the code, and each removal is the sweep lane's to
  confirm.
- The list of types that gain eta in stage 3 is from reading std's
  declarations with a rough script, so it misses types declared in a form
  it didn't parse; stage 3's first test gives the real list.
- It doesn't know SW-1829's cause (§4 says how the plan absorbs it).
- It didn't edit `board/tickets.json`. For the orchestrator: SW-1643's
  scope becomes stage 2′ (D2630); SW-1645 splits into 4a and 4b (D2631);
  stage 5 is a ticket only if stage 3 asks for it.
