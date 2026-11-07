# SW-1850: does the language guide still say what the language does?

*Accuracy audit, reading only, 7 Nov 2026, against `main` at `437852b04`. Scope:
`docs/guide/` (chapters 01–11, README, `examples/`), `docs/syntax.md` and the feature
tour (`web/guide/`), checked against the merges since 24 Oct 2026. Nothing was built or
run. The guide's and the tour's examples and quoted outputs are checked by tests
(`crates/cli/tests/tools/guide.rs`; the tour's web test), so what can be stale is prose,
unchecked blocks (no `<!-- snippet/output -->` marker), and house style in examples that
still check. Each claim below was read in the source or the merge named; where it wasn't,
it says so.*

## Summary

- **The guide is in good shape.** Most features of the last two weeks came with their own
  guide edits: clause lambdas, ranges, `NonEmptyList`, `.toSet`/`.toMap`, total division,
  brace syntax, leading-operator lines, arrays, `run --profile`, run icons and the Testing
  panel, W-MATCH-DECISION-IF. Nothing in a checked block is wrong.
- **Wrong (5):** the arrays section's `--js` sentence (SW-1817), the profiler example's
  day 11 numbers (Grid went onto arrays), "nothing is guessed from the field names" for
  record literals, "messages show the Unicode forms whichever you wrote", and the
  feature tour's arrays page saying arrays are "for numbers". In docs/syntax.md, three
  more: an example with `split`'s arguments the wrong way round (line 379), the printing
  rule (line 1871: "`->` stays `->`", and nothing on `Bool` operations printing in
  ASCII), and a code that doesn't exist (`E-MATCH-EQUATION`, line 2017).
- **Missing:** record eta (what now holds by `rfl`), `@[tailrec]`, `W-MATCH-NOT-FOUND`,
  `test --only/--json` in the testing chapter, Float in the tour.
- **Style:** parenthesised dot sections (`(.name)`, SW-1333) in seven guide examples,
  `List.range a (n + 1)` where a range reads better (two guide sites, one tour page),
  `Set.fromList`/`Map.fromList` and qualified calls in tour pages.

## 1. docs/guide/

| file:line | What it says | What's true now | Severity | Replacement |
|---|---|---|---|---|
| 06-namespaces-and-library.md:310 | "Under `--js` every operation runs as written, on the list, so it is correct but slow." | Since SW-1638 (`8a04aa211`) an array under `--js` is a version array: `get` and `set` on the newest version are one step; an old version reroots (docs/proposals/arrays.md §4.3). Day 15 under `--js` went 127 → 23 s. SW-1817 is this finding. | wrong | "Under `--js` an array is a *version array*: changing the newest version is one step too, and nothing is copied; reading an old version again is correct but slower, since it first undoes the changes made after it. So the advice is the same on both: pass the new array on." |
| 06-namespaces-and-library.md:312–318 | The copy note, and what to do about it | The text matches `crates/rt/src/prims.rs:766`. SW-1163 (§2.1, T7) asks for the idiom "take the state apart first, then don't refer to the old pair again" beside it, since a `match state.fst.pop` with `state` still live copies every turn (SW-1678). | outdated (incomplete) | Add after "…containing both.": "A common case is a loop whose state is a pair: `match state.fst.pop with … \| None => state` keeps `state`, array included, alive, so `pop` must copy. Take the pair apart first, `match state with \| (array, total) => match array.pop with …`, and use only the parts." |
| 11-running-and-shipping.md:19–42 | Profile of 2020 day 11, "a seating simulation that takes 20 s": `Std.Map.Tree.get` 68%, `Aoc.Common.Grid.lookup.λ` on a `Map` lookup, "Every neighbour of every seat is a `Map` lookup … 128 ns a step" | SW-1637 (`42b31a28a`) moved `Grid.lookup` onto arrays (`aoc/src/Aoc/Common/Grid.sw:204–206`, `table.getOr … \|> .get`); SW-1163 measured day 11 at 5.4 s. The block isn't checked, so it kept the old run. | wrong (quoted output) | Rerun `stitchwort run --profile --profile-top 8 Aoc.Year2020.Day11.main < inputs/2020/day11.txt` and requote it with the paragraph after it; or keep it as a before/after: "Before its grid moved onto arrays, day 11 took 20 s … now `Grid.lookup` is an array read, and the run takes about 5 s." A profile whose top row is a `Map` lookup is still the best teaching example, so a day that still has one (2020 day 17, `insertWith` about 20 µs a call, SW-1163 §1 item 4) would do as well. |
| 03-data.md:101 | "It needs to know which record type it is, from a signature, an argument's type or an annotation … Nothing is guessed from the field names." | Since SW-805 (`afea83956`, D1442, D1991) a literal whose type nothing in the declaration says takes the one record type in scope whose fields are exactly its own, at the end of the declaration (docs/syntax.md:452, `examples/accept/record-literal-inferred.sw`). | wrong | "Its type comes from where it's used: a signature, an argument's type, an annotation such as `({ … }: Person)`, or something later in the declaration, such as the other side of `==`. Only when nothing says it does the compiler look at the field names: the one record type in scope with exactly those fields. With none, or two, it asks for an annotation." |
| 10-proofs.md:597 | "They mean exactly the same as the ASCII, and messages show the Unicode forms whichever you wrote." | Statements print in Unicode, `Bool` operations in ASCII: the guide's own checked outputs show `fits: (n <= limit) = False` (line 549) and `` `(a && n <= 3) = True` holds`` (line 350), and line 555 says so. Since SW-1674 (`ff46f8404`) goals also print dot calls and `++` as written. | wrong | "They mean exactly the same as the ASCII. Messages show a statement in the Unicode forms (`n ≤ limit`, `a ∧ b`) and a `Bool` computation in ASCII (`(n <= limit) = False`, `a && b`), whichever you wrote, so a message tells you which of the two you have." |
| 03-data.md:241 | "Naming a bracket-declared constructor's fields works with named arguments instead, `Circle (id := "a") (radius := 1)`" | The chapter's `Circle` has one field, `radius`; `id` belongs to syntax.md's variant-fields example. A reader trying it on `Shape` gets an error. | outdated | "…works with named arguments instead, `Rect (height := 4) (width := 3)`, which also fill the defaults of fields left out." |
| 09-testing.md:17 | "Only `stitchwort test` and the playground's Tests tab run tests: checking, the editor and the playground's checks never do." | Since SW-1121 (`f75b243e2`) the editor runs tests on request: run icons and the Testing panel (chapter 1, lines 162–163). It still never runs them while checking. | outdated | "Tests run only when you ask: `stitchwort test`, the playground's Tests tab, or the editor's run icons and Testing panel. Checking a file, in the terminal or as you type, never runs them." |
| 09-testing.md (new paragraph after line 19) | Nothing on running some of the tests | `stitchwort test FILE --only "name"` runs one test; `--json` prints `{"ok", "tests": [...]}` for tools, `ok` false when nothing matches (SW-1121, SW-1685); a target matching no tests is a warning and a failure; `--verify-cache` reruns everything and compares with the cache (`crates/cli/src/main.rs:115–143`). | missing | "`stitchwort test FILE --only "counts words"` runs one test by its name. `--json` prints the results as one JSON object, which is what the editor reads. A target that matches no tests is a failure, so a typo in a name doesn't pass silently." |
| 07-recursion.md (end of "Structural recursion", or chapter 11's "Tail calls are loops") | Nothing on `@[tailrec]` | SW-1222 (`0050b91a3`): `@[tailrec]` before a `def`, `export def` or local `def` says it must run as a loop; a call that isn't a tail call is `E-TAILREC`, naming what holds it; JS fails loudly if it can't loop a marked definition. 89 std loops carry it (SW-1232). docs/syntax.md:666, 690. | missing | Add to chapter 11's "Tail calls are loops" bullet: "Mark such a function `@[tailrec]` (on the line before its `def`) and the compiler checks it: a recursive call with work left after it is `E-TAILREC`, which names that work. The library's loops are marked." With a checked snippet in `examples/recursion.sw` and an `errors/tailrec.sw`. |
| 10-proofs.md:569 | "That needs the equation's name: in a `match` without one, the error says to add it." | SW-1485 and SW-1721 (`2ee4d0839`, `f24ef4737`): a `match` whose expression isn't in the goal, named or not, warns `W-MATCH-NOT-FOUND` when its arms fail ("this `match` didn't find its expression in the goal, so every arm has the goal unchanged", with the goal and a note to write the expression as the goal shows it). An unnamed one whose arms check doesn't warn. | missing | Add after line 569: "If the expression isn't in the goal at all, every arm gets the goal unchanged, and when an arm then fails the compiler warns (`W-MATCH-NOT-FOUND`), showing the goal it searched: write the expression as the goal shows it, or bind it with a `let` first." |
| 10-proofs.md (new section, after "Types that mention values" or in chapter 3's Records) | Nothing on records in proofs | Record eta, stages 1 and 1b (SW-1642, `319c28c0c`): a record equals the record of its own fields, and a function that matches a record computes on an unknown one, both by `rfl`, for every one-constructor, non-recursive type with a data field, parameters included (`crates/core/tests/it/record_eta.rs`: `eta_works_through_parameters`, `a_match_on_an_unknown_record_takes_its_branch`). Pairs aren't yet (stage 3, record-eta.md §14). The guide update is record-eta.md stage 4's job. | missing | A short section with a checked snippet: `theorem positionEta (p: Position): p = { row = p.row, column = p.column } := rfl` and `theorem downColumn (p: Position): (down p).column = p.column := rfl` with `down` written as a record match; one sentence that a type with two constructors, a recursive type or a record of proofs only has no such rule, and `T.ext` is the tool there. |
| 05-interfaces.md:158–170 | `Vector.ext` for each law, with both records written out | Still correct. With record eta, `zeroAdd` and the others no longer need the records spelled out as `Vector.ext`'s first two arguments if the guide wants a shorter instance; leave as is until stage 4's sweep decides the idiom. | note only | none now |
| 01-getting-started.md:93 (examples/repl-session.txt) | `List.range 0 4` | Correct (`List.range (from) (until)`, SW-1357), but the docs now prefer range syntax (SW-1380). | style | `0 ..< 4` |
| 08-abilities.md:207–209 | `Each.each (List.range 1 (n + 1))`, `List.range a (n + 1)`, `List.range b (n + 1)` | Range syntax (SW-1358, SW-1380); `(n + 1)` as an exclusive end is what `..=` is for. | style | `Each.each (1 ..= n)`, `Each.each (a ..= n)`, `Each.each (b ..= n)` |
| 10-proofs.md:145 | "inside `List.sumBy f (List.range 0 n)` …" | Same; prose, so the range form reads better. | style | "inside `(0 ..< n).sumBy f` …" (check the congruence-lemma claim on that form when the snippet is touched) |
| 03-data.md:383 | `((findAdult []).map (.name)).getOrElse "nobody"` | No brackets around dot sections (SW-1333); forward chaining. | style | `(findAdult []).map .name \|> .getOrElse "nobody" == "nobody"` |
| 03-data.md:396 | `grid.map (.length) \|> .maximum \|> .getOrElse 0` | SW-1333 | style | `grid.map .length \|> .maximum \|> .getOrElse 0` |
| 04-functions.md:185 | `\|> .map (.length)` | SW-1333 | style | `\|> .map .length` |
| 05-interfaces.md:124 | `.sortOn (.suit)` | SW-1333 | style | `.sortOn .suit` |
| 06-namespaces-and-library.md:112 | `orders.filterMap (.price) \|> .sum` | SW-1333 | style | `orders.filterMap .price \|> .sum` |
| 09-testing.md:27 | `words.maxBy (.length)` | SW-1333 | style | `words.maxBy .length` |
| 11-running-and-shipping.md:68 | `items.map (.pence) \|> .sum` | SW-1333 | style | `items.map .pence \|> .sum` |
| 07-recursion.md:56 | `(values.foldLeft Leaf (tree value => tree.insert value)).toList` | Forward chaining; the lambda is `Tree.insert`. | style | `values.foldLeft Leaf Tree.insert \|> .toList` |
| 10-proofs.md:584–585 | `Both (And.right h) (And.left h)` | Propositions use operators; the projections read better as fields. Correct as written. | style | `Both h.right h.left` (if `∧`'s fields are `left`/`right` as `And.left` suggests; check by test) |

Checked and still right, for the record: the copy note's text; the `--profile` table's
column headings and footer (`crates/rt/src/profile.rs:106–142`); total division
(chapter 2, SW-1640); the leading-operator list (chapter 2:73, SW-1513);
`List.range (from) (until)` in the REPL session; brace syntax (chapter 3, SW-1632/1633);
clause lambdas and `matches` (chapter 4); W-MATCH-DECISION-IF (chapter 10:571); the
interface list (chapter 5:179 matches `^interface` in std); the commands table
(chapter 1) against `crates/cli/src/main.rs`'s `Command`. Bounded readback and Float
operators printing touch no guide passage: no guide block prints a `Float` computation,
and the `?` goals the guide quotes are checked outputs, so they moved with the code.
chapter 10:116 ("The goal is shown computed") still describes those outputs.

## 2. docs/syntax.md

Merges that updated syntax.md as they landed (SW-1719, SW-1630, SW-1650, SW-1121, SW-1638,
SW-1633, SW-1639, SW-1640, SW-1632, SW-1538, SW-1513, SW-1410, SW-1359, SW-1358, SW-1357,
SW-1318, SW-1305, SW-1294, SW-1217) read as current. The stale passages come from merges
that didn't touch the file: SW-1642 (record eta), SW-93 (proof irrelevance), SW-1685
(`test --json`), SW-1485/SW-1721 (`W-MATCH-NOT-FOUND`), SW-1763 (Float printing), SW-1380
(range syntax in docs), SW-1216 and SW-1256 (house style).

| file:line | What it says | What's true now | Severity | Replacement |
|---|---|---|---|---|
| docs/syntax.md:379 | `def words (line: Text): List Text := split ' ' line` | `Text.split (text: Text) (separator: Char)` takes the text first (`std/Text/Basics.sw:159`). The example doesn't type-check (it is in an unchecked block). | wrong | `def words (line: Text): List Text := split line ' '` |
| docs/syntax.md:1871 | "Goals and messages show `∧` `∨` `¬` `≠` `≤` `∈` `∉` `↔` …; `->` stays `->`. Comparison on `Nat`/`Int` under a binder may show unfolded (`Nat.leq k y = True`), as before." | Types print `→` (`b807b3f90`; the guide's checked REPL output shows `Nat → Text`). `Bool` operations print in ASCII as written (`34dafbde7`: `(n <= limit) = False`, `a && b`), and dot calls and `++` as written (SW-1674). | wrong | "Goals and messages show a statement's connectives in Unicode (`∧` `∨` `¬` `≠` `≤` `∈` `∉` `↔` `→`, `∃ (x: T) => P`), whichever spelling the source used, and a `Bool` computation in ASCII (`(n <= limit) = False`, `a && b`), so the two can be told apart. Dot calls and `++` print as the source writes them (SW-1674)." |
| docs/syntax.md:2017 | "`E-MATCH-EQUATION` is for an equality `h` that can't be formed … This version doesn't report it." | No such code exists in `crates/`. | outdated | Delete the sentence. |
| docs/syntax.md:159 | `test --json` gives "per test … `message`, and for a failure the `comparison` sides and the false `part`" | The object is `{"ok", "tests": [{…, "failure": {"part": {text, file, line, column}, "comparison": {op, left, right, difference}}}]}`; `ok` is false when `--only` or a target matches nothing (SW-1685; `crates/cli/src/main.rs:1486–1558`). A namespace target runs the namespaces under it (SW-1682). | outdated | "…`message`, and for a failure `failure`: `{part, comparison}`, with `comparison` as `{op, left, right, difference}`. `ok` is false if any test didn't pass, or if `--only` or the target matched no test (also a warning, exit 1). `stitchwort test NS` runs a namespace with those under it; the Testing panel runs groups this way." |
| docs/syntax.md:476 (`T.ext` bullet) | Records are equal through `T.ext`; nothing on eta | Record eta stages 1 and 1b (SW-1642): a record in `Type`, not recursive, with a data field (parameters allowed; not interfaces, not proof-only records, not `Pair` until stage 3) is `rfl`-equal to the record of its projections, and a record match computes on an unknown record. `Float.add`, which has a native, stays held (D2551, `examples/reject/float-add-is-held.sw`). | outdated | New bullet before `T.ext`: "**Record eta** (docs/proposals/record-eta.md, SW-1642). A record equals the record built from its own fields, by `rfl`: `theorem positionEta (p: Position): p = { row = p.row, column = p.column } := rfl`. A function that matches a record (`\| { row, column } => …`) computes on an unknown record, so `(down p).column = p.column` is `rfl`. This holds for a non-recursive record in `Type` with a field that isn't a proof; interfaces and proof-only records don't have it. `T.ext` is still the tool where the fields' equations are proved, not computed." |
| docs/syntax.md:466 | `({ p \| x = 1 }).x = 1` is `rfl` | Still true; eta also makes `{ p \| x = p.x } = p` `rfl` (not checked by a run). | outdated (incomplete) | add "and `{ p \| x = p.x } = p` is `rfl` (record eta)" once a test confirms it |
| docs/syntax.md:2165 | "If a proof-irrelevant comparison arrives (proof-irrelevance.md), a candidate …" | Proof irrelevance stage 1 is merged (SW-93). | outdated | "With proof irrelevance (SW-93), a candidate that equals the left side only by ignoring a proof field can match and then fail the round trip, as `E-REWRITE-MOTIVE`." |
| docs/syntax.md:2378 (Float, Arithmetic) | "a goal shows a double as its literal" | Float arithmetic prints as operators, `x + y`, not `x.add y` (SW-1763); a sum of unknown doubles stays a sum (`examples/reject/float-sum-stays-a-sum.sw`). | outdated (incomplete) | append "Goals and messages print `Float.add x y` as `x + y` (and `-`, `*`, `/` likewise). A sum of unknown doubles stays a call, never `Float.Model` bit arithmetic." |
| docs/syntax.md:1947–2088 (`match`) | No `W-MATCH-NOT-FOUND` | Fires when a `match`'s expression is in neither the goal nor a hypothesis, named or not, when the arms fail (SW-1485, SW-1721; `crates/elab/src/matching.rs:1566`). The only warning code in the source that syntax.md lacks. | missing | "**Not found.** If the expression is in neither the goal nor a hypothesis as they compute, the `match` refines nothing; when an arm then fails, `W-MATCH-NOT-FOUND` says so and shows the goal. Write the expression as the goal shows it, `rewrite` first, or bind it with a `let`." |
| docs/syntax.md:3 | "describes `crates/syntax` as of 1 November 2026" | Brace syntax, ranges, clause lambdas, total division since | outdated | the date of the sweep that fixes the rest |
| docs/syntax.md:141–142, 155–156, 297, 301, 315, 1014–1015, 1954–1960, 2208–2210 | `Cons x xs`, `Nil`, `Cons (n % 10) acc` in patterns and expressions | Bracket list syntax (CLAUDE.md, SW-1256) | style | `[x, ..xs]`, `[]`, `[n % 10, ..acc]`, `[_, ..a], [_, ..b]` |
| docs/syntax.md:477, 1245, 1467, 1786 | `Not (n = 0)`, `Not p`, `Not P`, `Not (x < y && y < z)` | Propositions with operators (SW-1216) | style | `n ≠ 0`, `¬p`, `¬P`, `¬(x < y ∧ y < z)` (and `x < y ∧ y < z` for the `then` branch at 1786) |
| docs/syntax.md:920–921, 1103 | `List.range 1 (n + 1)`, `List.range a (n + 1)`, `List.range 0 n \|> .attach` | Range syntax (SW-1380) | style | `1 ..= n`, `a ..= n`, `0 ..< n \|> .attach` |
| docs/syntax.md:151 | `Nat.leq (length (List.append [1] [2, 3])) 3` | Operators and forward chaining | style | `length ([1] ++ [2, 3]) <= 3` |
| docs/syntax.md:293 | `(lines.map (joltage k)).sum` | Forward chaining | style | `lines.map (joltage k) \|> .sum` |
| docs/syntax.md:592 | `Some (Nat.div n 2)` | The operator, total since SW-1640 | style | `Some (n / 2)` |
| docs/syntax.md:1421 | `IO.print (Nat.toText (collatzSteps 27))` | Interpolation reads better | style | `IO.print "${collatzSteps 27}"` |
| docs/syntax.md:1882–1885 | `people \|> List.map (p => p.age) \|> List.sum` | Shows piping into qualified functions, which is its point | style | keep, and add the house form beside it: `people \|> .map .age \|> .sum` |

Checked and current: total division (1484); brace syntax (456–462); leading-operator lines
(14); `if a && b` giving `a ∧ b` (1789); ranges (1809–1830); clause lambdas and `matches`
(2057–2088); `W-MATCH-DECISION-IF` (2007); `@[tailrec]` (666, 690); arrays under `--js`
(688); `W-MATCH-UNCONFIRMED`, `W-REWRITE-UNCONFIRMED`, `E-CASES-BUDGET`; "Goals are shown
computed" (1567), since bounded readback's goal display (stage 5) isn't built. Not in
syntax.md, and worth a line each: `run --profile` (guide chapter 11 has it) and the
dot-form printing of goals (SW-1674, SW-1706). Not checked: whether the `search` output at
1655–1665 still prints calls in prefix form (needs a run).

## 3. The feature tour (web/guide/)

The tour's examples and quoted messages (`data-failure-of`, `data-dts-of`) are tested; the
findings are in `guide.html`'s prose, page comments and house style.

| file:line | What it says | What's true now | Severity | Replacement |
|---|---|---|---|---|
| web/guide/guide.html:80 | Arrays section says nothing about JavaScript | Version arrays under `--js` and in exported code since SW-1638; at the boundary an `Array Nat` is `readonly bigint[]` in, `bigint[]` out (the extraction snapshot `extract__arrays.d.ts`) | outdated (SW-1817) | Append: "In JavaScript (`--js`, and exported code) an array is a version array, also one step per read and change, and it crosses the boundary as a JS array." |
| web/guide/guide.html:80 | "357 seconds with a Map to 16 seconds with an array" | Right: SW-1657 (`7abe44295`, 31 → 16 s) and `021bae2a9` updated it. SW-1817's second half (16 s against SW-1637's 27 s) can be closed. | none | keep |
| web/guide/guide.html:185 | How records, variants, `Nat`, `Option`, `SafeNat` look in JS | Arrays missing (SW-1638) | outdated | After "`Option a` is `a \| undefined`": ", and `Array a` is a JS array (`readonly a[]` as an argument)" |
| web/guide/35-arrays.sw:1 | "`Array a` is for numbers you look up and update by position" | `Array a` holds any `a` | wrong (minor) | "-- `Array a` is for values you look up and update by position, many times." |
| web/guide/guide.html:135 | "`omega` … `+`, `-`, comparisons and multiplication by constants" | Also `Int`, `/` and `%` by a constant, division by 0, `Int.natAbs` (SW-997, SW-1650, SW-1669) | outdated | "For facts about whole numbers and integers built from `+`, `-`, comparisons, multiplication by constants, and division and remainder by a constant, `omega` finds the proof itself, using the hypotheses in scope." |
| web/guide/24-omega.sw:1–2 | "only use +, comparisons and multiplication by constants" | Same | outdated | "-- `omega` proves facts about whole numbers and integers that use +, -, comparisons, multiplication by constants and division by constants, using the hypotheses in scope." |
| web/guide/guide.html:160 | "In a proof, `List.memRange` turns membership into the two bounds." | `omega` and `auto` read `x ∈ a ..< b` directly (SW-1359); page 34 shows it | outdated | "In a proof, `omega` reads membership as the two bounds (`List.memRange` states it as a lemma)." |
| web/guide/guide.html:10 | Basic types `Nat`, `Bool`, `Text`, `Char`, `Int` | `Float` exists; division is total (SW-1640) and page 02 divides | outdated | "…and `Int` when you need negatives, `Float` for measurements. Division never fails: `x / 0` is `0` and `x % 0` is `x`." |
| web/guide/guide.html:91 | "from a terminal, `stitchwort test` does the same for a whole project" | `--only`, `--json`, the Testing panel and run icons (SW-1121, SW-1682/1684) | outdated | "…from a terminal, `stitchwort test` does the same for a whole project (`--only NAME` picks one test), and in VS Code the run icons and the Testing panel do it." |
| web/guide/18-each.sw:8–9 | `each (List.range 1 (n + 1))`, `each (List.range a (n + 1))` | Range syntax (SW-1358, SW-1380) | style | `let a := each (1 ..= n)`, `let b := each (a ..= n)` |
| web/guide/34-ranges.sw:18 | `List (Pair Nat Nat)` | The tour writes `(Nat, Nat)` elsewhere | style | `List (Nat, Nat)` |
| web/guide/14-map-set.sw:18 | `Set.fromList [(0, 0), …]` | `.toSet` (SW-1347, SW-1594) | style | `[(0, 0), (0, 1), (1, 1), (0, 1)].toSet` |
| web/guide/14-map-set.sw:24 | `Map.fromList […] == Map.fromList […]` | `.toMap` (SW-1347) | style | `[("a", 1), ("b", 2)].toMap == [("b", 2), ("a", 1)].toMap` |
| web/guide/15-namespaces.sw:6, 14 | `import Text (split)` … `match split line ',' with` | Forward dot form | style | Drop the import, `match line.split ',' with` (the page still shows `import Std (Option)`) |
| web/guide/09-deriving.sw:14–15 | `List.sort [High, Low, Medium]`, `List.sort [b, a]` | Dot form | style | `[High, Low, Medium].sort`, `[b, a].sort` |
| web/guide/23-proofs.sw:12–13 | `List.length (List.append xs ys) = List.length xs + List.length ys` | Dot form and `++`, which goals now print as written (SW-1674) | style | `(xs ++ ys).length = xs.length + ys.length` (arms to be rechecked by the page test) |
| web/guide/31-mutual.sw:22, 26, 29 | `Forest.total kids`, `Tree.total first + Forest.total rest` | Dot form | style | `label + kids.total`, `first.total + rest.total`, `(Node 1 …).total == 6` |
| web/guide/32-dependent-types.sw:8, 11, 14 | `Vec.head v`, `Vec.zipWith a b (…)`, `Vec.sum (sums trio trio)` | Dot form | style | `v.head`, `a.zipWith b (x y => x + y)`, `(sums trio trio).sum == 12` |
| web/guide/35-arrays.sw:13, 23 | `.getOr 99 0`, `.set 10 7` | Two numbers in a call are named (D2367) | style | `.getOr (index := 99) (fallback := 0)`, `.set (index := 10) (value := 7)` |
| web/guide/12-option-list.sw:12, 18 | `"best ${scores.maximum}"` gives `"best Some 12"` | Right, but reads like a bug | style | Add "-- `maximum` is an `Option`: an empty list has none", or `scores.maximum.getOrElse 0` |
| web/guide/10-dot-pipes.sw:23 | Test "method call" uses `Person.greet { … } "Hi"` | Shows the qualified call, not the method call | style | `{ name = "Cy", age = 1 }.greet "Hi" == "Hi, Cy"`, or rename the test "the call it stands for" |
| web/guide/23-proofs.sw:9–11 | Run-on comment, capital after a colon | — | style | "-- A fact about every list is proved by cases on the list, like a function: the empty list, then a list with a first element, where the theorem used on the shorter list is the induction step. `Eq.cong` carries an equation through a function." |

The tour is otherwise current: pages 04 and 11 follow the brace rules (SW-1632/1633),
page 11 covers clause lambdas and `matches`, page 13 uses `.toSet`, and its two quoted
range errors match `crates/syntax/src/parser.rs:4040` and `:4127`.

## 4. Outside the guide, found on the way

- `crates/elab/src/std/Array/Array.sw:15–16`: the type's doc says "Under `--js` every
  operation runs as written, on the list", stale since SW-1638, like the guide (fold into
  the SW-1817 lane; std docs are user-facing through `stitchwort doc Array` and hover).
- `examples/accept/records.sw:57–61`: "An update that changes nothing isn't `rfl` until
  stage 2 (eta), but it's provable by matching", then proves `{ p | age = p.age } = p`
  by a record match. With record eta on `main` this is probably `rfl` now (rule 1 with
  the update's projections); not checked. Record-eta stage 4's sweep should take it.

## 5. Missing coverage, in priority order

1. **Record eta** (SW-1642): `p = { … p's fields … }` and a record-matching function on an
   unknown record are `rfl`. It removes the most confusing proof failure the AoC friction
   notes list (record-eta.md §1). Guide chapter 10 (or 3), syntax.md's Records, and a tour
   page. Its timing belongs to record-eta stage 4; until then a short section is still
   worth having, since stage 1 is what changed what users meet.
2. **`@[tailrec]`** (SW-1222): a promise the compiler checks, which is what a programmer
   from Scala expects (`@tailrec`). Guide chapter 7 or 11, and a tour page.
3. **Running some tests, and tests in the editor** (`--only`, `--json`, Testing panel):
   chapter 9 has none of it; chapter 1 lists the editor side.
4. **`W-MATCH-NOT-FOUND`** in chapter 10's `match` section: the warning a newcomer meets
   first when a `match` in a proof does nothing.
5. **Holes and live goals in the tour**: `?`, the goals panel and hover, `search --at`.
   The guide has it (chapter 10); the tour, the place a newcomer starts, has no page.
6. **`Float`** in the tour: literals, operators, that they print as operators (SW-1763),
   and that they never mix with `Nat`. One sentence in the "Definitions" page may do.
7. **Splitting an `if` in a proof** in the tour (`match fits: cond with`, D2525): extend
   page 26 or 27.
8. **`run --profile`**: covered in chapter 11; no tour page needed unless the playground
   gains it.

## 6. Tickets to file

Each is one lane of about 30–60 minutes. "Tour page" marks the ones that add one. All of
them run `task guide:update` (or the web test) only on what they touch, as `test:lane
AREA=guide` selects.

1. **[Sonnet] Guide arrays under `--js`, and the pair idiom** (absorbs SW-1817 and SW-1163
   T7's guide half). Chapter 6:310 and 312–318 as in §1; `Array.sw`'s doc lines 15–16;
   tour `guide.html:80`, `:185` and `35-arrays.sw:1`. Close SW-1817's 16 s question (the
   figure is right). About 30 min.
2. **[Sonnet] Requote chapter 11's profile.** Rerun 2020 day 11 (now about 5 s on arrays),
   or pick a day whose top row is still a `Map` operation (2020 day 17), and rewrite the
   reading of it. Needs one profiled run of about 5–20 s; say so in the brief. About 30 min.
3. **[DeepSeek] Guide prose fixes.** Chapter 3:101 (record literal types), 3:241 (the
   `Circle` example), 9:17 (the editor runs tests), 10:597 (how messages print the two
   spellings), and the `--only`/`--json` paragraph in chapter 9. Prose only, with the
   replacement texts above. About 30 min.
4. **[DeepSeek] Guide and tour house-style sweep.** The seven `(.field)` sections, the
   `List.range` sites (guide 1:93, 8:207–209, 10:145; tour 18-each.sw), `treeSort`,
   `Both h.right h.left`, and the tour's style rows (pages 09, 10, 12, 14, 15, 23, 31,
   32, 34, 35). Examples are checked, so the run is `task guide:update` and the tour's web
   test. About 45 min.
5. **[Sonnet] `@[tailrec]` in the guide, with a tour page.** A checked snippet and an
   `errors/tailrec.sw` with its E-TAILREC output in chapter 7 or 11; a tour page
   (`web/guide/36-tailrec.sw`). About 45 min. Tour page.
6. **[Sonnet] Record eta in the guide, with a tour page.** After confirming by test which
   forms are `rfl` today (records with and without parameters; not pairs until stage 3):
   a section in chapter 10, syntax.md's Records, `examples/accept/records.sw:57–61`, and a
   tour page. Coordinate with record-eta stage 4, or make this its docs half. About 45 min.
   Tour page.
7. **[DeepSeek] Tour prose for omega, ranges, Float and tests.** `guide.html:10`, `:91`,
   `:135`, `:160`, and `24-omega.sw:1–2`, as in §3. About 30 min.
8. **[Sonnet] W-MATCH-NOT-FOUND in chapter 10.** The sentence in §1 with a checked
   `errors/match-not-found.sw` and its output. About 30 min. Could join ticket 3 if the
   example is dropped.
9. **[Sonnet] Tour page: holes and live goals.** `?` in a proof, the goal it reports, the
   goals panel and `search --at`. About 45 min. Tour page.

10. **[DeepSeek] syntax.md accuracy fixes.** Lines 379 (`split`'s argument order, a
    wrong example), 1871 (printing), 2017 (`E-MATCH-EQUATION`), 159 (`test --json`), 2165
    (proof irrelevance), 2378 (Float printing), and `W-MATCH-NOT-FOUND` in the `match`
    section, with the texts in §2. About 40 min.
11. **[DeepSeek] syntax.md house-style sweep.** The `Cons`/`Nil`, `Not`, `List.range`
    and chaining rows of §2. About 40 min. Can join ticket 4 if one lane takes all the
    style rows.

Record eta in syntax.md (§2, lines 466 and 476) belongs to ticket 6.
