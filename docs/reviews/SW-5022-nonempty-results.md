# SW-5022: std functions that should give or take a NonEmptyList

Survey, Opus paper lane, 28 Nov 2026. Matt: "we should also consider if any
other stdlib functions would be better off returning NEL rather than List for
better type safety". The model case is D3778, `List.scanLeft` returning
`NonEmptyList b` (lane SW-5021), so it is left out below except as evidence.

Method: every `def` in `crates/elab/src/std` whose result type is `List …` or
`Option …` (about 600 signatures, Doc/Omega/Ring internals skimmed), read for
"can the result be empty?" and "is the `Option` there only for an empty
input?". Call sites counted with grep across std, `aoc/`, `games/rogue`,
`tools/`, `examples/`, `docs/` and `web/`, in `.sw` files (prose mentions in
`.md` left out). No builds or tests.

Already done before this survey, so not candidates: `Parse.many1`, `sepBy1`,
`lines`, `sections`, `section`, `grid`; `List.splitBy` (groups);
`Map.groupBy` / `groupMap` / `List.groupBy` (values); `Nat.digits`;
`Stream.cycle` (takes one). The proposal behind them is
`docs/proposals/non-empty-lists.md` (D2393-D2399); its §8 list of producers
mentions `Text.split` and passes over it without a decision.

## Summary, biggest benefit first

| # | Function | Today | Proposed | Callers | Verdict |
|---|---|---|---|---|---|
| 1 | `Parse.oneOf` (Parse/Parse.sw:313) | takes `List (() → {Parse t} a)`, fails at run time on `[]` | takes `NonEmptyList (…)` | 31, every one a literal | **change** |
| 2 | `Text.split` (Text/Basics.sw:187), `Text.splitOn` (Text/Text.sw:482) | `List Text` | `NonEmptyList Text` | 37 code sites | **change, once NEL has the methods callers use** (see §9) |
| 3 | `Parse.span1` (Parse/Parse.sw:268) | `{Parse t} List t` | `{Parse t} NonEmptyList t` | 0 outside its own tests and 3 lemmas | **change** (cheap; matches `many1`) |
| 4 | `Parse.pick` (Parse/Chars.sw:118) | takes `List (Text, a)` | takes `NonEmptyList (Text, a)` | ~140, nearly all literals (not all checked) | **change with #1** if it changes, else leave |
| 5 | `List.chunksOf` (List/Toolkit.sw:822) | `List (List a)` | `List (NonEmptyList a)` | 1 (plus `Text.chunksOf`) | **leave** |
| 6 | `List.tails` (List/Toolkit.sw:947) | `List (List a)` | `NonEmptyList (List a)` | 6 (one AoC day) | **leave** |
| 7 | the rest (§7) | | | | **leave** |

One finding outside std: 2020 day 15 calls `starting.numbers.toList.maximum.getOrElse 0`
on a field that is already a `NonEmptyList` (§8).

## 1. `Parse.oneOf`: take a NonEmptyList (the reverse shape)

- **Today:** `Parse.oneOf: (parsers: List (() → {Parse t} a)) → {Parse t} a`,
  with an arm `| [] => Parse.fail "`oneOf`: no alternatives"`. The loop
  under it, `Parse.oneOfFrom first rest`, already has the non-empty shape.
- **Always non-empty?** The input isn't a result, but `[]` is a programming
  error that today surfaces as a parse failure at run time, not a type
  error. There's a std test that pins it (`test "Parse: oneOf, none"`,
  Chars.sw:555) and a proof case for it (`Parse.declinesOneOf`, Runs.sw:2443:
  `| [], done => Parse.declinesFail "`oneOf`: no alternatives" input`).
- **Proposed:** `Parse.oneOf (parsers: NonEmptyList (() → {Parse t} a))`, the
  body `Parse.oneOfFrom parsers.head parsers.tail`.
- **Callers:** 31 `Parse.oneOf [ … ]` sites in aoc, tools, examples and std, all
  literals. A list literal checked against a `NonEmptyList` builds one
  (docs/syntax.md, "NonEmptyList brackets"), so **none of them changes**. The
  two lemmas that take a variable (`Reads.sw:1672`, `Gives.sw:183`) and
  `Parse.declinesOneOf` change their parameter type and lose the `[]` case;
  `Parse.DeclinesAll` would be stated on `parsers.toList` or get the
  `NonEmptyList` shape.
- **End-state cost:** zero `.toList` at call sites; the "no alternatives"
  error and its test go.
- **Verdict: change.** It is the clearest win in std: a run-time failure
  becomes `E-NONEMPTY-EMPTY` at compile time, and no caller writes anything
  new.

## 2. `Text.split` and `Text.splitOn`: give a NonEmptyList Text

- **Today:** `Text.split (text: Text) (separator: Char): List Text`
  (Basics.sw:187) and `Text.splitOn (text sep: Text): List Text` (Text.sw:482).
- **Always non-empty?** Yes, both by construction. `split` ends in
  `Text.splitTexts (MkPair field fields) = [MkText field, ..Text.textsOf fields]`,
  a cons for every input; its doc says `"".split ','` is `[""]`.
  `splitOnChars` gives `[MkText chars]` for an empty separator, and
  `splitOnLoop`'s end case is `List.reverseOnto [MkText …, ..acc] []`, again
  a cons; its doc says "Always at least one piece". **No lemma proves
  either** (`Text.joinSplit` is the only split theorem; nothing like
  `splitNotNil`).
- **Proposed:** `NonEmptyList Text` for both. (Not `Text.lines`: `"".lines` is
  `[]`, as Rust's `str::lines`. Not `Text.words` or `Text.chunksOf`: each
  piece is a non-empty `Text`, which a `NonEmptyList` can't say.)
- **Callers, 37 code sites** (std 3, aoc 1, tools 4, examples 22, docs/guide 6,
  web 1; comparisons scripts 1). They fall into three groups:
  - **Benefit, 4 sites.** A fallback or impossible arm goes:
    - `std/Files/Files.sw:110`, `Path.extension`:
      `match name.split '.' with | [] | [_] | ["", _] => None | pieces => match pieces.last with | Some "" => None | last => last`.
      The `[]` arm goes, and `pieces.last` is total, so the inner match is
      `if pieces.last == "" then None else Some pieces.last`.
    - `tools/fmt/src/Fmt/Rules.sw:1056`:
      `name.splitOn "." |> .reverse |> .headOr "" |> …` becomes
      `name.splitOn "." |> .last |> …`.
    - `docs/comparisons/aoc-2024-day03-community/scripts/sw/Split.sw:8`:
      `match memory.splitOn "don't()" with | Cons first later => … | Nil => memory`
      loses the `Nil` arm (the comparison's point is idiomatic code, so this
      reads better).
    - `examples/extract/text.sw:207`, `firstField`, whose `firstOfList` has a
      `Nil => "none"` arm, becomes `.head`. (This file tests the JS export;
      the export at line 130 still returns a `List`, so it would write
      `.toList`.)
  - **Unchanged, about 15 sites.** Matches on a fixed number of fields
    (`match line.split ' ' with | [dir, weightText, colour] => … | _ => abort()`,
    examples/accept/abort.sw:12, also fail.sw, extract/results.sw, the
    guide's testing.sw, web/guide/15-namespaces.sw) work as they are: list
    patterns match a `NonEmptyList`, and a `_` arm is still allowed.
    Comparisons with a literal (`… == ["abc"]`, std's own tests) build a
    `NonEmptyList` literal. `tools/fmt/src/Syntax/Parser.sw:48`
    (`match token.text.split '\n' |> .reverse with | [last, _, .._] => … | _ => …`)
    needs its `_` arm anyway, for the one-line case.
  - **Need `.toList` today, about 18 sites**, almost all because
    `NonEmptyList` lacks the method:
    `.filterMap` (guide errors/import.sw:1, failing/tests.sw:4), `.filter`
    (guide functions.sw:83), `.withIndex` (tools/fmt Lexer.sw:370),
    `.toSet` (2024 day 23 Examples.sw:59), `Text.join` / `.joinWith` (guide
    library.sw:56, `Text.joinSplit`), `concatMap` wanting a `List`
    (Files.sw:38), a declared `List Text` result (examples/accept
    dot-notation.sw:33/35, method-sections.sw:54), and the test helper
    `eqTexts: List Text → List Text → Bool` (text.sw ×6, text-prefix.sw ×8,
    which could instead take `NonEmptyList`s or use `==`).
- **End-state cost:** with `NonEmptyList.filter`, `filterMap`, `withIndex`,
  `toSet` and `Text.join`/`joinWith` for a `NonEmptyList Text` (see §9), the
  `.toList` sites drop to about 4: the JS export, `concatMap`, and the two
  example functions that declare `List Text` (which could declare the new
  type). Without them, 18 of 37 sites write `.toList` to gain 4 removed
  fallbacks, which reads worse than today.
- **Note on volume:** AoC hardly uses `split` (1 site): days parse with
  `Std.Parse`, whose `sepBy1`/`lines` already give `NonEmptyList`s. The
  users are newcomer-facing: the guide, the examples and the feature tour.
  That cuts both ways: the type teaches "a split always has a piece", but
  `.toList` noise lands in the first chapters.
- **Verdict: change, after the method gap is filled** (or a general
  mechanism, §9). Doing it first would trade 4 fallbacks for 18 `.toList`s.
  `Text.joinSplit` would become `Text.join (t.split s) s = t` with `join`
  taking the `NonEmptyList` (or a twin); the proof is unaffected in
  substance.

## 3. `Parse.span1`: give a NonEmptyList

- **Today:** `Parse.span1 (what: Text) (passes: t → Bool): {Parse t} List t`,
  defined as `match Parse.span passes with | [] => Parse.expected what | items => items`.
- **Always non-empty?** Yes: the `[]` arm fails. Its lemmas say so in prose
  ("a run that isn't empty", Reads.sw:936; Runs.sw:790 takes the run as
  `[x, ..xs]`-shaped `taken`) but the type doesn't.
- **Proposed:** `{Parse t} NonEmptyList t`, the second arm
  `| [first, ..rest] => [first, ..rest]` (a `NonEmptyList` literal).
- **Callers:** none outside std: its two tests (Tokens.sw:196, 201) and three
  lemmas (`Runs.sw:796`, `Runs.sw:911`, `Reads.sw:938`), whose `value` becomes
  `taken.toNonEmpty` or the lemma takes `first rest`. `Parse.takeWhile1`
  (Chars.sw:25) is its `Text` counterpart and stays `Text`.
- **End-state cost:** none at call sites. It brings `span1` in line with
  `many1` and `sepBy1`, the other "1" parsers, which the guide already says
  give a `NonEmptyList`.
- **Verdict: change.** Small benefit, near-zero cost, and the naming promise
  ("1") becomes a type.

## 4. `Parse.pick`: take a NonEmptyList (follows #1)

- **Today:** `Parse.pick (choices: List (Text, a))`. On `[]` it notes
  nothing (`Parse.noteWords` has a `[] => ()` arm) and stops, so the error
  says nothing was expected.
- **Callers:** about 140 `pick` sites (`pick (`, `pick [`, `Parse.pick …`),
  the ones read all literals (`pick [("L", Left), ("R", Right)]`); not every
  one checked, and the `pick (` sites need a look for a non-literal argument.
- **Verdict: change together with #1** for consistency (the two are "one of
  these alternatives"); on its own the gain is small, since an empty `pick`
  is a mistake nobody makes. Leave it if #1 is declined.

## 5. `List.chunksOf`: `List (NonEmptyList a)`, leave

- **Always non-empty chunks?** Yes: `chunksOfPositive` takes `[y, ..ys]` and
  emits `List.take [y, ..ys] size` with `size ≠ 0`; `size = 0` gives `[[y, ..ys]]`
  or `[]`. No lemma says each chunk is non-empty.
- **Callers:** one, `docs/comparisons/aoc-2024-day01-community/scripts/sw/Words.sw:8`,
  `… |> .chunksOf 2 |> .transpose`, which needs `List (List a)`. Plus
  `Text.chunksOf` (Text.sw:884), which maps them to `Text` and couldn't use
  the type, and one example (`examples/accept/day2-chunks.sw`, `Text.chunksOf`).
- **Verdict: leave.** No caller takes a chunk's `maximum` or `head`; the one
  user would write `.map .toList`. `List.splitBy`, the other grouping, is
  already `List (NonEmptyList a)`; if a caller ever wants chunk extremes,
  revisit.

## 6. `List.tails`: `NonEmptyList (List a)`, leave

- **Always non-empty?** Yes, `[] => [[]]`, and `List.lengthTails` proves
  length `Succ (length xs)`. (Each element is non-empty except the last, which
  no type here can say.)
- **Callers:** 6 in 2024 day 22 (`prices.tails.findMap …`, `.filterMap sale`,
  and three proofs over them), one in 2021 day 1's spec
  (`measurements.tails |> .map (.take size) |> .filter …`), and the
  `List.windowsTails` lemma in std.
- **Verdict: leave.** Every caller searches or filters the suffixes; none
  wants the first or last of them, so the change would only add `.toList`
  (or need NEL `findMap`, `filterMap`) and churn four proofs.

## 7. Everything else read and left

- **Can be empty, so `List` is right:** `Text.lines` (`""` gives `[]`),
  `List.windows` (none when the list is shorter than `size`), `List.range`,
  `rangeFrom`, `replicate`, `Stream.take`, `Parse.repeat`/`exactly` and
  `Nat.toBits` (a count of zero gives `[]`; a `Succ n` variant would need its
  own name for no caller), `Nat.divisors` (`0` gives `[]`), `List.combinations`,
  `pairs`, `cross`, `zipWithNext`, `Parse.looseRow`/`looseGrid`,
  `Graph.universe`. `Map.keys`/`values`, `Set.toList`, `Map.min`/`max`,
  `Set.min`/`max`: there's no non-empty `Map` or `Set` type, and adding one
  is far beyond this.
- **Non-empty but not worth a type:** `Char.utf8` (1 to 4 bytes; one
  internal caller, `IO.bytesOf`), `List.scanLeft` (D3778, in hand).
- **The `Option` only for an empty input, already twinned:** `List.maximum`,
  `minimum`, `maxBy`, `minBy`, `maximumOf`, `minimumOf`, `head`, `last` all
  have total `NonEmptyList` twins. Correctly left as `Option` on `List`
  (the proposal's §8). No std `List.reduce` exists to twin.
- **Not in std at all:** permutations, `inits`, run-length encoding or
  "group adjacent equal elements". If one is added, it should give
  `List (NonEmptyList a)` (or `List (a, Nat)`), as `splitBy` does. No AoC day
  defines one locally either.

## 8. Finding outside std

`aoc/src/Aoc/Year2020/Day15/Day15.sw:72`:
`turns + starting.numbers.toList.maximum.getOrElse 0 + 1`, where
`Starting.numbers: NonEmptyList Nat` (line 37). It should be
`starting.numbers.maximum`, no fallback; `Proofs/Turns.sw:16` states the
same shape and would use `NonEmptyList.maximumToList` or a `NonEmptyList`
lemma. A small Sonnet ticket. (The other `.headOr` / `.getOrElse` fallbacks
in AoC, about 60 lines, are on data types of the days, `Image.rows`,
`Report`, `lines.headOr ""` after `Text.lines`, which the proposal's N7
sweep covers per day, not std producers.)

## 9. A general mechanism instead of twins? (language design question for Matt)

The cost of every change above, and of D3778's `scanLeft`, is the same
shape: `NonEmptyList` lacks a `List` method, so the caller writes `.toList`.
What the surveyed callers reach for that `NonEmptyList` doesn't have:
`filter`, `filterMap`, `drop`, `take`, `withIndex`, `mapWithIndex`, `sum`,
`product`, `toSet`, `unique`/`dedup`, `findMap`, `zipWith` with a `List`, and
`Text.join`/`joinWith` on a `NonEmptyList Text`. Most were planned in the
proposal's §8 ("Give a plain `List`: `toList`, `filter`, `filterMap`, `take`,
`drop` … written out so dot notation finds them") but not written. The
`scanLeft` callers show the same gap: `.scanLeft … |> .drop 1 |> .count`
(2025 day 1), `|> .zipWith turns …|> .sum`, `|> .map … |> .dedup` (2024
day 9).

Two ways out:

- **Write the twins** (today's approach): about 12 one-line definitions,
  each `List.f xs.toList`, with `rfl` bridges. In the split survey this takes
  the `.toList` count from 18 of 37 sites to about 4.
- **A fallback rule for dot calls:** where `xs: NonEmptyList a` and
  `NonEmptyList.f` doesn't exist, `xs.f` resolves to `List.f xs.toList`
  (a declared "view" from one namespace to another, in the spirit of Lean's
  dot notation through a structure's parent). That removes the twin-writing
  for every future producer, but it is a new resolution rule and edges toward
  the coercions D1069 ruled out, and a missing total twin (say a future
  `NonEmptyList.minimum`) would silently resolve to `List`'s `Option` one.

Counts: at the end state after #1-#3 and D3778, `.toList` would appear about
4 times at the split sites, 0 at `oneOf`/`span1`, and 1 to 3 per `scanLeft`
caller that uses a missing method, so roughly 15 to 20 across the repo
without twins and under 10 with them. **That doesn't by itself justify a
language proposal**: a dozen one-line twins close most of it. It would if
`NonEmptyList` producers keep spreading (the N7 sweep moving AoC data types
over is the likely driver), in which case a short note in
`docs/proposals/` comparing the two is the next step. Matt's call.
