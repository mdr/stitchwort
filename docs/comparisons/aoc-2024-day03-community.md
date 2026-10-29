# AoC 2024 day 3: community solutions in other languages

**Date:** 29 October 2026. **Ticket:** SW-879. **Our version:** finished before this note:
`aoc/src/Aoc/Year2024/Day03/`, with part 2 proved for every list of instructions, and the
friction notes in `aoc/NOTES-2024.md` ("## Day 3"). The puzzle: corrupted memory holds
instructions like `mul(44,46)`, where each number has one to three digits, scattered through
noise. Part 1 adds up the products of the well-formed `mul`s. Part 2 also obeys `do()` and
`don't()`, which turn the `mul`s after them on and off. The input is
`aoc/inputs/2024/day03.txt`: 17,962 bytes on six lines. The answers are 174,960,292 and
56,275,602.

Like the day 9 note ([aoc-day09-community.md](aoc-day09-community.md)), this one compares
finished code: length, readability, speed, and what is proved at what cost. Day 3 is a scanning
puzzle, so the main questions are how our `Std.Parse` grammar reads beside regex and
combinator solutions, and who proves anything about a parser.

The labels are as before:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked page;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, but not confirmed.

Where things are:

- **Scratch area:**
  `/private/tmp/claude-501/-Users-matt-repos-mdr-stitchwort/3eef38f5-69c2-4f26-b1b3-39bd97dd0fd4/scratchpad/d2024-03/`.
  The fetched files are in `gh/files/`, the repository trees in `gh/trees/`, the megathread JSON
  in `arctic/`, and the Stitchwort scratch project in `proj/`.
- **Committed copies:** the scripts are in
  [aoc-2024-day03-community/scripts/](aoc-2024-day03-community/scripts/), and the Stitchwort
  scratch programs and timing drivers in `scripts/sw/`. The per-author method table is
  [classify.tsv](aoc-2024-day03-community/classify.tsv), and the raw timings are in
  [timings.txt](aoc-2024-day03-community/timings.txt).
- **Binary:** the main checkout's `target/release/stitchwort` as of 29 October, not rebuilt.
- **Timings:** wall clock and peak memory from `scripts/time3.sh`, two or three runs each, on
  a laptop running other lanes at the same time. They include process start-up. Treat them as
  rough, to a factor of about 1.5.

## 1. Summary

I fetched day 3 files from **227 GitHub authors**, one per author: 24 in Lean 4, 3 in Idris 2,
and one each in Agda and Dafny, plus 11 in Roc, 2 in Prolog, and the rest in Clojure, Elixir,
Haskell, Scala, F#, Gleam and OCaml (§2.1). I also read the r/adventofcode "2024 Day 3
Solutions" megathread through the Arctic Shift archive: 995 live top-level comments, 122 of them
in functional or array languages, with one each in Lean, Dafny and Roc (§2.2). There was no
Coq/Rocq, F\*, Isabelle, Koka or Unison day 3 in either source.

How Stitchwort compares:

1. **We are the only ones who prove anything about the answer, and nobody proves anything about
   their parser, including us.** No solution I found has a theorem about part 1 or part 2.
   The nearest things: andrewmw94's Lean has one theorem, a termination fact for its string
   scan, and it ends in `sorry`. shilangyu's Lean defines regular expressions and their
   matching relation, then proves by about 30 tactic steps that `"mul(30,5)"` matches its `mul`
   pattern. It computes no answer. jhgarner's Lean carries a proof field `lhs < 1000 ∧ rhs <
   1000` in each `mul`. BrianNormant's Idris is `%default total` and uses `Text.Parser`'s
   `Grammar`, whose type says whether a parser must consume input. hath995's Dafny opts out of
   termination with `decreases *` **[checked: read the 29 proof-language files; `grep` for
   theorem, lemma, ensures, sorry, Refl, decide, #guard, expect]**. Our `part2Correct`,
   `part2WithoutDont` and `part2AtMostPart1` hold for every instruction list. The parser is
   tested (30 tests, edge cases and error messages) but not proved. On proofs we are far ahead,
   but they stop exactly where this puzzle's difficulty is.
2. **The puzzle's rules are stricter than most solutions, and the input never tests them.** Of
   148 inline megathread regexes that a test harness could run, 75 accept a four-digit number
   such as `mul(1234,5)`, which the puzzle rules out ("X and Y are each 1-3 digit numbers").
   Three accept spaces and one a minus sign **[checked: `scripts/mulre3.py`]**. On GitHub, only
   3 of the 42 combinator solutions limit the digits at all **[inferred: regex tags in
   `classify3.py`, spot-read]**. None of this changes an answer: the real input has no `mul`
   with a longer number, so `\d+` and `\d{1,3}` agree **[checked: `scripts/regex3.py`]**.
   Ours reads the rules exactly (`natDigits 1 3`, no spaces, no sign) and tests each one.
3. **Length: ours is mid-pack, about twice the shortest, and the shortest bend the rules.** Our
   program is 37 code lines (65 with comments). The GitHub median is 44. A Python
   `re.finditer` solution is about 10. The shortest functional ones are 16 and 17 lines:
   LHolten's Lean, tromp's and ephemient's Haskell. Each of them is lax about the digits or the
   spaces (§4). mniip's Lean is the closest match to ours in shape (an instruction type, a
   choice of three alternatives, a fold) at 31 lines. It reads numbers with `int`, so it takes
   `mul(-1,2)`.
4. **Readability: the grammar reads as well as the best combinator code, and better than any
   regex.** `text "mul("`, `natDigits 1 3`, `char ','` and `pick [("do()", Do), ("don't()",
   Dont)]` say what the puzzle says. Only Prolog's DCGs (Liezere: two rules for part 1) are
   terser and as clear. `findAll` and `natDigits` are both in Std now; the friction notes'
   items 1 and 3 are fixed.
5. **Speed: correct, but slow, and the native build loses to JS on this program.** On the real
   input: `run` 0.55 s, `run --js` 0.50 s, native 0.14 s. Start-up is 0.20 s, 0.32 s and 0 s
   **[checked]**. Python's regex takes 0.4 ms in-process **[checked]**; bosyluke's Roc reports
   2 ms and 1 ms for the two parts **[cited: megathread]**. On the input repeated 100 times
   (1.8 MB), the native build takes 13.5 s against JS's 3.7 s. A pure hand-written scanner
   (`Scan.sw`) takes 0.76 s native and 0.83 s JS. So the native gap is in effect handling, not
   in list code **[inferred]**. `findAllStarting` (`m` or `d`) cuts the native time 7-fold on
   the real input (0.14 s to 0.02 s) and 8.5-fold at 1.8 MB (§5).

## 2. The solutions

### 2.1 GitHub

Method **[checked: scripts]**:

1. Started from the day 1 lane's 34 proof-language repositories and the 88 repositories linked
   from functional or proof-language megathread comments (`known.tsv`).
2. `repos3.py`: `gh search repos` for "advent of code 2024", "aoc 2024" and "aoc2024" per
   language. That gave up to 40 hits per query for proof languages and 12 for functional ones,
   so the functional side is a sample. Search's rate limit (shared with two other lanes) cut
   the first pass short, and a slower second pass for Agda, Dafny, Coq, Koka, Roc and Idris found
   11 new repositories, all Roc. 344 repositories in all.
3. `find3.py`: listed each repository's tree and kept the files that look like 2024 day 3,
   at most three per repository. That found 281 files in 236 repositories.
4. `fetch3.py`: fetched them from raw.githubusercontent.com. `classify3.py` kept the files that
   mention `mul` (or the character `'m'`, for list patterns), one repository per author, and
   tagged them by method with regexes. The tags are leads, not verdicts.

Authors by language: Clojure 28, Elixir 28, Haskell 27, Scala 26, F# 25, Lean 24, Gleam 23,
OCaml 23, Roc 11, Idris 3, Prolog 2 (two other `.pl` files were Perl), Common Lisp 3, and one
each in Agda, Dafny and Julia. That makes 227. GitHub's "Unison" language filter returned
other languages' repositories. I found no Unison day 3 and no Coq, F\*, Isabelle or Koka at all.

Methods, from the tags **[inferred: `classify.tsv`]**:

| method | authors | limit the digits to 1-3 |
|---|---|---|
| regex | 145 | 54 |
| parser combinators (a library, or a parser monad of their own) | 42 | 3 |
| by hand: prefix tests, list patterns, `splitOn "mul("` | 20 | 0 |
| other (state machines, folds over characters) | 20 | 2 |

By language, Clojure, Elixir, Scala, F#, OCaml and Gleam are mostly regex. Haskell (15 of 27)
and Lean (10 of 24) lean towards combinators, and Roc has no regex library in its standard
library, so it splits between its `parser` package and hand scans. For part 2, 20 authors split
the text on `don't()` and `do()` instead of tracking a flag.

I read all 29 proof-language files (Lean, Idris, Agda, Dafny):

- **Lean (24).** 10 use `Std.Internal.Parsec` or a parser of their own, 6 the `Regex` package
  (`regex% r"mul\((\d+),(\d+)\)"`), and 8 scan by hand with `dropPrefix?`, `takeWhile` and
  loops. 8 of the 24 use `partial def`, for hand scans and for combinator loops alike, so Lean
  doesn't check that they end. andrewmw94 tried `termination_by s.length` and left the
  `decreasing_by` lemma as `sorry`. mfornet wrote the regex as a 13-state automaton by hand.
  Three Lean authors limit the digits by count: alok reads `digit`, `optional digit`, `optional
  digit`; josephjunker uses `takeUpTo 3 ASCII.numeric`; and main-- uses `\d\d?\d?`. crvdgc (`n > 1000` fails) and jhgarner (`< 1000`) check the value instead, so they
  take `mul(0012,5)`, which has four digits.
- **Idris 2 (3).** BrianNormant lexes with `Text.Lexer` (`exact "mul"`, `digits`, `any`) and
  parses with `Text.Parser` under `%default total`. The parser's type says it consumes input,
  `Grammar state ProgToken True (Integer, Integer)`, and that is what lets `some` be total. The
  result type is still a hole (`?td`). BenBean18 and AugustUnderground scan by hand with
  `isPrefixOf`.
- **Agda (1).** aaronallen8455 writes a `State (List Char × Bool)` parser with `spanᵇ isDigit`
  and a length test (`> 0` and `< 4`). It is the only proof-language file that limits the
  digits by count, and it has no proofs.
- **Dafny (1).** hath995 ported a small regex engine to Dafny before AoC ("Dafny lacks them in
  its standard library … barely able to handle the task" **[cited: megathread]**). Its methods
  are `decreases *` and its checks are `expect`.

Roc (11) and Prolog (2), for the same reason as day 9. Roc has no regex in its standard library,
so five authors use the `parser` package (`Parser.const … |> Parser.skip (string "mul(") |>
Parser.keep digits`) and the rest split or scan, with `expect` tests on the examples. Prolog's
DCGs are the tersest grammar here. Liezere's part 1 is `mul_op(X-Y) --> string(_), "mul(",
number(X), ",", number(Y), ")".` with `sequence(mul_op, Ops), string(_)` around it
**[checked]**.

### 2.2 The Reddit megathread (via the Arctic Shift archive)

`arctic.py` made two requests: a post search for 3 December 2024 05:00 UTC, which found
`1h5frsp` "-❄️- 2024 Day 3 Solutions -❄️-" (1,620 comments), and its comment tree. That gave
1,011 top-level comments, 995 of them live, and 929 with a language tag **[checked]**. Python
227, Rust 95, Go 68, C 66, JavaScript 51, … Haskell 24, Elixir 18, Scala 11, Clojure 10, OCaml
6, Gleam 6, F# 3, and one each in Lean, Dafny, Roc and Erlang (`langs3.py`).

Word counts over live top-level comments (upper bounds; `langs3.py`, `words.txt`): a regex
mentioned in 615, a parser combinator in 28, a hand scanner or "no regex" in 49, a split on
`don't()` in 54, `eval` in 27. In the code itself, `{1,3}` appears in 161 and `\d+` in 168.

`mulre3.py` took the first `mul` regex line from each comment (343 comments) and ran the 148
that Python could compile, and that the harness read right on the puzzle's own positive
cases, against 12 edge cases **[checked]**:

| edge case | regexes that get it wrong (of 148) |
|---|---|
| `mul(1234,5)`, a four-digit first number | 72 |
| `mul(12,3456)`, a four-digit second number | 71 |
| `mul(1, 2)`, a space | 3 |
| `mul(-1,2)`, a sign | 1 |
| right on all 12 | 73 |

On the real input there is no `mul` with a longer number, so all of them give the right answers.

Comments about the method, in the functional languages:

- mstksg (Haskell): "You can think of the whole thing is essentially a state machine / finite
  automata." Part 2 is two mutually recursive parsers, `goEnabled` and `goDisabled`, each a
  `dropUntil` around a choice. His `parseMul` is `product <$> P.between "mul(" ")"
  (PL.decimal `P.sepBy` ",")`, which also takes `mul(1,2,3)` and gives 1 for `mul()`
  **[cited]**.
- Xyberista (Haskell): "I couldn't figure out how to parse the input with just Megaparsec for a
  while and ended up also using Replace.Megaparsec" **[cited]**. That is the library behind
  friction item 1, now `Parse.findAll`.
- sondr3\_ (Haskell): uses Megaparsec's `symbol` and `lexeme`, which skip spaces, so it accepts
  `mul ( 2 , 4 )`, which the puzzle says "does nothing" **[cited; inferred from Megaparsec's
  `symbol`]**.
- WhiteSparrow (Prolog): "Prolog's DCG's are so, so nice - no regex required" **[cited]**.
- marx38 (Lean): "implements required regex manually" **[cited]**.

Nobody in the megathread mentions a theorem, a lemma or a verified parser. In the whole tree of
1,851 comments, the few hits on "verify" are about checking a regex by hand **[checked]**.

## 3. The parser: who proves what

| who | what is proved or enforced about the parser | the answer |
|---|---|---|
| **Stitchwort (ours)** | Nothing proved; 30 tests, including every edge case of §2.2 and four error messages | part 2 = the spec, for every instruction list; part 2 = part 1 without `don't()`; part 2 ≤ part 1 |
| shilangyu (Lean) | A regex type, its matching relation as an inductive `Prop`, and one proof by tactic steps that `"mul(30,5)"` matches `mulPattern` | none computed |
| jhgarner (Lean) | Each parsed `mul` carries `lhs < 1000 ∧ rhs < 1000` (but `0012` passes) | none |
| BrianNormant (Idris) | Totality, from the `consumes` index of `Grammar` | none |
| andrewmw94 (Lean) | The scan ends, by `termination_by`, with the lemma left as `sorry` | none |
| everyone else | `#guard` / `expect` / `test` checks on the puzzle's examples, at most | none |

The libraries behind these do more than their users. Idris 2's `Text.Parser.Core` documents that
"the `consumes` flag is True if the language is guaranteed to be non-empty" **[cited:
`libs/contrib/Text/Parser/Core.idr`, fetched to `refs/`]**. agdarsec is "Total Parser
Combinators in Agda", ported to Coq (parseque) and Idris **[cited: its README]**. Neither proves
what a parser accepts. Totality is the guarantee that these languages give by type.

Our `Std.Parse` gets totality differently: `many`, `findAll` and `repeat` run on fuel (the
characters left, plus one), so nothing needs `partial`, and an Idris-style index isn't needed
**[checked: `Parse.findAllFuel`, `Parse.manyFuel`]**. What we lack is the next step, a proof of
what `parseInstructions` returns. `docs/proposals/parser-combinators.md` already says why:
there is no lemma for `optional p` or `oneOf` over an arbitrary `p`, because the handler wraps
every operation of `p`, and moving a fact under it is an induction over `p`'s computation tree
(§7 there, "Not proved"). Concrete runs do compute (`Parse.run "mul(2,4)".toList instruction =
Ok (Mul 2 4) := rfl`, friction item 6). **[cited: the proposal; checked: friction notes]**

A cheaper route to a parser guarantee, short of that lifting: `Scan.sw` (§5) is a pure, total
scanner that gives the same answers in 31 code lines. Pure code is something our proofs already
handle well. Proving `Scan.scan` against a spec of "leftmost non-overlapping matches", and
`parseInstructions` equal to it by tests on random noise, would be a real first. Nobody in
either source did either **[inferred]**.

## 4. Length and readability, side by side

Code lines, not counting blank or comment-only lines:

| solution | lines | method | rules followed in general? |
|---|---|---|---|
| Python, `re.finditer` with `mul\((\d{1,3}),(\d{1,3})\)\|do\(\)\|don't\(\)` (`regex3.py`'s core) | ≈10 | regex | yes |
| LHolten (Lean) | 16 | `splitOn "mul("`, `takeWhile isDigit`; part 2 `splitOn "do()"` then before `don't()` | no digit limit |
| tromp (Haskell) | 17 | `tails`, a `'m':'u':'l':s` pattern, then `reads s :: [((Int,Int),String)]` | `reads` takes spaces and signs: `mul( 2 , 4 )` counts |
| ephemient (Haskell) | 17 | `T.splitOn "mul("`, `T.decimal`; part 2 split as LHolten | no digit limit |
| Liezere (Prolog) | 27 | DCG | `number//1` reads any number **[unverified]** |
| mniip (Lean) | 31 | combinators, `foldlMany`, a fold | `int` takes `-1` |
| **Stitchwort, `Day03.sw`** | **37** | `Std.Parse`: `findAll`, `oneOf`, `natDigits 1 3`, `pick`, a fold | **yes, and tested** |
| mstksg (Haskell) | 37 | Megaparsec, two mutually recursive parsers for part 2 | `sepBy` takes `mul(1,2,3)` |
| GitHub median, all 227 | 44 | | |

Ours and mniip's, the two with the same shape:

```stitchwort
def instruction(): {Parse} Instruction :=
  oneOf [
    () =>
      text "mul("
      let left := shortNumber()
      char ','
      let right := shortNumber()
      char ')'
      Mul left right,
    () => pick [("do()", Do), ("don't()", Dont)]
  ]

def parseInstructions (memory: Text): {Fail} (List Instruction) := Parse.all memory (() => findAll instruction)
```

```lean
def parser : Parser (Array Insn)
  := (some <$> insn <|> Functor.mapConst none anyChar).foldlMany
    (λa m => Option.elim m a a.push) #[]
  where
    insn :=
      (string "mul(" *> Insn.Mul <$> int <* string "," <*> int <* string ")")
        <|> (Functor.mapConst Insn.Do $ string "do()")
        <|> (Functor.mapConst Insn.Dont $ string "don't()")
```

My judgement **[inferred]**: ours needs no operator vocabulary (`<$>`, `*>`, `<*`,
`Functor.mapConst`) and no hand-made "skip a character or match" loop. `findAll` is the
puzzle's "everything else is noise" in one word. mniip's is shorter and is fine for a reader
fluent in applicatives. The regex is shorter than both, and it is the version most people would
recognise, but it says nothing about the shape of what it returns. Python then pulls apart
`m.group(0)` by string comparison. Our part 2 is a seven-line `Tally.step` fold. The shortest
Haskell (`go m True s@(_:s') = getmul s + go m True s'`) is tighter, but its `reads` trick only
works because Haskell's tuple `Read` happens to look like `(2,4)`.

Where we are clumsier: a `do`-less ability style makes us bind each piece with `let`, so a
grammar line like `string "mul(" *> Mul <$> int <* string "," <*> int <* string ")"` becomes six
lines. That is a trade we chose (direct style), and it reads well, but it is not short.

## 5. Speed

### 5.1 Our program and the alternatives, in Stitchwort

Four scratch programs in `scripts/sw/`, each giving both answers **[checked]**:

- `Day03.sw`, the program: `findAll instruction`.
- `Starting.sw`: the same grammar with `findAllStarting (char => char == 'm' ∨ char == 'd')`,
  which skips noise with one `span`.
- `Scan.sw`: no `Std.Parse`, a pure recursive scan over `List Char` with
  `Text.stripPrefixChars`, as tromp's Haskell does.
- `Split.sw`: part 2 by the split trick (`splitOn "don't()"`, then what follows each `do()`),
  then part 1's parser on what is left.
- `Hello.sw`: read the input and print its length, for the start-up cost.

Real input (18 KB), wall-clock seconds, the middle of three runs (`time3.sh`):

| program | `run` | `run --js` | native (`build --native`) |
|---|---|---|---|
| Hello (start-up) | 0.20 | 0.32 | 0.00 |
| **Day03 (`findAll`)** | **0.55** | **0.50** | **0.14** |
| Starting (`findAllStarting`) | 0.38 | 0.49 | 0.02 |
| Scan (pure) | 0.28 | 0.40 | 0.01 |
| Split | 0.67 | 0.56 | 0.19 |

The input repeated 10 times (180 KB) and 100 times (1.8 MB), one or two runs:

| program | ×10 `run` | ×10 JS | ×10 native | ×100 JS | ×100 native |
|---|---|---|---|---|---|
| Day03 | 2.52 | 0.79 | 1.33 | 3.68 (304 MB) | 13.5 (200 MB) |
| Starting | 0.66 | 0.56 | 0.16 | 1.22 | 1.58 |
| Scan | 0.47 | 0.45 | 0.08 | 0.83 | 0.76 (114 MB) |
| Split | 3.50 | 1.00 | 1.89 | 5.86 | 18.8 |

What this shows **[inferred from the tables]**:

- **`findAll` costs about 7.5 µs a character natively**, linearly (1.33 s at 180 KB, 13.5 s at
  1.8 MB). Each try at a character makes a dozen or so operations across two or three handlers.
  The proposal measured the same on the interpreter ("about 12 µs a character of noise").
- **The native build is 3.7 times slower than JS on handler-heavy code and level with it on
  pure code.** Day03 and Split, which are dominated by `findAll`, lose. Scan, which has no
  handlers, is even. SW-593 (the effect representation: "allocation+freeing 49% vs dispatch
  14%", deferred until NO5–NO7) is the ticket this points at. Whether the gap is SW-593's
  allocation cost and not something else is **[unverified]**.
- **`findAllStarting` is the cheapest large win**: 7 times faster natively on the real input.
  Its correctness rests on the caller's claim that every match starts with `m` or `d`, which is
  obvious here but not checked.
- **Start-up dominates `run` on the real input**: 0.20 s of 0.55 s. After that the interpreter
  takes 0.35 s and JS 0.18 s.
- Memory: native peaks at 200 MB for 1.8 MB of input with `findAll`, and at 114 MB for the pure
  scan, whose cost is mostly the `List Char` (about 60 bytes a character) **[inferred]**.

### 5.2 Against the community

Python's `re.finditer` does both parts in 0.4 ms on the real input and 32 ms on 1.8 MB,
in-process **[checked: `regex3.py`]**. That is 350 times faster than our native `findAll` and
24 times faster than our native pure scan. bosyluke's Roc reports "SOLVING PART 1: 2ms, SOLVING
PART 2: 1ms" with its parser package **[cited]**. I didn't run the compiled Haskell, OCaml or
Lean solutions. From day 9's measurements, I expect them in the low milliseconds
**[unverified]**. On the real input every version of ours finishes in well under a second, so
this matters for larger inputs and for the "is Stitchwort fast" story, not for day 3.

## 6. Proofs and costs, and what to improve

What we proved, and its cost (from the friction notes, **[checked]**): the spec is 17 lines
(`Spec.sw`), quoting the puzzle's rules. The proofs are 87 code lines, with no axioms:
`tallyAfter` by induction on a prefix length, `part2Correct` by `calc`, `foldWithoutDont` by
cases, and `part2AtMostPart1` by `omega`. They took `rewrite Nat.addZero` and
`match … with | True | False` workarounds (friction items 8 and 9), and std gained
`List.takeSucc` and `List.lastSnoc` for them. Against the community the comparison is short.
Nobody else proves any answer, so nobody proves more, or with less effort.

The honest caveat: part 2's logic, the part we proved, is the easy half of this puzzle. The
community's real mistakes (four digits, spaces, signs, `sepBy`) are all in the parser, and there
we have tests, not proofs. They are good tests, covering every case of §2.2, but they are what
the Roc and Lean `expect`/`#guard` authors have too, only more of them.

One small friction point from writing `Scan.sw` **[checked]**: recursing on what follows a
match (`scan … after`, where `after` comes from `stripPrefixChars`) is refused with
`E-TERMINATION` ("the 4th argument, `after`, isn't seen as smaller"). Recursing on the next
character works, and is right for this grammar, because no match can start inside another. A
jump would need `decreasing chars.length` and a lemma that `stripPrefixChars` returns something
shorter, which std doesn't have **[checked: `grep` in `std/`]**. Lean's authors hit the same
wall and wrote `partial def`.

### 6.1 Candidate improvements, ranked by value over effort

| Rank | Candidate | Kind | Value | Effort | Evidence |
|---|---|---|---|---|---|
| 1 | **Add day 3's numbers to SW-593**: native is 3.7× slower than JS on `findAll` (13.5 s against 3.7 s at 1.8 MB) and even on pure code | runtime | sharpens an existing ticket; `Std.Parse` runs on every AoC day | trivial | §5.1 |
| 2 | **Point `findAll`'s doc comment, and the `Std.Parse` guide, at `findAllStarting` for literal-led grammars**, with day 3's 7× as the example | docs | the fast path is there but easy to miss: our own program doesn't use it | trivial | §5.1 |
| 3 | **A `List.stripPrefix`/`Text.stripPrefixChars` length lemma** (the rest is no longer than the input, and shorter for a non-empty prefix) | library | lets hand scanners jump past a match with `decreasing`, the thing Lean users reach `partial` for | small | §6 |
| 4 | **A property test: `parseInstructions` against `Scan.scan` on random noise built from the puzzle's fragments** | test | the first check of the parser beyond chosen cases; cheap insurance for `Std.Parse` changes | small (Std has `Random`) | §3 |
| 5 | **Prove `Scan.scan` against a leftmost-match spec** | proof | the first proof about a day 3 parser that I can find anywhere; shows pure scanners are provable now | medium | §3 |
| 6 | **Lifting lemmas for `optional`/`oneOf`/`findAll`** (the proposal's "Not proved") | library proof | would let the `Std.Parse` grammar itself be proved | large (an induction over computation trees) | §3 |
| — | Shorter grammar syntax (an applicative `*>`/`<*` style) | language | ours is longer, not less clear; direct style is a settled choice | — | §4 |

## 7. Decisions for Matt

| ID | Decision | Recommendation |
|---|---|---|
| D1650 | SW-593 (the native effect representation) is deferred until NO5–NO7 finish. Day 3 shows native at 3.7× JS's time on `Std.Parse`'s `findAll`, while pure code runs level. Keep it deferred, or move it ahead of what is left of NO5–NO7? | [keep it deferred, but add §5.1's numbers to SW-593; no AoC day is slow enough to need it yet, and the standalone binary comes first] |
| D1651 | Day 3's parser is tested, not proved. Do we aim to prove parsers at all: the cheap route (prove a pure scanner like `Scan.sw` against a spec, and property-test `Std.Parse` against it), the full route (lifting lemmas for `optional`/`oneOf`/`findAll`), or neither for now? | [the cheap route, as a one-day experiment on day 3 (candidates 4 and 5); leave the lifting lemmas until a second puzzle needs them] |
| D1652 | Should day 3's program switch to `findAllStarting (char => char == 'm' ∨ char == 'd')`? It is 7× faster natively, but the claim that every match starts with `m` or `d` is unchecked. | [no: keep `findAll` as the reference a user writes first, and record the faster form in the notes and in `findAll`'s doc comment (candidate 2)] |

---

**Status** (29 October 2026): SW-879, this note, is done once reviewed. D1650 (SW-593's
priority), D1651 (whether to prove parsers) and D1652 (`findAllStarting` in day 3) are pending.
