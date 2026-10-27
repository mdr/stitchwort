# Proposal: a parser library for puzzle input

**Status:** draft 1, 27 October 2026, for review. Research only: nothing here is in std. The experiments are scratch files, not committed (listed in [Appendix A](#appendix-a-experiments)).

Matt asked for a std parser-combinator library for turning puzzle input (Advent of Code first, but not only) into the program's own types. This note looks at how other languages do it, tries the main options in Stitchwort, and recommends one.

Tags: **[source]** read in this repository, **[ran]** run in a scratch file with the release build of `main` (27 October), **[web]** checked online (linked), **[inferred]** reasoned but not run, **[speculative]** a guess.

## 1. The recommendation in brief

- **A parser is ordinary direct-style code with two abilities, `{Parse, Fail}`.** `Parse` holds the input; `Fail` is the existing failure ability, so `ensure`, `need`, `toNatOrFail` and `Fail.context` work inside parsers unchanged. Code reads like today's AoC `parse` functions:

  ```
  def point(): {Parse, Fail} Point :=
    let x := nat()
    char ','
    let y := nat()
    char ','
    let z := nat()
    { x, y, z }

  def parsePoints (input: Text): {Fail} (List Point) := Parse.all input (() => lines point)
  ```

  A bad line fails with `line 3, column 6: expected ','`.
- **The operations are token-sized, not character-sized.** "Read the digits here" is one operation, so a line costs a handful of operations. Character-sized operations made parsing 25 to 33 times slower than today's `split` (§7).
- **Choice backtracks locally, as in a PEG.** `oneOf`, `optional` and `many` put the input back when an alternative fails. Nothing is ever retried after a choice has returned. There's no `try` to remember.
- **Loops are total because each repetition must read something.** `many` stops (or fails, see the open choices) if its parser matches without reading. Its fuel is the number of characters left, which is always enough.
- **Errors name the furthest point any alternative reached**, and everything expected there: `expected a number or ','`. Positions are counted as one number while parsing and turned into a line and column once, at the end.
- **For one-line formats, a pattern function**: `line.scan "p={},{} v={},{}"` gives the four texts between the literal pieces. Later, possibly, the same thing as a pattern in `match` (§6.3).

Rejected, with reasons in §4 and §7: parsers as data values (`Text → Result (a, Text)`), which read badly without do-notation or operators; nondeterminism (`Each`) as the way to backtrack; character-sized operations.

## 2. What today's AoC parsers need

Every `parse*` function in `aoc/src/Aoc/` **[source]**:

| Day | Input | Today | Needs |
|---|---|---|---|
| 2024 day 1 | `3   4` per line | `line.words.map Text.toNat`, match on `[Some a, Some b]` | numbers, a run of spaces, lines |
| 2025 day 1 | `L68` per line | `line.trim.uncons`, then `need rest.toNat` | a keyword table (L or R), a number |
| 2025 day 2 | `11-22,95-115` on one line | `text.trim.split ','` then `Range.parse` | a separated list, a range, spaces |
| 2025 day 3 | a row of digits per line | `line.trim.toList`, `need char.toDigit` | single digits, at least *n* of them |
| 2025 day 4 | grid of `@` and `.` | `findStray` for errors, then `Vec.ofList` per row | a grid of cells, line and column in errors, equal widths |
| 2025 day 5 | ranges, a blank line, ids | `takeWhile (.trim ≠ "")`, `parseLinesFrom` to keep line numbers right | two sections, line numbers that run across both |
| 2025 day 6 | a worksheet read in columns | transpose the character grid, split at blank columns | layout, not grammar: out of scope (§6.4) |
| 2025 day 7 | grid of `.`, `^`, `S` | `manifoldError` for errors, then find S | a grid of cells, line and column in errors |
| 2025 day 8 | `162,817,812` per line | `line.split ','`, match on `[Some x, Some y, Some z]` | numbers separated by commas |
| 2025 day 9 | `7,1` per line | as day 8 | as day 8 |

`Aoc.Common.parseLines` adds `line 3: ` to a failing line's message with `Fail.context`; day 5 needs `parseLinesFrom` so the ids' line numbers count the ranges and the blank line. Days 4 and 7 write their own loops to report `line 2, column 5`.

So the core set is: numbers (natural and signed), a literal, a keyword table, single characters by a test, a run of characters by a test, spaces, a line break, the end; then optional, choice, many, at-least-one, separated-by, lines, sections (blocks between blank lines), and a grid. Recursive grammars (2022 day 13's nested lists) need one more piece, §5.3.

## 3. What others do

### 3.1 The libraries

| Library | Parser is | Backtracking | Loops that read nothing | Errors | Link |
|---|---|---|---|---|---|
| Parsec (Haskell) | a monad | `p <\|> q` tries `q` only if `p` failed *without consuming input*; `try p` lifts that | `many` raises a run-time error: "combinator 'many' is applied to a parser that accepts an empty string" | position, expected items | [docs](https://hackage.haskell.org/package/parsec-3.1.17.0/docs/Text-Parsec.html), [source](https://hackage.haskell.org/package/parsec-3.1.17.0/docs/src/Text.Parsec.Prim.html) **[web]** |
| Megaparsec (Haskell) | a monad transformer | as Parsec; `try` "backtracks the parser state when p fails (either consuming input or not)" | not documented on the module page | line and column via `SourcePos`, `errorBundlePretty`; `label` / `<?>` names what was expected | [docs](https://hackage.haskell.org/package/megaparsec-9.6.1/docs/Text-Megaparsec.html) **[web]** |
| attoparsec (Haskell) | a monad, incremental | "attoparsec parsers always backtrack on failure"; `try` is only for Parsec compatibility | — | deliberately poorer than Parsec: "avoids the extra book-keeping in favour of higher performance" | [docs](https://hackage.haskell.org/package/attoparsec-0.14.4/docs/Data-Attoparsec-ByteString.html) **[web]** |
| Angstrom (OCaml) | a monad, a port of attoparsec | "backtracking by default and support unbounded lookahead" | — | its own comparison table says it doesn't report line numbers | [README](https://github.com/inhabitedtype/angstrom) **[web]** |
| Parseff (OCaml 5) | `unit -> 'a`: direct style, effects underneath | `or_` "backtracks (resets the cursor)" | not documented | the branch that "reached the furthest position" is reported | [docs](https://ocaml.org/p/parseff/0.3.0/combinators.html) **[web]** |
| fastparse (Scala) | methods taking an implicit context, inlined by macros | full, until a cut `~/`: past it "it can no longer backtrack"; cuts also sharpen errors | — | one index plus label, line:column; `.trace()` re-runs for detail | [docs](https://com-lihaoyi.github.io/fastparse/) **[web]** |
| cats-parse (Scala) | a data type; `Parser` must consume on success, `Parser0` may not | `orElse` recovers only from failures that consumed nothing ("epsilon failures"); `backtrack` rewinds | `rep` exists only on `Parser`, so a repeated parser always consumes | `Error(input, failedAtOffset, expected)` | [README](https://github.com/typelevel/cats-parse) **[web]** |
| nom (Rust) | functions on slices | per combinator | `many0` "will return an error, to prevent going into an infinite loop" | error kinds, positions as slices | [many0](https://docs.rs/nom/latest/nom/multi/fn.many0.html) **[web]** |
| winnow (Rust) | functions on a stream | `ErrMode::Backtrack` vs `cut_err` | `repeat` errors "to prevent going into an infinite loop" | contexts, cut errors | [repeat](https://docs.rs/winnow/latest/winnow/combinator/fn.repeat.html) **[web]** |
| chumsky (Rust) | combinator values | full | not documented on the overview | error recovery, labelled patterns; left recursion and memoisation are opt-in | [docs](https://docs.rs/chumsky/latest/chumsky/) **[web]** |
| Lean 4 `Std.Internal.Parsec` | `ι → ParseResult α ι` | `orElse`: "if it fails without consuming input, run `q ()`"; `attempt` rewinds | `manyCore` is a `partial def`, so nothing about it can be proved | `eof` or a message, with a position | [source](https://github.com/leanprover/lean4/blob/master/src/Std/Internal/Parsec/Basic.lean) **[web]** |
| Koka `std/text/parse` | effect `parse`: `satisfy`, `fail`, `pick`, `current-input` | the handler resumes `pick` with `True`, and on failure restores the input and resumes with `False`: full backtracking | `many` calls itself through `pretend-decreasing`, which sidesteps Koka's termination check | a message and the rest of the input | [source](https://github.com/koka-lang/koka/blob/master/lib/std/text/parse.kk) **[web]** |
| Effekt (case study) | effects `Nondet` (`alt`, `fail`) and `Lexer` (`peek`, `next`) | `alt` resumes with `true`, then with `false` if the rest failed: full backtracking | — | messages | [case study](https://effekt-lang.org/docs/casestudies/frontend) **[web]** |
| Idris 2 `Text.Parser` | `Grammar state tok (consumes: Bool) ty` | `<\|>` | `many : Grammar state tok True a -> Grammar state tok False (List a)`: the type demands a consuming parser | not checked | [Core.idr](https://github.com/idris-lang/Idris2/blob/main/libs/contrib/Text/Parser/Core.idr), [Parser.idr](https://github.com/idris-lang/Idris2/blob/main/libs/contrib/Text/Parser.idr) **[web]** |
| agdarsec (Agda) | indexed by the input's length; a `Success` carries `.small : size < n` | list of successes | a parser must consume to succeed; recursion goes through a "□" (box) type: "available on strictly smaller inputs" | — | [paper](https://gallais.github.io/pdf/agdarsec18.pdf), [repo](https://github.com/gallais/agdarsec) **[web]** |
| Danielsson's total parser combinators (Agda) | mixed induction and coinduction; the type says whether a parser accepts the empty string | list of successes | sequencing is read coinductively only when the other side can't accept the empty string; handles many left-recursive grammars | — | [paper](https://www.cse.chalmers.se/~nad/publications/danielsson-parser-combinators.pdf) **[web]** |

Unison: I found no parser library built on abilities whose design I could read; [unison-parsers](https://github.com/zenhack/unison-parsers) is marked work in progress and its README shows no code **[web]**. Eff and Frank: their papers and examples use nondeterminism and backtracking handlers ([Eff](https://github.com/matijapretnar/eff), [Bauer and Pretnar](https://arxiv.org/pdf/1203.1539)), but I found no parser library. A later paper describes a parser effect as "nondeterminism with cut" plus a token-consuming effect, following Wu, Schrijvers and Hinze 2014 ([Calculus for Scoped Effects](https://arxiv.org/pdf/2304.09697)) **[web]**; I didn't read the 2014 paper itself.

### 3.2 Pattern-shaped helpers for puzzle input

| Tool | Example | Link |
|---|---|---|
| Python `parse` | `parse("It's {}, I love it!", "It's spam, I love it!")` gives `('spam',)`; `{:d}` converts to an integer; `{item}` names a field; `search` and `findall` | [PyPI](https://pypi.org/project/parse/) **[web]** |
| Rust `aoc-parse` | `parser!(lines(u64 "x" u64 "x" u64))`; `{ "<" => -1, "=" => 0, ">" => 1 }` maps words to values; `line`, `lines`, `section`, `sections`; "Left-recursive grammars don't work, as usual for PEG parsers" | [docs](https://docs.rs/aoc-parse/latest/aoc_parse/) **[web]** |
| Rust `scan_fmt` | `scan_fmt!("-11 0x22", "{d} {x}", i8, [hex u8])` | [docs](https://docs.rs/scan_fmt/latest/scan_fmt/) **[web]** |
| Kotlin | `val (name, phone) = Regex("(\\w+) (\\d+)").find(s)!!.destructured` | [docs](https://kotlinlang.org/api/core/kotlin-stdlib/kotlin.text/-match-result/destructured.html) **[web]** |
| Scala 3 | "It is also possible to use string interpolation in patterns": `case s"Hello, $name!" =>` | [book](https://docs.scala-lang.org/scala3/book/string-interpolation.html) **[web]** |

### 3.3 The papers, in a sentence each

- **Hutton and Meijer, [Monadic Parser Combinators](https://people.cs.nott.ac.uk/pszgmh/monparsing.pdf) (1996)**, sections 2 to 7 read **[web]**. A parser is `String -> [(a,String)]`: a list of successes, so ambiguity is possible. They then add a deterministic choice `p +++ q = first (p ++ q)`, because returning every result is wasteful ("if p1 succeeds then p2 is never applied"), and state that "the repetition combinators … are defined using (+++)". Lexing is `token p` (a parser followed by `junk`). Section 7 takes the parser apart into two simpler pieces: `type Parser a = StateM Maybe String a`, state (the input) over failure, and the one primitive left is `item`, which reads a character from the state. That is this note's design with abilities in place of monads: `Parse` is the state, `Fail` the failure.
- **Swierstra, [Combinator Parsing: A Short Tutorial](https://ics-archive.science.uu.nl/research/techreps/repo/CS-2008/2008-044.pdf) (2008)**, sections 3 and 9 read **[web]**. Applicative parsers can be analysed before they run (first sets, error correction); monadic ones can't, because "we dynamically build new parses based on the input produced thus far: the whole idea of a static analysis is that it is static". Monadic sequencing buys context-sensitive formats (read *n*, then *n* things). Stitchwort's direct style is monadic in this sense. Static analysis would matter for big grammars; it doesn't for puzzle input.
- **Danielsson, Total Parser Combinators (ICFP 2010)**, introduction and §§3–5 read **[web]**. Termination is guaranteed by "reading choice inductively, and only reading an argument of the sequencing operator coinductively if the other argument does not accept the empty string". The reference back end is "at least exponential" in the worst case. Too heavy for us, but the idea, *track in the type whether a parser can succeed without reading*, is the one Idris 2, cats-parse and agdarsec use in lighter forms.
- **Allais, [agdarsec](https://gallais.github.io/pdf/agdarsec18.pdf) (2018)**, §§1–5 read **[web]**. "For a parser's run to be considered successful, it must have consumed some of its input": a success carries a proof that the rest is shorter. §5.1 below shows this works in Stitchwort today.
- **Round trips**: [Rendel and Ostermann](https://www.informatik.uni-marburg.de/~rendel/unparse/rendel10invertible.pdf) (Haskell 2010) write one description that runs as both parser and printer; [Narcissus](https://arxiv.org/abs/1803.04870) (ICFP 2019) derives, in Coq, a decoder "guaranteed to be the inverse" of an encoder for binary formats **[web]**, abstracts only. Neither is needed for puzzle input; §8 says what we would prove instead.

### 3.4 What to take from this

1. **Backtracking: choose PEG-style (always back up, locally).** attoparsec, Angstrom, Parseff and aoc-parse always back up; Parsec, Megaparsec, Lean and cats-parse back up only when nothing was consumed, and make you write `try`/`attempt`/`backtrack` otherwise. The consumed-input rule exists for speed and for sharper errors on large grammars. Puzzle lines are short, and the furthest-failure rule (Parseff, Megaparsec) gives sharp errors anyway.
2. **Full backtracking through the rest of the parse (Koka, Effekt) is the wrong default.** Resuming a choice a second time re-runs everything after it, which can be exponential **[inferred]** and makes the error a guess ("todo: merge or pick closest?" in Koka's handler).
3. **Loops: every library either errors (Parsec, nom, winnow) or rules it out by type (cats-parse, Idris 2, agdarsec).** Koka, a total-by-default effect language, cheats with `pretend-decreasing`; Lean marks `many` `partial`. We can do better than both (§5).
4. **Pattern helpers are popular for exactly this kind of input**, and aoc-parse's `{ "L" => …, "R" => … }` table and `lines`/`sections` are the shape AoC needs.

## 4. Representation: abilities, data, or a mix

### 4.1 The options

**A. A parser as a data value**: `(input: List Char) → Reply input a`, with combinators `map`, `flatMap`, `andThen`. This is Hutton–Meijer, Lean, cats-parse.

**B. A parser as effectful code**: `() → {Parse, Fail} a`, where `Parse` operations read from input the handler holds. This is Koka, Effekt, Parseff.

**C. B on the surface, A underneath**: `Parse` has one operation that runs a data-style parser. Not possible today: an ability's operation can't be polymorphic in its result type ([abilities.md](abilities.md), and `Each.each` works around it the same way) **[source]**.

### 4.2 How they compare in Stitchwort

| | A: data | B: abilities |
|---|---|---|
| Reading | Nested `flatMap`s: Stitchwort has no do-notation and no user-defined operators (no `<*>`, `*>`, D1207) **[source]**. See the example below | Direct style, like every AoC `parse` today |
| `Fail` inside a parser | Must be turned into a `Reply` | Works as is: `ensure`, `need`, `toNatOrFail` |
| Termination of `many` | Can be in the type: a reply carries `rest.length < input.length`, and `decreasing input.length` needs no run-time check (§5.1) **[ran]** | Fuel equal to the characters left, plus a run-time check that each round read something (§5.2) **[ran]** |
| Speed, 100k lines (§7) | 1.96 s machine, 0.65 s native, 0.83 s JS (per line) | 3.3 s machine, 1.8 s native, 1.0 s JS (per line) |
| Proofs | Plain functions: equations by `rfl` and induction | Bridging lemmas through the handler, `rfl` or one `rewrite` each (§8) **[ran]** |
| Input representation | Fixed in every parser's type | Private to the handler: it can change (to a native text cursor, §7.3) without touching any parser |

The data version of the day 8 line, as it has to be written today **[ran]**:

```
def point: Parser1 Point :=
  nat.andThen ((char ',').andThen (nat.andThen ((char ',').andThen (nat.map (z => (z, ()))).toParser).toParser).toParser).toParser
    |> .map (((x, (c1, (y, (c2, (z, u)))))) => ({ x, y, z }: Point))
```

and the ability version **[ran]**:

```
def point(): {Parse, Fail} Point :=
  let x := nat()
  char ','
  let y := nat()
  char ','
  let z := nat()
  { x, y, z }
```

**Recommendation: B.** Readability decides it: puzzle parsers are written often and read often, and B reads like the code Matt writes now. B is 1.7 to 2.8 times slower than A (machine and native), but a 5,000-line puzzle input still parses in about 0.15 s on the machine and under 0.1 s natively or in JS (§7, scaled from 100k lines). A's best idea, "a parser that must read something" in its type, isn't lost: B's `many` checks it at run time, as Parsec and nom do.

### 4.3 Why not backtrack with `Each`?

`Each` (Koka's `pick`, Effekt's `alt`) is Stitchwort's nondeterminism ability. With the `Parse` handler inside `Each.collect`, each choice gets its own copy of the input, and you get Hutton–Meijer's list of successes for free; this runs today (`eachparse.sw`) **[ran]**:

```
Each.collect (() =>
  let (pieces, rest) := Parse.run "abc".toList (() =>
    let first := chunk()     -- chunk picks any length with Each.each
    let second := chunk()
    (first, second))
  Each.require (rest == [])
  pieces) == [(['a'], ['b', 'c']), (['a', 'b'], ['c'])]
```

It's the wrong default (§3.4, point 2): all parses where you want one, exponential cases, no good error. But it's a nice property of the design that it composes: a puzzle with an ambiguous grammar can use `Each` with the same `Parse` operations, without a second library.

## 5. Termination

### 5.1 What the checker accepts today

All of these were checked with the release build **[ran]**:

- **Data parsers with a run-time check** (`data1.sw`): `many` with `decreasing input.length` and `if h: rest.length < input.length then … many p rest`, the guard style of [well-founded-recursion.md](well-founded-recursion.md). Accepted. But computing `length` each round makes a long `many` quadratic.
- **Data parsers that prove they read** (`data3.sw`), as agdarsec and cats-parse:

  ```
  type Step (input: List Char) (a: Type) =
    | Took (value: a) (rest: List Char) (shorter: rest.length < input.length)
    | Missed (expected: Text) (at: List Char)

  def manyFrom (p: Parser1 a) (input: List Char): Reply input (List a)
    decreasing input.length
  :=
    match p.run input with
      | Missed what at => Got [] input (Nat.leRefl input.length)
      | Took x rest shorter =>
        match manyFrom p rest with ...
  ```

  Accepted: `auto` finds `shorter` for the recursive call, and the proofs cost nothing at run time. The library's combinators carry the proofs (`Nat.leTrans` here and there); users never see them.
- **Effect parsers with fuel** (`proto.sw`): `many` runs `manyFuel (left + 1) p`, structural on the fuel, where `left` is the number of characters left (kept in the handler, so it costs nothing to ask). A round that reads nothing ends the loop. Each other round reads at least one character, so the fuel never runs out early: the fuel changes nothing about the result. Accepted.
- **A gap found on the way**: a definition with clauses `| [] | [p] | [p, ..ps]` whose last clause recurses on `ps` from inside a `match` is refused (`E-TERMINATION`), pure or effectful; without the `[p]` clause it's accepted (`term1.sw`). Easy to avoid, worth a ticket.

### 5.2 Recommendation

Use fuel equal to the characters left, inside the library, for `many`, `some`, `sepBy1`, `lines` and `sections`. Users write no fuel and no measures. The `decreasing` machinery doesn't apply to effect parsers, because the measure (the input left) lives in the handler, not in an argument.

What `many` does when its parser matched without reading anything is an open choice (§10).

### 5.3 Recursive grammars

A parser for nested input calls itself: `packet` contains a list of `packet`s. Nothing in its arguments gets smaller, so the checker refuses a plain recursive definition. The library offers a combinator with the same fuel argument, where each level of nesting uses one unit **[ran]** (`recursive.sw`):

```
def packet(): {Parse, Fail} Nat := recursive (nested =>
  oneOf [
    () => nat(),
    () =>
      char '['
      let items := optional (() => sepBy1 nested (() => char ','))
      char ']'
      (items.getOrElse []).sum
  ])
```

A grammar that nests without reading (left recursion, `self()` first) runs out of fuel after as many levels as there are characters left, and fails with `expected less deeply nested input` instead of looping. That matches aoc-parse's and Parsec's "left recursion doesn't work", but as an error rather than a hang.

(The example sums the numbers because `type Packet = … | Packets (items: List Packet)` is refused, `E-POSITIVITY`: a type can't contain itself inside a `List`. The known workaround is a tree type and a forest type defined together. That limit isn't the parser library's, but tree-shaped puzzle input will meet it.)

## 6. API for puzzle input

### 6.1 The library

Sketched from the prototype that ran (`proto.sw`, 330 lines with tests). Names are proposals. Everything below ran except `digit` (not written) and `label`, whose prototype adds its name to what `p` expected instead of replacing it (`expected 'L' or 'R' or a turn like L68`); replacing needs the handler to drop the expectations noted inside `p` at its starting point, a stage 1 detail.

```
-- std/Parse (sketch)

-- The operations. Each is a token's worth of work in the handler.
ability Parse where
  span: (Char → Bool) → {Parse} (List Char)       -- the longest prefix passing the test, read
  next: (Char → Bool) → {Parse} (Option Char)     -- one character, read if it passes
  literal: List Char → {Parse} Bool               -- read these characters if they come next
  mark: () → {Parse} (Mark, Nat)                  -- where we are, and how many characters are left
  reset: Mark → {Parse} ()                        -- go back to a mark
  expect: Text → {Parse} Text                     -- note what was expected here; all expected this far in

-- Running a parser. The whole input must be read.
def Parse.all (input: Text) (parser: () → {Parse, Fail} a): {Fail} a        -- "line 3, column 6: …"
def Parse.eachLine (input: Text) (parser: () → {Parse, Fail} a): {Fail} (List a)  -- the same messages, one handler per line

-- Pieces
def char (c: Char): {Parse, Fail} ()
def text (t: Text): {Parse, Fail} ()
def satisfy (what: Text) (test: Char → Bool): {Parse, Fail} Char
def takeWhile (test: Char → Bool): {Parse} Text
def takeWhile1 (what: Text) (test: Char → Bool): {Parse, Fail} Text
def nat(): {Parse, Fail} Nat
def int(): {Parse, Fail} Int
def digit(): {Parse, Fail} (Fin 10)
def spaces(): {Parse} ()                           -- spaces and tabs, possibly none
def newline(): {Parse, Fail} ()
def end(): {Parse, Fail} ()
def pick (choices: List (Text, a)): {Parse, Fail} a  -- the value of the first word that comes next

-- Choice and repetition. A failed alternative leaves the input as it was.
def optional (p: () → {Parse, Fail} a): {Parse} (Option a)
def oneOf (alternatives: List (() → {Parse, Fail} a)): {Parse, Fail} a
def many (p: () → {Parse, Fail} a): {Parse} (List a)
def some (p: () → {Parse, Fail} a): {Parse, Fail} (List a)
def sepBy1 (p: () → {Parse, Fail} a) (separator: () → {Parse, Fail} ()): {Parse, Fail} (List a)
def lines (p: () → {Parse, Fail} a): {Parse, Fail} (List a)       -- a final line break is allowed
def sections (p: () → {Parse, Fail} a): {Parse, Fail} (List a)    -- blocks separated by a blank line
def grid (cell: () → {Parse, Fail} a): {Parse, Fail} (List (List a))
def recursive (body: (() → {Parse, Fail} a) → {Parse, Fail} a): {Parse, Fail} a
def label (what: Text) (p: () → {Parse, Fail} a): {Parse, Fail} a  -- "expected a turn" in place of what `p` expected at its start (Megaparsec's `label`)
```

About twenty functions. Parsers that take parsers take thunks, `() => …`, like `Fail.toResult` and `Each.collect`. A parser of no arguments is written `nat()`, as `IO.readAll()` is.

### 6.2 AoC parsers rewritten

All of these ran as tests in `proto.sw`, with the error messages shown **[ran]**. Each replaces the function named.

**2025 day 1** (`Turn.parse`): a keyword table, aoc-parse style.

```
def turn(): {Parse, Fail} Turn :=
  let direction := pick [("L", Left), ("R", Right)]
  direction (nat())

-- Parse.eachLine "R5\nX5" turn fails: "line 2, column 1: expected 'L' or 'R'"
```

**2025 days 2 and 5** (`Range.parse`, `parseRanges`, `parseDatabase`): a check of our own inside the parser, two sections, and line numbers that run through the whole input, so `parseLinesFrom` goes.

```
def range(): {Parse, Fail} Range :=
  spaces()
  let from := nat()
  spaces()
  char '-'
  spaces()
  let to := nat()
  spaces()
  ensure (from ≤ to) "the range ends before it starts"
  { from, to }

def ranges(): {Parse, Fail} (List Range) :=
  let all := sepBy1 range (() => char ',')
  let final := optional newline
  all

def database(): {Parse, Fail} Database :=
  let fresh := sepBy1 range newline
  blankLine()
  let available := lines nat
  { fresh, available }

-- "11-22,3x5"            → "line 1, column 8: expected '-'"
-- "22-11"                → "line 1, column 6: the range ends before it starts"
-- "3-5\n10-14\n\n1\nx\n" → "line 5, column 1: expected a number or the end"
```

**2025 day 8** (`parsePoint`): §4.2's `point`. `"162,8x7,812"` fails with `column 6: expected ','`.

**2024 day 1** (`parseIdPair`):

```
def idPair(): {Parse, Fail} (Nat, Nat) :=
  let left := nat()
  let gap := takeWhile1 "a space" isSpace
  let right := nat()
  (left, right)
```

**2025 day 4** (`parseGrid`, `findStray`): the grid, with line and column for a stray character, in one line instead of two hand-written loops. Checking that the rows are equally wide stays with the `Vec` conversion.

```
def cells(): {Parse, Fail} (List (List Cell)) := grid (() => pick [("@", Roll), (".", Floor)])

-- "@.\n.x\n" → "line 2, column 2: expected '@' or '.' or a line break or the end"
```

**2024 day 14** (not in the repository yet): `p=0,4 v=3,-3`.

```
def robot(): {Parse, Fail} Robot :=
  text "p="
  let px := int()
  char ','
  let py := int()
  text " v="
  let vx := int()
  char ','
  let vy := int()
  { px, py, vx, vy }
```

### 6.3 Patterns: `scan`, and later text patterns in `match`

For a line whose shape is fixed, a pattern is shorter still. A pure function, no `Parse` needed, ran (`scan.sw`) **[ran]**:

```
-- The texts in the holes, if `text` has the pattern's shape. A hole is `{}`,
-- and takes the shortest text up to the next literal piece.
def Text.scan (text: Text) (pattern: Text): Option (List Text)

"p=0,4 v=3,-3".scan "p={},{} v={},{}"           -- Some ["0", "4", "3", "-3"]
"move 3 from 1 to 2".scan "move {} from {} to {}"  -- Some ["3", "1", "2"]

def parsePoint (line: Text): {Fail} Point :=
  match line.scan "{},{},{}" |> .map (.map .toNat) with
    | Some [Some x, Some y, Some z] => { x, y, z }
    | _ => fail "expected a box like 162,817,812, got '${line}'"
```

The holes come back as text, so the caller converts them, as with today's `split`. That last step is what a language feature could remove. **Can string interpolation be a pattern?** Scala 3 says yes (`case s"Hello, $name!" =>`, §3.2). In Stitchwort it could look like:

```
match line with
  | "p=${px: Int},${py: Int} v=${vx: Int},${vy: Int}" => { px, py, vx, vy }
  | _ => fail "expected a robot like p=0,4 v=3,-3, got '${line}'"
```

It would elaborate to a parser: each literal piece to `text`, each hole to its type's parser, found by an interface (`interface Read (a: Type) = { read: () → {Parse, Fail} a }`, with instances for `Nat`, `Int`, `Char`, and `Text` meaning "up to the next piece"), and the arm to `Parse.all` with `optional`. So text patterns and parsers would be one thing, not two. It is a language change (patterns are elaborated by the compiler), so it's a later stage, behind its own design review.

### 6.4 Out of scope

Day 6 reads its worksheet in columns: the meaning is in the layout (which characters line up), not in a grammar. A grid parser can check the characters (`grid (() => satisfy …)`), but the transposition stays ordinary list code. The same goes for puzzles that read pictures (ASCII-art letters).

## 7. Performance

### 7.1 Measured

100,000 lines like `47923,1203,99871` (1.77 MB), summing the first numbers, `stitchwort run` (the machine), `run --native` and `run --js`, user time in seconds, peak memory. Release build of `main`, Apple silicon, other work running on the machine, so treat differences under 20% as noise **[ran]**:

| Variant | File | Machine | Native | JS | Peak memory (machine) |
|---|---|---|---|---|---|
| Today's way: `split ','`, `toNat` | `split1.sw` | 0.85 | 0.39 | 0.65 | 256 MB |
| `Text.scan` (pure Stitchwort, no natives) | `scan.sw` | 2.32 | 0.80 | 0.89 | 250 MB |
| Data parsers with proofs, per line | `data3b.sw` | 1.96 | 0.65 | 0.83 | 264 MB |
| Data parsers, whole input at once | `data4.sw` | 1.55 | 0.55 | 1.24 | 312 MB |
| Abilities, token-sized operations, per line | `eff2.sw` | 3.07 | 1.52 | 1.66 | 194 MB |
| The prototype (§6), per line | `protolines.sw` | 3.29 | 1.79 | 0.99 | 265 MB |
| The prototype, whole input at once | `proto.sw` | 4.25 | 2.70 | 14.9 | 1,297 MB |
| Abilities, an operation per character | `eff1.sw` | 21.2 | 12.7 | – | 188 MB |

Startup (checking the file and std) is about 0.2 s of each machine figure. An empty input takes 0.15–0.23 s.

### 7.2 What the numbers say

- **Character-level operations are out.** One operation costs about 1.4 µs on the machine (effect-runtime.md §9.11 **[source]**); two per character makes 100k lines take 21 s.
- **Token-level operations cost 1.5 to 4.6 times today's `split`.** Per line the prototype is 3.3 s (machine), 1.8 s (native), 1.0 s (JS). A real AoC input is a few thousand lines: under 0.2 s of parsing anywhere.
- **Whole-input parsing is the weak spot.** The prototype holds the input as a `List Char`, and a list of 1.77 million characters alone peaks at 744 MB on the machine (`listlen.sw`: read, convert, count) **[ran]**, about 420 bytes per character. The JS run of the whole input took 15 s; per line it takes 1 s. Why the single long JS run is so slow I haven't found **[speculative: the same list, plus one long handler run]**.
- **Why a list at all:** the machine stores `Text` as `Rc<str>`, and `Text.uncons` copies the rest of the text into a new string (`crates/rt/src/prims.rs`, `TextUncons`) **[source]**, so walking a `Text` a character at a time is quadratic. A `List Char` makes each step O(1).

### 7.3 Recommendation

- Ship the per-line runner (`Parse.eachLine`) as the default for line-per-record input, and `Parse.all` for sectioned input. Both give the same messages.
- Later, if whole-input parsing of large files matters: keep a `Text` and a character offset in the handler, with three natives that take an offset (`Text.spanAt`, `Text.startsWithAt`, `Text.charAt`), each specified by its `toList` definition as the text natives are ([compact-text.md](compact-text.md)). No parser changes: the input's representation is private to the handler. Not needed for AoC.
- `Text.scan` wants a native "split at the first occurrence" (`Text.splitFirst`); with it, `scan` should approach `split`'s speed **[inferred]**.

## 8. Proofs

What we might want to prove, and whether it's feasible:

1. **Bridging lemmas**, as `Each` and `Fail` have: what the handler does to each operation followed by the rest of the parser. Feasible today, shown in `eff2proofs.sw` **[ran]**:

   ```
   theorem Parse.runPure (input: List Char) (x: a): Parse.run input (() => x) = (x, input) := rfl

   theorem Parse.runLiteralThere (chars: List Char) (rest: List Char) (k: Bool → {Parse} a):
       Parse.run (List.append chars rest) (() => k (Parse.literal chars)) = Parse.run rest (() => k True) :=
     rewrite Text.stripPrefixCharsAppend rest chars
   ```

   These are the stage that makes everything else possible; they belong with the library.
2. **Combinator laws**: `optional` leaves the input unchanged when it returns `None`; `oneOf [p]` is `p`; `many` returns what repeated `p` would. Feasible with `match reify` on `Fail` (as in `Fail.toResultThen`) plus the bridging lemmas **[inferred]**.
3. **Round trips** for a particular format: `Parse.all (show x) parser = x`, e.g. for `Range`. Feasible but per format, and it needs digit lemmas about `Nat.toText` **[inferred]**. Not needed for AoC: the theorems there are about the parsed types, not about text (house rule). Worth doing once, for `nat`, as the library's own example.
4. **Determinism** comes free: a parser is a function. **Termination** comes free: the definitions are accepted.
5. **Not consuming on failure** isn't a property we need: every choice resets the input, so a failed alternative's reading never shows.

Rendel–Ostermann style "one description, parser and printer" (§3.3) would give round trips by construction. Too much machinery for this library; not recommended.

## 9. Staged plan

Each stage is one lane.

1. **`Std.Parse` core.** The ability, the handler, `Parse.all` and `Parse.eachLine`, the pieces and combinators of §6.1, `label`, `recursive`, furthest-failure errors with line and column. Tests: §6.2's examples and their messages, a `many` over a parser that reads nothing, left recursion failing. A guide section in chapter 8. About 400 lines.
2. **Dogfood on AoC.** Rewrite the `parse*` functions of 2025 days 1, 2, 3, 4, 5, 7, 8, 9 and 2024 day 1 with it, delete `parseLinesFrom` and the hand-written error loops of days 4 and 7. Note what was awkward; fix the library, or file language gaps.
3. **Bridging lemmas** (§8.1) and `nat`'s round trip.
4. **`Text.scan`** and a native `Text.splitFirst`.
5. **Text patterns in `match`** (§6.3): a separate design note first; it's a language change.
6. **Only if needed:** the native text cursor of §7.3.

## 10. Open choices

**`many` over a parser that matched without reading: stop, or fail?** Stopping (the prototype) can never loop and never surprises a correct parser. Failing ("`many`: the parser matched without reading anything") is what Parsec, nom and winnow do, because it's always a bug in the parser. *Recommendation: fail, with that message.* A silent stop hides the bug until some input exercises it.

**The row: `{Parse, Fail}`, or `{Parse}` alone with its own `fail` operation?** One ability reads better in signatures. But reusing `Fail` lets `ensure`, `need`, `toNatOrFail` and `Fail.context` work inside parsers unchanged, and keeps one failure story in std. *Recommendation: `{Parse, Fail}`.* An ability alias (Effekt's `effect Parser = { Nondet, Lexer }`) would shorten it later; that's a separate language question.

**Backtracking: always (PEG), or only before input was read (Parsec), with a `try`?** *Recommendation: always.* Puzzle input is small, and furthest-failure errors are as sharp as the consumed-input rule's.

**Default runner: whole input or per line?** *Recommendation: offer both, with the same messages; recommend `Parse.eachLine` in the guide for one-record-per-line input*, because it is 1.3 to 15 times faster and uses a fifth of the memory on large inputs (§7).

**Where do errors from our own checks point?** `ensure (from ≤ to)` in `range` reports the column where the parser had got to (the range's end). Pointing at the range's start needs a `located` wrapper. *Recommendation: the current place, and no `located` until a puzzle wants it.*

**Text patterns in `match` (§6.3): pursue?** *Recommendation: yes, but after stage 2*, when the library's own `Read`-style pieces exist to elaborate holes to.

## 11. Language gaps met

None blocks the recommended design. In order of how much they matter here:

1. **No do-notation or user operators (D1207)**: rules out data-style parsers (§4.2). Abilities sidestep it.
2. **Ability operations can't be polymorphic in their result**: rules out option C (§4.1). `optional` uses `Fail.recover` and `reset` instead, which works.
3. **Termination checker**: `| [] | [p] | [p, ..ps]` with a recursive call inside a `match` is refused, pure or effectful (`term1.sw`). Small; worth a ticket.
4. **A type can't contain itself inside a `List`** (`E-POSITIVITY`): tree-shaped puzzle input needs a tree and a forest defined together.
5. **`Text.uncons` copies on the machine**, and a `List Char` costs about 420 bytes per character: fine per line, heavy for a whole large input (§7).

## Appendix A. Experiments

In `/private/tmp/claude-501/-Users-matt-repos-mdr-stitchwort/7712538a-c5aa-43af-9a47-8d4094a04350/scratchpad/parsers/`, not committed. Inputs: `points100k.txt` and `points10k.txt`, made with `awk` and `srand(1)`.

| File | What it shows |
|---|---|
| `data1.sw` | data parsers, `many` with `decreasing` and a run-time guard: accepted, test passes |
| `data2.sw`, `data3.sw`, `data3b.sw`, `data4.sw` | data parsers without and with "reads something" proofs; per line and whole input; timings |
| `eff1.sw` | abilities with an operation per character: works, 21 s for 100k lines |
| `eff2.sw` | abilities with token-sized operations: 3 s |
| `eff2proofs.sw` | bridging lemmas by `rfl` and one `rewrite` |
| `proto.sw`, `protolines.sw` | the prototype library and §6.2's AoC parsers, 15 tests with their error messages |
| `recursive.sw` | `recursive` for nested input; left recursion fails instead of looping |
| `eachparse.sw` | `Each` with `Parse`: all parses |
| `scan.sw` | `Text.scan`, 5 tests and timing |
| `term1.sw` | the termination-checker gap of §11 |
| `walk.sw`, `listlen.sw`, `effmem.sw`, `effmem2.sw` | where whole-input memory goes: the `List Char` itself |

## Sources

Libraries: [Parsec](https://hackage.haskell.org/package/parsec-3.1.17.0/docs/Text-Parsec.html), [Parsec source](https://hackage.haskell.org/package/parsec-3.1.17.0/docs/src/Text.Parsec.Prim.html), [Megaparsec](https://hackage.haskell.org/package/megaparsec-9.6.1/docs/Text-Megaparsec.html), [attoparsec](https://hackage.haskell.org/package/attoparsec-0.14.4/docs/Data-Attoparsec-ByteString.html), [Angstrom](https://github.com/inhabitedtype/angstrom), [Parseff](https://ocaml.org/p/parseff/0.3.0/combinators.html), [fastparse](https://com-lihaoyi.github.io/fastparse/), [cats-parse](https://github.com/typelevel/cats-parse), [nom `many0`](https://docs.rs/nom/latest/nom/multi/fn.many0.html), [winnow `repeat`](https://docs.rs/winnow/latest/winnow/combinator/fn.repeat.html), [chumsky](https://docs.rs/chumsky/latest/chumsky/), [Lean `Std.Internal.Parsec`](https://github.com/leanprover/lean4/blob/master/src/Std/Internal/Parsec/Basic.lean), [Koka `std/text/parse`](https://github.com/koka-lang/koka/blob/master/lib/std/text/parse.kk), [Effekt frontend case study](https://effekt-lang.org/docs/casestudies/frontend), [Idris 2 `Text.Parser.Core`](https://github.com/idris-lang/Idris2/blob/main/libs/contrib/Text/Parser/Core.idr), [Idris 2 `Text.Parser`](https://github.com/idris-lang/Idris2/blob/main/libs/contrib/Text/Parser.idr), [agdarsec](https://github.com/gallais/agdarsec), [unison-parsers](https://github.com/zenhack/unison-parsers), [Eff](https://github.com/matijapretnar/eff).

Pattern helpers: [Python `parse`](https://pypi.org/project/parse/), [aoc-parse](https://docs.rs/aoc-parse/latest/aoc_parse/), [scan_fmt](https://docs.rs/scan_fmt/latest/scan_fmt/), [Kotlin `destructured`](https://kotlinlang.org/api/core/kotlin-stdlib/kotlin.text/-match-result/destructured.html), [Scala 3 string interpolation](https://docs.scala-lang.org/scala3/book/string-interpolation.html).

Papers: Hutton and Meijer, [Monadic Parser Combinators](https://people.cs.nott.ac.uk/pszgmh/monparsing.pdf) (1996); Swierstra, [Combinator Parsing: A Short Tutorial](https://ics-archive.science.uu.nl/research/techreps/repo/CS-2008/2008-044.pdf) (2008); Danielsson, [Total Parser Combinators](https://www.cse.chalmers.se/~nad/publications/danielsson-parser-combinators.pdf) (ICFP 2010); Allais, [agdarsec](https://gallais.github.io/pdf/agdarsec18.pdf) (2018); Rendel and Ostermann, [Invertible Syntax Descriptions](https://www.informatik.uni-marburg.de/~rendel/unparse/rendel10invertible.pdf) (Haskell 2010); Delaware et al., [Narcissus](https://arxiv.org/abs/1803.04870) (ICFP 2019); Bauer and Pretnar, [Programming with Algebraic Effects and Handlers](https://arxiv.org/pdf/1203.1539); [A Calculus for Scoped Effects & Handlers](https://arxiv.org/pdf/2304.09697) (2023).

In this repository: [abilities.md](abilities.md), [effect-runtime.md](effect-runtime.md) §9.11, [compact-text.md](compact-text.md), [well-founded-recursion.md](well-founded-recursion.md), `crates/elab/src/std/{Fail,Each,Text}`, `crates/rt/src/prims.rs`, `aoc/src/Aoc/`.
