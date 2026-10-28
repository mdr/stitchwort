# Proposal: a parser library for puzzle input

**Status:** stage 1 built, 28 October 2026: `Std.Parse` is in std (`crates/elab/src/std/Parse/Parse.sw`), with one `Parse` ability rather than `{Parse, Fail}` (decided by Matt, §4.4). §6.1 lists the API as built, and §7.4 has its measurements. The research stage's experiments are scratch files, not committed (listed in [Appendix A](#appendix-a-experiments)).

Matt asked for a std parser-combinator library for turning puzzle input (Advent of Code first, but not only) into the program's own types. This note looks at how other languages do it, tries the main options in Stitchwort, and recommends one.

Tags: **[source]** read in this repository, **[ran]** run in a scratch file with the release build of `main` (27 October), **[web]** checked online (linked), **[inferred]** reasoned but not run, **[speculative]** a guess.

## 1. The recommendation in brief

- **A parser is ordinary direct-style code with one ability, `{Parse}`**, as in Unison's parser libraries (§4.4). `Parse` holds the input and also fails: `Parse.fail`, `Parse.ensure` and `Parse.need` mirror `Fail`'s, and `Parse.fromFail` turns an existing `{Fail}` helper (`toNatOrFail`) into a parse failure at the current point. The runners turn a parse error into an ordinary `Fail`, so `Fail.context` works on the result. Code reads like today's AoC `parse` functions:

  ```
  def point(): {Parse} Point :=
    let x := nat()
    char ','
    let y := nat()
    char ','
    let z := nat()
    { x, y, z }

  def parsePoints (input: Text): {Fail} (List Point) := Parse.eachLine input point
  ```

  A bad line fails with `line 3, column 6: expected ',', got ';'`.
- **The operations are token-sized, not character-sized.** "Read the digits here" is one operation, so a line costs a handful of operations. Character-sized operations made parsing 25 to 33 times slower than today's `split` (§7).
- **Choice backtracks locally, as in a PEG.** `oneOf`, `optional` and `many` put the input back when an alternative fails. Nothing is ever retried after a choice has returned. There's no `try` to remember.
- **Loops are total because each repetition must read something.** `many` fails the whole parse ("`many`: the parser matched without reading anything") if its parser matches without reading, as Parsec and nom do. Its fuel is the number of characters left, which is always enough.
- **Errors name the furthest point any alternative reached**, everything expected there, and what was found instead: `expected a number or ',', got 'x'` (§6.5). Positions are counted as one number while parsing and turned into a line and column once, at the end.
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

Unison: draft 1 found no parser library built on abilities ([unison-parsers](https://github.com/zenhack/unison-parsers) is marked work in progress). Two exist on Unison Share, [@rlmark/parsing](https://share.unison-lang.org/@rlmark/parsing) and [@dfreeman/yap](https://share.unison-lang.org/@dfreeman/yap), each with one `Parse` ability that also fails (§4.4) **[web]**. Eff and Frank: their papers and examples use nondeterminism and backtracking handlers ([Eff](https://github.com/matijapretnar/eff), [Bauer and Pretnar](https://arxiv.org/pdf/1203.1539)), but I found no parser library. A later paper describes a parser effect as "nondeterminism with cut" plus a token-consuming effect, following Wu, Schrijvers and Hinze 2014 ([Calculus for Scoped Effects](https://arxiv.org/pdf/2304.09697)) **[web]**; I didn't read the 2014 paper itself.

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

**B. A parser as effectful code**: `() → {Parse} a` (drafted as `{Parse, Fail}`, §4.4), where `Parse` operations read from input the handler holds. This is Koka, Effekt, Parseff.

**C. B on the surface, A underneath**: `Parse` has one operation that runs a data-style parser. Not possible today: an ability's operation can't be polymorphic in its result type ([abilities.md](abilities.md), and `Each.each` works around it the same way) **[source]**.

### 4.2 How they compare in Stitchwort

| | A: data | B: abilities |
|---|---|---|
| Reading | Nested `flatMap`s: Stitchwort has no do-notation and no user-defined operators (no `<*>`, `*>`, D1207) **[source]**. See the example below | Direct style, like every AoC `parse` today |
| `Fail` inside a parser | Must be turned into a `Reply` | `Parse.ensure` and `Parse.need` mirror `Fail`'s; `Parse.fromFail` runs a `{Fail}` helper such as `toNatOrFail` (§4.4) |
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
def point(): {Parse} Point :=
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

### 4.4 One ability, not `{Parse, Fail}` (decided)

Draft 1 recommended the row `{Parse, Fail}`, so that `Fail`'s helpers would work inside parsers unchanged. Matt chose a single `Parse` ability instead, following Unison's parser libraries **[web]**. In [@rlmark/parsing](https://share.unison-lang.org/@rlmark/parsing) a parser is a delayed computation with the `Parse` ability, run by `run : '{g, Parse err} a -> Text ->{g} Either (Error err) a`. In [@dfreeman/yap](https://share.unison-lang.org/@dfreeman/yap), "a parser is any delayed computation that uses the `Parse` ability", and `failWith` fails "at the current location for an arbitrary reason other than a combinator like `text` failing to match".

As built:

- **Failing is part of `Parse`.** `Parse.fail "message"`, `Parse.ensure` and `Parse.need` fail at the current point, so the nearest choice backs up and the message takes part in furthest-point errors. `Parse.expected "a number"` fails with an expectation, joined to others at the same point with "or".
- **`Parse.fromFail`** turns an existing `{Fail}` helper (`Text.toNatOrFail`, `Aoc.Common.Range.parse`) into a parse failure at the current point.
- **Runners turn a parse error into an ordinary `Fail`**, with `line L, column C: …`, so callers keep using `Fail.context` and `Fail.toResult`.
- **The cost:** a choice can't use `Fail.recover`, which would leave the `Parse` operations to the outer handler. `optional` and `label` instead handle `Parse` themselves and pass every operation but `stop` on to the outer handler. Inside a choice, each operation goes through one extra handler per enclosing choice. The per-line timings stayed within noise of the prototype's (§7.4).

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

When its parser matched without reading anything, `many` fails the whole parse with "`many`: the parser matched without reading anything" (decided, §10). The failure is the `Parse.fatal` operation, which no choice backs out of: it's a bug in the parser, not a mismatch in the input.

### 5.3 Recursive grammars

A parser for nested input calls itself: `packet` contains a list of `packet`s. Nothing in its arguments gets smaller, so the checker refuses a plain recursive definition. The library offers a combinator with the same fuel argument, where each level of nesting uses one unit **[ran]** (`recursive.sw`):

```
def packet(): {Parse} Nat := recursive (nested =>
  oneOf [
    nat,
    () =>
      char '['
      let items := sepBy nested (() => char ',')
      char ']'
      items.sum
  ])
```

A grammar that nests without reading (left recursion, `self()` first) runs out of fuel after as many levels as there are characters left. As built, it then fails the whole parse with "`recursive`: the parser called itself without reading anything" instead of looping. Running out always means that: the nesting reached more levels than there are positions in the input, so some level called itself at the point where it started, and would do so forever. That matches aoc-parse's and Parsec's "left recursion doesn't work", but as an error rather than a hang.

(The example sums the numbers because `type Packet = … | Packets (items: List Packet)` is refused, `E-POSITIVITY`: a type can't contain itself inside a `List`. The known workaround is a tree type and a forest type defined together. That limit isn't the parser library's, but tree-shaped puzzle input will meet it.)

## 6. API for puzzle input

### 6.1 The library

**Built** (stage 1) in `crates/elab/src/std/Parse/Parse.sw`, namespace `Parse`, with 107 tests, the exact error messages among them, and the examples `examples/accept/parse-basics.sw` and `examples/accept/parse-aoc-day05.sw`. Import the pieces by name: `import Std.Parse (char, nat, lines)`. A function says in its doc comment when it can't fail.

```
-- The operations. Each is a token's worth of work in the handler.
ability Parse where
  span: (Char → Bool) → {Parse} (List Char)       -- the longest prefix passing the test, read
  next: (Char → Bool) → {Parse} (Option Char)     -- one character, read if it passes
  literal: List Char → {Parse} Bool               -- read these characters if they come next
  mark: () → {Parse} Parse.Mark                   -- where we are: the characters left, the offset, how many are left
  reset: Parse.Mark → {Parse} ()                  -- go back to a mark
  note: Parse.Problem → {Parse} ()                -- note `Expected what` or `Message text` here, for the error
  stop: () → {Parse} Empty                        -- fail here; the nearest choice backs up
  fatal: Text → {Parse} Empty                     -- fail the whole parse: for bugs, such as a loop that reads nothing

-- Runners. The parser must read all of its input.
def Parse.all (input: Text) (parser: () → {Parse} a): {Fail} a              -- "line 3, column 6: …, got 'x'"; line breaks at the end are allowed
def Parse.eachLine (input: Text) (parser: () → {Parse} a): {Fail} (List a)  -- one handler per line of `Text.lines`, the same messages
def Parse.line (line: Text) (parser: () → {Parse} a): {Fail} a              -- "column 6: …", for one line; one line break at the end is allowed
def Parse.run (input: List Char) (parser: () → {Parse} a): Result a Parse.Failure  -- needn't read everything; `Failure = { offset, messages, expected, width }`, made one message by `Parse.Failure.describe`

-- Failing at the current point
def Parse.fail (message: Text): {Parse} a                  -- replaces what attempts that didn't fail expected here (§6.5)
def Parse.expected (what: Text): {Parse} a                 -- "expected what", joined to others here with "or"
def Parse.ensure (ok: Bool) (message: Text): {Parse} ()
def Parse.ensureAt (at: Parse.Mark) (ok: Bool) (message: Text): {Parse} ()   -- reported at the mark
def Parse.need (option: Option a) (message: Text): {Parse} a
def Parse.fromFail (computation: () → {Fail} a): {Parse} a  -- a `Fail` helper's failure, here

-- Pieces
def Parse.char (expected: Char): {Parse} ()
def Parse.text (expected: Text): {Parse} ()
def Parse.satisfy (what: Text) (passes: Char → Bool): {Parse} Char
def Parse.takeWhile (passes: Char → Bool): {Parse} Text    -- never fails
def Parse.takeWhile1 (what: Text) (passes: Char → Bool): {Parse} Text
def Parse.nat(): {Parse} Nat
def Parse.natDigits (atLeast: Nat) (atMost: Nat): {Parse} Nat  -- "expected a number of 1 to 3 digits" where it starts
def Parse.int(): {Parse} Int                               -- an optional '-', then digits
def Parse.digit(): {Parse} (Fin 10)
def Parse.spaces(): {Parse} ()                             -- spaces and tabs, possibly none; never fails
def Parse.spaces1(): {Parse} ()                            -- spaces and tabs, at least one
def Parse.token (parser: () → {Parse} a): {Parse} a        -- spaces, `parser`, spaces: `token nat` reads " 12 "
def Parse.newline(): {Parse} ()                            -- "\n" or "\r\n"
def Parse.lineEnd(): {Parse} ()                            -- a line break or the end of the input
def Parse.blankLine(): {Parse} ()                          -- a line break, spaces or tabs, a line break; reported where it starts
def Parse.end(): {Parse} ()
def Parse.pick (choices: List (Text, a)): {Parse} a        -- the value of the first word that comes next

-- Choice and repetition. A failed alternative leaves the input as it was.
def Parse.optional (parser: () → {Parse} a): {Parse} (Option a)    -- never fails
def Parse.oneOf: List (() → {Parse} a) → {Parse} a
def Parse.many (parser: () → {Parse} a): {Parse} (List a)          -- fails only on a parser that reads nothing (fatal)
def Parse.many1 (parser: () → {Parse} a): {Parse} (List a)
def Parse.repeat (atLeast: Nat) (atMost: Nat) (parser: () → {Parse} a): {Parse} (List a)   -- Megaparsec's count'
def Parse.sepBy (parser: () → {Parse} a) (separator: () → {Parse} ()): {Parse} (List a)   -- never fails
def Parse.sepBy1 (parser: () → {Parse} a) (separator: () → {Parse} ()): {Parse} (List a)
def Parse.lines (parser: () → {Parse} a): {Parse} (List a)         -- the final line break is left to what follows
def Parse.sections (parser: () → {Parse} a): {Parse} (List a)      -- blocks separated by a blank line
def Parse.section (parser: () → {Parse} a): {Parse} (List a)       -- lines, then a blank line: `section rule`, then `lines update`
def Parse.findAll (parser: () → {Parse} a): {Parse} (List a)       -- every match in noise, as `re.findall`; never fails, reads everything
def Parse.findAllStarting (starts: Char → Bool) (parser: () → {Parse} a): {Parse} (List a)  -- the same, skipping characters that can't start a match
def Parse.grid (cell: () → {Parse} a): {Parse} (List (List a))
def Parse.looseGrid (cell: () → {Parse} a): {Parse} (List (List a))   -- possibly no rows, and rows possibly empty
def Parse.recursive (body: (() → {Parse} a) → {Parse} a): {Parse} a
def Parse.label (what: Text) (parser: () → {Parse} a): {Parse} a   -- "expected what" in place of what `parser` expected at its start
def Parse.labelWhole (what: Text) (parser: () → {Parse} a): {Parse} a   -- "expected what" where it started, wherever `parser` failed
```

Choices made while building it:

- **`lines` leaves the last line break alone**, and `Parse.all` allows one at the end of the input. With the prototype's `lines`, which ate it, `sections (() => lines nat)` couldn't find the blank line between sections.
- **`label` replaces, as Megaparsec's does.** Its handler drops the problems that `parser` notes at its starting point. If `parser` fails without getting further, `label` notes its own name there instead.
- **Messages and expectations at one point are both reported**: `not this; expected 'x', got 'y'`, the messages first, except that a message replaces what attempts that didn't fail expected before it (§6.5).
- **`recursive` running out of fuel is fatal**, as `many` reading nothing is (§5.3).
- **Proofs:** the per-operation lemmas `Parse.runFromPure`, `runFromMark`, `runFromReset`, `runFromNote`, `runFromStop`, `runFromFatal` and `runFromSpan` hold by `rfl`, and `runFromLiteralThere` by one `rewrite`. Each is stated over `Parse.runFrom state`, the handler from any state, because the state now carries the offset and the furthest problems as well as the input. The per-piece and choice lemmas are in §8.
- **The handler resumes in tail position.** `runFrom`'s clauses for `span`, `next` and `literal` call helpers (`Parse.State.span`, `.next`, `.literal`) that return the value and the next state as a pair, and resume with `k step.fst step.snd`. Written with a `match` in the clause, `k` was not in tail position as the runtime's state-handler loop recognises it (§7.5), and each of those operations kept a frame until the parse ended.
- **`findAll`** tries the parser at each character, so it is right for any parser; a match that reads nothing is kept and a character skipped after it, as `re.findall` does. `findAllStarting starts` skips characters for which `starts` is false with one `span`: correct only if no match starts at one of them, which is the caller's claim.
- **`section`** is aoc-parse's `section`: lines, then a blank line. A failing line after the first also notes "a blank line before this line" where it failed, so a missing blank line between sections reads `line 2, column 2: expected '|' or a blank line before this line, got ','` (the line's own error gets further than the blank line does, so it is the one reported). The last section is `lines`, which keeps its plain messages. At the end of the input, where there is no line, it notes plain "a blank line": `3-5\n4-6\n` with no ids reads `line 3, column 1: expected a number or a blank line, got the end of the input`. `blankLine` is reported where it starts whatever it read (`labelWhole`), so when its second line break is missing it doesn't add "or a line break" to the line's own error further on.
- **`natDigits` reads all the digits first**, so `1234` with at most 3 is "expected a number of 1 to 3 digits" at its first digit, not 123 followed by an unexpected 4. `repeat` stops at `atMost`, as `count'` does.

Parsers that take parsers take thunks, `() => …`, like `Fail.toResult` and `Each.collect`. A parser of no arguments is written `nat()`, as `IO.readAll()` is, and passed as `nat`.

### 6.2 AoC parsers rewritten

All of these ran as tests in `proto.sw`, with the error messages shown **[ran]** (the prototype's messages: §6.5 gives what the library says now), and are written here for the library as built (`{Parse}`, and `lines` leaving the final line break to the runner). Day 5 is `examples/accept/parse-aoc-day05.sw`; days 1, 4 and 8 and the robot are in `examples/accept/parse-basics.sw`. Each replaces the function named.

**2025 day 1** (`Turn.parse`): a keyword table, aoc-parse style.

```
def turn(): {Parse} Turn :=
  let direction := pick [("L", Left), ("R", Right)]
  direction (nat())

-- Parse.eachLine "R5\nX5" turn fails: "line 2, column 1: expected 'L' or 'R'"
```

**2025 days 2 and 5** (`Range.parse`, `parseRanges`, `parseDatabase`): a check of our own inside the parser, two sections, and line numbers that run through the whole input, so `parseLinesFrom` goes.

```
def range(): {Parse} Range :=
  spaces()
  let from := nat()
  spaces()
  char '-'
  spaces()
  let to := nat()
  spaces()
  Parse.ensure (from ≤ to) "the range ends before it starts"
  { from, to }

def ranges(): {Parse} (List Range) := sepBy1 range (() => char ',')

def database(): {Parse} Database :=
  let fresh := lines range
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
def idPair(): {Parse} (Nat, Nat) :=
  let left := nat()
  let gap := takeWhile1 "a space" isSpace
  let right := nat()
  (left, right)
```

**2025 day 4** (`parseGrid`, `findStray`): the grid, with line and column for a stray character, in one line instead of two hand-written loops. Checking that the rows are equally wide stays with the `Vec` conversion.

```
def cells(): {Parse} (List (List Cell)) := grid (() => pick [("@", Roll), (".", Floor)])

-- "@.\n.x\n" → "line 2, column 2: expected '@' or '.' or a line break or the end"
```

**2024 day 14** (not in the repository yet): `p=0,4 v=3,-3`.

```
def robot(): {Parse} Robot :=
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

It would elaborate to a parser: each literal piece to `text`, each hole to its type's parser, found by an interface (`interface Read (a: Type) = { read: () → {Parse} a }`, with instances for `Nat`, `Int`, `Char`, and `Text` meaning "up to the next piece"), and the arm to `Parse.all` with `optional`. So text patterns and parsers would be one thing, not two. It is a language change (patterns are elaborated by the compiler), so it's a later stage, behind its own design review.

### 6.4 Out of scope

Day 6 reads its worksheet in columns: the meaning is in the layout (which characters line up), not in a grammar. A grid parser can check the characters (`grid (() => satisfy …)`), but the transposition stays ordinary list code. The same goes for puzzles that read pictures (ASCII-art letters).

### 6.5 Error messages

Rewriting the AoC parsers with the library showed four faults in its messages, all fixed as Megaparsec 9.8 handles them: its `withHints` ignores hints when the error is a `fail` ("if the resulting continuation gets a ParseError that has custom data in it, the hints are ignored", [Text.Megaparsec.Internal](https://hackage-content.haskell.org/package/megaparsec-9.8.3/docs/src/Text.Megaparsec.Internal.html)), and `mergeError` keeps the longest unexpected prefix of errors at one point ("Our aim here is to choose the longest prefix", [Text.Megaparsec.Error](https://hackage-content.haskell.org/package/megaparsec-9.8.3/docs/src/Text.Megaparsec.Error.html)).

- **What was found.** A message that lists expectations ends with what the input holds there: `, got 'x'`, or `got the end of the line`, `got the end of the input`, `got a tab`. As Megaparsec's "unexpected" does, it shows as many characters as the longest text expected there (a `text` or `pick` word, noted as `Literal`), up to the end of the line: `mul ( 1,2)` against `pick` of `mul(`, `do()` and `don't()` gives `got 'mul ( 1'`, not `got 'm'`. `Parse.line` calls a line break in its text "a line break". The parser's own messages (`fail`, `ensure`) get nothing added: they say what they mean.
- **Hints.** What an attempt that didn't fail the parse expected is a hint, such as the digit `many1 digit` tried after the last one. A `fail` or `ensure` message at the same point replaces the hints, as Megaparsec's `fail` does, so a check after a repetition reads `expected at least 12 batteries, got 3`, not `…; expected a digit`. An "expected" failure keeps them, since they are real alternatives there: `expected a digit or the end of the line, got 'x'`.
- **The end of the line.** After a repetition, "a line break" (the next row may follow) and "the end" (the input may end) are both true but read as noise. A runner names them as one, "the end of the line"; on its own, "the end" is "the end of the input" in `Parse.all` and "the end of the line" in the line runners.
- **The blank line between sections.** Day 5 read `lines range`, then `blankLine`; a missing blank line came out as `expected a number or a line break`, vaguer than the hand-written `expected a blank line between the ranges and the ids, got none`. With `section range` it is `expected a number or a blank line, got the end of the input`, or, with ids straight after, `expected '-' or a blank line before this line, got the end of the line`.

The AoC days and examples, old message then new; each names the same point and says at least as much:

| Input | Before | Now |
|---|---|---|
| 2025 day 3, `123` | `line 1, column 4: expected at least 12 batteries, got 3; expected a digit` | `line 1, column 4: expected at least 12 batteries, got 3` |
| 2025 day 3, `1234567x9012` | `line 2, column 8: expected a digit or the end` | `line 2, column 8: expected a digit or the end of the line, got 'x'` |
| 2025 day 5, `3-5\nx-7\n\n1\n` | `line 2, column 1: expected a number or a line break` | `line 2, column 1: expected a number or a blank line before this line, got 'x'` |
| 2025 day 5, `3-5\n4-6\n` | `line 3, column 1: expected a number or a line break` | `line 3, column 1: expected a number or a blank line, got the end of the input` |
| 2025 day 5, `3-5\n\n1\ntwo\n` | `line 4, column 1: expected a number or the end` | `line 4, column 1: expected a number or the end of the input, got 't'` |
| 2024 day 5, `…\n3;4\n` | `line 4, column 2: expected ',' or a line break or the end` | `line 4, column 2: expected ',' or the end of the line, got ';'` |
| 2025 day 9, `7,1,2` | `line 1, column 4: expected the end` | `line 1, column 4: expected the end of the line, got ','` |
| 2024 day 3, `mul ( 1,2)` | `column 1: expected 'mul(' or 'do()' or 'don't()'` | `column 1: expected 'mul(' or 'do()' or 'don't()', got 'mul ( 1'` |
| 2025 day 7, `..S..\n..x..` | `line 2, column 3: expected . or ^ or S, got 'x'` (hand-written) | `line 2, column 3: expected '.' or '^' or 'S' or the end of the line, got 'x'` |

The rest only gain what was found, as `expected a number` → `expected a number, got 'x'`.

**2025 days 4 and 7.** Their grids are built by pure functions that the proofs are about, so a grammar can only check the input. `looseGrid` allows what their checks allow, no rows and rows of any length, empty ones too. Day 7's `manifoldError` is now `Parse.all` of `looseGrid (() => pick [(".", ()), ("^", ()), ("S", ())])` over the joined lines; its proof only splits on whether `manifoldError` gives a message, so it is untouched. Its messages quote the characters and add "or the end of the line", which is true, since a row may end anywhere. Day 4 keeps its hand-written `findStray`: its proof (`parseGridCells`) splits on `findStray`'s line, column and character, so a grammar there would change the proof.

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

### 7.4 The library as built

The same 100,000 lines, parsed by `point` (§4.2) with `Std.Parse`, summing the first numbers. Release build of this branch, 28 October, Apple silicon, other work on the machine **[ran]**. Times are user seconds; memory is the peak resident size of the process tree (`/usr/bin/time -l`).

| Variant | Machine | Peak (machine) | JS | Peak (JS) |
|---|---|---|---|---|
| Today's way, `split ','` (`split1.sw`, for comparison) | 0.68 | 242 MB | 0.61 | 347 MB |
| `Parse.eachLine input point` | 3.44 | 276 MB | 1.04 | 359 MB |
| `Parse.all input (() => lines point)` | 3.45 | 1,066 MB | 11.3 | 1,435 MB |

Per line, the library is as fast as the prototype (3.29 s machine, 0.99 s JS): the forwarding handlers that one ability needs (§4.4) don't show, because `point` makes no choice. On the whole input it is the same speed on the machine but uses four times the memory, and JS is eleven times slower. So `Parse.eachLine` stays the recommendation for line-per-record input. A real AoC input of a few thousand lines takes under 0.2 s and about 60 MB either way **[inferred: scaled]**.

### 7.5 Memory per operation, and scanning

AoC 2024 day 3 (scanning 18 KB of noise for `mul(…)`) used about 6.5 KB per input character, and day 5's whole-input parse about 1.5 KB.

**Cause** **[ran]**. The runtime runs a state-passing handler such as `runFrom` as a loop (crates/rt/src/fusion.rs, "State-passing handlers run as a loop"): a clause's `k v s′` in tail position becomes a jump of the loop. The pass follows tail positions through `let`, applied lambdas, `if` and `Decidable.elim`, but not through `match`, which elaborates to a call of a separate case-tree definition (`Term::Case` appears only at the top of a definition). `runFrom`'s `span` clause destructured a pair with `let (taken, after) := …`, and its `next` and `literal` clauses matched on the input; there `k` was the real continuation, which "runs the same loop from where the operation was": a nested loop whose frames stay until the parse ends. So every `span`, `next` and `literal` kept a frame for the rest of the parse, while `mark`, `reset` and `note` (written `k x s′` directly) did not. Small programs over random noise, release build, peak resident memory:

| program (per character) | 40 KB | 80 KB | 160 KB | growth per character |
|---|---|---|---|---|
| read the input as a `List Char` | 74 MB | 84 MB | 116 MB | about 400 B (the list) |
| one `next` (before) | 97 MB | 118 MB | 165 MB | 590 B |
| `many (satisfy any)`: 4 operations and an `optional` (before) | 178 MB | 285 MB | 501 MB | 2.7 KB |
| one `next` (after) | 89 MB | 95 MB | 120 MB | the list |
| `many (satisfy any)` (after) | 88 MB | 103 MB | 135 MB | the list and the result |

`many`'s fuel and the backtracking marks hold nothing extra: a mark is a pointer into the input list, and `optional`'s forwarding handler resumes lazily.

**Fix.** The clauses resume with `k step.fst step.snd` from helpers that return the pair (§6.1). Memory is now the input list (about 400 bytes a character on the machine) plus the result.

**Scanning.** `Parse.findAll` replaces day 3's hand-written `many`/`oneOf`/`filterMap` scan. Day 3 (`findAll instruction`), the real input repeated, release build, Apple silicon, load average 30 to 40 on the machine, so user time is the steadier figure; the 1.8 MB "before" runs were stopped at a 4 GB cap **[ran]**:

| | 180 KB, machine | 1.8 MB, machine | 180 KB, JS | 1.8 MB, JS |
|---|---|---|---|---|
| before (hand-written scan, old handler) | 3.5 s, 1,170 MB | over 4 GB at 11 s, stopped | 18.3 s, 1,970 MB | over 4 GB at 63 s, stopped |
| after (`findAll`) | 2.9 s, 142 MB | 22.1 s, 793 MB | 0.9 s, 111 MB | 4.5 s, 305 MB |
| `findAllStarting (char => char == 'm' ∨ char == 'd')` | 0.8 s, 135 MB | 4.1 s, 823 MB | | |

(Start-up is about 0.8 s of user time in these runs.) Memory now grows with the input, not with the operations. Time on the machine is still about 12 µs a character of noise for `findAll`: each try at a character makes about a dozen operations (marks, two failed `literal`s, notes, a `stop` and a reset), and each crosses two or three handlers (the alternative's `optional`, `findAll`'s own, `runFrom`). JS does the same work about five times faster. The same day-3 grammar with `findAllStarting` makes one `span` per stretch of noise and runs at about 0.2 s per 100 KB on the machine. Day 5 at 0.9 MB (the updates repeated 100 times): 17.3 s and 1,329 MB before, 12.6 s and 453 MB after.

A `findAll` that skips ahead by itself for any parser would need to know where a match can start. The parser's first operation doesn't tell: before it reads, a parser may look at `mark()`, whose offset differs at every character (`end` does, and `oneOf` always marks first), so a skip worked out from one failed try isn't sound in general. That is why the faster scan takes `starts` from the caller.

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

**Built** (with the lemmas of §6.1), each stated over `Parse.runFrom state` with the rest of the parser as `k`, and each by `rewrite` and `rfl` unless noted:

- Reading operations where the input has what they read: `runFromSpanThere` (the input starts with `taken`, all passing, and the next character, if any, doesn't), `runFromNextThere`, and the existing `runFromLiteralThere`. They rest on four new list lemmas: `List.takeWhileAppend`, `List.dropWhileAppend`, `List.dropWhileStops` and `List.spanAppend` (by induction).
- Pieces: `runFromTextThere`, `runFromCharThere` (with `Parse.sameChar`, `c == c` for a variable `c`, by a `match` on `Char.decEq`), `runFromNatThere` (a non-empty digit run followed by a non-digit or nothing; its value is `Nat.fromDigits` of the digits) and `runFromEndThere`.
- `optional`: `runFromOptional` (it marks the current point and runs `optionalFrom state.at parser`); `runFromOptionalFromSpan`, `…Next` and `…Literal` (the handler passes each reading operation on, so the parser's own lemmas apply under it); success, `runFromOptionalFromPure` (a parser that has given a value gives `Some` of it); and backtracking, `runFromOptionalFromStop` (a parser that has stopped leaves the input at the mark and gives `None`). `runFromOptionalTextThere` and `runFromOptionalTextNotThere` are the two cases for `text`.
- `oneOf`: `runFromOneOfFromSome` and `runFromOneOfFromNone`, by applying a hypothesis about `optional first`, and `runFromOneOfFromLast` by `rfl`. The hypothesis is stated for any `choose` and `finish` after `optional first`, because the elaborated `oneOfFrom` is a `bind` of a `bind`, and that form is what lets one application close the goal without `Effect.bindAssoc` and function extensionality. `oneOfFrom` now continues with a named `Parse.valueOr` rather than a `match`, so that the continuation can be written in the proof. `runFromOneOfExample` shows a concrete `oneOf` of two words computing after one `rewrite`.

Not proved: a lemma for `optional p` or `oneOf` over an arbitrary `p` given only a lemma about `p` on its own ("if `p` reads to state `s′` giving `v`, so does `optional p`"). The handler `optionalFrom` wraps every operation of `p`, so moving such a fact under it is an induction over `p`'s computation tree, with function extensionality at each `Call`, as `Effect.foldCompBind` does; `p` given as an opaque thunk has no tree to induct on without `match reify`, which splits only on its first step. For a concrete parser the run computes, as in `runFromOneOfExample`. No lemmas for `many`, `findAll`, `section` or `repeat`: each is a fuelled loop around `optional`, so each needs the same lifting first.

Rendel–Ostermann style "one description, parser and printer" (§3.3) would give round trips by construction. Too much machinery for this library; not recommended.

## 9. Staged plan

Each stage is one lane.

1. **Built, 28 October.** **`Std.Parse` core.** The ability, the handler, `Parse.all` and `Parse.eachLine`, the pieces and combinators of §6.1, `label`, `recursive`, furthest-failure errors with line and column. Tests: §6.2's examples and their messages, a `many` over a parser that reads nothing, left recursion failing. A guide section in chapter 8. About 400 lines.
2. **Dogfood on AoC.** Rewrite the `parse*` functions of 2025 days 1, 2, 3, 4, 5, 7, 8, 9 and 2024 day 1 with it, delete `parseLinesFrom` and the hand-written error loops of days 4 and 7. Note what was awkward; fix the library, or file language gaps.
3. **Bridging lemmas** (§8.1) and `nat`'s round trip.
4. **`Text.scan`** and a native `Text.splitFirst`.
5. **Text patterns in `match`** (§6.3): a separate design note first; it's a language change.
6. **Only if needed:** the native text cursor of §7.3.

## 10. Open choices

**`many` over a parser that matched without reading: stop, or fail?** Stopping (the prototype) can never loop and never surprises a correct parser. Failing ("`many`: the parser matched without reading anything") is what Parsec, nom and winnow do, because it's always a bug in the parser. *Recommendation: fail, with that message.* A silent stop hides the bug until some input exercises it. **Decided (Matt): fail**, as built.

**The row: `{Parse, Fail}`, or `{Parse}` alone with its own `fail` operation?** One ability reads better in signatures. But reusing `Fail` lets `ensure`, `need`, `toNatOrFail` and `Fail.context` work inside parsers unchanged, and keeps one failure story in std. *Recommendation: `{Parse, Fail}`.* **Decided (Matt): `{Parse}` alone**, following Unison's libraries, with `Parse.fromFail` as the bridge (§4.4).

**Backtracking: always (PEG), or only before input was read (Parsec), with a `try`?** *Recommendation: always.* Puzzle input is small, and furthest-failure errors are as sharp as the consumed-input rule's. **Decided (Matt): always**, with no `try`.

**Default runner: whole input or per line?** *Recommendation: offer both, with the same messages; recommend `Parse.eachLine` in the guide for one-record-per-line input*, because it is 1.3 to 15 times faster and uses a fifth of the memory on large inputs (§7). **Still open.** Both are built, and the guide recommends `Parse.eachLine`. On 100k lines the whole-input runner takes the same time on the machine but four times the memory, and eleven times as long in JS (§7.4).

**Where do errors from our own checks point?** `ensure (from ≤ to)` in `range` reports the column where the parser had got to (the range's end). Pointing at the range's start needs a `located` wrapper. *Recommendation: the current place, and no `located` until a puzzle wants it.*

**Text patterns in `match` (§6.3): pursue?** *Recommendation: yes, but after stage 2*, when the library's own `Read`-style pieces exist to elaborate holes to.

## 11. Language gaps met

None blocks the recommended design. In order of how much they matter here:

1. **No do-notation or user operators (D1207)**: rules out data-style parsers (§4.2). Abilities sidestep it.
2. **Ability operations can't be polymorphic in their result**: rules out option C (§4.1). The prototype's `optional` used `Fail.recover` and `reset` instead. With one ability, the built one handles `Parse` and passes the other operations on (§4.4).
3. **Termination checker**: `| [] | [p] | [p, ..ps]` with a recursive call inside a `match` is refused, pure or effectful (`term1.sw`). Small; worth a ticket.
4. **A type can't contain itself inside a `List`** (`E-POSITIVITY`): tree-shaped puzzle input needs a tree and a forest defined together.
5. **`Text.uncons` copies on the machine**, and a `List Char` costs about 420 bytes per character: fine per line, heavy for a whole large input (§7).
6. **No `DecEq` instance for `()`** (met in stage 1): `test … := lineResult "a" (() => char 'a') == Ok ()` is refused with `E-INSTANCE-NONE: no DecEq instance for ()`. The library's tests compare the error text instead.
7. **A handler must list every operation** (abilities.md, "Coverage"): `optional` and `label` each repeat six clauses that pass operations on unchanged.

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

Libraries: [Parsec](https://hackage.haskell.org/package/parsec-3.1.17.0/docs/Text-Parsec.html), [Parsec source](https://hackage.haskell.org/package/parsec-3.1.17.0/docs/src/Text.Parsec.Prim.html), [Megaparsec](https://hackage.haskell.org/package/megaparsec-9.6.1/docs/Text-Megaparsec.html), [attoparsec](https://hackage.haskell.org/package/attoparsec-0.14.4/docs/Data-Attoparsec-ByteString.html), [Angstrom](https://github.com/inhabitedtype/angstrom), [Parseff](https://ocaml.org/p/parseff/0.3.0/combinators.html), [fastparse](https://com-lihaoyi.github.io/fastparse/), [cats-parse](https://github.com/typelevel/cats-parse), [nom `many0`](https://docs.rs/nom/latest/nom/multi/fn.many0.html), [winnow `repeat`](https://docs.rs/winnow/latest/winnow/combinator/fn.repeat.html), [chumsky](https://docs.rs/chumsky/latest/chumsky/), [Lean `Std.Internal.Parsec`](https://github.com/leanprover/lean4/blob/master/src/Std/Internal/Parsec/Basic.lean), [Koka `std/text/parse`](https://github.com/koka-lang/koka/blob/master/lib/std/text/parse.kk), [Effekt frontend case study](https://effekt-lang.org/docs/casestudies/frontend), [Idris 2 `Text.Parser.Core`](https://github.com/idris-lang/Idris2/blob/main/libs/contrib/Text/Parser/Core.idr), [Idris 2 `Text.Parser`](https://github.com/idris-lang/Idris2/blob/main/libs/contrib/Text/Parser.idr), [agdarsec](https://github.com/gallais/agdarsec), [unison-parsers](https://github.com/zenhack/unison-parsers), [@rlmark/parsing](https://share.unison-lang.org/@rlmark/parsing), [@dfreeman/yap](https://share.unison-lang.org/@dfreeman/yap), [Eff](https://github.com/matijapretnar/eff).

Pattern helpers: [Python `parse`](https://pypi.org/project/parse/), [aoc-parse](https://docs.rs/aoc-parse/latest/aoc_parse/), [scan_fmt](https://docs.rs/scan_fmt/latest/scan_fmt/), [Kotlin `destructured`](https://kotlinlang.org/api/core/kotlin-stdlib/kotlin.text/-match-result/destructured.html), [Scala 3 string interpolation](https://docs.scala-lang.org/scala3/book/string-interpolation.html).

Papers: Hutton and Meijer, [Monadic Parser Combinators](https://people.cs.nott.ac.uk/pszgmh/monparsing.pdf) (1996); Swierstra, [Combinator Parsing: A Short Tutorial](https://ics-archive.science.uu.nl/research/techreps/repo/CS-2008/2008-044.pdf) (2008); Danielsson, [Total Parser Combinators](https://www.cse.chalmers.se/~nad/publications/danielsson-parser-combinators.pdf) (ICFP 2010); Allais, [agdarsec](https://gallais.github.io/pdf/agdarsec18.pdf) (2018); Rendel and Ostermann, [Invertible Syntax Descriptions](https://www.informatik.uni-marburg.de/~rendel/unparse/rendel10invertible.pdf) (Haskell 2010); Delaware et al., [Narcissus](https://arxiv.org/abs/1803.04870) (ICFP 2019); Bauer and Pretnar, [Programming with Algebraic Effects and Handlers](https://arxiv.org/pdf/1203.1539); [A Calculus for Scoped Effects & Handlers](https://arxiv.org/pdf/2304.09697) (2023).

In this repository: [abilities.md](abilities.md), [effect-runtime.md](effect-runtime.md) §9.11, [compact-text.md](compact-text.md), [well-founded-recursion.md](well-founded-recursion.md), `crates/elab/src/std/{Fail,Each,Text}`, `crates/rt/src/prims.rs`, `aoc/src/Aoc/`.
