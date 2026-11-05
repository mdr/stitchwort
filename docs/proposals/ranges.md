# Ranges, `a ..< b` and `a ..= b` (SW-1356)

**Status:** design note, 5 November 2026, for Matt's decisions (§14). No
implementation yet. Background: D2403. The prompt was Day 17 of 2021,
`List.range (Int.toNat target.right)`, and Matt asked about Haskell's
`[2..n]`. He asked for a thorough look at what other languages do first
(§3).

Claims about Stitchwort are **[checked]** when I read or ran the thing named
(on `main` at `a6abce4d2`), and **[estimate]** when they are my reading of
what will happen. Claims about other languages were checked against the
official documentation or the language's source code, at the URLs under
"Sources". Where I couldn't check one, it is marked **unverified**.

## 1. In short

- **The problem.** The library counts with three functions:
  - `List.range n` gives 0 to n − 1.
  - `List.rangeFrom count start` gives the count first and the start
    second. That order has caused at least one real mistake (SW-1236,
    SW-1258).
  - `List.between lo hi` includes both ends.

  So "1 to n" is written three ways, sometimes in one file. The 2025 day 2
  proofs write `List.between 2 size` and `List.rangeFrom (size - 1) 2` for
  the same list. Ranges over `Int` don't exist, so Day 17 converts its
  bound to `Nat` and adds 1 to every element afterwards. There are about
  1,100 uses (§2), and 85% of those in aoc are in proofs.
- **The change.**
  - `a ..< b` is the numbers from `a` up to, not including, `b`.
  - `a ..= b` is the numbers from `a` through `b`.
  - Both are ordinary `List`s: everything that works on a list works on a
    range, and every list lemma applies.
  - There is no bare `a..b`, and no bracket form `[a..b]`. Both get an
    error that says what to write. This avoids the clash with the spread
    `[x, ..xs]`, and the question of which ends `..` includes, which
    languages answer in opposite ways (§3, §4).
  - Steps and counting down are methods (`.reverse`), not syntax (§8).
  - Ranges come for `Nat` first and `Int` second (§7).
- **What it does.**
  - `x ∈ a ..< b ↔ a ≤ x < b` is a library lemma, and `auto` and `omega`
    use it, so it pairs with chained comparisons.
  - Goals print a range back as `a ..< b`.
  - `List.range`, `List.rangeFrom` and `List.between` become one function
    with named ends, `List.range (from := a) (until := b)`, whose notation
    is `a ..< b`. That settles SW-1258's argument-order question for ranges.
- **Nothing breaks.** `..<` and `..=` are parse errors today (§4.1), so no
  program changes meaning. The sweep of the existing sites is separate and
  optional.
- **Size.** About 6 to 8 hours over four lanes, plus the sweep (§13).

## 2. What happens today

### 2.1 The library

In crates/elab/src/std/List/Toolkit.sw:244-255 **[checked]**:

```
def List.rangeFrom (count: Nat) (start: Nat): List Nat := …   -- `List.rangeFrom 3 5` is `[5, 6, 7]`
def List.range (n: Nat): List Nat := List.rangeFrom n 0
def List.between (lo: Nat) (hi: Nat): List Nat := List.rangeFrom (hi + 1 - lo) lo
```

`rangeFrom` recurses on the count, which is why the count comes first. Its
lemmas are stated in count form:

- `List.memRangeFrom` (Toolkit.sw:482) and `List.memRangeFromIntro`
  (Lemmas.sw:1019) give `s ≤ x ∧ x < s + c`, one direction each.
- `List.lengthRangeFrom`, `List.rangeFromAppend` (Lemmas.sw:108),
  `List.mapRangeShift` (:731), `List.distinctRangeFrom` (:1099).
- `List.sumRangeLast` (Split.sw:342) and the `List.sumRange*` family
  (SortLemmas.sw:336-384).
- `between` has its own `memBetween`, `lengthBetween`, `distinctBetween`
  and `sortedBetween`.

Two parts of the compiler know about the count form:

- **The unifier** has a rule for `List.rangeFrom (Succ ?hi - ?lo) ?lo`
  (crates/elab/src/unify.rs:241, SW-896).
- **`rewrite`** has congruence lemmas, `List.foldLeftCongRange` among them,
  that give the facts `s ≤ x` and `x < s + c` (crates/elab/src/congruence.rs:13).

`Fin.all n: List (Fin n)` (std/Fin/Fin.sw:61) lists the positions below `n`,
and `Fin.instFinite` is built from it.

### 2.2 Uses

These are counts of occurrences from `rg -o` over `*.sw` **[checked]**:

| | `List.range` | `List.rangeFrom` | `List.between` |
|---|---|---|---|
| std (crates/elab/src/std) | 106 | 184 | 33 |
| aoc/src | 441 | 152 | 86 |
| games | 21 | 0 | 1 |
| examples | 60 | 19 | 6 |

The 679 uses in aoc split into 578 in `Proofs/`, 39 in `Spec/`, 27 in
`Tests/` and 35 in the programs. So ranges are mostly a proof-writing
matter, and the design has to work for proofs first.

Some shapes stand out:

| Shape | Uses | What it means |
|---|---|---|
| `List.range (x + 1)` | 20 | "0 through x" |
| `List.rangeFrom n 1` | 43 | "1 through n" |
| `List.range (Int.toNat …)` | 4 | Day 17 2021 |
| `List.range n` followed by `.reverse` | 2 | counting down |
| a range then a stepping `.map` (`i => 2 * i`) | 0 | |
| `List.range n` followed by `.map (_ => …)` | 2 | n draws from `Random`, in games/rogue/src/Rogue/Generate.sw:33-34 |

`aoc/src/Aoc/Common/Range.sw` already has its own
`type Range = { from: Nat, to: Nat }`, with `contains`, `size` and `ids`.
Its `ids` is `List.rangeFrom (count := range.size) (start := range.from)`.

### 2.3 What `..` already means

`..` is one token, `Tok::DotDot` (crates/syntax/src/lexer.rs:627-630)
**[checked]**. It is used in these places:

- **List spreads in expressions:** `[x, ..xs]`, `[..xs, y]`, `[..xs]`, any
  number of times (docs/syntax.md, "List spreads"; D2325).
- **List rest patterns:** `[x, ..rest]`, last only.
- **Record and constructor patterns:** `{ name, .. }`.
- **Imports:** `import N (..)`.
- **Fact lists:** `omega [..]`.

Run on today's binary **[checked]**:

```
def t (n: Nat): List Nat := [2..n]     -- E-PARSE: expected `,` or `]`, but found `..`
def t (n: Nat): List Nat := [2, ..n]   -- E-TYPE-MISMATCH: expected `List Nat`, but this has type `Nat`
def t (n: Nat): List Nat := [..n]      -- the same
match n with | 1 ..= 9 => …            -- E-PARSE: expected `=>`, but found `..`
```

So Haskell's `[2..n]` is free today, but it would sit one comma away from
the spread `[2, ..n]`. With a list `n`, both versions type-check.

## 3. What other languages do

### 3.1 The survey

"Excl." means up to but not including the end, and "incl." means through
the end.

| Language | Exclusive | Inclusive | Steps, counting down | `5 to 1` gives | What a range is | In patterns |
|---|---|---|---|---|---|---|
| **Swift** | `a..<b` | `a...b` | `stride(from:to:by:)`, `stride(from:through:by:)` (unverified) | a run-time trap: "Range requires lowerBound <= upperBound" | a `Range` / `ClosedRange` value. Any `Comparable` type, but only integer-like types can be iterated | yes, via `~=` (unverified) |
| **Rust** | `a..b` | `a..=b` | `.step_by(k)`, `.rev()` | empty | structs `Range` / `RangeInclusive` with `start`, `end`, `contains`. An iterator when the element type implements `Step`. Not `Copy` | `a..=b`, and since 1.80 also `a..b`. Integers, `char`, floats. Must be non-empty |
| **Kotlin** | `a..<b` (stable since 1.8), `a until b` | `a..b` | `step k`, `downTo` | empty (unverified) | `IntRange`, `CharRange`, a "progression" with `first`, `last`, `step` | `in a..b ->` in `when` |
| **Haskell** | none | `[a..b]` | `[a, a+s .. b]` | `[]` (Report §3.10) | a lazy list, for any `Enum` type. `[a..]` is infinite | no |
| **Python** | `range(a, b)` | none | `range(a, b, s)`, negative `s` | empty | a sequence object with O(1) `in` | no |
| **Scala** | `a until b` | `a to b` | `by s` | empty (unverified) | a `Range` (start, end, step) in constant space; `NumericRange` for others | no |
| **Ruby** | `a...b` | `a..b` | `.step(s)`, `%` | no values | a `Range`, for anything with `<=>`. Endless `a..` and beginless `..b` | `when 1..50` (by `===`) |
| **Julia** | none | `a:b` | `a:s:b`, `b:-1:a`, `reverse` | empty, stored as `5:4` | `UnitRange`, `StepRange` | no |
| **Lean 4** | `[a:b]` (old), `a...<b` (since 4.22) | `a...=b` (since 4.22) | `[a:b:s]` (old); none in the new syntax so far | empty | old: `Std.Range`, `Nat` only, for `for` loops. New: polymorphic ranges, also for slices | no |
| **Idris 2** | none | `[a..b]` | `[a, b..c]` | counts down (`Nat`) | a `List`, through the `Range` interface | no |
| **Agda** (stdlib) | `upTo n` | none | `downFrom n` | | `List ℕ`; `allFin n : List (Fin n)` | no |
| **F#** | none | `[a..b]`, `seq { a..b }` | `[a..s..b]`, `[10 .. -1 .. 1]` | empty (unverified) | a list, array or seq | no |
| **Elixir** | none | `a..b` | `a..b//s` | counts down when no step is given, which is deprecated: write `//-1` | a struct `%Range{first, last, step}` | `x in a..b` in guards (unverified) |
| **C#** | `a..b`, for indexing only | none | none | | `System.Range`, of `Index`es; `^1` counts from the end | no |
| **C# LINQ** | `Enumerable.Range(start, count)`, taking a count, not an end | | | | lazy | |
| **Go** | `for i := range n`, 0 to n − 1 (since 1.22) | none | none | | no value | no |
| **JavaScript** | none; `Iterator.range` is a stage 2 proposal | | `Iterator.range(1, 100, 2)` | | | |
| **Zig** | `for (0..n)` only | `a...b` in `switch` arms only | none | | no value | `switch` arms, inclusive |
| **Nim** | `a..<b` | `a..b` | `countup`, `countdown` | | `HSlice` | |
| **Odin** | `a..<b` | `a..=b` | `#reverse` | | loops and `switch` only | `switch` cases, e.g. `'A'..='Z'` |
| **Raku** | `a..^b`, `^n` | `a..b` | `...` (the sequence operator) | empty | lazy when open-ended | `~~` |
| **Dart** | none (`Iterable.generate(count, f)`) | | | | | |
| **Perl** | none | `a..b` in list context (a flip-flop in scalar context) | none | the empty list | a list | no |
| **D** | `a .. b` (`foreach`, slices), `iota(a, b)` | none | `iota(a, b, s)` | empty | a lazy range | no |
| **Ada** | none | `for I in A .. B` | `reverse` | the loop runs no times | a subtype | `case` choices (unverified) |

### 3.2 What the survey says

- **`..` alone means different things.** It includes the end in Kotlin,
  Ruby, Perl, Elixir, Nim, F#, Raku and Haskell (`[a..b]`). It stops
  before the end in Rust, C# and D. Anyone reading `0..n` has to know
  which language they're in.
- **The newer designs spell out the end.** Swift (`..<`, `...`), Kotlin
  (it added `..<` because `until` reads as if it included its bound), Odin
  and Nim (`..<`, `..=`), Rust (`..=`), and Lean 4's 2025 syntax (`...<`,
  `...=`) all do this.
  - Rust waited years before allowing exclusive ranges in patterns,
    because of "confusion and increase the chance of off-by-one errors"
    (its 1.80 release notes).
  - Kotlin's case for `..<` was the same.
- **Ruby's `..` against `...`** is the best-known trap. The two spellings
  differ by a dot and mean different things. Zig has a milder form of it:
  `0..n` is exclusive in a `for` loop, but `a...b` is inclusive in a
  `switch`.
- **Reversed bounds give the empty range almost everywhere:** Rust,
  Haskell, Python, Julia, Raku, Perl, D, Ada and Ruby. Swift traps at run
  time. Elixir counted down and has deprecated it. Idris 2 counts down on
  `Nat`. In a total language only "empty" is available, and it is what
  `List.between 5 0 == []` already does.
- **Counts against ends.** `Enumerable.Range(start, count)` in C#,
  `List.range' start len` in Lean, and Stitchwort's own
  `List.rangeFrom count start` all take a count. Each is a known source of
  confusion. Python's, Rust's and Swift's ranges take two ends.
- **Steps are rare and are never the base syntax**, except in Haskell and
  F#. Haskell gives the second element, not the step: `[1, 3 .. 9]`.
  Float steps are a known trap: Haskell's report lets `[0.1, 0.2 .. 1.0]`
  go past the end by half a step.
- **What a range is.** The lazy-list languages (Haskell, Idris, F#, Agda)
  make a range a list. The others make it a small value (start, end,
  maybe a step) with O(1) `contains` and `size` that can also be iterated
  (Rust, Swift, Kotlin, Python, Scala, Ruby, Elixir, Julia). The value
  only pays off with a lazy sequence or an iterator protocol to plug into,
  and Stitchwort has neither (§6).
- **Two habits to guard against:**
  - Writing a range inside brackets, `[0 ..< n]`, which in a language
    where a range is a list makes a list of one list. Rust's `vec![0..n]`
    is the same trap. I remember Clippy has a lint for it, but that is
    unverified.
  - Writing `0..n.len()` and getting `0..(n.len())`. This one is usually
    what was wanted, and it is in Stitchwort too (§11).

## 4. Syntax

### 4.1 The options

1. **`a ..< b` and `a ..= b`**, as in Odin, with the same meanings in
   Swift (`..<`), Kotlin (`..<`), Nim (`..<`) and Rust (`..=`). Each form
   says where it stops, so neither needs to be remembered.
   - Both are new tokens. `..` followed by `<` or `=` can't occur in a
     valid program today: a spread's list doesn't start with `<` or `=`,
     and `{ x, .. }` is followed by `}`.
   - Outside brackets they are unambiguous. Inside, `[x, ..<n]` would now
     lex as `..<` and fail to parse as a spread. That's harmless, since it
     didn't mean anything before either.
2. **Haskell's `[a..b]`.** Free today, but `[2..n]` and `[2, ..n]` differ
   by one comma, and `[..n]` is already a spread. It also forces inclusive
   ends, gives no exclusive form, and puts the range in brackets, which
   look like a list literal. Not recommended.
3. **A bare `a..b`, as in Rust or Kotlin.** It has the clash with `..xs` in
   a lighter form (`[a, ..b]` against `[a..b]`), and half the languages
   read it as inclusive while the other half read it as exclusive. Not
   recommended.
4. **Ruby's `a..b` and `a...b`.** Its known trap. Not recommended.
5. **Words, `a to b` and `a until b`, as in Scala.** These read well, but
   they are two new reserved words, and they clash with names already in
   use. `to` is a field of `Aoc.Common.Range`, and `until` would become a
   parameter name in §6. Not recommended.
6. **Julia's `a:b`.** `:` is type ascription. Not possible.
7. **Functions only:** `List.range (from := 2) (until := n + 1)`. No
   syntax at all. This is the base of option 1 anyway (§6), and it is
   enough on its own if Matt wants no new syntax.

I recommend option 1 on top of option 7 (R1).

- **Spaces.** Ranges are written with spaces, `0 ..< n`, like the other
  binary operators. The formatter puts them in.
- **Unicode.** Unicode is optional elsewhere in the language. No standard
  symbol exists for either form, so I propose none.

### 4.2 The error for the forms not taken

`a .. b` or `a..b` after an operand is an `E-PARSE` whose message says what
to write: "a range is `a ..< b` (up to, not including, `b`) or `a ..= b`
(through `b`)". Inside brackets (`[2..n]`) the message also says that the
spread is `[2, ..n]` and that a range needs no brackets.

### 4.3 Both forms

Should both forms be kept, or just one?

- **Exclusive is needed** for indices: `0 ..< xs.length`, 568 uses of
  `List.range n` today.
- **Inclusive is needed** for puzzle text: "1 to n", "from `low` to
  `high`", the 126 uses of `between`, and the 43 uses of `rangeFrom n 1`.

Swift, Kotlin, Rust, Odin and Nim all have both. Without one of them, every
site of the other kind is written with a `+ 1` or a `- 1`, which is the
off-by-one these designs are meant to prevent. I recommend both (R2), with
`a ..= b` meaning exactly `a ..< b + 1` (§6).

## 5. Ranges in brackets, and in spreads

- **A range in brackets.** A range is a list, so `[0 ..< n]` is a list of
  one list. This is the Haskell habit (§3.2), and it is almost never
  meant. I propose the warning `W-RANGE-IN-BRACKETS`: "this is a list with
  one element, the range `0 ..< n`; a range is already a list, so drop the
  brackets". It appears when a list literal has a range as its only item.
  The rare case that means it writes `[(0 ..< n)]`.
- **A range in a spread.** A spread takes everything up to the next `,` or
  `]` as its list, so `[0, ..2 ..< n]` and `[..0 ..< 3, 7]` already work
  once a range is a list. The formatter leaves them alone.

## 6. What a range is

### 6.1 The options

- (a) **A `List Nat`, as the call of a named function.** `a ..< b` is
  `List.range a b`, and `List.range (from: Nat) (until: Nat) :=
  List.rangeFrom (until - from) from`.
  - Every list function, lemma, `.map`, `.all`, `|>`, `each`, `sumBy`, `in`
    and `attach` works as it is.
  - Goals print the call back as `a ..< b`, as `List.append` prints as
    `++`.
  - It is the representation Haskell, Idris, F# and Agda use.
- (b) **A `Range` record `{ from, until }`** with `toList`, `contains`
  (O(1)), `size`, `map`, `all` and so on, as in Rust, Swift, Kotlin and
  Python.
  - `x in r` could be the proposition `r.from ≤ x < r.until` itself.
  - But every list operation would have to be written again for `Range`,
    or reached through `.toList`, and the lemmas twice. The 578 uses in
    proofs all go through list lemmas today.
  - The benefits of a value need an iterator protocol or laziness, and
    Stitchwort has neither: its loops are `.map`, `.foldLeft`, `.all` and
    `each`, all on lists.
- (c) **The same record, turned into a list by the expected type**, as
  `NonEmptyList` brackets are. That costs two meanings for one piece of
  text, and a rule about which one a pipe or a `.method` gets, all to save
  allocation that nothing has needed so far.

I recommend (a) (R3). Two costs come with it:

- **Allocation.** `0 ..< 1000000 |> .sumBy f` builds a million cons cells
  before summing. That is true of `List.range` today, and no site has
  needed better. If a site does, the backends can fuse the
  `List.rangeFrom` consumers into loops later, without changing the
  language.
- **A membership test walks the list.** As a `Bool`, `x in 0 ..< n` would
  be decided by walking the list. §9.2 deals with that.

### 6.2 The terms

- `a ..< b` is `List.range a b`.
- `a ..= b` is `List.range a (b + 1)`.
- Both elaborate to calls of the definition. They are not unfolded to
  `rangeFrom`, so that goals can print them back.
- `List.range a b` is `List.rangeFrom (b - a) a` by its definition, so
  every existing `rangeFrom` lemma applies after unfolding, and so does the
  SW-896 unifier rule.

Some useful equations hold by `rfl`, because `-` recurses on its second
argument **[estimate]**:

- `0 ..< n` is `rangeFrom n 0`.
- `0 ..< n + 1` is `[0, ..1 ..< n + 1]`.
- `1 ..= n` is `rangeFrom n 1`.
- `2 ..= size` and `List.rangeFrom (size - 1) 2` are the same term after
  unfolding. Today's 2025 day 2 proofs mix the two.

**The printer** shows `List.range a (b + 1)` as `a ..= b` and every other
`List.range a b` as `a ..< b`. So `0 ..< n + 1` written by hand prints as
`0 ..= n`. The two are the same term, so this loses nothing.

### 6.3 `List.range`, `rangeFrom` and `between`

This is SW-1258's question.

- **One function with two ends** removes the count-first order from
  everything a user writes:
  - `List.range n` becomes `0 ..< n`.
  - `List.between lo hi` becomes `lo ..= hi`.
  - `List.rangeFrom n 1` becomes `1 ..= n`.
  - Anyone who wants words instead of symbols writes
    `List.range (from := 1) (until := n + 1)`.
- **`rangeFrom` stays** as the form that recursion and induction use,
  because its count goes down by one per step. It keeps the named
  parameters it has today, so `List.rangeFrom (count := c) (start := s)`
  reads right.
- **`List.between` goes**, along with its five lemmas, which are
  `List.range`'s lemmas at `b + 1`.
- **The one-argument `List.range n` goes too.** `List.range 5` becomes a
  partial application, and the error points to `0 ..< 5`.

Decision R4 covers this. Migration cost doesn't count, so the question is
only how the end state reads.

## 7. Which types

- **`Nat`.** Every site in §2 uses `Nat`. This comes first.
- **`Int`.** Day 17 wants `1 ..= target.right` on `Int`, so that `aimed`
  can use the velocity directly instead of `i.toInt + 1` (Day17.sw:94-99,
  **[checked]**). Grids with negative coordinates would want it too.
  - It would be `Int.range a b := (0 ..< (b - a).toNat).map (i => a +
    i.toInt)`, with its own membership and length lemmas, proved by
    `omega`.
  - The elaborator chooses the definition by the operands' type, as it
    does for `<` and `+` on `Nat` and `Int`.
- **`Char`.** `'a' ..= 'z'` reads well, and Kotlin, Rust and Odin have it.
  No site builds a list of characters by counting today **[checked]**, and
  the tests that do exist are comparisons, now chains. So `Char` waits for
  a site that needs it, and would get a `Char.range` of the same shape.
- **Any ordered type with a successor**, through an interface, as Haskell's
  `Enum`, Rust's `Step` and Lean 4's new polymorphic ranges do.
  - Such an interface needs laws (the successor is the next element, the
    distance counts steps), and the membership lemma is proved once from
    those laws.
  - That is more design than three types need, and nothing else in the
    library would use the interface yet.
  - I recommend dispatching on `Nat` and `Int` by type, with an interface
    only if a user's own type asks for ranges (R5).

## 8. Steps and counting down

- **Reversed bounds** give the empty list: `5 ..< 1 = []` and `5 ..= 1 =
  []`, as in nearly every language (§3.2) and as `List.between` does
  today. A total language can't trap, and counting down silently (as
  Elixir did) turns a wrong bound into a wrong answer.
- **Counting down** is `(a ..< b).reverse`, or `a ..< b |> .reverse`. There
  are two sites (§2.2), and both already use `.reverse`. The library has no lemma
  for membership in a reversed list yet **[checked]**; `List.memReverse`
  (`x ∈ xs.reverse ↔ x ∈ xs`) would come with §9.1. I propose no `downTo`.
- **Steps.** No site uses one **[checked]**. A range followed by
  `.map (i => 2 * i)` says what it does. If one is wanted later, it would
  be a function with named arguments,
  `List.stepRange (from := 0) (until := 10) (by := 2)`, not syntax.
  Haskell's "give the second element" form and F#'s `a..s..b` both add a
  third operand that is easy to misread. Decision R6.

## 9. Membership and the lemmas proofs need

### 9.1 The lemmas

These are stated with the notation, in `Std.List`. The names are a first
proposal.

| Lemma | Statement | Replaces |
|---|---|---|
| `List.memRange` | `x ∈ a ..< b ↔ a ≤ x < b` | `memRangeFrom` and `memRangeFromIntro` (one direction each), `memBetween` |
| `List.lengthRange` | `(a ..< b).length = b - a` | `lengthRangeFrom`, `lengthBetween` |
| `List.rangeEmpty` | `b ≤ a → a ..< b = []` | |
| `List.rangeCons` | `a < b → a ..< b = [a, ..a + 1 ..< b]` | |
| `List.rangeSnoc` | `a ≤ b → a ..= b = [..a ..< b, b]` | `sumRangeLast`'s step |
| `List.rangeAppend` | `a ≤ b ≤ c → (a ..< b) ++ (b ..< c) = a ..< c` | `rangeFromAppend` |
| `List.mapRangeShift` | `(a + 1 ..< b + 1).map f = (a ..< b).map (i => f (i + 1))` | the same name, restated |
| `List.distinctRange` | `(a ..< b).Distinct` | `distinctRangeFrom`, `distinctBetween` |
| `List.sortedRange` | sorted | `sortedBetween` |
| `List.sumByRange*` | the existing `sumRange*` family, restated | |

The `↔` form pairs with chained comparisons, which merged today:

- From `h: x ∈ 0 ..< n`, `(List.memRange.mp h).right` is `x < n`.
- In the other direction, `List.memRange.mpr (Both (omega) (omega))`
  proves the membership.

Two parts of the compiler should know the lemma:

- **`auto`** and **`omega`** should take `x ∈ a ..< b` apart into
  `a ≤ x` and `x < b`, the way `auto.rs`'s `membership_facts` already
  collects memberships. This turns the common
  `List.memRangeFromIntro i n 0 (omega) (omega)` (GridGraph.sw:64,
  Day17 Answers.sw:27) into `auto`.
- **The congruence lemmas** (`foldLeftCongRange` and the others) should be
  stated over `List.range a b`, so `rewrite` under `.map` and `.sumBy` of a
  range gets the bounds.

### 9.2 `in` and the membership test

In a proposition, `x in a ..< b` is `List.Mem x (List.range a b)`, the same
term as any other membership. That matters, because the facts proofs get
from `List.memMap`, `List.all` and `each` are memberships.

As a `Bool` (`if x in 0 ..< n`), the decision would walk the list. I
propose that the elaborator decide a membership whose right side is a
written range by `a <= x && x < b`, carried through `List.memRange`. The
proposition stays `List.Mem` and the test costs O(1). The alternative is a
warning that suggests the chain `a <= x < b`. Decision R7, in a later lane.

## 10. Patterns, guards, `Fin`, loops

- **Patterns.** `| 1 ..= 9 =>` exists in Rust, Swift, Kotlin (`in` in
  `when`), Odin and Zig.
  - Today a guard with a chain does the same: `| n if 1 <= n <= 9 =>`,
    since pattern guards and chained comparisons both exist.
  - A range pattern would need interval reasoning in the coverage checker,
    which reports "numbers other than 0 and 1" today, and an equation for
    each arm.
  - The one site that would gain is `Char.isAsciiSpaceCode`'s
    `| 9 | 10 | 11 | 12 | 13 | 32` (std/Text/Basics.sw:31), which would
    become `| 9 ..= 13 | 32`.
  - I recommend leaving range patterns out for now. If they come, they
    should follow Rust and require a non-empty range (R8).
- **`Fin`.** `Fin.all n` stays. A `0 ..< n` of `Fin n` would need ranges on
  `Fin`, whose `+ 1` isn't closed. Where a proof needs `i < n` for each
  `i`, `(0 ..< n).attach` with `List.memRange` gives it. That is the
  counterpart of Lean's `for h : i in [0:n]`.
- **Loops.** Stitchwort has no `for`. Its loops are `.map`, `.all`,
  `.foldLeft`, `.sumBy` and `each`, and all of them take a range as it is:
  `0 ..< height |> .flatMap (row => …)`,
  `let a := each (1 ..= n)`. Nothing new is needed. A `for` statement, if
  one ever comes, would take any list.

## 11. Precedence, the formatter, errors

**Level.** A range sits between `|>` (level 7) and `++` (level 8) in
docs/syntax.md's table, and is not associative. So:

| Written | Means |
|---|---|
| `a ..< b + 1` | `a ..< (b + 1)` |
| `0 ..< xs.length` | `0 ..< (xs.length)`, the wanted reading |
| `-3 ..= 3` | `(-3) ..= 3` (`Int`) |
| `0 ..< n \|> .map f` | `(0 ..< n) \|> .map f` |
| `x in 0 ..< n` | `x in (0 ..< n)` |
| `0 ..< 3 == [0, 1, 2]` | `(0 ..< 3) == [0, 1, 2]` |

Some consequences of that level:

- `(0 ..< n).map f` needs its brackets, since a dot binds tighter than a
  range. The pipe form reads better anyway, and the house call-site style
  prefers it.
- `a ..< b ..< c` is `E-PARSE`.
- `a ..< b ++ c` is `a ..< (b ++ c)`, a type error whose note suggests
  bracketing the ranges, or `[..a ..< b, ..c ..< d]`.

**In the parser** this is one function, `range_expr`, between `cmp_expr`
and `append_expr` (crates/syntax/src/parser.rs:3778, :3987), called from
`cmp_expr` and `membership` where they call `append_expr` today.

**The formatter** writes a range with one space on each side. A range in a
spread keeps no brackets of its own.

**Errors:**

- the bare `..` of §4.2;
- `W-RANGE-IN-BRACKETS` (§5);
- a range of a type that has none (`"a" ..< "z"`), which is
  `E-TYPE-MISMATCH` with a note listing `Nat` and `Int`;
- the one-argument `List.range` of §6.3.

## 12. Sites, before and after

| Site | Today | With ranges |
|---|---|---|
| aoc 2021 day 17, Day17.sw:95-99 (stage 3, `Int`) | `List.range (Int.toNat target.right)` and then `dx = i.toInt + 1` | `1 ..= target.right`, `dx = i` |
| aoc/src/Aoc/Common/Grid.sw:102 | `List.range height \|> .flatMap (row => List.range width \|> .map …)` | `0 ..< height \|> .flatMap (row => 0 ..< width \|> .map …)` |
| Common/Grid.sw:73 | `List.between (at.row - 1) (at.row + 1)` | `at.row - 1 ..= at.row + 1` |
| aoc 2024 day 13, Day13.sw:73 | `List.range (limit + 1)` | `0 ..= limit` |
| Common/Range.sw, `Range.ids` | `List.rangeFrom (count := range.size) (start := range.from)` | `range.from ..= range.to` |
| aoc 2025 day 2, Proofs/Part2.sw:322 | `List.rangeFrom (size - 1) 2`, `List.rangeFrom size 1` | `2 ..= size`, `1 ..= size` |
| aoc 2025 day 2, Proofs/Templates.sw:82 | `List.between 2 size` (the same list as the line above) | `2 ..= size` |
| aoc 2025 day 2, Day02.sw:61 | `each (List.between 1 maxDigits)` | `each (1 ..= maxDigits)` |
| aoc 2025 day 6, Spec/Spec.sw:64 | `List.rangeFrom (hi - lo) lo \|> .reverse` | `lo ..< hi \|> .reverse` |
| aoc 2025 day 2, Tests/Examples.sw:31 | `(List.rangeFrom 11 2).map copiesWeight` | `2 ..= 12 \|> .map copiesWeight` |
| Common/GridGraph.sw:64 | `List.memRangeFromIntro column width 0 (omega) (omega [before])` | `auto`, or `List.memRange.mpr (Both (omega) (omega [before]))` |
| games/rogue Tests/Turn.sw:116 | `(List.range 20).count (seed => …)` | `0 ..< 20 \|> .count (seed => …)` |
| std Fin/Fin.sw:61 | `Fin.all n` | unchanged |

A few more notes on the sites:

- **Where nothing improves.** `List.range n` used as "n seeds" or "n
  draws" (games/rogue Generate.sw:33-34, Turn.sw) gains little from
  `0 ..< n`, beyond saying where the count starts. Keeping a one-argument
  form only for that would bring back two ways to say one thing.
- **Proofs.** In the 578 proof uses, most of the change is rewriting
  `List.rangeFrom c s` to `s ..< s + c` in statements, and switching to the
  `↔` lemma. The terms after unfolding are the same, so proofs that work
  by `rfl` or computation keep working **[estimate]**. Proofs that name
  `List.memRangeFrom` change their call.

## 13. Build plan

The sizes are **[estimate]**.

1. **Std function and lemmas** (Sonnet, 1.5-2 h):
   - `List.range (from) (until)` and the lemmas of §9.1, keeping
     `rangeFrom`;
   - `between` and the one-argument `range` go, and std's own uses (about
     320) move over;
   - `foldLeftCongRange` and the other congruence lemmas move to the new
     form.
   - No syntax yet. Callers write `List.range 0 n`. This step can merge on
     its own.
2. **Syntax** (Sonnet, 2-2.5 h):
   - the `..<` and `..=` tokens, `range_expr`, the printer's read-back, the
     formatter;
   - the errors of §11 and `W-RANGE-IN-BRACKETS`;
   - examples `examples/accept/ranges.sw` (with `.map`, `each`, `in`, a
     spread, the `↔` lemma, `rfl` cases) and `examples/reject/range-*.sw`;
   - the docs/syntax.md section, and a precedence table row.
3. **`auto`, `omega` and the `Bool` test** (Sonnet, 1-1.5 h): the
   membership facts of §9.1, and R7's O(1) decision.
4. **`Int` ranges** (Sonnet, 1 h): `Int.range`, its lemmas, choosing by
   type, Day 17 rewritten.
5. **Sweep** (DeepSeek or Sonnet, split by year, 2-4 h altogether): aoc,
   games, examples, running `task test:one` for each day touched. Proof
   files first, since they are most of the uses. This step is optional and
   can come later.

Steps 1-4 total about 6-7 hours, and the kernel is untouched. Step 1 is
useful even if Matt rejects the syntax: it settles SW-1258 for ranges.

## 14. Decisions for Matt

These are numbered R1 to R9 here; the orchestrator gives them D numbers.

- **R1. Syntax.** `a ..< b` and `a ..= b`, with no bare `a..b`, no
  `[a..b]`, and an error that names both forms. **[rec: yes]**
- **R2. Both ends.** Keep both forms, with `a ..= b` defined as
  `a ..< b + 1`. **[rec: yes]**
- **R3. What a range is.** (a) a `List Nat`, the call `List.range a b`,
  printed back as a range; (b) a `Range` record with `toList`; (c) a
  record that becomes a list when a list is expected. **[rec: (a)]**
- **R4. The library's names (SW-1258).**
  - `List.range (from) (until)` with two ends replaces the one-argument
    `List.range` and `List.between`.
  - `List.rangeFrom (count) (start)` stays, for induction.
  - The lemmas are restated as in §9.1.

  **[rec: yes]**
- **R5. Types.** `Nat` now and `Int` next, chosen by type. `Char` when a
  site needs it. No `Enum`-style interface until a user's own type asks
  for ranges. **[rec: yes]**
- **R6. Reversed, down and steps.** Reversed bounds give `[]`. Count down
  with `.reverse`. No step syntax: if a site needs a step, add a function
  with named arguments. **[rec: yes]**
- **R7. `x in a ..< b` as a `Bool`.** (a) decided by the comparisons in
  O(1), while the proposition stays `List.Mem`; (b) left as a list walk,
  with a warning that suggests the chain. **[rec: (a)]**
- **R8. Range patterns (`| 1 ..= 9 =>`).** Not now. Use guards with
  chains. **[rec: not now]**
- **R9. `W-RANGE-IN-BRACKETS`** for `[a ..< b]` used alone in brackets.
  **[rec: yes]**

For the orchestrator: once R1-R9 are settled, start step 1, then steps 2-4
one after another (they touch the same files), and the sweep after them.

## Sources

Checked on 5 November 2026 (fetched pages):

- Swift: the Swift book, BasicOperators.md
  (https://raw.githubusercontent.com/swiftlang/swift-book/main/TSPL.docc/LanguageGuide/BasicOperators.md);
  the standard library's Range.swift, for the precondition message
  (https://raw.githubusercontent.com/swiftlang/swift/main/stdlib/public/core/Range.swift).
  Not checked: `stride`, `switch` patterns, `Character` ranges (marked
  unverified above).
- Rust: https://doc.rust-lang.org/std/ops/struct.Range.html,
  …/struct.RangeInclusive.html,
  https://doc.rust-lang.org/reference/expressions/range-expr.html,
  https://doc.rust-lang.org/reference/patterns.html,
  https://blog.rust-lang.org/2024/07/25/Rust-1.80.0/.
- Kotlin: https://kotlinlang.org/docs/ranges.html,
  https://kotlinlang.org/docs/whatsnew19.html,
  https://kotlinlang.org/docs/control-flow.html.
- Haskell: Haskell 2010 report, §3.10 and chapter 6
  (https://www.haskell.org/onlinereport/haskell2010/haskellch3.html).
- Python: https://docs.python.org/3/library/stdtypes.html#ranges.
- Scala: https://docs.scala-lang.org/overviews/collections-2.13/concrete-immutable-collection-classes.html,
  https://www.scala-lang.org/api/2.13.x/scala/collection/immutable/NumericRange.html.
- Ruby: https://docs.ruby-lang.org/en/master/Range.html.
- Julia: https://docs.julialang.org/en/v1/base/math/,
  https://docs.julialang.org/en/v1/base/collections/.
- Lean 4:
  - https://lean-lang.org/doc/reference/latest/releases/v4.22.0/: the new
    syntax `1...*`, `1...=3`, `1...<3`, `1<...=2`, `*...=3`, "polymorphic,
    in contrast to the existing `Std.Range` which only supports natural
    numbers";
  - https://lean-lang.org/doc/reference/latest/releases/v4.28.0: `Std.Range`
    renamed `Std.Legacy.Range`; that plain `a...b` is closed-open there
    comes from a search summary, not read;
  - Init/Data/Range/Basic.lean;
  - the reference's linked-lists page, for `List.range'` (start, length,
    step).
- Idris 2: Prelude/Types.idr, `interface Range`.
- Agda: https://agda.github.io/agda-stdlib/master/Data.List.Base.html.
- F#: https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/loops-for-in-expression.
- Elixir: https://elixir.hexdocs.pm/Range.html.
- C#: https://learn.microsoft.com/en-us/dotnet/csharp/language-reference/operators/member-access-operators,
  https://learn.microsoft.com/en-us/dotnet/api/system.linq.enumerable.range.
- Go: https://go.dev/blog/go1.22.
- JavaScript: https://github.com/tc39/proposal-iterator.range (stage 2).
- Zig: https://ziglang.org/documentation/master/.
- Nim: https://nim-lang.org/docs/system.html.
- Odin: https://odin-lang.org/docs/overview/.
- Raku: https://docs.raku.org/type/Range.
- Dart: https://api.dart.dev/stable/dart-core/Iterable/Iterable.generate.html.
- Perl: https://perldoc.perl.org/perlop.
- D: https://dlang.org/spec/statement.html,
  https://dlang.org/phobos/std_range.html.
- Ada: Ada 2022 RM 5.5
  (https://www.adaic.org/resources/add_content/standards/22rm/html/RM-5-5.html).
- From memory, **unverified**: Clippy's lint for `vec![0..n]`; Kotlin's,
  Scala's and F#'s behaviour on reversed bounds; Elixir guards.
