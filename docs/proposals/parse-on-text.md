# Parsing on `Text`: what `Std.Parse` reads in the end

**Status:** design note, 14 November 2026 (SW-3269; Matt's question: "Are
we anticipating moving to text for all our parsing rather than a list of
Char?"). Paper lane: nothing is built. It connects three of today's notes
that don't mention each other: [generic-parse.md](generic-parse.md)
(SW-3235), [file-io-and-text.md](file-io-and-text.md) (SW-3234) and
[text-patterns.md](text-patterns.md) (SW-3231). It stops for Matt's
decisions ([§9](#9-questions-for-matt)).

Claims are marked **[measured]** (run for this note on Speedwell with the
main checkout's release binary, load 3–4, one or two runs each; probes in
[Appendix A](#appendix-a-the-probes)), **[source]** (read in the code at
`e04e26537`) or **[estimated]** (my reasoning, not tested). Fast `Text`
isn't built, so every figure about it is an estimate from its design.

## In plain words

**What the two things are.** A `Text` is a piece of writing: `"hello"`. A
`List Char` is the same letters as a chain, one link per character, each
link pointing at the next. Stitchwort *defines* a text as a box holding
such a chain (`type Text = | MkText (chars: List Char)`), which is why
proofs about text are proofs about lists and can use every list lemma.
When a program runs, the two are stored differently: a text is one block
of memory, a chain is a separate small object per character. Today a
running text is awkward to walk through (taking the first character off
copies the rest), so anything that reads a text character by character,
`Std.Parse` included, first turns it into a chain. SW-3234's "fast text"
fixes the block: taking a character off, cutting a piece out and asking
the length all become free.

**The problem.** Once text is fast, should `Std.Parse` read the text
itself and stop making the chain? Nothing had decided it: the generic
parser design reads "a list of whatever", and the fast-text design doesn't
mention parsing.

**The answer.** Yes, in the end state, but it is not where the speed is,
and it should not hold up the generic parser.

- *Programs* hold `Text`, and at run time the parser should walk the
  text's own block: no chain, and a token is a window on the source, not a
  copy.
- *Proofs* keep talking about `List Char`. A parser's guarantee still says
  "the characters read were these", as a list. That is what every AoC
  proof already says (`input.toList = read ++ ending`), so no AoC
  statement or proof changes [source, grep].
- *How:* not by teaching every lemma about "any kind of input" (tried: it
  costs a third more checking and the checker can't work out the input by
  itself [measured]), but by giving the parser one input type, a *slice*:
  to proofs a list in a box, exactly as `Text` is; at run time a window on
  a block of memory. A text turns into a slice of characters, and back,
  for free, because they share the block.

**What it should do.**

- Lexing with `Std.Parse` gets perhaps 10–20% faster [estimated from a
  measured profile], and stops allocating an object per character.
  It does **not** close the 15× gap to a hand-written lexer: about 70% of
  the time is the parser's own bookkeeping per token, whatever the input
  is [measured].
- Checking `Std.Parse` costs about what the generic design already costs:
  a miniature of it went from 488 k to 505 k steps (+3.5%), against +31%
  for the "any kind of input" route [measured].
- A small simplification falls out: the parser no longer has to carry a
  count of what's left and a promise that the count is right. One leaf
  lemma dropped from 70 k steps to 22 k without it [measured].
- generic-parse.md's stages and its questions D3588–D3590 stand as
  written. This is two later stages and their JavaScript twin, about 9–12
  lane hours [estimated], after fast text and after the generic parser.

## 1. Where things stand [source]

- **`Std.Parse` already takes `Text` at its surface and gives `Text`
  back.** The runners people call are `Parse.all (input: Text)`,
  `Parse.eachLine (input: Text)` and `Parse.line`; `Parse.takeWhile` gives
  a `Text`. Inside, the runner calls `input.toList` once, the handler's
  state holds `rest: List Char`, `span` builds a `List Char` and
  `takeWhile` turns it back with `Text.fromList`.
- **`List Char` shows in four places:** the raw operations (`Parse.span`,
  `Parse.literal`), `Parse.Mark.rest`, the low-level runners (`Parse.run`,
  `Parse.whole`, `Failure.describe`), and every reading theorem's spec
  (`Parse.Reads parser (spec: List Char → a → Prop)`).
- **`aoc/` never touches the first three** [measured, grep over
  `aoc/src`]: no use of `Parse.span`, `Parse.run`, `Parse.whole` or
  `Parse.Mark`; one of `Parse.mark`. It calls `Parse.eachLine` (52 files),
  `Parse.all` (37) and `Parse.line` (8). `List Char` appears on 420 lines
  of 87 files, and where the parser is concerned it is always the fourth
  place: the characters a spec talks about (`∃ (read: List Char) => …
  input.toList = read ++ ending`, 16 times word for word).
- **Fast text (SW-3234, stage T1)** makes a running text a shared buffer
  with a start and a length: `uncons`, `get`, `take`, `drop`, `slice` and
  `length` constant-time, no copy. The kernel's view doesn't change.
  Before T1, parsing on `Text` would be a disaster: `Text.uncons` copies
  the rest of the text each time (2.3 s to peel 400,000 characters,
  file-io-and-text.md §1.2). So T1 comes first, whatever is decided here.
- **Generic parse (SW-3235)** gives the ability a parameter for what it
  reads, `{Parse Char}` or `{Parse Token}`, over `List t`. Its §3.2 says
  it "would not make the input's container generic as well", because
  `Reads` is stated with `++` on lists. This note agrees about the lemmas
  and disagrees about the container.

## 2. Should characters be read from `Text`?

| | Today: a chain of characters | On fast `Text` |
|---|---|---|
| **Speed** | A 1 MB lex takes 4.4 s interpreted [measured; generic-parse.md had 4.0 s]. Of a 500 KB lex's 2.07 s, the list work is 17.6%: walking the taken characters again to count them (`List.lengthOnto`, 6.4%), reversing them (`reverseOnto`, 4.8%) and the scan itself (`spanOnto`, 6.4%); `toList` up front is about 0.08 s a megabyte, 2% [measured] | Counting and reversing go (a slice knows its length); the scan becomes a loop over the buffer; `takeWhile` copies nothing. About 10–20% of a lex [estimated] |
| **What stays slow** | The handler's own loop is 31% of the time and the closures of `oneOf`, `optional` and `token` most of the rest: 1.5 million operations for 176,000 tokens, about 8.5 a token [measured] | The same. This is generic-parse.md's finding (a choice costs three operations per failed alternative), and it is the 15× |
| **Memory** | One list cell per character for as long as the parse runs (the runner keeps the list for the error message). A 1 MB lex peaked at 363 MB against 242 MB for building the input alone [measured]; how much of the 121 MB is cells and how much tokens wasn't separated | No cells; the buffer is 1–2 bytes a character; a token's text is a window on it |
| **Positions and messages** | Offsets are counts of characters, kept by the handler; line and column are worked out from the source only when a message is made | The same offsets. `Failure.describe` cuts the "got" text out with `slice`; a located token (generic-parse.md §2) can give its text back from the source by offset and length without storing it |
| **Proofs** | Specs are on `List Char` | Specs are still on `List Char`: [§3](#3-proofs-a-list-in-a-box) |
| **What a user writes** | `Parse.all input parser`, `{Parse}` | The same. Only the raw operations change type: `Parse.span` gives a slice of characters, not a list |

So the case is not speed today. It is the end state: with fast text and
text patterns, a hand-written lexer on `Text` never makes a chain, files
arrive as `Text`, tokens are cut out of the source for nothing, and
`Std.Parse` would be the one place that still explodes a text into a
million objects and copies each token twice. And the share grows: once the
operations per token are fixed (generic-parse.md's two speed findings),
the list work is a much larger part of what is left.

## 3. Proofs: a list in a box

The question was whether every reading theorem can still be stated and
proved when the input is a `Text`, and at what cost.

**The statement.** Today:

```
def Parse.Reads (parser: () → {Parse} a) (spec: List Char → a → Prop): Prop :=
  ∀ (state: Parse.State) (value: a) (after: Parse.Mark) => state.at.left = state.at.rest.length
    → Parse.runFrom state (() => (parser(), Parse.mark())) = Ok (value, after)
    → ∃ (read: List Char) => state.at.rest = read ++ after.rest ∧ after.left = after.rest.length ∧ spec read value
```

With `rest` a boxed list (a `Text`, or the slice of [§4](#4-the-input-abstraction)),
the only change is the projection: `state.at.rest.toList = read ++
after.rest.toList`. The spec stays `List Char → a → Prop`. So:

- **No lemma's spec changes,** and no client statement: `readsNat`'s
  "the digits read are those of the number" and an AoC day's `Written`
  predicates are about the characters read, as lists, as now.
- **Proofs see a list after one step.** A proof about the handler's step
  splits the box (`| MkText [] => … | MkText [first, ..more] => …`) and is
  then looking at the goal it has today. Tried: the same lemma ("`next`
  reads the character it gives") against a list state and a text state
  gives the same goals, and the same proof text with `MkText` added to two
  patterns [measured, p3b].
- **Why not state specs on the text** (`spec: Text → a → Prop`, `rest =
  read ++ after.rest` with text append)? Every list fact a proof uses on
  `read` (append is associative, `all` over a `takeWhile`, induction on
  the characters) would need a `Text` twin or a conversion at each use.
  `Text` has few lemmas of its own by design: its operations are defined
  on the list so that the list's lemmas apply.
- **The "honest mark" goes.** `Reads` carries `left = rest.length` in and
  out because `Parse.end` and the fuel of `many` read `left` rather than
  measure the list. When the length is free at run time, `left` isn't
  needed, and neither is the promise. The probe's lemma took 70.4 k steps
  with it (most of it `omega` discharging the count) and 22.3 k without
  [measured]. Whether that scales to `Std.Parse`'s 298 theorems is a gate
  for the stage, not a promise.
- **Completeness (`Parse.Runs`)** is stated on `read` and `rest` as lists
  too, and changes the same way.

## 4. The input abstraction

generic-parse.md makes the parser generic over the *element* (`Char`,
`Token`). Reading characters from a text means the *container* differs
too: a text for characters, something else for tokens. Five ways to do
it; the first three were tried in miniature (an ability with `next`,
`mark`, `reset` and `stop`, its handler, the step lemma, the induction
over the computation tree, a leaf lemma and a client proof: probes `ga`,
`gb`, `gc`).

| | A. Lists only (generic-parse.md as written) | B. A stream interface: the handler is given a record of operations and laws | C. One input type, a slice: a list in a box |
|---|---|---|---|
| Row for characters, for tokens | `{Parse Char}`, `{Parse Token}` | two parameters, `{Parse Text Char}`, `{Parse (List Token) Token}` (or a set name, D3596) | `{Parse Char}`, `{Parse Token}` |
| Checking the miniature (7 declarations) | 488 k steps | 641 k (+31%); the tree induction alone 334 k to 445 k (+33%) | 505 k (+3.5%); the tree induction +1.5% |
| A client proof `Prs.readsNext isLetter` | checks | **fails** (`E-TYPE-MISMATCH`: the record isn't worked out from the expected type) until `[input := …]` is written; then +35% steps | checks, +2% |
| Language features it needs | none | an interface of two parameters (`E-INTERFACE-SHAPE` today), or the record passed by hand everywhere | none |
| Run time | a cell per character | one indirect call per read: +0.14 s on 4 million reads interpreted (about 35 ns each), nothing native [measured] | none beyond the slice's own natives |
| New trusted runtime code | none | none beyond T1 | the slice's natives |
| Anyone can add an input type | no | yes | no |

All [measured] except the last three rows [source, estimated].

**D. Lists that are secretly views.** Leave every type alone and have the
runtime store a `List Char` that came from a text as a cursor into the
buffer, as the kernel already does for literals (compact-text.md). No std
change at all. But every `Cons` match in the machine, in native code and
in JavaScript would test for the second representation: the most used
data type gets slower to make one library faster, and the trusted change
is the widest of all [estimated]. Not proposed.

**E. Two handlers.** One ability, a handler for text and one for lists.
The 22 handler lemmas are 59% of `Std.Parse`'s check (generic-parse.md
§3.1), and they would be proved twice: about 60 million steps more. Not
proposed.

**Recommendation: C.** It is the only one that reads the text's buffer
and leaves the proof layer as generic-parse.md designed it.

### 4.1 The slice

```
--| A run of items: to proofs a list; at run time a window on a shared buffer.
type Slice (t: Type) = | MkSlice (items: List t)

def Slice.toList (slice: Slice t): List t                     -- the model
def Slice.uncons (slice: Slice t): Option (t, Slice t)
def Slice.length (slice: Slice t): Nat
def Slice.get (slice: Slice t) (index: Nat): Option t
def Slice.take, Slice.drop, Slice.slice                        -- as Text's
def Slice.span (slice: Slice t) (passes: t → Bool): (Slice t, Slice t)
def Slice.stripPrefixBy (same: t → t → Bool) (items slice: Slice t): Option (Slice t)

def Text.toSlice (text: Text): Slice Char                      -- free: the same buffer
def Slice.toText (slice: Slice Char): Text                     -- free when it came from a text
def List.toSlice, Array.toSlice                                -- one pass
```

(A sketch: names are for review, the shape is the proposal.)

- **To the kernel** it is `Text` with a type parameter: every operation
  is defined on `items`, each with a `…ToList` lemma, as `Text`'s and
  `Array`'s are. Nothing new in the kernel.
- **At run time** it is T1's text value with one more kind of buffer.
  T1's buffer stores characters at 1, 2 or 4 bytes; a slice's buffer may
  also store whole values. `uncons`, `get`, `take`, `drop`, `slice` and
  `length` are the same start-and-length arithmetic at every width, so
  `Text.toSlice` and `Slice.toText` hand over the same buffer. A slice of
  characters made from a list is packed on `toText` (one pass).
- **Read-only.** No `set`, no `push`: it is a view. That keeps the
  natives few, which is why I'd take a new type over making `Array`
  itself sliceable (every `Array` native would then have to know four
  widths and a start).
- **It is tested as the text natives are** (file-io-and-text.md §4.4):
  each native tied to its definition's hash, the three tiers of tests,
  slices of slices, and `Text` to slice and back across widths.
- **Useful beyond parsing** [estimated]: windows on an array for binary
  search and sliding windows, which AoC days do today with `drop` and
  `take` on lists.

### 4.2 `Parse` on slices

```
type Parse.Mark (t: Type) = { rest: Slice t, offset: Nat }

ability Parse (t: Type) where
  span: (t → Bool) → {Parse t} Slice t
  next: (t → Bool) → {Parse t} Option t
  literal: Parse.Literal t → {Parse t} Bool
  mark: () → {Parse t} Parse.Mark t
  …

def Parse.run (input: Slice t) (parser: () → {Parse t} a): Result a Parse.Failure
```

Against generic-parse.md §1.2: `rest` and `span`'s result are `Slice t`
where it has `List t`; `Mark` loses `left`; `Parse.Literal`'s `items` is a
slice. Everything else there stands: one ability, `literal` carrying its
comparison, the two layers under one namespace, `Failure` and `Problem`.

- **Characters:** `Parse.all` starts from `input.toSlice`; `takeWhile` is
  `Parse.span passes |> .toText`; `nat` reads its digits from the slice;
  `Parse.text` passes `expected.toSlice`. Nothing is copied.
- **Tokens:** `Parse.tokens` (generic-parse.md §2) hands the lexer's
  tokens over as a slice (`tokens.toSlice`, one pass). `Parse.one` and
  `next` are an index step.
- **Marks and backing up** are a start and a length; going back copies
  nothing, as now.
- **What the proofs touch.** The handler lemmas treat a step as a
  function of the state (`s.span passes`, `s.next passes`) and never look
  inside it [source: `runFromThenOkTree`; the other 21 not read one by
  one]. So the change lands in the three step functions, their three
  step lemmas, the leaf lemmas (`readsSpan`, `readsNext`, `readsLiteral`
  and the `…There` lemmas of `Runs`), the definitions of `Reads` and
  `Runs`, and wherever `honest` is passed along.
- **Checking tests in the kernel.** A proof by `rfl` that runs a parser
  on a literal still computes: a slice of a literal is a boxed list to
  the kernel, and `uncons` is one match. `length` there walks the list,
  so `Parse.end` should ask `isEmpty`, not `length == 0`.

## 5. Text patterns (D3591, D3592)

- **D3591 (text literals as patterns, on `Text` and on `List Char`):
  unchanged, still "yes, both".** The reason for the `List Char` half
  shifts. text-patterns.md gave "the formatter's lexer is a state machine
  over `List Char`, and `Std.Parse` works on `List Char` too". In the end
  state neither does. What remains is proofs and specs: a spec is a
  predicate on the characters read, and `| "->" ++ rest` in a spec or a
  proof's `match` reads better than `['-', '>', ..rest]`. It costs
  nothing beyond the parser (its §4.2), so it stays; it is just less
  important than it looked.
- **D3592 (prefix patterns): unchanged as a question; one stage moves.**
  On a `Text`, `"->" ++ rest` binds `rest` as `MkText r`. Today the
  runtimes build the whole character list at `MkText cs` before reading
  the first character (its §4.6), so a lexer matching prefixes on a long
  text would be quadratic. With fast text the right compilation is a
  cursor: under a `MkText` match, `Cons` is a bounds check and a read,
  and a tail that is only wrapped again in `MkText` is a `drop`, so
  `rest` is a slice of the same buffer and no list is made. That is
  text-patterns.md's stage 5 ("lazy characters"), which it left optional
  and to be measured. With T1 it becomes part of stage 2: prefix patterns
  on `Text` shouldn't ship without it once text is fast. The kernel term
  doesn't change.
- **`Slice Char`** needs no pattern syntax: a parser reads it through
  `Parse`, and anything else converts with `.toText`, which is free.

## 6. What is left for `List Char`

In the end state a program rarely holds one, and proofs always talk about
one:

- **Specs and theorems.** What a parser read, `text.toList` in a
  statement, a predicate such as `NumberWritten (read: List Char)
  (number: Nat)`. This is where its lemma library pays.
- **Small structural helpers** whose point is the recursion (and the
  induction that follows it): `Text.toNatDigits`, a day's digit folds.
- **Not** a lexer's state, a parser's input, a token's text or a line of
  a file: those are `Text` (or a slice) at run time.
- `text.toList` stays a one-pass conversion at run time and a projection
  in proofs. The 763 `.toList` lines in `aoc/src` (not all of them on
  text) aren't a target: a day that converts once and folds is fine.

## 7. How it sequences

Nothing below changes the order of work already recommended (D3587: T1
next; D3589: generic parse stages 0–2 before the toy formatter).

| Stage | What | Model | Hours [estimated] |
|---|---|---|---|
| T1 (SW-3234) | Fast text, as designed. **One line added to its brief:** the buffer's width is a closed list the lane can extend by one ("whole values"), or the lane says why not. No slice is built here | Opus | 5–6, unchanged |
| G0–G2 (SW-3235) | generic-parse.md's stages 0, 1 and 2, as written, on `List t` | as there | 7–10, unchanged |
| S1 | `Slice` in std with its lemmas; the values-width buffer and the slice natives on the machine and native code; `Text.toSlice`, `Slice.toText`; the three test tiers; a performance-log entry | Opus (value layout, natives bound to std, D2506) | 4–6 |
| S2 | `Parse` on slices ([§4.2](#42-parse-on-slices)): `Mark`, `span`, the step functions and lemmas, `Reads` and `Runs` without `left`, the character layer's runners; guide and `docs/syntax.md` where `Parse.span` and `Parse.run` are shown | Opus (re-types the std theorems; the orchestrator checks statements one by one, D2436) | 3–4 |
| S3 | JavaScript natives for the slice, with T3 | Sonnet | 2 |
| text-patterns stage 2 | gains the cursor compilation ([§5](#5-text-patterns-d3591-d3592)) when T1 has landed | Opus | within its 3–5 plus stage 5's 4–6 |

**Gates for S2:** `Std.Parse` within 5% of its steps after G1 (the
miniature says +3.5%; dropping `left` may pay that back); no statement in
`aoc/` changed; a 1 MB lex at least 10% faster and its peak memory lower,
measured by the verifier or Overmind, not by the lane.

**When.** S1 and S2 don't block the toy formatter, and their gain is
speed and memory, which are parked (D3465). I'd queue them behind G2 and
build them when speed work resumes, together with generic-parse.md's two
handler findings (a choice by the next token; a `span` that counts), since
it is those that make the list's share of the time worth removing. Doing
G1 on lists first costs S2 nothing extra: the handler lemmas don't look
inside a step, so S2 edits the same few dozen declarations either way.

**Why not fold it into G1?** It would need T1 and S1 first, which puts
9–12 hours of runtime work in front of the toy formatter for a 10–20%
gain it doesn't need.

## 8. What I did not check

- Fast text and the slice don't exist: nothing about their speed is
  measured. The 10–20% is the profile's list rows plus the two hidden
  conversions, not a run.
- The proof miniature has four operations and one tree lemma.
  `Std.Parse` has eight and 22; `labelWhole`'s lemmas (31% of the check)
  weren't modelled. The +3.5% and +31% are indications.
- Only one of the 22 handler lemmas was read to see that it treats steps
  as opaque.
- Whether T1's `Value` layout (a buffer pointer and two 32-bit numbers in
  three words) has room for a width tag that includes "values" without
  growing: T1's lane must say.
- The memory split between list cells and tokens.
- The cursor compilation of `MkText` matches is described, not designed:
  it needs its own short note in the text-patterns lane.

## 9. Questions for Matt

Neither replaces an earlier question. **D3588, D3589 and D3590
(generic-parse.md) can be answered as written**, and so can **D3591 and
D3592 (text-patterns.md)**: this note changes a reason behind D3591 and
the stage order behind D3592, not what is asked. The ticket had held
them; they are released.

**D3597: in the end state, does `Std.Parse` read characters from the
text itself, with `List Char` kept as the language of proofs?**
*The problem:* once text is fast, the parser would be the one place that
still turns a text into an object per character and copies every token
twice. Nothing has said whether that is the plan.
*The change:* the parser's input becomes a window on the text's own
memory; specs and theorems stay about lists of characters, so no AoC
statement or proof changes [source]. Built as two later stages (S1, S2:
7–10 Opus hours [estimated]) after fast text and the generic parser, and
queued with speed work, since the gain is 10–20% of lexing time and a
cell per character of memory [estimated from a measured profile], not the
15× gap.
*What it should do:* programs see `Text` everywhere and never a chain of
characters at run time; proofs are untouched; the generic parser and the
toy formatter go ahead now without waiting. **[rec: yes, and later, not
now]**

**D3599: is the parser's input one new std type, `Slice`, rather than an
interface that any input type can implement?**
*The problem:* characters want to be read from a text and tokens from
something else, so the parser needs one idea of "input". An interface
("anything with a first item and a rest") is the usual answer, but tried
in miniature it cost 31% more checking, and the checker couldn't work out
which input a lemma was about without being told [measured]. `Std.Parse`
is already std's most expensive namespace to check.
*The change:* a read-only type `Slice t`: to proofs a list in a box, as
`Text` is; at run time a window on a block of memory. A text becomes a
slice of characters and back for free; tokens are put in one. It adds
trusted runtime code (the slice's natives, tested as the text natives
are) and one std type; the proof layer stays as generic-parse.md has it
(+3.5% in the miniature [measured]). Its one cost today: a line in T1's
brief so the text buffer can later hold whole values.
*What it should do:* `{Parse Char}` and `{Parse Token}` as planned, one
handler, one set of lemmas, and `Slice` is there for array windows too.
What it gives up: a program can't plug in an input type of its own.
**[rec: yes, `Slice`]** (If no to D3597, this one lapses.)

## Calls made here as implementation

Say if any should be a question: specs stay on `List t`, not on the
input; `Mark` loses `left` when the input's length is free; `Slice` is
read-only and a new type, not a sliceable `Array`; `Parse.end` tests
`isEmpty`; S1 and S2 queue behind G2 with the parked speed work.

## Alternatives considered, briefly

- **`Text` is `Slice Char`** (one type, not two that convert for free).
  The tidiest model, but `Text` has its own `Show`, literals,
  interpolation and JavaScript string boundary, and an interface can't
  tell `Slice Char` from `Slice a`. A language decision of its own; not
  proposed.
- **An input type with a case for text and a case for lists.** A type
  indexed by the element type is `E-UNIVERSE` in `Type` [measured, p1];
  with the element as a parameter the text case needs functions or an
  equation between types inside the data [measured, p2: it checks, but
  the laws aren't provable from the type]. Too clever for std's central
  library.
- **Splitting the ability** into control (`mark`, `reset`, `stop`) and
  reading, so combinators need no parameter at all. `reset` has to move
  the reader, so the two are handled together and the handler lemmas
  double as in E.
- **Stay on lists for good** (A). Costs nothing, and is where G1 lands
  anyway. It leaves the cell per character and the two copies per token
  in the end state, which is what D3597 asks about.

## Findings worth tickets

- **The checker can't find an implicit record from the expected type
  through `Reads`.** With `Prs.readsNext ∀ [input: Input i t] …:
  Prs.Reads input …`, the proof `Prs.readsNext Char.isAsciiLetter` of
  `Prs.Reads Input.text …` is `E-TYPE-MISMATCH` ("`?2` … wasn't worked out
  from the other arguments or the expected type"), though the expected
  type names it; it checks with `[input := Input.text]`. The same family
  as generic-parse.md's stage 0 (an ability's parameter settled late),
  but here it fails outright. Probe `gb2.sw`; worth adding to stage 0's
  tests.
- **Interfaces take one parameter** (`E-INTERFACE-SHAPE`: "interfaces
  with several parameters, or over type constructors, aren't
  supported"). An interface relating a container to its element can't be
  written. Not needed by this design; noted for whoever next wants one.
- **The "honest mark" costs proofs.** `Reads` threads `left =
  rest.length` through every lemma; the probe's leaf lemma is 70 k steps
  with it and 22 k without. Before slices exist it could be a proof field
  of `Mark` (a mark that carries its own honesty), which would take the
  hypothesis out of `Reads` today. Worth a measurement on the real
  `readsNext` and `readsSpan`.
- **`Text.repeat` runs through lists at run time.** Building a 1 MB text
  with it peaks at 242 MB against 146 MB for 100 KB, about 100 bytes a
  character, and the profile shows `List.replicate`, `List.concat` and
  `List.append` under it. It has no native. T1 or T2 should give it one.
- **text-patterns.md's stage 5 stops being optional once T1 lands**
  ([§5](#5-text-patterns-d3591-d3592)): a prefix match on a long `Text`
  builds the whole character list per match. Its stage table should say
  so.
- **self-hosted-fmt.md plans the lexer as "a state machine over `List
  Char`".** With T1 and prefix patterns on `Text` it can stay on the
  text; a line in that plan when T1 lands.
- **`--profile` shows no row for the text natives** (`Text.fromList`,
  `Text.toList`), though `takeWhile1` called `fromList` 128,000 times in
  the run: their time is inside their callers' self time, so the list's
  share of a lex can't be read off exactly. A row per native would help
  the next performance lane.

## Appendix A: the probes

In the lane's scratch folder (`sw3269/`); none is kept.

| Probe | What | Result |
|---|---|---|
| `p1.sw` | an input type indexed by its element type, `OfText: Src Char`, `OfList: Src t` | `E-UNIVERSE` in `Type`; in `Type 1`, `Option (t, Src t)` is refused |
| `p2.sw` | the same with the element as a parameter and the text case carrying its conversions | checks; two tests pass; no laws |
| `p3b.sw` | "`next` reads the character it gives" for a list state with `left` and the honesty hypothesis, and for a text state without | both check; 70.4 k and 22.3 k steps; the same goals after `MkText` is split |
| `ga.sw` | miniature generic parser over `List t`: ability (4 operations), handler, step lemma, tree induction, `Reads`, leaf lemma, two client proofs | checks; 488 k steps over the seven declarations |
| `gb.sw`, `gb2.sw` | the same over any input, given as a record of `items`, `uncons` and two laws; an instance for `Text`; a test running it on a text | checks only with `[input := Input.text]` in the client proof; 641 k steps; an `interface` of two parameters is refused |
| `gc.sw` | the same over one boxed input type, `MkSlice (items: List t)` | checks; 505 k steps |
| `dict.sw` | 4 million `uncons` steps over a list, called directly and through a record field | interpreted 0.70 s and 0.85 s beyond start-up; `--native` both 0.06 s, within noise |
| `lex.sw` | generic-parse.md's three-alternative lexer on today's `Parse`: `none`, `tolist` and `lex` modes at 100 KB and 1 MB, with `/usr/bin/time -l`; `--profile` at 500 KB | 1 MB: 0.46 s, 0.54 s, 4.86 s; peak 242, 249, 363 MB (that run's input ended in a space, so it lexed everything and then failed at the end; the profile's run had none); profile in [§2](#2-should-characters-be-read-from-text) |
