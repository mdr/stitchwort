# A generic `Std.Parse`: parsing any token type

**Status:** design note, 14 November 2026 (SW-3235, D3579). Paper lane:
nothing is built. The probes were throwaway `.sw` files and scratch copies
of std and `aoc/`, run with the main checkout's release binary
([Appendix A](#appendix-a-the-probes)). It stops for Matt's decisions
([§7](#7-questions-for-matt)).

Claims are marked **[measured]** (run for this note on Speedwell, load
18–25, one or two runs each, so rough), **[source]** (read in the code at
`dc26a104f`) or **[estimated]** (my reasoning, not tested).

## In plain words

**The problem.** `Std.Parse` reads characters and nothing else: the ability,
its state and all 298 of its theorems are written against `List Char`
[source]. A program that wants to split text into tokens first (a
formatter, a compiler, a calculator with proper error messages) can lex
with it but can't then parse the tokens with it, so it writes its second
half by hand and gets none of the proved lemmas.

**The change.** Give the `Parse` ability a parameter for what it reads:
`{Parse Char}` is today's parser, `{Parse Token}` reads a list of tokens.
The combinators that don't care what they read (`many`, `optional`,
`oneOf`, `sepBy`, `chainLeft`, `recursive`, `label` and their lemmas) become
generic; the ones about text (`nat`, `text`, `char`, `lines`, `eachLine`
and theirs) stay as they are, now over `Parse Char`. A small new layer
gives tokens their place in the source, so a token-level error still says
"line 3, column 9: expected ',' or ')', got ';'".

**What it should do.**

- Existing code changes in one way only: `{Parse}` becomes `{Parse Char}`.
  No function, lemma or theorem statement is renamed. Tried: with the
  ability parameterised, all of `Std.Parse` (438 declarations) and the
  parser proofs of three AoC days check after that one substitution
  [measured].
- A lexer and a token parser written with the same combinators, with no
  type annotations beyond the signatures, parse 100 KB in about 0.4 s
  native, 0.7 s interpreted, in a straight line up to 1 MB [measured].
- Run time doesn't change: the generic handler ran a lexer at the same
  speed as today's, within noise [measured].
- Checking `Std.Parse` costs 11–19% more steps (104 million today, 115
  million measured for the parameter alone, about 123 million estimated
  for the full design); the wall-clock difference was within noise on an
  11 s check [measured].
- One thing to fix on the way: the checker works out the new parameter
  slowly in `readsThen` chains (77% more steps on a small proof, 3% when
  told the type) [measured]. It is an elaborator inefficiency, found by
  this note, and stage 0 below.
- About 7–10 lane hours in three stages [estimated]; the toy-language
  formatter needs the first two.

## 1. The generic parser

### 1.1 What is there now [source]

`crates/elab/src/std/Parse/`: `Parse.sw` (1,473 lines: the ability, the
handler `Parse.runFrom`, 80 functions, the runners), `Reads.sw` (2,731
lines, 118 theorems: what a successful parse read) and `Runs.sw` (3,884
lines, 149 theorems: that a parser succeeds on good input).

```
type Parse.Mark = { rest: List Char, offset: Nat, left: Nat }

ability Parse where
  span: (Char → Bool) → {Parse} List Char
  next: (Char → Bool) → {Parse} Option Char
  literal: List Char → {Parse} Bool
  mark: () → {Parse} Parse.Mark
  reset: Parse.Mark → {Parse} ()
  note: Parse.Problem → {Parse} ()
  stop: () → {Parse} Empty
  fatal: Text → {Parse} Empty
```

`aoc/` uses it in 68 files (139 `{Parse}` rows) and proves things about
its parsers in 43, almost always through the high-level lemmas:
`readsThen` (92 uses), `Runs` and `runsBind`, `readsNat`, `readsChar`,
`eachLineReads`. No AoC file mentions `Parse.State`, `Parse.Mark`'s type,
`Parse.run` or `Parse.runFrom` [measured, grep]. Nothing in the Rust code
depends on the ability's shape [source, grep].

### 1.2 The design

Abilities already take parameters (`ability State (s: Type) where`,
docs/syntax.md), so no language change is needed:

```
type Parse.Mark (t: Type) = { rest: List t, offset: Nat, left: Nat }

ability Parse (t: Type) where
  span: (t → Bool) → {Parse t} List t
  next: (t → Bool) → {Parse t} Option t
  literal: Parse.Literal t → {Parse t} Bool
  mark: () → {Parse t} Parse.Mark t
  reset: Parse.Mark t → {Parse t} ()
  note: Parse.Problem → {Parse t} ()
  stop: () → {Parse t} Empty
  fatal: Text → {Parse t} Empty

def Parse.runFrom (initial: Parse.State t) (parser: () → {Parse t} a): Result a Parse.Failure
def Parse.run (input: List t) (parser: () → {Parse t} a): Result a Parse.Failure
```

`Parse.State` gains the same parameter. `Parse.Problem` and
`Parse.Failure` don't: they hold texts and an offset, which is now a count
of tokens.

**One ability, not two.** The combinators are written against the ability
(`optionalFrom` is a handler that passes each operation on), so a second
ability for tokens would mean a second copy of every combinator and every
lemma. A parser as a plain function (`List t → Result …`) would lose the
direct style all of `aoc/` is written in.

**`literal` carries its comparison.** Today's `literal` compares
characters with `Text.sameChar` inside the handler. A generic handler has
no equality to use, and shouldn't ask for one: a token that carries its
position must not be compared position and all. So the operation's
argument is `type Parse.Literal (t: Type) = { items: List t, same: t → t →
Bool }`; `Parse.text` passes `Text.sameChar`, and its callers see no
difference. It stays one operation for a whole text, as now.

**The two layers, one namespace.** Everything keeps its name under
`Parse.`:

| | Generic over `t` | Characters only (`Parse Char`) |
|---|---|---|
| Functions | `fail`, `expected`, `ensure`, `ensureAt`, `need`, `fromFail`, `satisfy`, `optional`, `oneOf`, `many`, `many1`, `repeat`, `exactly`, `sepBy`, `sepBy1`, `chainLeft`, `attempt`, `findAll`, `findAllStarting`, `label`, `labelWhole`, `recursive`, `end`, `whole`, `run`, `runFrom` | `char`, `text`, `takeWhile`, `takeWhile1`, `nat`, `natDigits`, `int`, `digit`, `spaces`, `spaces1`, `token`, `before`, `newline`, `lineEnd`, `blankLine`, `pick`, `lines`, `sections`, `section`, `grid`, `looseRow`, `looseGrid`, `all`, `line`, `eachLine`, and the message functions (`Failure.describe`, `lineAndColumn`) |
| New | `Parse.one what select` (the next token if `select: t → Option a` gives a value: `Parse.one "a number" (match some \| Num n => n)`), `Parse.span1` (`takeWhile1` giving the tokens) | `Parse.located`, `Parse.tokens` ([§2](#2-lex-then-parse)) |

In files: `Parse/Parse.sw` (generic), `Parse/Chars.sw`, and the two lemma
files each split the same way, so a program that only parses tokens
doesn't check the line and number lemmas (a library file is checked only
when a program needs it [source, `--std-dir` help]).

### 1.3 Does AoC code get noisier?

By five characters a signature: `def point(): {Parse Char} Point`. Nothing
else changes: `Parse.many (() => Parse.char ',')` finds `t` from the row,
and so do the lemmas. **[measured]** In a scratch copy I parameterised the
ability, `Mark` and `State`, replaced `{Parse}` by `{Parse Char}`
throughout std's `Parse/` and `aoc/src`, and changed nothing else:

| Checked | Result | Steps before | Steps after |
|---|---|---|---|
| `Std.Parse`, all 438 declarations (298 theorems) | checks | 103.6 M | 115.2 M (+11%) |
| 2020 day 2's proofs (32 declarations) | checks | 8.07 M | 8.80 M (+9%) |
| 2020 day 7's proofs (104) | checks | 9.87 M | 10.62 M (+8%) |
| 2020 day 18's proofs (90) | checks | 3.05 M | 3.22 M (+6%) |

So the sweep over `aoc/` is one substitution, on this evidence. The whole
of `aoc/` wasn't checked here (that is the verifier's and Overmind's job).

**Could `{Parse}` keep meaning characters?** Not today: a row lists
abilities by name, and a synonym isn't accepted (`type Chars = Parse
Char` is `E-ABILITY` [measured]). It would take a new language feature, an
ability synonym or a default for an ability's parameter. I don't think
five characters earn one: `{Parse Char}` beside `{Parse Token}` says what
each reads, and matches `{State s}`. It is Matt's call
([D3588](#7-questions-for-matt)).

**Where `t` can't be worked out.** Only in a statement where neither the
parser nor the spec says what is read: `Parse.Reads (() => x) (read value
=> read = [] ∧ value = x)`. Three of std's own lemma statements needed
`(read: List t)` written in [measured, on a 900-line slice]. User code
always has a parser with a row, so it doesn't arise there.

**One instantiation per row.** A function can't perform `Parse Char` and
`Parse Token` at once (abilities.md, "Labels"). A lexer and a parser are
separate runs, so this costs nothing; a token parser that needs to look
inside a token's text calls `Parse.run` on it, which is pure.

### 1.4 The reading theorems

`Parse.Reads` and `Parse.Runs` generalise as written:

```
def Parse.Reads (parser: () → {Parse t} a) (spec: List t → a → Prop): Prop := …
def Parse.Runs (parser: () → {Parse t} a) (read rest: List t) (value: a): Prop := …
```

with `Then`, `Maybe`, `Each`, `SepBy`, `ChainStep`, `Declines`,
`ManyRuns` and `CannotStart (canStart: t → Bool)` the same way. By name,
174 of the 298 theorems are generic and 124 are about characters
[measured, a rough classification by name]:

- **Generic** (statement has `t` for `Char`, proof unchanged): the handler
  lemmas (`runFromThenOk`, `runFromOptionalFromOk`, the `label` and
  `attempt` ones), `readsPure`, `readsBind`, `readsThen`, `readsDone`,
  `readsMap`, `readsWeaken`, `readsSatisfy`, `readsOptional`,
  `readsMany`, `readsMany1`, `readsSepBy`, `readsSepBy1`, `readsOneOf`,
  `readsChainLeft`, `readsRecursive`, `readsRepeat`, `readsExactly`,
  `readsAttempt`, `readsFindAll`, `readsLabel`, `wholeReads`, and the
  matching `runs…` and `declines…`.
- **Characters only** (statement and proof unchanged, the parser is a
  `Parse Char` one): `readsNat`, `readsChar`, `readsText`,
  `readsTakeWhile1`, `readsDigit`, `readsInt`, `readsNatDigits`,
  `readsSpaces`, `readsToken`, `readsNewline`, `readsPick`, `readsLines`,
  `readsSections`, `readsGrid`, `eachLineReads`, `lineReads`, `allReads`,
  `runsNat`, `runsText`, `runsEachLine`, `cannotStartAtBreaks`, and the
  rest about digits, lines, blank lines and sections.

A 900-line slice made properly generic (the ability, the handler,
`optional`, `oneOf`, `many`, the four tree lemmas, `readsBind`,
`readsThen`, `readsSatisfy`, `readsDone`, `readsMap`) checked with no
proof edited, including the inductions over the computation tree
(`match reify p with | Parse.span passes, q => …`) [measured]. An AoC-style
proof written against it (`readsThen readsSatisfy (… => readsThen
readsSatisfy (… => readsDone …))`) checked word for word the same as
against today's [measured].

**New proofs needed:** the generic `literal` lemma (the tokens read are
`same` as the items, one small induction on the new `stripPrefixBy`), with
`readsText` and `runFromLiteralThere` then following from "`Text.sameChar`
holds exactly of equal characters", which std has (`Text.sameCharEq`
[source]); and lemmas for the new
pieces (`readsOne`, `runsOne`, `readsLocated`). About ten theorems.

## 2. Lex, then parse

```
--| A value with where it was read: `offset` characters in, `length` long.
type Parse.Located (a: Type) = { value: a, offset: Nat, length: Nat }

--| `parser`'s value with where it was read.
def Parse.located (parser: () → {Parse Char} a): {Parse Char} Parse.Located a

--| Lexes all of `input`, then parses all of the tokens; fails with
--| "line 3, column 9: expected ',' or ')', got ';'".
def Parse.tokens (input: Text) (lexer: () → {Parse Char} List (Parse.Located token))
    (parser: () → {Parse (Parse.Located token)} a): {Fail} a
```

A program would look like this (a sketch with the proposed names; the
probe ran the same shape with what exists today: a lexer giving located
tokens, then `many`, `optional`, `next` and `end` over them [measured]):

```
type Token = | Ident (name: Text) | Num (n: Nat) | Sym (c: Char)

def token(): {Parse Char} Parse.Located Token :=
  Parse.spaces()
  Parse.located (() => Parse.oneOf [
    () => Ident (Parse.takeWhile1 "a name" Char.isAsciiLetter),
    () => Num Parse.nat(),
    () => Sym (Parse.satisfy "a symbol" isSymbol)])

def symbol (c: Char): {Parse (Parse.Located Token)} () := …   -- "expected ','"

def call(): {Parse (Parse.Located Token)} Expr :=
  let name := Parse.one "a name" (match some | { value = Ident name } => name)
  symbol '('
  let arguments := Parse.sepBy expression (() => symbol ',')
  symbol ')'
  Call name arguments

def parse (input: Text): {Fail} Program := Parse.tokens input (() => Parse.many token) program
```

**Positions.** `located` takes a mark before and after its parser; the
offsets are already in the marks, so it is two cheap operations a token. A
token keeps its offset and length, not its line and column: those are
worked out from the source only when a message is made, as today
(`Parse.lineAndColumn`). A tree that wants spans takes them from its
tokens. Comments and blank lines a formatter must keep are the lexer's to
attach (a `trivia` field in the program's own token type); `Parse` doesn't
need to know.

**Error messages.** Three cases, all through today's
`Parse.Failure.describe`:

- *Lexing fails:* today's message, unchanged.
- *Parsing fails at token `i`:* the failure's `offset` is `i`. The runner
  turns it into a character failure at `tokens[i].offset` with `width =
  tokens[i].length`, and describes that against the source. "Got" is then
  the token as the author wrote it, so tokens need no `Show`. The furthest
  failure and its expectations are kept exactly as for characters: the
  probe gave `expected ["an operator", "','", "')'"]` at the stray `;` of
  `foo(1, 2;` [measured].
- *Parsing fails after the last token:* "got the end of the input".

A program with its own token type or positions uses `Parse.run tokens
parser` and maps `failure.offset` itself.

**What this doesn't do.** Layout-sensitive grammars (blocks ended by
columns, as Stitchwort's own) need each token's column, which a lexer can
store in its token; nothing here helps or hinders. The self-hosted
formatter's parser stays hand-written for the reasons in
self-hosted-fmt.md §3.2 (it must match the Rust parser function for
function); this library is for the toy language and for ordinary
programs.

## 3. Performance

### 3.1 Checking

`Std.Parse`'s own declarations take 103.6 M steps (11.5 s wall for `check
--std Parse --no-cache`, with what it imports) [measured; the brief's 121 M
is SW-3223's figure]. Where they go:

| | Steps | Share |
|---|---|---|
| 22 handler lemmas (inductions over the computation tree, one arm per operation) | 60.8 M | 59% |
| of which the three about `labelWhole` | 31.8 M | 31% |
| everything else (416 declarations) | 42.8 M | 41% |

The cost of the parameter [measured]:

| Experiment | Before | After | |
|---|---|---|---|
| All of `Std.Parse`, parameter added, every use at `Char` | 103.6 M | 115.2 M | +11%; wall 11.5 s and 11.1 s, so within noise |
| A 900-line slice, properly generic | 9.18 M | 11.17 M | +22%; elaboration 550 ms to 714 ms |

The generic part is about 75 M of today's steps and the character part
28 M, so the full design is about 75 × 1.22 + 28 × 1.11 = **123 M steps,
+19%** [estimated from the two rows], perhaps a second of an 11 s check,
paid once and then cached.

**The cost that needs fixing first.** A user's proof against the properly
generic slice:

| `readsTwo`, a two-step `readsThen` chain | Steps |
|---|---|
| today's `Parse` | 281 k |
| generic lemmas, `t` worked out by the checker | 498 k (+77%) |
| generic lemmas, `[t := Char]` written on each `readsThen` | 312 k (+11%) |
| the same, and on `readsSatisfy` and `readsDone` | 289 k (+3%) |

So the extra is not the parameter but how late the checker settles it:
with the type given, the cost is back. The expected type (`Parse.Reads
twoLetters Written`) already fixes `t`, so this looks like an ordering
matter in the elaborator, not something inherent [estimated]. Parser
proofs are 43 files of `aoc/`, so this decides whether the sweep costs the
whole-AoC check 8% of its parser proofs' time or 77%. Stage 0 is to fix it
(or, failing that, state the client lemmas so `t` is settled first).

**Cheaper regardless of this design:** the `labelWhole` lemmas are 31% of
the namespace. Each handler-wrapping combinator proves its own eight-arm
induction; one shared lemma for "a handler that passes every operation on
and acts only at `stop`" would serve `optional`, `label`, `labelWhole`,
`attempt` and `sectionLine` [estimated; a ticket below].

### 3.2 Running

One input line repeated: `total(alpha, 12 + beta * 345); gamma(delta, 7,
epsilon) + 99;`, 11 tokens to 31 characters. Times are after subtracting
the run with empty input (1.0–1.5 s of checking and compiling the probe)
[measured]:

| | 100 KB (35,200 tokens) | 1 MB (352,000 tokens) |
|---|---|---|
| Lexer, today's `Parse`, interpreter | 0.47 s | 4.0 s |
| Lexer, generic `Parse`, interpreter | 0.53 s | 4.0 s |
| Lexer, today's, `--native` | – | 1.9 s |
| Lexer, generic, `--native` | – | 1.9 s |
| Lex with positions, then parse the tokens (generic), interpreter | 0.67 s | 7.2 s |
| The same, `--native` | 0.36 s | 3.5 s |
| Peak memory, lex then parse | 151 MB (148 MB with no input) | 257 MB |

- **The generalisation is free at run time:** type arguments are erased,
  and the two lexers are within noise of each other.
- **It scales in a straight line** to 1 MB (10 times the input, 10.7
  times the time), about 110 bytes of memory per input byte.
- **A 100 KB file is fine** for a formatter of a toy language: under half
  a second native.
- **It is slow against a hand-written scanner:** self-hosted-fmt.md
  measured 0.11–0.13 s/MB for one, native; this lexer is 1.9 s/MB, about
  15 times slower on a different but comparable input. The profile says
  why: 35% of the time is the handler's own loop, at 8.5 operations a
  token (each failed alternative of `oneOf` is a `note`, a `stop` and a
  `reset`), and about another 19% is list work around `span` and `many` (building,
measuring and reversing). This
  is `Parse` as it is today, not the generalisation, and speed work is
  paused (D3465); two cheap improvements are listed as findings.

**Backtracking.** A mark holds the rest of the input as a list, so going
back is one pointer, for tokens as for characters; nothing is copied.
Choice always backs up fully and nothing is memoised, so a grammar whose
alternatives share a long prefix reads it once per alternative, as today;
`Parse.pick` and, for tokens, `Parse.one` with a `match` over the token's
constructors choose in one operation. Fuel for `many` and `recursive` is
the number of tokens left, which is what it is for characters.

**The input as a list.** 100 KB is 100,000 list cells before lexing; the
measurements above include that. A cheaper `Text` (slices, indexed reads)
is SW-3234's design (IO and text), and would change how `Parse Char` holds
its input without changing this design: the parameter is what is read,
not how the input is stored. I would not make the input's container
generic as well (an interface for streams): `Reads` is stated with `++` on
lists, and every lemma would pay for it.

## 4. Stages

| Stage | What | Model | Hours [estimated] |
|---|---|---|---|
| 0 | Find why the checker settles an ability's parameter late in `readsThen` chains and fix it; the probe is the test (498 k steps to about 300 k) | Opus (the unifier, D2506) | 1–2 |
| 1 | The parameter: `Parse (t: Type)`, `Mark`, `State`, `Parse.Literal`; generic functions and lemmas, the character layer, the file split; `{Parse}` to `{Parse Char}` in `aoc/`, `examples/`, the tests and docs; the guide (`docs/guide/06`, `08`, `web/guide/20-parse.sw`) and docs/syntax.md | Opus for std (it re-types 298 theorems and the split is a judgement); DeepSeek for the substitution outside std | 4–5 |
| 2 | Tokens: `Parse.Located`, `located`, `one`, `span1`, `Parse.tokens` and its messages, their lemmas, a guide section "Lex, then parse" and a feature-tour page | Sonnet | 2–3 |
| later | Speed: the findings below, when speed work resumes | – | – |

Gates for stage 1: `Std.Parse` under 130 M steps; the three AoC days above
within 15% of their steps today; no theorem statement in `aoc/` changed
apart from the row. The orchestrator checks statements one by one as for
any re-typing refactor (D2436).

**What the toy-language formatter needs first:** stages 1 and 2, and
reading a file (SW-3234). It needs none of the `Runs` lemmas for tokens
and not stage 0, though stage 0 should land before stage 1's sweep so the
rolling check isn't slowed. I'd have the toy formatter lex and parse with
this library: it is the cheapest real test of it, and it tells us whether
combinators are fast and pleasant enough before the full twin is decided
([D3589](#7-questions-for-matt)).

## 5. Alternatives considered

- **A second ability for tokens.** Two copies of every combinator and
  lemma ([§1.2](#12-the-design)).
- **Parsers as values** (`Parser t a = List t → Result …`). Loses direct
  style; all of `aoc/` rewritten, not swept.
- **Equality from an interface** (`[auto eq: DecEq t]` on the runner).
  Wrong for tokens that carry positions, and an instance argument in every
  lemma about `runFrom`.
- **Generic over the input's container too.** [§3.2](#32-running), last
  paragraph.
- **Leave `Parse` alone; hand-write token parsers.** Costs nothing now,
  but every program with a lexer loses the error messages and the lemmas,
  and the gap was the first thing the formatter plan ran into.

## 6. Decided here as implementation

Say if you disagree: `literal` carries its comparison; `Failure` and
`Problem` keep their shape; tokens keep offset and length, not line and
column; a token failure is described by today's `Failure.describe` against
the source; the input stays a list; one file per layer.

## 7. Questions for Matt

**D3588: write `{Parse Char}`, or keep `{Parse}` for characters?**
*The problem:* once `Parse` says what it reads, every character parser's
signature says so too: `def point(): {Parse Char} Point`, in 68 AoC files
and the guide.
*The change:* either accept the five characters (a one-line substitution
over the repo, tried on three days' proofs), or add a language feature so
`{Parse}` can stand for `{Parse Char}` (an ability synonym, or a default
for an ability's parameter), with the generic one under another name.
*What it should do:* written out, there is one ability, no new feature,
and a token parser's `{Parse Token}` reads the same way. The feature would
keep AoC signatures as they are at the cost of a rule newcomers must
learn. **[rec: write `{Parse Char}`]**

**D3589: build it now, and write the toy formatter with it?**
*The problem:* the toy-language formatter (D3579's next step) needs a
lexer and a parser. By hand it tests nothing of std; with this it needs
stages 1 and 2 first.
*The change:* stages 0 to 2, 7–10 lane hours [estimated], before the toy
formatter starts; the toy formatter then lexes and parses with
`Std.Parse`. Checking `Std.Parse` costs about 19% more steps [estimated
from measurements]; run time is unchanged [measured].
*What it should do:* programs can lex then parse with proved combinators
and positioned errors, and the toy formatter becomes the test of whether
combinators are fast enough (0.4 s for 100 KB today) before the full twin
is decided. **[rec: yes]**

**D3590: keep the text parsers under `Parse.`?**
*The problem:* `Parse.nat`, `Parse.text` and `Parse.eachLine` only make
sense for characters; in a generic library they could move to a namespace
of their own (`Parse.Chars.nat`).
*The change:* keep them where they are, in their own file but the same
namespace; or move them and rename every use.
*What it should do:* kept, no AoC call or lemma name changes and
`Parse.nat` stays the short thing people reach for; moved, the names say
which layer a function is in, and every day's imports and proofs are
renamed. **[rec: keep]**

## Findings worth tickets

- **The checker settles an ability's parameter late.** A `readsThen` chain
  against generic lemmas takes 77% more steps than with `[t := Char]`
  written on each call (498 k against 289 k), though the expected type
  fixes it. Stage 0; probe `cgeneric.sw` against `cgeneric2.sw`.
- **`labelWhole`'s three handler lemmas are 31% of `Std.Parse`'s check**
  (31.8 M of 103.6 M steps; `runFromLabelWholeFromOkTree` alone is
  13.4 M), and the 22 handler lemmas together 59%. One shared lemma for
  handlers that pass every operation on would replace most of each.
- **`oneOf` costs about three operations per failed alternative** (`note`,
  `stop`, `reset`), which is most of a lexer's 8.5 operations a token. A
  choice by the next token (`Parse.oneOfBy (first: t → Option …)`, or a
  `peek` operation) would make a lexer's dispatch one operation. Parked
  with speed work.
- **The handler walks what `span` took a second time to measure it**
  (`List.lengthOnto` is 8% of the lexer's time, and with `reverseOnto` and
  `spanOnto` 19%): a `span` that counts as it goes would save the walk.
- **`Parse.token` is a confusing name in a library that now has tokens:**
  it means "with spaces allowed around". `Parse.padded` would match its
  spec, `Parse.Padded`. Ten AoC files import it [measured, grep].
- **`Text.stripPrefixChars` and its three lemmas are a special case** of a
  list function `List.stripPrefixBy` that std doesn't have; stage 1 adds
  it, and the text lemmas become corollaries.
- **The brief's 121 M steps for `Std.Parse` and this note's 103.6 M
  differ.** Mine sums `STITCHWORT_TIMINGS=decls` over declarations named
  `Std.Parse.*`; SW-3223's may count imports or tests. Worth one line in
  SW-3223's guard saying which.
- **Row synonyms don't exist** (`type Chars = Parse Char` is `E-ABILITY`).
  Not needed if D3588 is "write it out"; noted because a program with a
  long token type will want to name `{Parse (Parse.Located Token)}`.

## Appendix A: the probes

All in the lane's scratch folder; none is kept. `Prs` is `Parse` renamed
so a copy can sit beside std's.

| Probe | What | Result |
|---|---|---|
| `p1b.sw` | a five-operation generic ability, a handler, `optional`, a character and a token parser | checks; tests pass |
| `fixed2.sw` / `generic.sw` | lines 30–417 and 838–886 of `Parse.sw` and 45–533 of `Reads.sw`, as they are and made generic by script (`gen.py`), `literal` taking its comparison | both check; 9.18 M and 11.17 M steps; three statements needed `(read: List t)` |
| `cfixed.sw` / `cgeneric.sw` / `cgeneric2.sw` | an AoC-style `readsThen` proof against each | same proof text; 281 k, 498 k, 289 k steps |
| `stdchar/`, `aocchar/` | std and `aoc/src` with the ability parameterised and `{Parse}` replaced by `{Parse Char}` (`char.py`) | `check --std Parse` and three days' `Proofs` check; steps in [§1.3](#13-does-aoc-code-get-noisier) |
| `rfixed.sw` / `rgeneric.sw` | a three-alternative lexer on 100 KB and 1 MB | [§3.2](#32-running) |
| `lexparse.sw` | lex with positions, then a fuelled expression parser over `Located Tok` with `many`, `optional`, `next`, `end` | [§3.2](#32-running); the error case in [§2](#2-lex-then-parse) |
| `syn.sw` | a type synonym in a row | `E-ABILITY` |
