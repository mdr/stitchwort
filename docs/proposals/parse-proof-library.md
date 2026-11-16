# Std's parser-proof library: the end state

Opus paper lane, SW-3493, 16 November 2026. Takes in SW-3460 (offsets in
`Reads`), SW-3465 (one `Reads` with an invariant) and SW-3478 (a generic
"keeps P" walk), and §2.1 and §4.7 of
[after-the-toy-proof.md](after-the-toy-proof.md). No builds or tests were
run. Numbers marked **[measured]** were counted with `grep` at `6767eb4ef`;
**[estimated]** ones are mine. Judged by the end state only (D2303):
what the migration costs doesn't count.

## In plain words

**The problem.** Std's parser proofs say what a parser read and gave
(`Parse.Reads`) and that it succeeds on good input (`Parse.Runs`). The toy
formatter's proof needed three more things `Reads` can't say, and each
became a copy: `Parse.Paced` for offsets (19 theorems), `Parse.ReadsAmong`
for "every token is good" (18 theorems, the combinator proofs again), and
three walks over the parser's 65 functions, one per property (201
theorems; 31 of their lemmas take the handler's state apart to see the
next token). A real
formatter's parser has 234 functions.

**The change.** One `Reads`, parameterised by what is true of the input
left, whose "honest state" also says where the parse is; a `Gives` layer
on top that proves several properties in one walk; a `peek` lemma so walk
proofs never open the state; a declines toolkit for token parsers; and an
elaborator change so `readsThen` finds its two parsers from the proof
instead of guessing from the goal.

**What it should do.** In std, `Paced.sw` and `Among.sw` go (37 theorems,
829 lines [measured]) for about 8 new ones. In the toy, the 201 walk
theorems become about 135, and the 31 proofs that take the state apart
to peek no longer do [estimated]. For the real formatter, the walk is about 250 theorems
instead of 700, the declines toolkit saves 50 to 100 more, and no lemma
has a second "…Of" version for when inference fails [estimated].

## 0. What there is now

| Piece | Where | What it says | Size [measured] |
|---|---|---|---|
| `Parse.Reads p spec` | `std/Parse/Reads.sw:45` | from any honest state (`left = rest.length`), a success read a start `read` of the input, left an honest state, and `spec read value` | Reads.sw 78 theorems; ReadsChars 43, ReadsOperators 10, ReadsTokens 3 |
| `Parse.ReadsAmong fine p spec` | `std/Parse/Among.sw:20` | the same, given `List.All fine` of what is left | 18 theorems, 491 lines |
| `Parse.Paced p` | `std/Parse/Paced.sw:13` | a success leaves `offset + left` unchanged | 19 theorems, 338 lines (with `ReadsFrom` and `locatedToEnd`) |
| `Parse.ReadsFrom state p spec` | `std/Parse/Paced.sw:148` | `Reads` from one state, so `spec` may depend on the input | 12 uses |
| `Parse.Runs`, `RunsFrom` | `std/Parse/Runs.sw:38,52` | completeness, already with the offset clause (`after.offset = state.at.offset + read.length`) | Runs 88, RunsChars 76, RunsOperators 15, RunsTokens 7 |
| `Parse.Declines p input` | `std/Parse/Runs.sw:526` | `optional p` gives `None` and stays put | 17 character lemmas (`RunsChars.sw:109` on), 8 generic |

Users: aoc has 24 files with 322 references to `Parse.reads…` lemmas, 92 of
them `readsThen`, and none that opens a `Reads` at the state level; the
roguelike has none. The toy's walks take the state apart (`match e: state.at.rest`) in 31
lemmas (11 in `ShapeProofs.sw`, 11 in `ParsedProofs.sw`, 9 in
`HeadProofs.sw`), which then pass `state value after honest h` on by hand
145 times across the four proof files; it has 60 uses of `Parse.paced…`
[all measured].

## 1. One `Reads`, with an invariant and offsets (SW-3460, SW-3465)

### 1.1 The statements

The key choice: put the offset in the *honesty* of a mark rather than in
`Reads`' conclusion. Honesty is threaded through every combinator
unopened, so a stronger honesty changes the primitives' proofs and no
combinator's. Stating `after.offset = start.offset + read.length` directly
would instead put an `omega` into every combinator that chains (as
`pacedThen`, `Paced.sw:24`, has today).

```
--| A mark of a run over `total` items: `left` counts the items in
--| `rest`, and the offset and the count left add up to `total`. Every
--| mark of a run from the start is honest.
def Parse.Honest (total: Nat) (at: Parse.Mark t): Prop :=
  at.left = at.rest.length ∧ at.offset + at.left = total

--| What `parser` reads and gives when run from the mark `start`: from
--| any state at an honest `start`, a success read a start `read` of
--| `start.rest`, stopped at an honest mark, and `spec read value` holds.
def Parse.ReadsAt (start: Parse.Mark t) (parser: () → {Parse t} a) (spec: List t → a → Prop): Prop :=
  ∀ (total: Nat) (state: Parse.State t) (value: a) (after: Parse.Mark t) =>
    state.at = start
    → Parse.Honest total start
    → Parse.runFrom state (() => (parser(), Parse.mark())) = Ok (value, after)
    → ∃ (read: List t) => start.rest = read ++ after.rest ∧ Parse.Honest total after ∧ spec read value

--| A property of the input left that reading keeps: if it holds of
--| `read ++ rest`, it holds of `rest`.
type Parse.Invariant (t: Type) = {
  holds: List t → Prop,
  kept: ∀ (read rest: List t) => holds (read ++ rest) → holds rest
}

--| `parser` reads as `spec` says from every mark where `inv` holds of the
--| input left.
def Parse.ReadsIn (inv: Parse.Invariant t) (parser: () → {Parse t} a) (spec: List t → a → Prop): Prop :=
  ∀ (start: Parse.Mark t) => inv.holds start.rest → Parse.ReadsAt start parser spec

--| From every mark: the case of no invariant.
def Parse.Reads (parser: () → {Parse t} a) (spec: List t → a → Prop): Prop :=
  Parse.ReadsIn Parse.Invariant.any parser spec
```

with `Parse.Invariant.any` (`holds := _ => True`), `Parse.Invariant.every
fine` (`List.All fine`, kept by `List.allAppendRight`), and
`Parse.Invariant.both`. A list-level invariant, not only an item-wise one,
because "tokens' offsets increase" or "the input ends in `Eof`" are kept
by reading and aren't of each item alone; it costs nothing extra, since
`kept` is proved once per invariant, not per lemma.

The offset fact users want is a corollary, proved once:

```
theorem Parse.honestMoved ∀ (total: Nat) (start after: Parse.Mark t) (read: List t)
    (before: Parse.Honest total start) (now: Parse.Honest total after)
    (starts: start.rest = read ++ after.rest):
    after.offset = start.offset + read.length
```

and `spec` can mention the start's offset because `ReadsAt` names the
start mark: `Parse.ReadsAt start lexeme (read value => value.offset =
start.offset ∧ …)`.

### 1.2 How the three become instances

- **Plain `Reads`** is `ReadsIn any`. Its name and meaning stay; every
  aoc statement (64 `Parse.Reads` statements [measured]) reads as before.
  The lemmas are stated once over `ReadsIn [inv]` with `inv` implicit, so
  `Parse.readsThen` serves both; `inv` is found by unfolding `Reads`, as
  the toy's `Gives` (a `def` over `Reads`, `ShapeProofs.sw:16`) is
  unfolded by std's lemmas today.
- **`ReadsAmong fine`** is `ReadsIn (Parse.Invariant.every fine)`.
  `Parse.amongOf` (`Among.sw:35`) becomes `Parse.readsInOf`: a lemma under
  a weaker invariant holds under a stronger one (`any` is the weakest).
  `Parse.amongOne` (`Among.sw:90`) stays as the one lemma that *uses* the
  invariant: `Parse.readsOneEvery`, "the item `one` read is `fine`".
- **`Paced`** goes: every `ReadsIn` says the marks count. `ReadsFrom`
  (`Paced.sw:148`) is `ReadsAt` (a mark, not a whole state), and
  `locatedToEndReads` (`Paced.sw:277`) loses its `paced` hypothesis.

### 1.3 Which proofs change

| Proof | Change | Count [measured] |
|---|---|---|
| Primitives: `readsPure`, `readsMark`, `readsNote`, `readsSpan`, `readsNext`, `readsLiteral`, `readsLiteralSame` (`Reads.sw:322-489`) | prove the second half of `Honest` too: one more `omega` over the same facts (`Parse.pacedSpan`, `Paced.sw:69`, is that proof already) | 7 |
| Failing ones: `readsStop`, `readsFatal`, `readsExpected`, `readsFail` | none | 4 |
| Combinators that run a sub-parser from a later mark: `readsBind`, `readsThen`, `readsManyFrom`, `readsSepBy1`, `readsChainLeft`, `readsRepeat…`, `readsFindAll…`, `readsOperatorsFrom` … | one line where the second parser starts: `inv.kept firstRead middle.rest (rewrite <- starts1 in holds)`, exactly `amongThen`'s `amongRest` (`Among.sw:69-70`) | about 25 |
| Combinators that back up (`optional`, `attempt`, `label`, `oneOf`) | none beyond renaming `honest` to `fit`: the start mark's `Honest` is reused | about 10 |
| Corollaries built from other lemmas (`readsSatisfy`, `readsOne`, `readsMap`, the ReadsChars pieces) | none | about 75 |
| The handler lemmas (`runFromThenOk2Tree` etc.) | none: they don't mention `Reads` | 12 |

So "every primitive's proof, no combinator's" (friction 42) is right for
the offset, and the invariant adds one line to each chaining combinator.
That line is the whole of `Among.sw`'s 491 lines, written once.

### 1.4 `Runs` stays separate

Completeness doesn't merge. `Runs p read rest value` is given its input
(`read ++ rest`), so an invariant of the input adds nothing: whoever
states a `Runs` knows the input. It already has the offset
(`Runs.sw:44`). Its proofs construct a run rather than take one apart,
so no proof is shared with `Reads`. The one change is cosmetic and I'd
skip it: restating `RunsFrom`'s two clauses as `Honest`. **Decided: `Runs`
unchanged.**

## 2. A "keeps P" layer: `Gives` (SW-3478)

### 2.1 The layer

```
--| Whenever `parser` succeeds from input where `inv` holds, `holds` of its value.
def Parse.Gives [inv: Parse.Invariant t] (parser: () → {Parse t} a) (holds: a → Prop): Prop :=
  Parse.ReadsIn inv parser (read value => holds value)
```

Its lemmas, each a corollary of the `reads…` one (a line or two): `givesDone`,
`givesThen`, `givesWeaken`, `givesOptional` (with `Parse.Perhaps`, from
`ShapeProofs.sw:94`), `givesMany`, `givesMany1`, `givesSepBy`,
`givesOneOf`, `givesOperators` (each level's combining function keeps
`holds`), `givesRecursiveWith` (the nested parser gives `holds`),
`givesNote`, `givesExpected`, and the join:

```
theorem Parse.givesBoth ∀ [inv] [p] [holds other: a → Prop]
    (first: Parse.Gives p holds) (second: Parse.Gives p other):
    Parse.Gives p (value => holds value ∧ other value)
```

and its general form `Parse.readsBoth` (two specs of one parser hold of
the same `read`, by cancelling `after.rest` on the right).

Two new lemmas remove the state-level proofs (friction 5). 31 of the
toy's walk lemmas open the state to see the next token for a
`match peek() with` (the toy's `peek`, `Syntax/Parser.sw:59`, is
`Parse.mark().rest.head`). Std gets `Parse.peek` and:

```
--| A parser that looks at the next item: prove it at each start.
theorem Parse.readsInPeek ∀ [inv] (k: Option t → {Parse t} a) (spec: List t → a → Prop)
    (each: ∀ (start: Parse.Mark t) => inv.holds start.rest → Parse.ReadsAt start (() => k start.rest.head) spec):
    Parse.ReadsIn inv (() => k (Parse.peek())) spec

theorem Parse.readsAtThen ∀ [start] [p] [j] [first spec]
    (readsFirst: Parse.ReadsAt start p first)
    (rest: ∀ (read: List t) (v: a) (after: Parse.Mark t) => start.rest = read ++ after.rest → first read v
      → Parse.ReadsAt after (() => j v) (taken w => spec (read ++ taken) w)):
    Parse.ReadsAt start (() => j (p())) spec
```

A walk lemma for a peeking function then reads `start fine => match e:
start.rest with …`, and `k start.rest.head` computes after the `match`,
with no `runFrom`, no `Result.okInjective` and no `Pair.mkInjective…`.

### 2.2 Generic, derived, or one lemma per function

- **Generic in the logic: no.** A theorem can't quantify over "every
  function of this parser": the functions are code, and only a parser
  written as data (a grammar value interpreted by a runner) would let one
  induction cover them. That would change how parsers are written and
  cost speed, which §4.6 of the toy note says the formatter can't spare.
  Rejected.
- **One lemma per function, one walk for all properties: yes, now.** The
  toy's three walks (45, 43 and 29 walk lemmas, 117 in all [measured])
  become one walk proving `Shaped ∧ Lexical ∧ Headed` under
  `Invariant.every Good`, about 50 walk lemmas [estimated]. The 84 value
  lemmas (`shapedItemsAppend`, `headedCleared`, …) stay: they are the
  properties' own content. `givesBoth` lets a later property be proved as
  a separate walk and joined, when that is easier to review.
- **Derived by a tactic: later, if the residue is still mechanical.** In
  the toy's walks most of each lemma is dictated by the parser's syntax
  (`givesAtomOf`, `ShapeProofs.sw:250-311`: one `givesThen` per bind,
  `givesDone` with a value fact at each leaf). A `gives` tactic that
  unfolds a parser function and applies the matching lemma, leaving the
  leaf facts and loop invariants, would turn ~250 formatter walk lemmas
  into ~250 short calls. It is a tactic, so it is Matt's call, and it
  should be judged on the joint walk's residue (lane 4 below measures
  it). Not asked now: no lane needs it.

### 2.3 Relation to §1

`Gives` is `ReadsIn` with a spec that ignores what was read, so it gets
the invariant and offsets for free, and the toy's `Fair`
(`ParsedProofs.sw:32`) is `Gives [inv := Invariant.every Good]`. Without
§1, `Gives` would need its own `among` copy again; that is why §1 goes
first.

## 3. A declines toolkit for token parsers (frictions 4, 77, 80)

`Parse.Declines` (`Runs.sw:526`) stays as it is. Std has its character
cases; the toy built the token and combinator cases by hand
(`ExpressionProofs.sw:2177-2311`). New generic lemmas in
`std/Parse/Runs.sw`:

| Lemma | Says | Replaces in the toy |
|---|---|---|
| `declinesBind` (exists, `Runs.sw:540`), `declinesAfter` (exists, `:1060`) | first part declines; or succeeds and the rest declines | — |
| `declinesNote` | `note problem` then `j ()` declines where `j ()` does | the `declinesAfter`+`runsNote` pair in `postfixDeclines` (`:2219`); friction 77 |
| `declinesPeek` | `k (peek())` declines on `input` where `k input.head` does | the `rewrite starts … in rfl` steps of `atomDeclines`, `negationsDecline`, `chainRuleStops` (`:2206-2277`) |
| `declinesOptionalThen` | `optional p` then `j` declines where `p` and `j None` do | — |
| `declinesManyThen` | `many p` then `j` declines where `p` and `j []` do | — |
| `declinesOperators` | `operators` declines where its operand does | `operatorsDecline` (`:2251`), verbatim |
| `declinesOneOf` | every alternative declines | generalises `declinesOneOfTwo` (`:1324`) |
| `declinesRecursiveWith` | `recursiveWith body argument` declines where `body self argument` does for every `self` | `fuelDeclines`, `expressionDeclines` (`:2299-2311`) |
| `declinesOne`, `declinesOneEnd` (exist, `:564-575`) | the token case of `one` | — |

The `Runs` side of recursion (friction 80): `Parse.runsRecursiveWith`'s
step (`Runs.sw:1180`) may assume only what the nested parser reads. The
end state gives the step a fact about the nested parser too:

```
theorem Parse.runsRecursiveWithFact ∀ (body: (b → {Parse t} a) → b → {Parse t} a)
    (good: b → List t → List t → a → Prop) (fact: (b → {Parse t} a) → Prop)
    (facts: ∀ (fuel: Nat) => fact (inner => Parse.recursiveWithFuel (Succ fuel) body inner))
    (step: ∀ (self: b → {Parse t} a) (argument: b) (read rest: List t) (v: a) => good argument read rest v
      → fact self
      → (∀ … shorter … → Parse.Runs (() => self nestedArgument) nestedRead nestedRest w)
      → Parse.Runs (() => body self argument) read rest v)
    (argument: b) (read rest: List t) (v: a) (holds: good argument read rest v):
    Parse.Runs (() => Parse.recursiveWith body argument) read rest v
```

with `Parse.recursiveFacts`: if `fact (inner => body self inner)` for
every `self`, then `facts` (the toy's case: "declines at a keyword"
holds whatever reads the nested parts). `runsRecursiveWith` becomes the
case `fact := _ => True`, and the toy's copied induction,
`runsExpressionFuel` (`ExpressionProofs.sw:1417`, 45 lines), goes.

Friction 4's other gaps, `Runs` lemmas for `lastRead` and
`locatedToEnd`, are in std now (`Runs.sw:1201-1230`,
`Parse.runsLocatedToEnd`, `RunsTokens.sw`) and need nothing here.

## 4. `readsThen` that finds its parsers in the proof (frictions 19, 44)

**The problem.** `Parse.readsThen [p] [j] … readsFirst rest` is checked
expected type first (postponement.md, stage 7), so `?j (?p ())` is
unified with the goal's parser before `readsFirst` is looked at. That is
a higher-order problem with many solutions. When the continuation ignores
its argument, or the first step is `mark()`, or the goal reaches `j
(p())` only after unfolding a `let`, the guess is wrong and the error is
reported on the first lemma. So std has `readsThenOf` (13 uses in std, 7
in the toy [measured]) and `amongThenOf`, with the parsers written out,
and a `match` can't be written there (`E-MATCH-MOTIVE`, friction 44).

**The change.** An elaborator rule, not a new lemma: when unifying an
expected type would mean solving an application whose head is an unknown
(`?j (?p ())`, not a pattern), postpone it instead of guessing, check the
explicit arguments first, and come back. `readsFirst: Parse.Reads p
first` then fixes `?p` first-order. With `p` known, `?j` is found by
abstracting the occurrences of `p ()` in the goal's parser after
weak-head unfolding (Lean 4 has both pieces: `kabstract`, and the
`elab_without_expected_type` attribute). This uses the postponement queue that exists
(`crates/elab/src/unify.rs:100`, stage 6) and helps every lemma about a
higher-order shape, not only parsers.

**What it should do.** `readsThenOf`, `amongThenOf` and `pacedThen […]`
spellings go; the toy's `stringSegment` (friction 44, done at the state
level because the continuation needed a `match`) becomes an ordinary
chain. Risk: a different solution where the old guess happened to be
right; aoc's 92 `readsThen` uses are the test set.

## 5. Cost and payoff

### 5.1 Std

| | Before [measured] | After [estimated] |
|---|---|---|
| `Among.sw` | 18 theorems, 491 lines | gone; `readsInOf`, `readsOneEvery`, three invariants |
| `Paced.sw` | 19 theorems, 338 lines | gone; `honestMoved`; `locatedToEnd…` move to `ReadsTokens.sw` without `paced` |
| `Reads*.sw` | 134 theorems | 134, about 40 touched by a line or two |
| New | — | `Gives` and its ~14 lemmas, `readsAtThen`, `readsInPeek`, `readsBoth`, ~8 declines lemmas, `runsRecursiveWithFact` |

### 5.2 The toy

| What goes or shrinks | Theorems | Notes |
|---|---|---|
| Three walks → one joint walk | 117 → about 50 | value lemmas (84) stay |
| State-level peek proofs | 31 lemmas → 0; 145 hand-passed states → about 15 | `readsInPeek`, `readsAtThen` |
| `…Paced` lemmas in `LexTextProofs.sw` | 8 → 0 | offsets come with `Reads` |
| Declines lemmas, `runsExpressionFuel` | 15 → about 5 | the token-specific ones stay (`notMinusAtReserved`, …) |
| `readsThenOf` and `[p := …] [j := …]` | 7 calls | ordinary `readsThen` |

So the toy's 1,262 theorems drop by about 85, and its three walk files
(3,800 lines) to about 1,600 [estimated]. The toy is the test of the
library, so its tidy-up is part of the lanes, not optional.

### 5.3 The real formatter (about 234 parser functions)

One joint walk: about 250 walk lemmas against about 700 for three walks
(after-the-toy-proof.md §2.1). Peek proofs at the mark level make each
lemma about a third shorter than the toy's state-level ones, judging by
`givesAtomOf` (`ShapeProofs.sw:250`, no opening) against
`givesSignInBrackets` (`:66`, opened) [estimated]. The declines toolkit
saves 50 to 100 theorems in the read-back (§4.7). With `readsThen`
inference, the retries it caused go; the toy's NOTES don't time them, so I
give no figure.

### 5.4 aoc

Lemma names and `Parse.Reads`' meaning stay, so most of the 24 files
check unchanged [estimated]; some `readsThen` chains will need `inv`
found through `Reads`' unfolding, which works for `Gives` today. What aoc
gains: a parse proof can say where a value was read (offsets, as day
positions need) without a second property, and a proof over tokens can
use the lexer's guarantee through `Invariant.every`.

## 6. Lanes, in order

Agent-time estimates, from past actuals (median 0.3 of a human-style
estimate). Each lane checks only the std files or toy files it edits
(`stitchwort check` of that namespace), with named tests as CLAUDE.md
says. Checking all of `tools/toyfmt` (about 23,000 lines of proof) is a
whole-project check: the orchestrator should ask Matt to allow it for the
toy lanes, or leave it to the verifier.

| # | Lane | Model | Est. | After |
|---|---|---|---|---|
| L1 | `Honest`, `ReadsAt`, `Invariant`, `ReadsIn`; restate `Reads.sw`'s 78 theorems; `honestMoved`, `readsInOf`, `readsOneEvery`, `readsAtThen`, `readsInPeek`, `Parse.peek` | Opus (the definitions fix every later proof) | 60 min | — |
| L2 | ReadsChars, ReadsOperators, ReadsTokens and `locatedToEnd` onto L1; delete `Among.sw`, `Paced.sw`; move the toy's `Fair`/`Paced` uses and aoc's call sites | Sonnet | 60 min | L1 |
| L3 | `readsThen` inference: postpone non-pattern expected-type problems, abstract `p ()`; then remove `readsThenOf`/`amongThenOf` | Opus (elaborator) | 60 min | — (parallel with L1) |
| L4 | `Parse.Gives` and its lemmas, `givesBoth`, `readsBoth` in std; the toy's three walks into one, with `readsInPeek`; report how much of each walk lemma is still mechanical (for the tactic question) | Sonnet for std, Opus for the toy walk (a large proof refactor with judgement) | 30 + 90 min | L1, L2 |
| L5 | Declines toolkit and `runsRecursiveWithFact`; the toy's declines lemmas and `runsExpressionFuel` onto them | Sonnet | 40 min | — (parallel; touches `Runs.sw` only) |
| L6 | `docs/guide/` section on proving parsers (`Reads`, `ReadsIn`, `Gives`, `Declines`), since these are std functions people will reach for | Sonnet | 20 min | L1-L5 |

L1, L3 and L5 can start at once (different files: `Reads.sw`, the
elaborator, `Runs.sw`). L2 and L4 clash with each other in the toy and run
one after the other.

## 7. Decisions

**For Matt: one (D3625, provisional number; the orchestrator renumbers
if it is taken).**

**D3625: adopt this end state for std's parser proofs?**
*The problem:* the toy rebuilt parts of the parser-proof library three
times (`Paced`, `ReadsAmong`, three walks), and a real formatter would
rebuild them at three and a half times the size.
*The change:* one `Reads` with an invariant and honest offsets, `Gives`
with joint walks and a `peek` lemma, a declines toolkit, and `readsThen`
inference in the elaborator (lanes L1-L6).
*What it should do:* 37 std theorems and about 85 of the toy's go
[estimated]; the formatter's walk is about 250 theorems instead of 700;
every proved parser, aoc's included, gets offsets and token facts
without a second property. **[rec: yes]**

**Decided here (the orchestrator's to overrule):**

1. The offset goes into honesty (`Parse.Honest total`), not into `Reads`'
   conclusion, so combinators don't change (§1.1).
2. The invariant is of the list left, with `kept`, not of each item (§1.1).
3. `Parse.Reads` keeps its name as the `any` case; one set of lemmas over
   `ReadsIn [inv]` (§1.2).
4. `Runs` is unchanged (§1.4).
5. The walk is one lemma per parser function with a joined property; no
   parser-as-data (§2.2).
6. `Declines` keeps its definition; the toolkit is lemmas (§3).
7. `readsThen` is fixed in the elaborator, not by more `…Of` lemmas (§4).

**Later, not now:** a `gives` tactic that derives walk lemmas (§2.2),
asked of Matt with L4's measurement of what is left by hand.

## Sources

- `crates/elab/src/std/Parse/Reads.sw:45` (`Reads`), `:322-489`
  (primitives), `:535` (`readsThen`); `Among.sw:20,35,57-78,90`;
  `Paced.sw:13,24,69,148,277`; `Runs.sw:38,52,526,540,1060,1180`;
  `ReadsOperators.sw:11-43`; `Parse.sw:117` (`advance`), `:697-715`
  (`recursiveWith`).
- `tools/toyfmt/src/Toy/Syntax/ShapeProofs.sw:16-96, 250-311`;
  `Fmt/ParsedProofs.sw:32`; `Fmt/HeadProofs.sw`; `Syntax/Parser.sw:59,
  201-230`; `Syntax/ExpressionProofs.sw:1417, 2177-2311`;
  `Fmt/LexTextProofs.sw:15-90`.
- `tools/toyfmt/NOTES.md` frictions 4 and 5 (line 691), 19 (1100), 42
  (1721), 44 (1733), 52 (1875), 77 (2659), 80 (2672).
- [after-the-toy-proof.md](after-the-toy-proof.md) §2.1, §4.5-4.7;
  [postponement.md](postponement.md) stages 6 and 7.
