# Slice 1 consolidation: un-numbered predicates and the shape walk (SW-4210)

Fable, paper lane, 19 Nov 2026, for D3692 (Matt). Read against `main` at
6aedb33b7. Nothing was built or checked; the counts are text counts over
`tools/fmt/src/Fmt/*.sw` and `tools/fmt/src/Syntax/*.sw` (5,556 lines
starting `theorem` [measured]; the retrospective's 6,232 was over all of
`tools/fmt/src` at an earlier commit, and I did not reconcile the two).

How claims are marked: **[measured]** counted today; **[read]** taken from
the file named; **[estimated]** my judgement; **[heuristic]** a count by
name or shape that over- or under-counts.

## In plain words

Two consolidations were asked for. One holds up, smaller than billed. The
other rests on a number of mine that was wrong.

**C7, the uniform shape walk: the premise is wrong, and I withdraw it.**
The retrospective (SW-4205) said the shape walk costs 16 theorems per
parser function against 1.6 for the two-run walk, and blamed the form of
the statements. That 16 divided all 951 parser-walk theorems by the 58
functions slice 1 reaches. But those theorems walk about 500 functions,
not 58: the shape walk already covers nearly the whole parser, most of it
with the spec "this builds a tree outside the slice". Counted per function
walked, the three walks cost the same [measured]:

| Walk | Theorems | Distinct functions named in a statement | Per function |
|---|---|---|---|
| Shape (`ParseWalk`, `ParseWalkOthers`, `ParseProofs`) | 665 | 504 | 1.3 |
| Tokens kept (`ParseKept`, `ParseCarries*`) | 261 | 142 | 1.8 |
| Two-run (`Follows*`, without `DeafProofs`) | 854 | 524 | 1.6 |

And the shape walk is already in the uniform form: 414 of `ParseWalk.sw`'s
548 theorems state `Parse.Gives GoodItems (() => f …) spec`, one per
function, built from the combinator lemmas in std
(`crates/elab/src/std/Parse/Gives.sw`) [measured, read]. There is nothing
to convert. What is left is a small tidy (section 2), worth about ten
theorems.

This also changes two estimates that used the 16:

- the retrospective's idea A ("4,000 to 8,000 parser-walk theorems for
  slices 2 to 6, against 1,000 to 2,000 in the uniform form") has no
  saving left in it. On the present form the remaining parser walks are
  about **2,100 to 2,500 theorems** [estimated: about 500 functions at 1.75
  for shape and 1.84 for tokens, plus 0.65 a function of spec helpers, the
  in-slice rates measured below];
- slice 2's sketch has the parser walk at 500 to 800 theorems "at 16 a
  function" for 65 functions. At the measured in-slice rates it is about
  **250 to 350** [estimated].

So the parser side of the rest of the formatter is cheaper than the
retrospective said, and no restructuring is needed to get there.

**C5, un-numbering the predicates: do it, but it frees fewer theorems than
the retrospective implied.** 1,052 theorems name a numbered definition
[measured; the retrospective's 1,392 also caught local variables such as
`v1`]. They split three ways:

| Theorems that name | Count | If slice 2 happens |
|---|---|---|
| only tree properties (`shaped1`, `lexical1`, `kinds1`, …) | 177 | stand as they are, once the properties are un-numbered |
| a property and the slice's gate (`within1`, `grammar1`, …) | 308 | the property half stands; the gate must be switched |
| only the gate | 567 | the gate must be switched |

So the rename itself saves 177 restatements a slice. The other 875 depend
on how the gate is switched, which is a slice 2 design question; section
1.4 gives the rule that keeps it to a mechanical step. The rename is
cheap (one Sonnet lane), changes no statement's meaning, and touches no
top statement.

**Slice 1 alone gains little from either.** After both, slice 1 has about
ten fewer theorems, clearer names, and the slice named in a handful of
definitions instead of scattered. Nearly all the value is for slice 2
onwards. If slice 2 is not going to happen, only lane 1 (names) and the
file split already planned are worth doing.

**For Matt:** no top statement changes, no narrowing, no new hypothesis
(D3688). Nothing here needs a decision of his, except to know that the
retrospective's headline comparison was wrong (section 4).

## 1. C5: un-numbered tree predicates

### 1.1 Three kinds of numbered name

There are 130 numbered definitions (`def` or `type` ending in `1`)
[measured]. They are not all the same kind of thing:

| Kind | What it is | Where | Rule |
|---|---|---|---|
| **Scope** | the slice itself: the grammar, the driver and its tree test, the token alphabet, the driver's printing entry | `Grammar1.sw` (9), `Driver1.sw` (10), `Slice1.sw` (26), `Formats1` and `Printed1` in `TopStatements.sw`, `alphabet1`, `plain1`, `sourcePlain1` in `Syntax/SettleProofs.sw`, `Expr.numeral1` in `Spacing.sw` (program code) | **numbered, frozen.** A slice is a new set of these; they are never edited to make a proof go through |
| **Token tables** | facts about token kinds of the alphabet: `Tok.symbolic1`, `fixedKind1`, `Token.fixed1`, `spelledPlain1`, `movable1`, `home1`, `walk1`, `Lexed.laid1`, `Lexed.wordsSettled1` | `Syntax/LexProofs.sw`, `GoodItemProofs.sw`, `SettleBareProofs.sw`, `ParseSettledStatements.sw` | **left numbered here.** They grow by token kind, not by tree form; the lexer and rule N lanes of a later slice own them |
| **Properties and functions of the tree** | what the proofs say of a tree: `shaped1`, `lexical1`, `settled1`, `unreturned1`, `operators1`, `autoPlaced1`, `homed1`, `quiet1`, `stands1`, and the functions the statements are written with: `kinds1`, `spacing1`, `slots1`, `shapes1`, `leaves1`, `mapIn1`, … | the 18 files of the table in 1.3: 77 names, used on 1,772 lines in 64 files [measured] | **un-numbered: one definition each, for every slice** |

`Parsed1` (`Syntax/ParseProofs.sw`) is a spec that names the gate; section
2 deals with it.

### 1.2 The definitions

Each property keeps today's text with the `1` dropped. Two examples in
full, since the form matters:

```
--| The tree is one the parser can give: a call's head is an atom, a bracket or a negative numeral, and its arguments
--| atoms, brackets or signs on them; operands of an infix sit at their ladder levels, the right operand of a chain
--| that nests to the left one level up; a tuple has two items or more.
--|
--| One definition for every slice. A form has an arm once some slice's proofs cover it; until then it is not shaped
--| (the last arm), so a shaped tree is made only of covered forms.
def Expr.shaped: Expr → Bool
  | Atom kind _ => kind.wordWithin1
  | Paren _ inner _ => inner.shaped
  | Tuple _ items _ _ => items.length >= 2 && allShaped items
  | ListOf _ items _ _ => allShaped items
  | App head arguments =>
    head.callHead && head.shaped && !arguments.isEmpty && arguments.all Expr.callArgument && allShaped arguments
  | Infix kind left operator right =>
    left.shaped
      && right.shaped
      && leftNeeds kind operator.text <= left.level
      && rightNeeds kind operator.text <= right.level
  | Prefix _ operand => operand.shaped && 18 <= operand.level
  | _ => False

def allShaped: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.shaped && allShaped rest

def Expr.unreturned: Expr → Bool
  | Atom _ word => word.unreturned
  | Paren open inner close => open.unreturned && inner.unreturned && close.unreturned
  | Tuple open items _ close => open.unreturned && allUnreturned items && close.unreturned
  | ListOf open items _ close => open.unreturned && allUnreturned items && close.unreturned
  | App head arguments => head.unreturned && allUnreturned arguments
  | Infix _ left operator right => left.unreturned && operator.unreturned && right.unreturned
  | Prefix operator operand => operator.unreturned && operand.unreturned
  | _ => False
```

`Expr.lexical`, `Decl.settled`, `Decl.shaped`, `Decl.lexical`,
`SourceFile.shaped` and the rest follow the same way: the body is
today's, with each name of the table below un-numbered.

**The last arm stays `False`.** Two reasons. It is today's text, so the
change is a rename and no proof changes. And in the end state (the whole
language, no gate left) a statement reads "for every shaped, lexical tree"
with no slice in it; `False` for an uncovered form is what lets `shaped`
carry that on its own. I considered `True` ("says nothing yet"), which
would let the parser's lemma drop its `within1 →` guard; it fails, because
`shaped (App head arguments)` asks every argument to be an atom or a
bracket, and the whole language has arguments (`f { x }`, records) that
slice 1's `callArgument` does not know. Writing the whole language's
`callArgument` now is slice 2 to 6's work.

How a later slice grows one (an illustration, not slice 2's design):

```
  | Binding BindsLambda None params arrow body => paramsShaped params && body.shaped
```

Nothing proved in slice 1 about `App` mentions this arm.

### 1.3 The renames

Drop the `1` from every `def` and `type` in these files [measured list],
with the exceptions below. Theorem names are **not** changed: a theorem
called `printedHangs1` takes `within1` and is rightly slice 1's, and eight
of the 107 numbered theorem names would collide (`printedHangs`,
`groupKeepsTokens`, `spellsText`, …) [measured].

| File | Names |
|---|---|
| `Fmt/Predicates1.sw` → `Fmt/Predicates.sw` | `Decl.lexical1`, `Decl.settled1`, `Decl.shaped1`, `Expr.argument1`, `Expr.atomic1`, `Expr.head1`, `Expr.lexical1`, `Expr.numberAtom1`, `Expr.shaped1`, `SourceFile.lexical1`, `SourceFile.settled1`, `SourceFile.shaped1`, `allLexical1`, `allShaped1` |
| `Fmt/Kinds1.sw` → `Fmt/Kinds.sw` | `Expr.kinds1`, `argsKinds1`, `binaryKind1`, `itemsKinds1`, `prefixKind1`, `restKinds1` |
| `Fmt/StandsProofs.sw`, `Fmt/SettleOutputProofs.sw` | `Expr.unreturned1`, `allUnreturned1`, `Decl.unreturned1`, `SourceFile.unreturned1`, `SourceFile.words1` |
| `Fmt/TreeJoinProofs.sw` | `Expr.operators1`, `AllOperators1`, `Decl.operators1` |
| `Syntax/AutoPlaced.sw` | `Expr.autoCall1`, `Expr.autoPlaced1`, `Decl.autoPlaced1`, `SourceFile.autoPlaced1`, `autoLead1` (`arrowKind1` keeps its `1`: `arrowKind` is taken) |
| `Fmt/ElementsHomed.sw`, `Fmt/ExprHangProofs.sw`, `Fmt/OneLineStatements.sw` | `Expr.homed1`, `allHomed1`, `Decl.homed1`, `Word.quiet1`, `Expr.quiet1`, `allQuiet1`, `Word.lead1`, `Expr.leadQuiet1`, `Word.edge1`, `Expr.edgeQuiet1`, `lastEdgeQuiet1`, `Decl.edgeQuiet1` |
| `Fmt/OutputStatements.sw`, `Fmt/TriviaStatements.sw`, `Fmt/FileLexProofs.sw` | `Decl.laid1`, `Decl.leaves1`, `Decl.spacing1`, `Expr.spacing1`, `SourceFile.hung1`, `SourceFile.lexed1`, `argumentsSpacing1`, `commaSpacing1`, `Decl.stands1`, `SourceFile.stood1`, `Decl.pieces1` |
| `Fmt/PassProofs.sw` | `Expr.mapIn1`, `Decl.mapIn1`, `mapAll1`, `Fixes1` |
| `Fmt/SourcePlainProofs.sw` | `Shape1` and its 17 companions (`Tok.shape1`, `Expr.shapes1`, `shapeStep1`, `Seg1`, `After1`, `Opened1`, `GroupShapes1`, …) |
| `Fmt/SpeltSlots.sw`, `Fmt/SplitProofs.sw` | `Expr.firstKind1`, `Expr.slots1`, `argumentSlots1`, `commaSlots1`, `infixText1`, `Expr.codeTexts1`, `Word.clean1`, `argumentTexts1`, `commaTexts1` |
| `Syntax/ReadBackLine.sw` | `Expr.nest1`, `Expr.prefix1`, `Expr.signArg1`, `Expr.signed1`, `Expr.unary1` |

Exceptions, where the plain name is taken or reads badly [measured
collisions: `Expr.atomic` in `Fmt/Meaning.sw`, `Shape` in
`Syntax/SettleProofs.sw`, `arrowKind`]:

- `Expr.atomic1` → `Expr.primary` (an atom or a bracket);
- `Expr.head1` → `Expr.callHead`, `Expr.argument1` → `Expr.callArgument`
  (so `head.head1` does not become `head.head`);
- `Shape1` → `PlainShape` (it classifies tokens for `sourcePlain`);
- any other name the checker reports as taken or ambiguous keeps its `1`,
  listed on the ticket.

What does not change: `Grammar1.sw`, `Driver1.sw`, `Slice1.sw`,
`Accepts1.sw`'s statement, `Fmt/Tests/MustAccept1.sw`, and every name of
the Scope and Token-table kinds.

### 1.4 The rules that make slice 1's lemmas stand

These go in `Predicates.sw`'s header and `tools/fmt/NOTES.md`. They are
what "the slice enters only through a hypothesis" means in practice.

1. **A slice is its Scope definitions and nothing else.** A property never
   names a slice. (One exception stays for now: `shaped`'s atom arm reads
   `kind.wordWithin1`, as today; slice 2's statements lane moves that test
   to where it belongs.)
2. **A lemma that splits on the tree's forms and needs "there is no other
   form" takes the gate (`within1`) and closes the other arms with the
   gate, not with a property's last arm.** Then filling a property's arm
   cannot break it. 105 theorems take `within1` and split on expression
   forms [measured, heuristic]; they are the ones a later slice re-ties.
3. **A lemma about one form takes facts about that node and its children
   and no gate.** `appParsed` (`ParseWalk.sw`) is the pattern: a head and
   arguments each with their fact give the call its fact. Such a lemma
   stands in every slice. New forms' proof content is written this way.
4. **A lemma with no gate that splits on a property** (41 of the 177
   [measured, heuristic]; `argLevel`, `atomicArgument`) gains an arm when
   that property gains one, with its statement and callers unchanged.
   That is the right size of per-slice work, and it is how a property is
   grown without leaving `main` unproved: one property's arm and its
   handful of ungated lemmas in one lane.

### 1.5 What each lemma family becomes

| Family | Now | After |
|---|---|---|
| The four top statements | name `formatWithin1`, `inGrammar1`, `parse1`, `tidy1`, `calmTop`, `meaning`, `lex`, `parseFile` [read: `TopStatements.sw:380`, `:410`, `:484`, `Accepts1.sw:26`] | **word for word.** None names a property |
| Statements that name a property (485 theorems) | `decl.shaped1 = True` | the same statement with `decl.shaped`; the proposition is unchanged, since the definition's body is |
| Proofs | `rewrite …`, `byComputing` over the numbered names | the same text with the names changed |
| `Parsed1`, `ArgParsed`, `AtomParsed`, `HeadParsed` | four definitions each spelling `within1 → shaped1 ∧ lexical1 ∧ …` | section 2 |
| Deleted | | none |

### 1.6 If slice 2 happens: the gate

Not part of the consolidation, but it decides what C5 is worth, so the
finding is recorded here for slice 2's statements lane.

- 875 theorems name the gate. The sketch plans `within2` beside
  `within1` and the layers "re-proved for the new names". With the
  properties un-numbered, the cheapest honest route I can see is a
  **switch per layer**: new forms get gate-free lemmas (rule 3) while
  slice 1 stays proved; then one lane per layer renames the gate in that
  layer's proofs and adds one arm per new form to each of its re-tying
  lemmas (rule 2), each arm a call of a rule 3 lemma. `slice1Formats`
  stays word for word and is re-derived through the sketch's
  `grammar1In2` and `sameOnSlice1`.
- That only works if **`within2`'s arms for slice 1's forms have the shape
  of `within1`'s**, so that the old arms' proof text still checks. Today
  they do not: `Expr.within2`'s atom arm is `kind.wordWithin2` with no
  spelling test, and its infix arms have no operator test
  [read: `Fmt/Slice2.sw:34`]. Slice 2's lane B2 should either keep
  `within1`'s tests in those arms or say where the spelling facts now come
  from. This is the one finding here that changes slice 2's sketch.
- I looked at three other gate designs and do not recommend them: one
  growing `within` with no number (every lemma that splits on forms breaks
  at once when it grows, so `main` is unproved for the length of a slice);
  a gate with the slice as an argument (`expr.within Slice2`: the same
  break arrives one slice later, when a third slice adds an arm); and
  lemmas generic in any gate closed under sub-trees (the re-tying lemmas
  need "no other form", which no generic gate gives).
- A growth test would price the switch before slice 2 commits to it: on a
  scratch branch, add one arm to `shaped`, `lexical`, `unreturned` and
  `operators` and count the slice 1 theorems that stop checking. Rule 2
  predicts only rule 4's lemmas do (41 or fewer).

## 2. C7: the shape walk

### 2.1 What is there [measured, read]

`Syntax/ParseWalk.sw`, 7,141 lines and 548 theorems, by its own section
comments:

| Part | Lines | Theorems | Distinct functions | What the specs say |
|---|---|---|---|---|
| Slice 1's path: atoms, brackets, lists, calls, the ladder, `expr_inline`, statements, the recursion | 1 to 2,751 | 199 (129 about a function, 70 about the specs) | 108 | `Parsed1 floor`, `ArgParsed`, `AtomParsed`, `HeadParsed`, `AtomFrom open`, `ConjunctionOk`, … |
| The parsers outside slice 1: patterns, binders, lambdas, `match`, handlers, `let`, `calc`, `rewrite` | 2,752 to 6,333 | 287 | 286 | `Out` (77): the tree is outside the grammar; `value => True` (about 190): the function reads forward and returns |
| The `def` frame, declarations, a file | 6,334 to 7,141 | 62 | 47 | `DeclOk`, `DeclOut`, `PartsOk`, `NameOk`, `BodyOk` |

Statement forms in the file: 414 `Parse.Gives GoodItems`, 31 `Reads0` (a
look-ahead reads nothing), 19 `Parse.ReadsAt`, 2 `Parse.ReadsIn`.

So:

- **the form is already uniform**: one `Parse.Gives` lemma per function,
  proved as a chain of `Parse.givesThen` and `Parse.givesDone`, as
  `Parse/Gives.sw`'s header describes;
- **the spec per function is not an accident of style.** What `additive`
  returns sits at level 14 and what `atom` returns is a bracket or a name;
  an infix's shape needs exactly those facts of its operands. A single
  spec for all functions would have to be the weakest of them, and the
  callers' proofs would fail. The two-run walk can use one relation per
  result type because "alike up to comments" does not depend on which
  function read the tree;
- **the 190 `value => True` lemmas cannot be had from a general
  theorem.** "Every parser reads forward" is false of a parser that resets
  to a mark it made up [read: `Parse/Reads.sw`, header], so each function
  needs its line. They hold in every slice as they are;
- **the 77 `Out` lemmas are slice 1's**, but each is the function's walk
  with `Parse.givesDone byComputing` at the leaf [read: `givesSemiAfter`,
  `givesSemi`, `givesAnnotatedEnd`]. For a function still outside a later
  slice the same text checks against the later grammar; for one that moves
  in, the lemma is replaced by one with a real spec, which is that slice's
  new work in any form.

### 2.2 The tidy that is worth doing

The four in-slice specs repeat one guard. Make it one definition, so the
shape walk names the slice in one place and has one set of helper lemmas:

```
--| What a parser function gives of a tree of the slice: it is shaped and lexical, and `holds` of it. A tree outside
--| the slice says nothing, so the forms of later slices need no case.
def InSlice (holds: Expr → Prop) (expr: Expr): Prop :=
  expr.within1 = True → expr.shaped = True ∧ expr.lexical = True ∧ holds expr

--| At least at the level `floor` of the precedence ladder.
def Parsed (floor: Nat): Expr → Prop := InSlice (expr => floor <= expr.level)

--| An atom or a bracket, or a sign on one.
def ArgParsed: Expr → Prop := InSlice (expr => expr.callArgument = True)

--| An atom or a bracket.
def AtomParsed: Expr → Prop := InSlice (expr => expr.primary = True)

--| A call's head.
def HeadParsed: Expr → Prop := InSlice (expr => expr.callHead = True)

theorem inSliceOut ∀ (holds: Expr → Prop) [expr: Expr] (out: Out expr): InSlice holds expr

theorem inSliceWeaken ∀ [holds weaker: Expr → Prop] [expr: Expr]
    (found: InSlice holds expr)
    (implies: holds expr → weaker expr):
    InSlice weaker expr

theorem givesOutIn ∀ [p: () → {Parse Item} Expr] (holds: Expr → Prop)
    (gives: Parse.Gives GoodItems p Out):
    Parse.Gives GoodItems p (InSlice holds)
```

Each of the four specs unfolds to the proposition it is today, so every
lemma stated with them keeps its meaning and, I expect, its proof text
[estimated: the proofs take the spec apart as `parsed within`, which
unfolding gives; if the checker does not see through the two definitions,
keep the four bodies as they are and add only the three lemmas].

What it replaces: `outParsed`, `outArg`, `outAtom`, `outHead` become
`inSliceOut`; `givesOut`, `givesOutArg` become `givesOutIn`; `atomArg`,
`atomHead`, `headParsedParsed`, `parsedWeaken` become one line each over
`inSliceWeaken`. About ten theorems fewer.

After it, the slice enters the two gated walks through a short, written
list: `InSlice` and `GoodItem` (`within1`), `Out` and `DeclOut`
(`grammar1`), `KeptTree` (`grammar1` and `within1`), `DeclOk`.

The uniform statement for a function on the slice's path, which 45 lemmas already have [measured: the statements ending in
`Parsed1 floor` or `ArgParsed`], is then:

```
theorem givesF ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) …
    (nested: Nested self)
    (outside: Outside self):
    Parse.Gives GoodItems (() => f self modes …) (InSlice holds)
```

with `holds` the function's own fact, and for a function off the path
`Parse.Gives GoodItems (() => f …) Out` or `(value => True)`, as now.

### 2.3 What I do not recommend

- **Restating the 665 shape-walk theorems.** They are in the form already.
- **Merging the shape walk and the tokens-kept walk into one walk with a
  joint spec.** It would save about one lemma per function on the path
  (100 to 150 theorems) and rewrite about 460 proofs to do it; std's
  `Parse.readsBoth` already joins the two results where both are wanted.
  A later slice may state a new function's two facts in one lemma if it
  reads better; nothing needs converting for that.
- **Replacing `Out` by a slice-free "this function builds form X".** The
  `Out` proofs are one `byComputing` each and re-check against a later
  grammar as they stand.

### 2.4 Splitting `ParseWalk.sw`

Already item 6 of the retrospective's list; the table in 2.1 gives the
cut: the slice's path (2,751 lines), the outside parsers by section
(expression forms; patterns; binders and lambdas; `match` and handlers;
`let`, `calc`, `rewrite`), and the frame. It matters more after this
note: a later slice's parser work is moving lemmas from the outside files
to the path, and the file a lane must check shrinks from 7,141 lines to
under 1,500.

## 3. Lanes

Estimates are agent time. Proof work is counted at slice 1's 87 theorems
an hour; renames are not proof work and are sized from the line counts.
Each lane leaves `main` proved: every one is a rename or a restating that
unfolds to the same proposition.

| # | Lane | Model | Est. | Worth it without slice 2? |
|---|---|---|---|---|
| 1 | **Un-number the properties** (1.3): 77 names on 1,772 lines in 64 files, two files renamed, the header and `NOTES.md` rules of 1.4. A script with word boundaries, then the formatter | Sonnet | 45 min | yes, mildly: names |
| 2 | **`InSlice`** (2.2): the definition, three lemmas, the four specs restated, ten helper theorems folded. `Parsed1` → `Parsed`. After lane 1, in the same files | Sonnet | 45 min | marginal |
| 3 | **Split `ParseWalk.sw`** (2.4), the retrospective's item 6 | Sonnet | 60 min | yes: the check loop |
| 4 | **Correct the two estimates** that used 16 a function: the retrospective's section 4 row A and section 7 step 3, and slice 2's sketch §4 and §5.1 | orchestrator, or Sonnet 20 min | — | yes: they are wrong as they stand |
| 5 | *Only if slice 2 goes ahead:* the growth test of 1.6, on a scratch branch that is not merged | Opus | 60 min | no |
| 6 | *Only if slice 2 goes ahead:* slice 2's sketch revised for 1.6: the switch per layer, and `within2`'s arms | Fable, paper | 30 min | no |

Order: 1, then 2 and 3 (3 conflicts with 2 in `ParseWalk.sw`: run 2
first, or give 3 the split and 2 the path file after it). Lane 4 any
time.

**Checking.** Lane 1 touches 64 files, so no check of "the namespace I
edited" covers it, and a lane may not run the whole `tools/fmt` check
(396 s [read: SW-4195]). The check after merging is the whole project's,
by the verifier or Overmind; the orchestrator should arrange that before
the lane starts, as the test budget asks. Lanes 2 and 3 can be checked by
the files they touch plus their direct users.

Model choice (D3682): these are renames and restatings that keep each
statement's meaning, so Sonnet, with the orchestrator checking the
restated specs statement by statement (D2436). Nothing here weakens a
statement, so no Opus review is called for.

## 4. Counts, before and after

| | Before | After lanes 1 to 3 |
|---|---|---|
| Theorems, `Fmt` and `Syntax` | 5,556 [measured] | about 5,546 [estimated] |
| Numbered definitions | 130 [measured] | about 55: the Scope and Token-table kinds |
| Places the shape walk names the slice | 22 lines of `ParseWalk.sw` name `within1` or `grammar1`, and 99 of its theorems a numbered definition [measured] | six definitions |
| Largest proof file | 7,141 lines | under 3,600 (`ParseWalk`'s outside part, less if cut by section) |

Savings if later slices happen [estimated]:

- 177 theorems a slice not restated, and 308 more touched only by the
  gate switch;
- no `shaped2`, `settled2`, `lexical2`, `unreturned2` (slice 2's lane B5
  becomes "add arms");
- nothing from C7 beyond the ten theorems: the saving the retrospective
  claimed was never there, and the parser walk's remaining cost is lower
  than it said for the same reason.

**The correction, stated once more because Matt read the original.** The
retrospective's "one measurement the checkpoint did not draw out" (1.6
theorems a function against 16) compared a whole-language walk with a
whole-language walk and divided the second by the wrong number. Its
conclusion "the difference is the form" does not follow. What survives of
its section 4: idea I (do parser-side layers once for the whole language)
is already largely true of the shape walk's `value => True` lemmas; ideas
B, D and E do not depend on the number. Its totals for slices 2 to 7 lean
lower by the parser-walk difference, roughly 2,000 to 5,000 theorems at
the top of the range [estimated].

## 5. Risks

- **Name clashes in lane 1.** Proofs bind locals called `shaped`,
  `lexical`, `settled`; a method call `expr.shaped` cannot clash with
  them, but a bare function such as `mapAll` or `shapeStep` might meet a
  std name or a local. The fallback (keep the `1`, list it) bounds the
  cost.
- **The numbers here are text counts.** "Distinct functions" is the name
  after `(() =>` within eight lines of a `theorem` line; I expect it right
  to about 5%. "Splits on expression forms" is a line starting `| App`,
  `| Infix`, `| Prefix`, `| Tuple`, `| ListOf` or `| Paren`.
- **`InSlice` may not unfold where a proof needs it.** Then lane 2 adds
  the lemmas and leaves the four bodies; the saving falls to four or five
  theorems.
- **Rule 2 is a claim about 105 proofs I did not read one by one.** The
  growth test (lane 5) is the check, and it is only needed if slice 2
  goes ahead.
- **I did not run anything.** Whether a renamed tree still checks is for
  the whole-project check after lane 1.

## What this lane did not do

- No build or check, not even of one file.
- It did not design slice 2's gate switch; 1.6 records what was found on
  the way.
- It did not look at the Token-table names or the lexer and rule N
  layers, which have their own numbered names (53 with the Scope kind).
- It did not reconcile 5,556 with the retrospective's 6,232.
- It did not edit the retrospective or slice 2's sketch (lane 4).

## Sources

`docs/reviews/SW-4205-slice1-retrospective.md` (branch `lane/SW-4205`),
§1, §4, §5; `docs/proposals/self-hosted-fmt-s2-sketch.md` §3, §4, §5.1;
`tools/fmt/src/Fmt/Predicates1.sw`, `Slice1.sw`, `Slice2.sw`,
`Grammar1.sw`, `TopStatements.sw`, `Accepts1.sw`, `PassProofs.sw`,
`StandsProofs.sw`, `TreeJoinProofs.sw`; `tools/fmt/src/Syntax/ParseWalk.sw`
(lines 1 to 420, 2,752 to 2,800, 3,594 to 3,640, 6,265 to 6,425, 7,004 to
7,141), `ParseProofs.sw`, `ParseKept.sw` (to line 100), `FollowsBase.sw`
(header); `crates/elab/src/std/Parse/Gives.sw`, `Reads.sw` (to line 162),
`Follows.sw` (to line 110). The counting scripts are in the lane's scratch
folder and are not kept.
