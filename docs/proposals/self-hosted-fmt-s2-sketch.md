# Slice 2 of the proved formatter (binders): the sketch (SW-4196)

Fable, 19 November 2026. Paper, with small runs of the release binary.
Step 2 of [the proof plan](self-hosted-fmt-proof-plan.md) §1.3 for slice
2, in the shape of [slice 1's sketch](self-hosted-fmt-s1-sketch.md).

How claims are marked: **[source]** read in the code today, place given;
**[run]** `stitchwort dev tree --print` or `stitchwort fmt -` (the Rust
formatter) on the input shown, in my scratch folder; **[measured]** a
count by `grep` today; **[reported]** from `tools/fmt/NOTES.md` or a
review; **[inferred]** my reasoning, not run; **[estimated]** my estimate.

**Not done, and it matters:** the self-hosted formatter was not run (its
project is 70,000 lines of proofs, and a lane may not check a whole
project), and no statement here was checked or searched. Slice 1's sketch
ran 9,900 generated files before its proof lanes; slice 2's equivalent is
lane 3 of §6 and should not be skipped.

## In plain words

**The problem.** Slice 1 is proved for definitions with no parameters.
Slice 2 adds parameters: `def` and `theorem` headers with groups, lambdas,
`∀`, `∃` and ability rows. A program for it exists (SW-3959), but it was
built to a narrower set of forms than the plan's row names, nobody has
written down the grammar the theorem must cover, and three of the four
tidy passes run for the first time.

**The change.** This note pins the grammar down (§1), lists what is built
and what is not (§2), gives the top statement (§3), says which of slice
1's 6,232 theorems carry over and which are redone (§4), predicts the
count by layer (§5) and orders the lanes (§6).

**What it should do.** The lanes start from a fixed grammar and a known
list of gaps, not from the program's own idea of the slice.

**Found:**

- **The grammar is undecided in seven places** (§1.2), and the program's
  slice leaves out all seven: a row after `→`, a `fun` lambda, an empty
  row, `auto` groups, defaults, `()`, and dependent function types.
  That is the one decision for Matt (§7).
- **The Rust formatter is not idempotent on three slice 2 inputs** [run],
  all one bug: a bracket dropped after a row uncovers a binder the same
  pass has already walked past (§2.3). The self-hosted pass does its two
  steps in the other order and should not have it [inferred].
- **`meaning` is no longer a risk for this slice.** The four passes keep
  it, proved for the whole language with no axioms (`tidyKeepsMeaning`,
  `Fmt/MergeProofs.sw`) [reported]. The plan had it as S2's work.
- **Most of the two-run framework is whole-language already** (1,006
  theorems with no slice hypothesis) [measured], so "rule N keeps the
  parse" costs slice 2 a closing lemma, not a walk.
- **The count: 2,400 to 3,900 new theorems** [estimated], against the
  plan's 500 to 800. Slice 1 came to 6,232 against 550 to 850. The plan's
  9,000-theorem question to Matt (§4 of the plan) is reached during slice
  2 on these figures; that is the checkpoint's to bring (SW-4195), not
  this note's.
  *Corrected 19 Nov (SW-4210): the count is **2,150 to 3,450** [estimated].
  The parser walk was priced at "16 a function"; the right rates are 1.3
  (shape) and 1.8 (tokens kept) per function walked, so that row is 250 to
  350, not 500 to 800 (§5.1 shows the arithmetic). Source:
  `fmt-consolidation-statements.md`, §1 and §2.*
- **`slice1Formats` doesn't say comments are kept.** `CommentsKept` is a
  definition with no theorem (`Fmt/Meaning.sw:288`) [source]. Slice 2's
  top statement inherits the gap; see §3.3.

## 1. The grammar

### 1.1 Grammar2, as recommended

A superset of Grammar1 (`Fmt/Grammar1.sw`): everything there stays, and
"nothing moves out" (D3689). As in slice 1 the definition is a test on the
tokens and tree the language's own lexer and parser read; layout and
comments are free.

```
File    ::= Decl*
Decl    ::= "def" name Group* ":" Expr ":=" Expr
          | "theorem" name [forall Group+ | Group*] ":" Expr ":=" Expr
Group   ::= "(" lower+ ":" Expr ")"            explicit
          | "[" lower+ ":" Expr "]"            implicit
          | "(" lower+ ":" Expr ":=" Expr ")"  with a default        (choice 5)
          | "[" "auto" lower ":" Expr "]"      an instance, named    (choice 4)
          | "[" "auto" Expr "]"                an instance           (choice 4)
          | "(" ")"                            the unit parameter    (choice 6)
Expr    ::= … slice 1's forms …
          | "Type" | "Prop"
          | [fun] Param+ "=>" Expr             a lambda; `fun` is choice 2
          | forall Param+ "=>" Expr
          | exists Param+ "=>" Expr
          | Row Expr                           where the language reads a row:
                                               a header's result, and the right of
                                               an arrow (choice 1)
          | Group arrow Expr                   a dependent function type (choice 7)
Param   ::= lower | "_" | Group                a lambda's group takes no default
Row     ::= "{" [Expr ("," Expr)*] "}"         no last comma; empty is choice 3
forall  ::= ∀ | forall        exists ::= ∃ | exists        fun ::= fun
```

New tokens: `theorem`, `∀`, `∃`, `=>`, `_`, `{`, `}`, `Type`, `Prop`
(the program's `Tok.within2`, `Fmt/Slice2.sw:99`), and `fun` with
choice 2. `auto`, `:=`, `(`, `[` are slice 1's.

Where the language makes a case odd, the tree decides [run, each]:

- A `∀` after a theorem's name needs a group after it (`theorem t ∀: P`
  doesn't parse), and a `def` can't have one. A theorem with no
  parameters is fine.
- `∀ (x: A) y => P` mixes groups and names; so do lambdas and `∃`.
- `(x y: A) => x` is a lambda with a group. `(x) => x`, `(x, y) => x`,
  `(_: A) => 1`, `((x, y): P) => x` and `() => 1` are patterns
  (`PatternParen`, `PatternTuple`, `PatternTyped`, `PatternAbsurd`):
  outside, with the pattern family in S4.
- `g x => x` is a lambda of two parameters, not `g` applied to one. A
  lambda as an argument needs brackets, and `a + x => x` and `-x => x`
  don't parse.
- A header's `(_: A)` doesn't parse; a lambda's is a pattern (above).
- A row is read only after a header's `:` and after an arrow. `{Fail} A`
  as a value, in a parameter's type or as a lambda's body doesn't parse.
  `A → {Fail} B → C` is `A → ({Fail} (B → C))`.
- `{e} T` is a row. `{e} -x` is the record `{e}` applied to `-x`, so the
  bare form of `{e} (-x)` is another tree; P3 keeps that bracket
  (`rowReadsAsRecord`, `Fmt/Passes.sw:190`) [source; Rust keeps it, run].
- `{Fail, IO,} T` doesn't parse: a row has no last comma, and P2 has
  nothing to do there.
- `Type 1` is a `Universe` node, outside; `Type` and `Prop` alone are
  atoms.
- A lambda's body on the line below its `=>` reads as the same lambda,
  not as a block [run: `x =>⏎  g x`, and the printed forms of four long
  inputs: no `Block` in any].

Outside, each with the slice it belongs to: a row variable (`{IO | e}`:
its `|` is rule N's bar clause, S3, as spike K1 assigned it); patterns as
parameters (S4); `Type 1` (S4); `instance`, `export`, `opaque`,
attributes, `decreasing`, `unfolding`, definitions by arms or with no
body (S5).

**`PatternWord` leaves the plan's row.** The parser never builds
`PatternParam (PatternWord …)` for a lambda's parameter: a name or `_`
there is a `NameParam` [reported, NOTES "Slice 2, the program"; run:
`∀ _ => P`]. The arm in `paramsWithin2` is dead and should go, so the
grammar doesn't list a form no source has.

### 1.2 The seven choices

Each is a form the parser reads as one of the plan's S2 constructs (or,
for 7, as a binder the plan assigns to no slice), which the program's
`within2` leaves out [source: `Fmt/Slice2.sw`]. By D3687 the target is
the whole of a slice's grammar, and what the grammar is belongs to Matt.

| # | Form | Example | `within2` today | In Grammar2? [rec] | What it costs |
|---|---|---|---|---|---|
| 1 | A row after `→` | `(f: A → {Fail} B)` | out: `Expr.within2` has no `Effect` arm; a row is allowed only as a header's whole result | **in** | the rule exists (`Expr.el`, `Rules.sw:363`); the walk and read-back meet `effectResult` at one more call site |
| 2 | `fun` | `fun x => x` | out: only `Binding BindsLambda None` | **in** | one token; the lambda rule ignores the keyword today (`Rules.sw:356`), so a rule fix and its lemmas |
| 3 | An empty row | `{} T` | out: `!abilities.isEmpty` | **in** | one arm in `effectDoc`; P3 already treats it (`rowReadsAsRecord` is true of it) |
| 4 | `auto` groups | `[auto Ord a]`, `[auto h: P]` | out: `auto = None` | **in** | `namelessAutoAt` and `headerGroupAuto` on the walk; slice 1 already paid for `auto` as a name (SW-4128, SW-4175) |
| 5 | A default | `(x: A := v)` | out: `default = None` | **in** | header groups only (a lambda's doesn't parse [run]); one more part in the group rule |
| 6 | The unit parameter | `def f (): T` | out: `!names.isEmpty` | **in** | one arm |
| 7 | A dependent function type | `(x: A) → B`, `[a: Type] → B` | out: no `FunctionType` arm, and no rule for it in `Rules.sw` [source: grep] | **in** | a rule to build; `piHere`, `piBinder`, `piExpr` on the walk; P3 and `meaning` already treat it (`spineBinders`, `plainExpr`) |

Why all seven in: 1 to 6 are the plan's own constructs ("effect rows",
"`Lambda`", "parameter groups") in a spelling or position the program
skipped, so leaving them out is the kind of narrowing D3688 stops. 7 is
an addition to the plan's row. It is the same `Group` in a third place,
P3 and `meaning` handle it today, and no later slice names it, so it
would otherwise arrive unannounced in S5's "2b complete".

Decided here as detail (say if you disagree): `Type` and `Prop` as words
(the program's choice; most groups need them); `forall` and `exists`
kept as written, as the formatter keeps them [run]; the alphabet clause
of `inGrammar2` kept, as slice 1's.

## 2. What exists, and what must be built

### 2.1 On main

| Piece | Where | State |
|---|---|---|
| The parser for every form of §1.1 | `Syntax/DeclParser.sw` (headers, groups, rows, `piExpr`), `Syntax/Parser.sw` (`lambda`, `quantifier`, the look-aheads) | built; stage 2b [reported] |
| P1, P3, P4 on the tree | `Fmt/Passes.sw` | built; identical to Rust on the passes gate (739 hand cases, goldens, samples) [reported] |
| `meaning`, and the four passes keep it | `Fmt/Meaning.sw`, `MeaningProofs.sw`, `MergeProofs.sw`, `Walk.sw`, `BlankProofs.sw` (253 theorems) | **proved, whole language, no axioms** [reported; counted] |
| Rules for headers with groups, a theorem's `∀`, lambdas, `∀`, `∃`, rows | `Fmt/Rules.sw` (`paramsHeader`, `premisesOf`, `groupDoc`, `Param.el`, `lambdaBoth`, `quantifier`, `effectDoc`, `huggedLambda`) | built; 230 of 230 golden and 444 of 444 sampled declarations match Rust [reported] |
| `within2`, `Tok.within2`, `printed2` | `Fmt/Slice2.sw` | built, to the narrower set of §1.2 |
| Two runs of the parser on items alike but for comments give alike trees | `Syntax/Follows*.sw`, `DeafProofs.sw` (1,006 theorems) | **proved for every parser function**, lambdas, quantifiers, header groups and rows among them [source: the files' lists] |
| Rule N keeps every token | `settledOnceTokens`, no hypothesis | proved [reported, SW-4191] |

### 2.2 To build before the proofs (§1.3 step 1 of the plan)

Estimates are agent minutes, from the nearest past lanes (SW-3959 built
the slice 2 program in one Opus lane; SW-4120 wrote Grammar1 and its
must-accept file in one).

| # | What | Model | Est. |
|---|---|---|---|
| B1 | `Fmt/Grammar2.sw` (`inGrammar2`, the alphabet, closed examples inside and outside, one per bullet of §1.1) and `Fmt/Tests/MustAccept2.sw`. After Matt's answer to §7. The statement file: checked by the orchestrator line by line | Opus | 30 |
| B2 | The program widened to Grammar2: `within2` for choices 1 to 7; the `fun` keyword in the lambda rule; a rule for `FunctionType`; the empty row; `auto`, default and `()` in `groupDoc`; the dead `PatternWord` arm out. Gate: `dev/fmt-twin s2`, and a hand file with each choice against `stitchwort fmt -` | Opus | 60 |
| B3 | `Fmt/Driver2.sw`: `formatWithin2`, `parse2`, `tidy2`, `leavesWithin2`, refusal messages, as `Driver1.sw`. Today's `formatWithin` (`Slice6a.sw:291`) covers every built slice at once and is not a driver a theorem can be about | Sonnet | 30 |
| B4 | The Rust bug of §2.3, fixed in `crates/fmt` with a test on both sides (D3677) | Sonnet | 30 |
| B5 | `Fmt/Predicates2.sw`: `shaped2`, `settled2`, `lexical2`, `unreturned2`, with `Group.bare` tied to the group's comments (§4.3) | with lane 3 of §6 | — |

### 2.3 Found: the Rust P3 is not idempotent

[run, `stitchwort fmt -` twice]

```
def f: {Fail} ((x: (A)) => x) := g
  once:  def f: {Fail} (x: (A)) => x := g
  twice: def f: {Fail} (x: A) => x := g

def f: {Fail} (∀ (x: (A)) (y: A) => P) := g
  once:  def f: {Fail} ∀ (x: (A)) (y: A) => P := g
  twice: def f: {Fail} ∀ (x y: A) => P := g

def f: {Fail} (x => (y: (A)) => x) := g
  once:  def f: {Fail} x => (y: (A)) => x := g
  twice: def f: {Fail} x => (y: A) => x := g
```

P3 has two jobs: drop a bracket pair at the left end of a row's result,
and drop pairs around the type of each binder reached from the header's
type without entering brackets. Dropping the first kind puts a binder on
that path. Rust looks for binders first. The second input also shows a
merge (P4) that only the second run makes.

The self-hosted traversal applies the row step at the `Effect` node
before the declaration step walks the header (`Syntax/Traverse.sw:92`,
`:305`; `dropAfterRow` is an `expr` step, `dropDeclBinders` a `decl`
step) [source], so one run should give the second line [inferred, not
run]. The harness didn't see the difference because no sampled
declaration has the shape. B4 fixes Rust; lane 3 runs the three inputs
through the Twin first.

Smaller, same family: Rust drops the pair in `{Fail} (- 1)` and keeps it
in `{Fail} (-1)` [run]; the tree has no gap to tell them apart, and
`keepsBrackets` keeps both [source]. A harness difference, not a proof
matter. NOTES already lists `{Fail}T` and `)(`, where Rust copies the
source's gap and the rules write a space.

## 3. The predicates and the top statements

### 3.1 The definitions

- `inGrammar2` (B1): as `inGrammar1`, with `Expr.grammar2`,
  `Group.grammar2`, `Header.grammar2`, `Decl.grammar2`. No formatter
  function in it.
- `within2` (B2), the driver's tree test, and `Tok.within2`. Proved equal
  on parses: `parsedWithin2` (a `grammar2` parse is `within2`) and
  `grammarOfWithin2`, as slice 1.
- `leavesWithin2`: `alphabet2 ∧ sourcePlain` on the tokens.
  `sourcePlain1`'s two clauses are about `->` and a comma that starts its
  line (`Syntax/SettleProofs.sw:1684`) [source]; slice 2 adds no clause.
  `{` and `}` are an opener and a closer like the others, and `=>` is
  read by rule N only inside `recordBar`, which only a `|` reaches
  (`Syntax/Settle.sw:34`, `:98`) [source]. That is why the row variable
  stays out: with no `|` in the alphabet, rule N's bar clause is dead.
- `shaped2`, `settled2`, `lexical2`, `unreturned2` (B5).
- `tidy2` is `tidy1`, the four passes; all four now do something.

### 3.2 The top statement

One statement, slice 1's with the names changed:

```
theorem slice2Formats ∀ (source: Text)
    (inGrammar: inGrammar2 source = True):
    ∃ (out: Text) (lexed lexedOut: Lexed) (file fileOut: SourceFile) => formatWithin2 source = Ok out
      ∧ lex source = Ok lexed
      ∧ parseFile lexed = Ok file
      ∧ lex out = Ok lexedOut
      ∧ parseFile lexedOut = Ok fileOut
      ∧ fileOut.meaning = file.meaning
      ∧ inGrammar2 out = True
      ∧ formatWithin2 out = Ok out
```

One hypothesis. From three theorems, as in slice 1: `formatAccepts2`
(the driver refuses nothing in the grammar), `formatKeepsProgram2` and
`formatIdempotent2`, each with `formatWithin2 source = Ok out` as its
only hypothesis.

Two more, cheap, which keep slice 1 honest:

- `grammar1In2`: `inGrammar1 source = True → inGrammar2 source = True`.
- `sameOnSlice1`: `formatWithin1 source = Ok out → formatWithin2 source
  = Ok out`. Both drivers run the same passes and the same rules, so this
  is the two tree tests and the two alphabets.

### 3.3 What `meaning` must forget (D3678)

Nothing new. `Meaning.sw` already forgets exactly what P1, P3 and P4
change, where they change it [source: its doc and `plainExpr`,
`plainHeader`, `forgetLeft`, `Group.pieces`]:

| Pass | Changes | `meaning` forgets |
|---|---|---|
| P1 | writes `∀` after a theorem's name | `forallKeyword` on every header (the lowering skips it) |
| P3 | drops a pair at the left end of a row's result | the same pairs, but at an application's head only round a form that never lowers to an application, and never round a negative numeral |
| P3 | drops pairs round a binder's whole type | the same, in a header, `∀`, `∃`, lambda, function type and annotation |
| P4 | merges adjacent groups of one type | a group's split, for a header (not an instance), `∀` and lambda (not `∃`), where the type names none of the names |

It had its Opus review (SW-3878) and has a compiler oracle
(`dev/fmt-meaning-oracle`, 120 pairs, 0 findings) [reported]. What slice
2 adds to the trust story is only that these rows are now reachable from
a top theorem; the checkpoint should read the four rows again against
`slice2Formats`, which is ten minutes.

**Comments.** `meaning` blanks every comment, and no top theorem of slice
1 says a comment survives. In slice 1 the passes delete only commas. In
slice 2, P3 deletes brackets and P4 deletes `: T) (`, each only where the
tokens hold no comment (`Word.bare`, `Group.bare`,
`next.open.above.isEmpty`) [source], and that guard is exactly what a
comments theorem would rest on. I recommend stating
`CommentsKept (lex source) (lex out)` as a fourth conjunct of
`slice1Formats` first (a ticket of its own, Opus, since the statement
may need adjusting), then carrying it into slice 2. It is not in the
count of §5.

## 4. How slice 1's proofs extend

Slice 1 on main: 6,232 theorems in `tools/fmt/src` [measured:
`grep -c '^theorem'`, files grouped by name].

| Layer | Files | Slice 1 | For slice 2 |
|---|---|---|---|
| Two-run parse | `Syntax/Follows*`, `DeafProofs` | 1,006 | **unchanged**: no slice hypothesis in any of the five `Follows` files [measured]. New: the closing lemma (`groupKeepsTokens2`, `grammar2Deaf`) and the file layer, where slice 1 used "both are definitions" for the parser's `Seen` state and slice 2 has theorems too |
| `meaning` and the traversal | `Walk`, `MeaningProofs`, `BlankProofs`, `MergeProofs`, `TraverseFail` | 253 | **unchanged** |
| Lexer | `Syntax/Lex*` | 331 | generalises by token: nine kinds. `=>` shares its first character with `=` and `==`; `theorem`, `forall`, `exists`, `Type`, `Prop` go through the name path's keyword table; `∀` and `∃` are new first characters |
| Rule N | `Syntax/Settle*`, `GoodItemProofs`, `GlueQuietProofs` | 523 | **restated over a larger alphabet, no new clause** (§3.1). `SettleProofs.sw` names a slice 1 predicate on 74 lines [measured]; the others on 2 to 15. The mark bookkeeping stays inside the tidying step (D3690): `startsWalk` is untouched |
| Parser walk | `Syntax/ParseWalk*`, `ParseProofs`, `ParseKept`, `ParseCarries*` | 951 | **the largest redo.** About 65 parser functions move from "outside the slice" (`Out` facts, `readsOut`) to walked: header groups (17), rows and results (12), `forallPart` and header parameters (6), lambdas (10), quantifiers (10), `piExpr` (3), and the look-aheads (`lambdaAhead`, `lambdaResultType`, `annotatedParamAhead`, `implicitGroupAt`, `namelessAutoAt`, `rowAhead`, `piHere`) [source: `FollowsForms.sw`'s and `FollowsDecl.sw`'s lists]. The spec (`Parsed1`, `KeptTree`), combinators and knot carry; each needs a slice 2 spec with arms for the new nodes |
| Read-back | `Syntax/ReadBack*` | 494 | new rungs: lambda, `∀`, `∃`, a group, a header with groups, a row, a function type. **New kind of hypothesis:** slice 1's look-aheads were false by alphabet (no `=>`); in slice 2 `lambdaAhead` must be proved true at each printed lambda and false at each printed thing that isn't one |
| Printer: tokens, spelling, joins | `Fmt/SpellProofs`, `JoinProofs`, `TouchProofs`, `OutputFileProofs`, `SettleOutputProofs`, … | 883 | arm lemmas per new node; the dispatchers gain arms |
| Printer: layout | `Fmt/*Hang*`, `Elements*`, `Told*`, `Stands*`, `Lays*`, … | 1,311 | the header's balanced fill (`paramsHeader`, premises alone on a line) is new machinery, not a new arm; lambdas, quantifiers and rows are arms; `huggedLambda` joins `huggedBracket` |
| Passes and `calm` | `Fmt/PassProofs`, `CalmProofs`, `CalmTopProofs`, `PlacedProofs`, `UnreturnedProofs` | 292 | slice 1 proves P1, P3, P4 are the identity (`forallSame1`, `bracketsSame1`, `mergeSame1`) and P2 keeps each predicate. Slice 2: all four keep `within2`, `shaped2`, `settled2`, `lexical2`, `unreturned2`, and `tidy2` is idempotent (§4.2) |
| Top, grammar, acceptance | `TopStatements`, `Accepts1`, `SettleParseProofs`, `SourcePlainProofs`, … | 188 | same shape, re-proved for the new names |

### 4.1 Where slice 1 leaned on what slice 2 brings

1. **Three passes were the identity.** `tidyIs1` rewrites `tidy1` to P2
   alone, and `tidiedFacts` carries every tree fact through P2 only
   (`TopStatements.sw:148`, `:199`) [source]. This is slice 2's main new
   proof content after the walk.
2. **Idempotence came from "no last comma".** `tidySame1` needs
   `commaFree` and nothing else. Slice 2 needs §4.2.
3. **No look-ahead for `=>`** (the read-back row above).
4. **"Both are definitions"** in the file layer of rule-N-keeps-the-parse
   (`Fmt/SettleParseProofs.sw`'s doc) [source].
5. **`Group.bare`** didn't exist in a slice 1 tree. It is a field the
   parser sets from comments, the tree equality of read-back compares it,
   and P4 reads it (§4.3).
6. **Layout readers: nothing new.** SW-4184 §1.2 found `lineIndent`
   read only by `headIndentOn`, for `match`, `if` and `|>`. Slice 2's
   parser functions read a line start or column in the common stop test
   only (`DeclParser.sw:32`) and for a `:=` that starts its line (`:948`)
   [source: grep of `DeclParser.sw`; the lambda and quantifier functions
   in `Parser.sw` have no read of their own]. And since SW-4183 the
   driver parses the lexer's own tokens, so the question no longer
   depends on the slice. Nobody should reintroduce a marked parse
   (SW-4184 follow-up 6).
7. **The printed header runs over several lines in a new way**: groups
   on continuation lines, then `:` and the result [run, §2.3's long
   theorem]. Slice 1's `hangs` covers a value's continued lines; the
   header's lines are right of the `def`'s column, so the same stop rule
   reads them [inferred], but `hangs` and `stands` need the header's
   shape added.

### 4.2 Idempotence of the passes (spike K5, widened)

`formatIdempotent2` needs the second run's passes to change nothing:

```
tidyTwice:   file.tidy2.tidy2 = file.tidy2            for within2 trees
calmTidy:    file.calmTop.tidy2 = file.tidy2.calmTop
```

`calmTidy` should be direct: the passes read whether a token has
comments, never a blank-line flag [source: `Word.bare`, `Passes.sw:62`].
`tidyTwice` is the risk. My reading of each part [inferred, none
searched]:

- P4 alone: merging is greedy left to right, and a merged group can only
  fail more tests with a later group, since both name tests get more
  names (`rustJoins`' last line, `Group.namesItself`). So a second pass
  finds nothing. This is K5's "merging uncovers no new merge".
- P3 alone: `dropLeft` recurses into what it uncovers and
  `stripBinderType` strips every layer, so each is a fixed point; the
  order of the two steps is §2.3.
- P3 after P4: no P3 test reads a group's names, and a merge keeps the
  first group's type, so merging uncovers no bracket.
- P4 after P3: P3 runs first, so P4 sees stripped types. But P3 strips
  binder types only along the header's type, and P4 merges in every
  lambda and `∀`: `(x: (A)) (y: A) => …` in a value is neither stripped
  nor merged, on either run. Stable, and a second harness difference
  from nothing.
- P1 and P2: nothing later adds a comma or removes a `∀` or an explicit
  group.

The blind-alley signal is the plan's: a counterexample to `tidyTwice`
that isn't a bug to fix in both formatters. The three inputs of §2.3 are
the first seeds.

### 4.3 `Group.bare`

`shaped2` must say `group.bare` is what the group's comments make it, the
parser must be proved to set it so (`consumedBare`), and each pass must
keep it. P4's merged group keeps the first group's `bare`, which is
`True` since `mergeable` asks it of both [source: `Passes.sw:312`,
`:378`], and the printed merged group has no comment but above its
bracket, so it reads back `True` [inferred]. P3 drops only brackets with
no comment. A small invariant, but tree equality fails silently without
it, so it is named here.

### 4.4 `standsAt` (spike K2), as it now stands

The plan's risk was a predicate that replaces Rust's trial parse. Stage
4a replaced the trial with a table (`Expr.level`, `leftNeeds`,
`keepsBrackets`), read off Rust's answers and agreeing with the parser's
ladder rung for rung [reported, NOTES "P3's table against the parser"].
So the risk is now one statement: **P3 keeps `shaped2`** (the tree it
leaves is one the parser builds, so it reads back as itself). NOTES
judged it "provable as part of `printParses`, not on its own".

In slice 2 the table is small: a row's result can hold slice 1's forms
and the three binders, so the live entries are `App` (20), the binary
levels, `Prefix` (18), arrows (kept, by `holdsFunction`), binders (0:
bare only when the pair is the whole result) and the two exceptions (a
negative numeral; a row that reads as a record). `∈`, chains and field
access are not in the slice. The cases to search first [run on Rust,
all read back]: `{Fail} (x => x)`, `{Fail} (∀ (x: A) => P)`,
`{Fail} (-x)`, `{e} (-x)` (kept), `{Fail} (f) x`, `{Fail} ((a + b)) * c`,
`{Fail} ([a])`.

## 5. Counts, spikes, risks

### 5.1 Theorems per layer (the prediction)

New theorems for slice 2 [estimated]. Slice 1's sketch predicted 950 to
1,400 and the slice took 6,232, so these are scaled from slice 1's
actuals per parser function and per construct, not from the plan.

| Layer | Slice 1 actual | Slice 2 new | Basis |
|---|---|---|---|
| Lexer | 331 | 60–110 | nine token kinds |
| Rule N | 523 | 60–120 | restated alphabet; no new clause |
| Two-run parse | 1,006 | 20–40 | closing and file lemmas only |
| Parser walk | 951 | ~~500–800~~ **250–350** | 65 functions. *Corrected 19 Nov (SW-4210):* the original basis, "slice 1 ran at 16 a function over 58", divided all 951 theorems by the 58 functions slice 1 reaches, but those theorems walk about 500 functions. Measured per function walked, shape is 1.3 (665 theorems over 504) and tokens kept 1.8 (261 over 142), so 65 × 4.2 (1.75 + 1.84 + 0.65 for spec helpers) ≈ 276 to 65 × 5.4 ≈ 350 [estimated from measured rates] |
| Read-back | 494 | 350–550 | seven rungs and the look-aheads both ways |
| Printer: tokens, spelling, joins | 883 | 300–500 | seven node kinds against slice 1's eight, sharing the machinery |
| Printer: layout | 1,311 | 700–1,100 | the header fill is new; the rest are arms |
| Passes and `calm` | 292 | 250–400 | three passes × five predicates, `tidyTwice`, `Group.bare` |
| `meaning` | 253 | 0–20 | done |
| Top, grammar, acceptance | 188 | 150–250 | as slice 1 |
| **Total** | **6,232** | **~~2,400–3,900~~ 2,150–3,450** | |

*Corrected 19 Nov (SW-4210).* The other nine rows are unchanged, so the
total moves by the parser row alone: low 2,400 − 500 + 250 = **2,150**,
high 3,900 − 800 + 350 = **3,450** [estimated]. In agent time at slice
1's 87 theorems an hour that is 25 to 40 hours, not 28 to 45 (2,150 / 87 =
24.7; 3,450 / 87 = 39.7).

The plan's stop rules read against this table at the checkpoint: one
layer over twice its count is re-sketched; the total over twice (7,800;
*corrected 19 Nov (SW-4210): 2 × 3,450 = 6,900*)
stops the slice.

### 5.2 Spikes due

| # | Spike | State | When |
|---|---|---|---|
| K2 | `standsAt` | changed shape (§4.4): "P3 keeps `shaped2`", searched on generated rows | lane 3 |
| K5 | P4's idempotence | widened to `tidyTwice` (§4.2); Rust fails it on three inputs (§2.3) | lane 3 |
| K6 (new) | look-ahead read-back: state, for the printed items of each slice 2 node, that `lambdaAhead` is true at a lambda's start and false at every other expression start, and search it | new | lane 3; first read-back lane proves it |
| K3b | block read-back | not due (S3) | |

### 5.3 The plan's four risks for S2

| Risk | Now |
|---|---|
| `standsAt` | a table exists and matches Rust; the open statement is "P3 keeps `shaped2`" (§4.4). Medium |
| P4's idempotence | plausible by the monotone argument (§4.2), unsearched. The live risk is the P3 and P4 interaction, where Rust already fails. Medium |
| P3 before P4 | the order inside P3 matters more than P3 against P4 (§2.3). The self-hosted order looks right; to run |
| `meaning` | settled: proved for all four passes (§3.3) |

New risks: the header's balanced fill in the layout layer (the largest
range in §5.1); the look-aheads (K6); and the size itself.

## 6. Lane plan

Models by D3682: routine proofs (walks, case splits, "this pass keeps
X") to Sonnet; a hard invariant or a statement that may need adjusting to
Opus; what to prove to Fable. Estimates are agent minutes [estimated]:
I had no lane times for slice 1 to hand, so they are set from the lane
sizes NOTES records and should be rescaled by the rate SW-4195 measures.

| # | Lane | Needs | Model | Est. |
|---|---|---|---|---|
| 1 | B1: `Grammar2.sw`, `MustAccept2.sw` | Matt's answer (§7) | Opus | 30 |
| 2 | B2 + B3: the program widened, `Driver2.sw`; B4 beside it | 1 | Opus; Sonnet | 60; 30 + 30 |
| 3 | Statements and search: `Predicates2.sw`; every layer's statements written open in a scratch copy; the Twin on generated slice 2 files (comments, blank lines and breaks in every gap, as slice 1's 9,900) for `tidyTwice`, read-back, K2, K5, K6; the false ones fixed or reported | 2 | Fable | 90 |
| 4 | Lexer: the nine kinds | 1 | Sonnet | 45 |
| 5 | Rule N over the larger alphabet | 1 | Sonnet (Opus if a statement must change) | 60 |
| 6 | Two-run closing and file layer for theorems | 1 | Sonnet | 30 |
| 7 | Parser walk: the slice 2 spec and knot | 3 | Opus | 60 |
| 8 | Parser walk: header groups and parameters; rows, results, `piExpr`; lambdas and quantifiers (three lanes, side by side) | 7 | Sonnet | 3 × 60 |
| 9 | Read-back: K6 first; then binders; then headers and rows | 3 | Opus | 3 × 60 |
| 10 | Passes: P1 (Sonnet); P3 keeps the predicates (Opus); P4 and `Group.bare` (Opus); `tidyTwice`, `calmTidy` (Opus) | 3 | mixed | 30 + 75 + 60 + 45 |
| 11 | Printer, tokens and spelling: arms for the seven nodes | 3 | Sonnet | 3 × 45 |
| 12 | Printer, layout: the header fill; lambdas and hugging; quantifiers, rows, function types | 3 | Opus | 4 × 60 |
| 13 | Acceptance: `parsedWithin2`, `formatAccepts2` | 5, 6, 8 | Opus | 60 |
| 14 | Top: the three theorems, `slice2Formats`, `grammar1In2`, `sameOnSlice1`, `axioms` clean | all | Opus | 45 |
| 15 | Checkpoint, against §5.1 | 14 | Fable | 30 |

About 22 agent hours as listed. Slice 1's lanes multiplied (the
`printedHangs` work alone ran to seven), so the honest range is **25 to
40 agent hours** [estimated], three build lanes at a time, lanes 4 to 12
side by side once 3 is in.

Rules for every proof brief, from slice 1: no narrowing of `within2`,
the driver or the grammar and no new hypothesis on a top theorem
(D3688); `Grammar2.sw`, `MustAccept2.sw` and the top statements are not
edited by a proof lane; a statement found false is reported, not
patched round.

## 7. The decision for Matt

**Is slice 2's grammar the full reading of binders (§1.1), not the
narrower set the program was built to?** [rec: yes]

*The problem.* The plan's row for slice 2 names constructs: headers with
parameter groups, lambdas, `∀`, `∃`, effect rows. The program built for
it takes a subset: no row after an arrow (so no `(f: A → {Fail} B)`), no
`fun`, no `{}`, no `[auto Ord a]`, no default, no `()`. And dependent
function types, `(x: A) → B`, are in no slice at all. Proving the
program as built would repeat slice 1's mistake, where narrowings stood
in for the grammar.

*The change.* `Grammar2.sw` is written to §1.1 with all seven in, and
the program is widened to it before any proof (lane 2, about an hour).
Left out by name, each with its slice: the row variable (`{IO | e}`, S3,
with rule N's `|`), patterns as parameters (S4), `Type 1` (S4),
instances and the header clauses (S5).

*What it should do.* "Slice 2 is proved" then means every `def` and
`theorem` with parameters, written with slice 1's expressions, lambdas,
quantifiers, rows and function types. The cost is in the estimate
already: about a tenth of the slice's theorems [estimated]. Any of the
seven can be answered separately; the one I would let go first if the
answer is "smaller" is 7, since it alone is an addition to the plan.

## 8. Found on the way (tickets)

| # | What | Size |
|---|---|---|
| 1 | Rust P3 not idempotent after a row (§2.3): fix in `crates/fmt`, test on both sides | B4 |
| 2 | `slice1Formats` has no comments conjunct; `CommentsKept` has no theorem (§3.3) | Opus, a ticket before lane 14 |
| 3 | The lambda rule drops a `fun` keyword (`Rules.sw:356` matches it with `_`) [source, not run]; in B2 | with B2 |
| 4 | `paramsWithin2`'s `PatternWord` arm is dead (§1.1) | with B2 |
| 5 | Rust and the rules differ on `{Fail} (- 1)`, `{Fail}T`, `)(` (§2.3): harness differences to list in the drift report, or settle in Rust | DeepSeek, 20 |
| 6 | The plan's 9,000-theorem question (§5.1) falls due inside slice 2 | SW-4195's |
| 7 | `(x: (A)) (y: A) => …` in a value is neither stripped nor merged (§4.2): P3 strips binder types only along a header's type. Intended in Rust; worth a line in `fmt-passes.md` | note |

## Sources

- Proposals: `self-hosted-fmt-proof-plan.md` (all), `self-hosted-fmt-s1-sketch.md` (headings and §1 only).
- Reviews: `SW-4184-slice1-checkpoint.md`, `SW-4191-slice1-final.md`.
- `tools/fmt/NOTES.md`: stages 4a and 4b, the traversal lemma, the comment-free `meaning`, slices 1 and 2's programs; the rest by heading.
- Code: `Fmt/{Grammar1,TopStatements,Slice2,Passes,Meaning,Driver1}.sw` in full; `Syntax/Decl.sw` (types), `Settle.sw` (to line 160), `SettleProofs.sw` (the `plain` definitions); the header docs of the `Follows`, `ParseWalk`, `ParseKept`, `ReadBack` and `SettleParseProofs` files; `grep` of `Rules.sw`, `Traverse.sw`, `Parser.sw`, `DeclParser.sw`. No proof was read.
- Runs: about 80 one-line sources through `stitchwort dev tree --print` and 40 through `stitchwort fmt -` (release binary, the Rust formatter), in the scratch folder.
