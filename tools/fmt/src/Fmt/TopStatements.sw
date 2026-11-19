--| Slice 1's two top theorems (SW-4079; docs/reviews/SW-4078-slice1-stock-take.md, recommendation 1), about the
--| driver `formatWithin1`:
--|
--| - `formatKeepsProgram1`: what it prints parses back, to `calmTop` of the tree it printed, with the source's
--|   `meaning`.
--| - `formatIdempotent1`: formatting what it prints gives the same text.
--|
--| Both are proved from the layers' theorems: the element facts (`Fmt.ElementsProofs`, under `declElements1`) and
--| read-back (`Fmt.TopReadBack`).
--|
--| The third top theorem, `formatAccepts1` (`Fmt.Accepts1`), says which sources the driver must accept:
--| all of slice 1's grammar (`Fmt.Grammar1`).
--|
--| What slice 1 covers: files of `def name: Type := value` with no parameters, the type and value names, numerals,
--| brackets, tuples, lists, calls, `-`, `!`, `¬`, binary operators and `->`, with comments and blank lines, laid out
--| over any number of lines; the driver refuses anything else.

namespace Fmt.TopStatements
import Std (Bool, Eq, List, Nat, Option, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Fmt.Driver1 (..)
import Fmt.Accepts1 (formatAccepts1)
import Fmt.TopReadBack (..)
import Fmt.OutputStatements (..)
import Fmt.TriviaStatements (..)
import Fmt.PassProofs (..)
import Fmt.CalmTopProofs (..)
import Fmt.Proofs (firstThreeKeepMeaning)
import Fmt.FileLexProofs (printedFileLexes1)
import Fmt.OutputFileProofs (printedAlphabet1, printedNoLast1, printedPlain1)
import Fmt.SettleOutputProofs (..)
import Fmt.StandsProofs (..)
import Fmt.UnreturnedProofs (commaUnreturned)
import Fmt.DeclFactsProofs (DeclElements, declHangsOf, printedHangs1)
import Fmt.ElementsProofs (declElements1)
import Fmt.TreeJoinProofs (lexKind, printLexes1Tree)
import Fmt.TokenProofs (declRealOfLexical)
import Fmt.SpellProofs (declSoundOfSettled)
import Syntax.ParseWalk (parseLexical1, parseShaped1)
import Syntax.ParseWalkOthers (frameRest, parseSettledSourceProved)
import Syntax.GoodItemProofs (settledGood)
import Syntax.GlueQuietProofs (settledItemsQuiet)
import Syntax.SettleProofs (alphabet1, plain1, settledKeepsTokens, sourcePlainOfPlain, tokens)
import Syntax.SettleBareProofs (settledOnceNone)
import Syntax.AutoPlaced (..)
import Fmt.PlacedProofs (commaKeepsPlaced, parsedPlaced1)

--| P2 is the identity on an expression with no last comma.
theorem uncommaSame ∀ (expr: Expr) (free: expr.commaFree = True): expr.mapIn1 withoutCommaExpr = expr := match expr with
  | Paren open inner close => rewrite uncommaSame inner free
  | Tuple open items comma close =>
    match comma, free with
      | False, free => rewrite uncommasSame items free
      | True, free => (Bool.falseNotTrue free).impossible
  | ListOf open items comma close =>
    match comma, free with
      | False, free => rewrite uncommasSame items free
      | True, free => (Bool.falseNotTrue free).impossible
  | App head arguments => rewrite uncommaSame head (Bool.andLeft free), uncommasSame arguments (Bool.andRight free)
  | Infix kind left operator right =>
    rewrite uncommaSame left (Bool.andLeft free), uncommaSame right (Bool.andRight free)
  | Prefix operator operand => rewrite uncommaSame operand free
  | _ => cases

theorem uncommasSame ∀ (items: List Expr) (free: allCommaFree items = True): mapAll1 withoutCommaExpr items = items :=
  match items with
    | [] => byComputing
    | [first, ..rest] => rewrite uncommaSame first (Bool.andLeft free), uncommasSame rest (Bool.andRight free)

theorem declUncommaSame ∀ (decl: Decl)
    (within: decl.within1 = True)
    (free: decl.commaFree = True):
    decl.uncomma = decl :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      match header with
        | {
            exportKeyword = None,
            opaqueKeyword = None,
            kind = DefPlain,
            keyword,
            name,
            forallKeyword = None,
            params = [],
            colon,
            result,
            decreasingClause = None,
            unfoldingClause = None
          } => rewrite uncommaSame result (Bool.andLeft free), uncommaSame value (Bool.andRight free)
        | _ => cases

theorem declsUncommaSame ∀ (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (free: decls.all Decl.commaFree = True):
    decls.map Decl.uncomma = decls :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      rewrite declUncommaSame decl (Bool.andLeft within) (Bool.andLeft free),
          declsUncommaSame rest (Bool.andRight within) (Bool.andRight free)

--| `commaSame1`: P2 changes nothing in a slice 1 tree with no last comma (the stock take's row 10).
theorem commaSame1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (commaFree: file.commaFree = True):
    file.withoutTrailingCommas = file :=
  rewrite commaMap file within, declsUncommaSame file.decls within commaFree

-- `calmTop` keeps `calm`'s facts: `calmTopWithin`, `calmTopCommaFree`, `calmTopPrints` and
-- `calmTopMeans` are in `Fmt.CalmTopProofs`.

-- The driver, both ways.

--| What `formatWithin1` accepting a source says: it lexes, its leaves pass the tests, it parses to a tree within the
--| slice, and the output is that tree's tidied form printed.
def Formats1 (source out: Text) (lexed: Lexed) (parsed: SourceFile): Prop :=
  lex source = Ok lexed
    ∧ leavesWithin1 lexed.leaves = True
    ∧ parseFile lexed.settledOnce = Ok parsed
    ∧ parsed.within1 = True
    ∧ out = parsed.tidy1.printed1

theorem formatsOf ∀ (source out: Text)
    (formats: formatWithin1 source = Ok out):
    ∃ (lexed: Lexed) (parsed: SourceFile) => Formats1 source out lexed parsed :=
  match lexes: lex source, formats with
    | Err message, formats => (Result.errNotOk formats).impossible
    | Ok lexed, formats =>
      match leaves: leavesWithin1 lexed.leaves, formats with
        | False, formats => (Result.errNotOk formats).impossible
        | True, formats =>
          match parses: parseFile lexed.settledOnce, formats with
            | Err message, formats => (Result.errNotOk formats).impossible
            | Ok parsed, formats =>
              match within: parsed.within1, formats with
                | False, formats => (Result.errNotOk formats).impossible
                | True, formats => (lexed, parsed, lexes, leaves, parses, within, (Result.okInjective formats).flipped)

-- The tidied tree.

--| In slice 1 the passes are P2 alone: P1, P3 and P4 change nothing.
theorem tidyIs1 ∀ (file: SourceFile)
    (within: file.within1 = True):
    file.withForall.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters = file.withoutTrailingCommas :=
  let commaWithin := commaKeepsWithin file within
  rewrite forallSame1 file within,
      bracketsSame1 file.withoutTrailingCommas commaWithin,
      mergeSame1 file.withoutTrailingCommas commaWithin

theorem tidyComma1 ∀ (file: SourceFile) (within: file.within1 = True): file.tidy1 = file.withoutTrailingCommas :=
  tidyIs1 file within

--| `tidiedDeclsUnreturned1` (the stock take's U6): no comment of the tree the driver prints ends in a carriage
--| return or a space, above or after any word of any declaration. `printedStands1` takes it. It is false of a tree
--| outside the slice (`Decl.unreturned1` is false of a namespace line), so it takes `Formats1`'s hypotheses.
--|
--| Proof idea: the lexer strips both (`lexUnreturned`), rule N and the parser carry comments without changing their
--| texts, and P2 keeps every word (`commaUnreturned`).
theorem tidiedDeclsUnreturned1 ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (leaves: leavesWithin1 lexed.leaves = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (within: parsed.within1 = True):
    parsed.tidy1.decls.all Decl.unreturned1 = True :=
  rewrite tidyComma1 parsed within then
    (commaUnreturned source lexed parsed lexes (Bool.andLeft leaves) (Bool.andRight leaves) parses within).left

--| `tidiedUnreturned1` (SW-3973's parser side): the tree the formatter prints has no own-line comment ending in a
--| carriage return or a space, which is `printedSettle1`'s hypothesis `unreturned1`. Same route and hypotheses as
--| `tidiedDeclsUnreturned1`.
theorem tidiedUnreturned1 ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (leaves: leavesWithin1 lexed.leaves = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (within: parsed.within1 = True):
    parsed.tidy1.unreturned1 = True :=
  rewrite tidyComma1 parsed within then
    (commaUnreturned source lexed parsed lexes (Bool.andLeft leaves) (Bool.andRight leaves) parses within).right

--| A tree within the slice with no last comma is tidy.
theorem tidySame1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (commaFree: file.commaFree = True):
    file.tidy1 = file :=
  rewrite tidyIs1 file within, commaSame1 file within commaFree

--| The tree facts the output's theorems take.
def TreeFacts (file: SourceFile): Prop :=
  file.within1 = True ∧ file.shaped1 = True ∧ file.settled1 = True ∧ file.lexical1 = True ∧ file.commaFree = True

--| The tree the driver prints has the facts: the parser's (`parseShaped1`, `parseLexical1`, `parseSettledSourceProved`
--| from the source, `good` by `settledGood`), carried through P2.
theorem tidiedFacts ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (leaves: leavesWithin1 lexed.leaves = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (within: parsed.within1 = True):
    TreeFacts parsed.tidy1 :=
  let alphabet := Bool.andLeft leaves
  let plain := Bool.andRight leaves
  let good := settledGood source lexed lexes alphabet plain
  let quiet := settledItemsQuiet source lexed lexes alphabet
  let shaped := parseShaped1 frameRest lexed.settledOnce parsed good quiet parses within
  let lexical := parseLexical1 frameRest lexed.settledOnce parsed good quiet parses within
  let settled := parseSettledSourceProved source lexed parsed lexes alphabet plain parses within
  rewrite tidyComma1 parsed within then
    (
      commaKeepsWithin parsed within,
      rewrite commaKeepsShaped parsed within then shaped,
      rewrite commaKeepsSettled parsed within then settled,
      rewrite commaKeepsLexical parsed within then lexical,
      commaBare parsed within
    )

-- Line breaks and comments of the printed declarations.

--| A declaration of the tree the driver prints hangs as the rules lay it out, over one line or several, and stands.
theorem declHangs1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (unreturned: decl.unreturned1 = True):
    hangs decl.leaves1 = True ∧ (decl.unreturned1 = True → decl.stands1 = True) :=
  let sound := declSoundOfSettled decl within settled (declRealOfLexical decl within lexical)
  let elements := declElements1 decl within shaped settled lexical unreturned
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      let doc := defDoc header colonEq value
      (
        printedHangs1
          (Definition [] header (Assigned colonEq value))
          doc
          width
          within
          shaped
          sound
          lexical
          elements
          byComputing _
          (printLexes1Tree
            (Definition [] header (Assigned colonEq value))
            doc
            width
            within
            shaped
            sound
            lexical
            byComputing),
        unreturned =>
          printedStands1
            (Definition [] header (Assigned colonEq value))
            within
            shaped
            settled
            lexical
            unreturned
            (declHangsOf (Definition [] header (Assigned colonEq value)) within sound elements)
      )

--| Each declaration's facts give `p` of it, so all declarations' give `p` of all.
theorem declsAll ∀ (decls: List Decl) (p: Decl → Bool)
    (within: decls.all Decl.within1 = True)
    (shaped: decls.all Decl.shaped1 = True)
    (settled: decls.all Decl.settled1 = True)
    (lexical: decls.all Decl.lexical1 = True)
    (unreturned: decls.all Decl.unreturned1 = True)
    (each: ∀ (decl: Decl) => decl.within1 = True
      → decl.shaped1 = True
      → decl.settled1 = True
      → decl.lexical1 = True
      → decl.unreturned1 = True
      → p decl = True):
    decls.all p = True :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      Bool.andIntro
        (each decl
          (Bool.andLeft within)
          (Bool.andLeft shaped)
          (Bool.andLeft settled)
          (Bool.andLeft lexical)
          (Bool.andLeft unreturned))
        (declsAll rest p
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight settled)
          (Bool.andRight lexical)
          (Bool.andRight unreturned)
          each)

-- The output parses.

--| The output's text lexes to `file.lexed1`, and its settled-once leaves parse to `calmTop` of the printed tree.
--|
--| Proof idea: `printedFileLexes1`; no last comma (`printedNoLast1`), so `settledOnce` is `settled`; rule N gives the
--| tree's words back (`printedSettle1`, whose `hung1` and `stood1` come from each declaration's element facts); then
--| read-back in file form, with each declaration's group read back by `readsBackDecl1`.
theorem outputParses1 ∀ (file: SourceFile)
    (facts: TreeFacts file)
    (declsUnreturned: file.decls.all Decl.unreturned1 = True)
    (unreturned: file.unreturned1 = True)
    (placed: file.autoPlaced1 = True):
    lex file.printed1 = Ok file.lexed1 ∧ parseFile file.lexed1.settledOnce = Ok file.calmTop :=
  let (within, shaped, settled, lexical, commaFree) := facts
  let declsSettled: file.decls.all Decl.settled1 = True := Bool.andLeft settled
  let hung: file.hung1 = True :=
    declsAll file.decls
      (decl => hangs decl.leaves1)
      within
      shaped
      declsSettled
      lexical
      declsUnreturned
      (decl w s t l u => (declHangs1 decl w s t l u).left)
  let stood: file.stood1 = True :=
    declsAll file.decls Decl.stands1 within shaped declsSettled lexical declsUnreturned (decl w s t l u =>
      (declHangs1 decl w s t l u).right u)
  let once := settledOnceNone file.lexed1 (printedNoLast1 file within shaped settled lexical)
  let (words, ends) := printedSettle1 file within shaped settled lexical hung stood unreturned
  (
    printedFileLexes1 file within shaped settled lexical,
    rewrite once then
      readsBackFile1 file file.lexed1.settled within shaped settled lexical commaFree hung placed
        (settledKeepsTokens file.lexed1)
        words
        ends
        declsReadBack
  )

--| The tree the driver prints is placed (`Syntax.AutoPlaced`): the parser's `parsedPlaced1`, carried through P2.
theorem tidiedPlaced1 ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (leaves: leavesWithin1 lexed.leaves = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (within: parsed.within1 = True):
    parsed.tidy1.autoPlaced1 = True :=
  rewrite tidyComma1 parsed within then
    commaKeepsPlaced parsed within (parsedPlaced1 source lexed parsed lexes leaves parses within)

--| The facts of the tree the driver prints for an accepted source.
def Printed1 (source: Text) (lexed: Lexed) (parsed: SourceFile): Prop :=
  TreeFacts parsed.tidy1
    ∧ lex parsed.tidy1.printed1 = Ok parsed.tidy1.lexed1
    ∧ parseFile parsed.tidy1.lexed1.settledOnce = Ok parsed.tidy1.calmTop

theorem printedOf ∀ (source out: Text) (lexed: Lexed) (parsed: SourceFile)
    (formats: Formats1 source out lexed parsed):
    Printed1 source lexed parsed :=
  let (lexes, leaves, parses, within, _) := formats
  let facts := tidiedFacts source lexed parsed lexes leaves parses within
  let unreturned := tidiedUnreturned1 source lexed parsed lexes leaves parses within
  let declsUnreturned := tidiedDeclsUnreturned1 source lexed parsed lexes leaves parses within
  let placed := tidiedPlaced1 source lexed parsed lexes leaves parses within
  let (lexOut, parseOut) := outputParses1 parsed.tidy1 facts declsUnreturned unreturned placed
  (facts, lexOut, parseOut)

-- The top theorems.

--| **The same program.** If slice 1's driver formats `source` to `out`, then both parse (as the driver parses: lexed,
--| settled once, `parseFile`), `out` to `calmTop` of the tidied tree of `source`, and the two trees have the same
--| `meaning`.
--|
--| `calmTop` is `calm` (each word's blank-line flag kept only where the rules print a blank line) with the file's first
--| flag cleared; it changes comments' flags only, so `meaning`, which reads no comment, is kept. Slice 1 excludes
--| everything `formatWithin1` refuses: a token outside the slice's alphabet, a source that isn't `sourcePlain1`, one
--| that doesn't lex or parse, and a tree outside `within1`. `formatAccepts1` proves that none of it is in slice 1's
--| grammar.
--|
--| Proof idea: `formatsOf` inverts the driver; `tidiedFacts` gives the printed tree's facts from the parser's
--| theorems through P2; `outputParses1` parses the output; `meaning` is kept by the passes (`firstThreeKeepMeaning`,
--| P1 and P3 being the identity in the slice) and by `calmTop`.
theorem formatKeepsProgram1 ∀ (source out: Text)
    (formats: formatWithin1 source = Ok out):
    ∃ (before after: SourceFile) => parse1 source = Ok before
      ∧ parse1 out = Ok after
      ∧ after = before.tidy1.calmTop
      ∧ after.meaning = before.meaning :=
  let (lexed, parsed, accepted) := formatsOf source out formats
  let (lexes, leaves, parses, within, outIs) := accepted
  let (facts, lexOut, parseOut) := printedOf source out lexed parsed accepted
  let commaWithin := commaKeepsWithin parsed within
  let kept: parsed.withoutTrailingCommas.meaning = parsed.meaning :=
    let three := firstThreeKeepMeaning parsed
    rewrite forallSame1 parsed within, bracketsSame1 parsed.withoutTrailingCommas commaWithin at three then three
  (
    parsed,
    parsed.tidy1.calmTop,
    rewrite lexes then parses,
    rewrite outIs, lexOut then parseOut,
    byComputing,
    rewrite calmTopMeans parsed.tidy1, tidyComma1 parsed within then kept
  )

--| **Idempotence.** If slice 1's driver formats `source` to `out`, it formats `out` to `out`.
--|
--| Slice 1 excludes what `formatKeepsProgram1` says; on an accepted source the theorem has no other condition.
--|
--| Proof idea: the second run lexes `out` to the printed tree's leaves, which pass the alphabet (`printedAlphabet1`)
--| and are `plain1` (`printedPlain1`, so `sourcePlain1`), and parse to `calmTop` of the printed tree (`printedOf`);
--| that tree is within the slice and has no last comma, so tidying changes nothing (`tidySame1`), and it prints `out`
--| (`calmTopPrints`).
theorem formatIdempotent1 ∀ (source out: Text) (formats: formatWithin1 source = Ok out): formatWithin1 out = Ok out :=
  let (lexed, parsed, accepted) := formatsOf source out formats
  let (_, _, _, _, outIs) := accepted
  let (facts, lexOut, parseOut) := printedOf source out lexed parsed accepted
  let (within, shaped, settled, lexical, commaFree) := facts
  let file := parsed.tidy1
  let declsSettled: file.decls.all Decl.settled1 = True := Bool.andLeft settled
  let hung: file.hung1 = True :=
    declsAll file.decls
      (decl => hangs decl.leaves1)
      within
      shaped
      declsSettled
      lexical
      (tidiedDeclsUnreturnedOf source out lexed parsed accepted)
      (decl w s t l u => (declHangs1 decl w s t l u).left)
  let leaves: leavesWithin1 file.lexed1.leaves = True :=
    Bool.andIntro
      (printedAlphabet1 file within shaped settled lexical)
      (sourcePlainOfPlain _ (printedPlain1 file within shaped settled lexical hung))
  let topWithin := calmTopWithin file within
  let same := tidySame1 file.calmTop topWithin (calmTopCommaFree file within commaFree)
  let again := formatsFrom out file.lexed1 file.calmTop (rewrite outIs then lexOut) leaves parseOut topWithin
  rewrite same, calmTopPrints file within lexical at again then
    Eq.trans again (Eq.cong (text => (Ok text: Result Text Text)) outIs.flipped)

--| The declarations' comments of an accepted source's printed tree end in neither a carriage return nor a space.
theorem tidiedDeclsUnreturnedOf ∀ (source out: Text) (lexed: Lexed) (parsed: SourceFile)
    (formats: Formats1 source out lexed parsed):
    parsed.tidy1.decls.all Decl.unreturned1 = True :=
  let (lexes, leaves, parses, within, _) := formats
  tidiedDeclsUnreturned1 source lexed parsed lexes leaves parses within

-- A source the theorems apply to (D3684).

--| A source with comments above, after and at the end of declarations, a value after a comment on the `:=` (so on the
--| next line), a tuple, a list, a call, a sign and an arrow.
def witnessSource: Text :=
  "-- top\ndef d: A -> B := f (a, -b) [1, 2] -- end\n\n\ndef e: C := -- after\n  g x\n-- last\n"

def witnessOut: Text := "-- top\ndef d: A -> B := f (a, -b) [1, 2] -- end\n\ndef e: C := -- after\n  g x\n-- last\n"

--| The top theorems' one hypothesis holds of `witnessSource`.
theorem witnessFormats: formatWithin1 witnessSource = Ok witnessOut := byComputing

theorem witnessIdempotent: formatWithin1 witnessOut = Ok witnessOut :=
  formatIdempotent1 witnessSource witnessOut witnessFormats

theorem witnessSameProgram: ∃ (before after: SourceFile) => parse1 witnessSource = Ok before
      ∧ parse1 witnessOut = Ok after
      ∧ after = before.tidy1.calmTop
      ∧ after.meaning = before.meaning :=
  formatKeepsProgram1 witnessSource witnessOut witnessFormats

--| What the layers' theorems take and give, run on a source's printed tree: the tree facts their hypotheses ask, and
--| each conclusion that is a test (the `calmTop` facts, the comments without returns, and read-back in file form,
--| compared as `OutputStatements.readsBack` does).
def goalsHoldOn (source: Text): Bool := match tidiedOf source with
  | None => False
  | Some file =>
    file.within1
      && file.shaped1
      && file.settled1
      && file.lexical1
      && file.commaFree
      && file.unreturned1
      && file.decls.all Decl.unreturned1
      && file.calmTop.within1
      && file.calmTop.commaFree
      && file.calmTop.printed1 == file.printed1
      && readsBack file.lexed1.settled file

--| The layers' hypotheses and conclusions hold of `witnessSource`'s printed tree.
theorem witnessGoals: goalsHoldOn witnessSource = True := byComputing

--| `tidiedUnreturned1`'s and `tidiedDeclsUnreturned1`'s hypotheses hold of `witnessSource` (its `Formats1`), and so do
--| their conclusions.
theorem witnessUnreturned: ∃ (lexed: Lexed) (parsed: SourceFile) => parsed.tidy1.unreturned1 = True
      ∧ parsed.tidy1.decls.all Decl.unreturned1 = True :=
  match formatsOf witnessSource witnessOut witnessFormats with
    | Witness lexed (Witness parsed (lexes, leaves, parses, within, _)) =>
      Witness lexed
        (Witness parsed (
          tidiedUnreturned1 witnessSource lexed parsed lexes leaves parses within,
          tidiedDeclsUnreturned1 witnessSource lexed parsed lexes leaves parses within
        ))
