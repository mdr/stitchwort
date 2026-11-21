--| Reading this proof for the first time: `tools/fmt/GLOSSARY.md` defines its words and `tools/fmt/PROOF-MAP.md` maps it.
--|
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
--| `slice1Formats` puts the three together in one statement about the language's own lexer and parser.
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
import Fmt.BlankProofs (meaningBlanksFirst)
import Fmt.MeaningProofs (firstThreeKeepMeaning)
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
import Syntax.ParseWalkDecls (parseLexical1, parseShaped1)
import Syntax.ParseWalkOthers (frameRest, parseSettledSourceProved)
import Syntax.GoodItemProofs (settledGood, settledOnceTokens)
import Syntax.GlueQuietProofs (settledItemsQuiet)
import Syntax.SettleProofs (alphabet1, plain1, settledKeepsTokens, sourcePlainOfPlain, tokens)
import Syntax.SettleBareProofs (settledOnceNone)
import Syntax.AutoPlaced (..)
import Fmt.PlacedProofs (commaKeepsPlaced, parsedPlaced1)
import Fmt.Grammar1 (..)
import Fmt.Kinds (..)
import Fmt.SettleParseProofs (parseKeepsTokens1, settledParses1)

--| P2 is the identity on an expression with no last comma.
theorem uncommaSame ∀ (expr: Expr) (free: expr.commaFree = True): expr.mapIn withoutCommaExpr = expr := match expr with
  | Paren open inner close => rewrite uncommaSame inner free
  | Tuple _ items comma _ | ListOf _ items comma _ =>
    match comma, free with
      | False, free => rewrite uncommasSame items free
      | True, free => (Bool.falseNotTrue free).impossible
  | App head arguments => rewrite uncommaSame head (Bool.andLeft free), uncommasSame arguments (Bool.andRight free)
  | Infix kind left operator right =>
    rewrite uncommaSame left (Bool.andLeft free), uncommaSame right (Bool.andRight free)
  | Prefix operator operand => rewrite uncommaSame operand free
  | _ => cases

theorem uncommasSame ∀ (items: List Expr) (free: allCommaFree items = True): mapAll withoutCommaExpr items = items :=
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
  let commaWithin := commaKeepsWithin within
  rewrite forallSame1 file within,
      bracketsSame1 file.withoutTrailingCommas commaWithin,
      mergeSame1 file.withoutTrailingCommas commaWithin

theorem tidyComma1 ∀ (file: SourceFile) (within: file.within1 = True): file.tidy1 = file.withoutTrailingCommas :=
  tidyIs1 file within

--| `tidiedDeclsUnreturned1` (the stock take's U6): no comment of the tree the driver prints ends in a carriage
--| return or a space, above or after any word of any declaration. `printedStands1` takes it. It is false of a tree
--| outside the slice (`Decl.unreturned` is false of a namespace line), so it takes `Formats1`'s hypotheses.
--|
--| Proof idea: the lexer strips both (`lexUnreturned`), comment placement and the parser carry comments without changing their
--| texts, and P2 keeps every word (`commaUnreturned`).
theorem tidiedDeclsUnreturned1 ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (leaves: leavesWithin1 lexed.leaves = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (within: parsed.within1 = True):
    parsed.tidy1.decls.all Decl.unreturned = True :=
  rewrite tidyComma1 parsed within then
    (commaUnreturned source lexed parsed lexes (Bool.andLeft leaves) (Bool.andRight leaves) parses within).left

--| `tidiedUnreturned1`: the tree the formatter prints has no own-line comment ending in a
--| carriage return or a space, which is `printedSettle1`'s hypothesis `unreturned`. Same route and hypotheses as
--| `tidiedDeclsUnreturned1`.
theorem tidiedUnreturned1 ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (leaves: leavesWithin1 lexed.leaves = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (within: parsed.within1 = True):
    parsed.tidy1.unreturned = True :=
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
  file.within1 = True ∧ file.shaped = True ∧ file.settled = True ∧ file.lexical = True ∧ file.commaFree = True

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
      commaKeepsWithin within,
      rewrite commaKeepsShaped parsed within then shaped,
      rewrite commaKeepsSettled parsed within then settled,
      rewrite commaKeepsLexical parsed within then lexical,
      commaBare parsed within
    )

-- Line breaks and comments of the printed declarations.

--| A declaration of the tree the driver prints hangs as the rules lay it out, over one line or several, and stands.
theorem declHangs1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True)
    (unreturned: decl.unreturned = True):
    hangs decl.leaves = True ∧ (decl.unreturned = True → decl.stands = True) :=
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
    (shaped: decls.all Decl.shaped = True)
    (settled: decls.all Decl.settled = True)
    (lexical: decls.all Decl.lexical = True)
    (unreturned: decls.all Decl.unreturned = True)
    (each: ∀ (decl: Decl) => decl.within1 = True
      → decl.shaped = True
      → decl.settled = True
      → decl.lexical = True
      → decl.unreturned = True
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

--| The output's text lexes to `file.lexed`, and its settled-once leaves parse to `calmTop` of the printed tree.
--|
--| Proof idea: `printedFileLexes1`; no last comma (`printedNoLast1`), so `settledOnce` is `settled`; comment placement gives the
--| tree's words back (`printedSettle1`, whose `hung` and `stood` come from each declaration's element facts); then
--| read-back in file form, with each declaration's group read back by `readsBackDecl1`.
theorem outputParses1 ∀ (file: SourceFile)
    (facts: TreeFacts file)
    (declsUnreturned: file.decls.all Decl.unreturned = True)
    (unreturned: file.unreturned = True)
    (placed: file.autoPlaced = True):
    lex file.printed1 = Ok file.lexed ∧ parseFile file.lexed.settledOnce = Ok file.calmTop :=
  let (within, shaped, settled, lexical, commaFree) := facts
  let declsSettled: file.decls.all Decl.settled = True := Bool.andLeft settled
  let hung: file.hung = True :=
    declsAll file.decls
      (decl => hangs decl.leaves)
      within
      shaped
      declsSettled
      lexical
      declsUnreturned
      (decl w s t l u => (declHangs1 decl w s t l u).left)
  let stood: file.stood = True :=
    declsAll file.decls Decl.stands within shaped declsSettled lexical declsUnreturned (decl w s t l u =>
      (declHangs1 decl w s t l u).right u)
  let once := settledOnceNone file.lexed (printedNoLast1 file within shaped settled lexical)
  let (words, ends) := printedSettle1 file within shaped settled lexical hung stood unreturned
  (
    printedFileLexes1 file within shaped settled lexical,
    rewrite once then
      readsBackFile1 file file.lexed.settled within shaped settled lexical commaFree hung placed
        (settledKeepsTokens file.lexed)
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
    parsed.tidy1.autoPlaced = True :=
  rewrite tidyComma1 parsed within then
    commaKeepsPlaced parsed within (parsedPlaced1 source lexed parsed lexes leaves parses within)

--| The facts of the tree the driver prints for an accepted source.
def Printed1 (source: Text) (lexed: Lexed) (parsed: SourceFile): Prop :=
  TreeFacts parsed.tidy1
    ∧ lex parsed.tidy1.printed1 = Ok parsed.tidy1.lexed
    ∧ parseFile parsed.tidy1.lexed.settledOnce = Ok parsed.tidy1.calmTop

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
  let commaWithin := commaKeepsWithin within
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
  let declsSettled: file.decls.all Decl.settled = True := Bool.andLeft settled
  let hung: file.hung = True :=
    declsAll file.decls
      (decl => hangs decl.leaves)
      within
      shaped
      declsSettled
      lexical
      (tidiedDeclsUnreturnedOf source out lexed parsed accepted)
      (decl w s t l u => (declHangs1 decl w s t l u).left)
  let leaves: leavesWithin1 file.lexed.leaves = True :=
    Bool.andIntro
      (printedAlphabet1 file within shaped settled lexical)
      (sourcePlainOfPlain _ (printedPlain1 file within shaped settled lexical hung))
  let topWithin := calmTopWithin file within
  let same := tidySame1 file.calmTop topWithin (calmTopCommaFree file within commaFree)
  let again := formatsFrom out file.lexed file.calmTop (rewrite outIs then lexOut) leaves parseOut topWithin
  rewrite same, calmTopPrints file within lexical at again then
    Eq.trans again (Eq.cong (text => (Ok text: Result Text Text)) outIs.flipped)

--| The declarations' comments of an accepted source's printed tree end in neither a carriage return nor a space.
theorem tidiedDeclsUnreturnedOf ∀ (source out: Text) (lexed: Lexed) (parsed: SourceFile)
    (formats: Formats1 source out lexed parsed):
    parsed.tidy1.decls.all Decl.unreturned = True :=
  let (lexes, leaves, parses, within, _) := formats
  tidiedDeclsUnreturned1 source lexed parsed lexes leaves parses within

-- All of slice 1 in one statement.

--| The driver's alphabet is the grammar's: a token the driver lets through is one of the grammar's.
theorem tokenAlphabetOfWithin1 ∀ (kind: Tok): (!kind.within1 || kind.alphabet1) = True := cases

theorem leavesAlphabetOfWithin1 ∀ (leaves: List Leaf)
    (within: alphabet1 leaves = True):
    leaves.all (leaf => leaf.token.kind.alphabet1) = True :=
  match leaves, within with
    | [], within => byComputing
    | [leaf, ..more], within =>
      let both := tokenAlphabetOfWithin1 leaf.token.kind
      Bool.andIntro
        (rewrite Bool.andLeft within at both then both)
        (leavesAlphabetOfWithin1 more (Bool.andRight within))

--| A file within the driver's slice is a file of the grammar.
theorem fileGrammarOfWithin1 ∀ (decls: List Decl)
    (within: decls.all Decl.within1 = True):
    decls.all Decl.grammar1 = True :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      Bool.andIntro
        (Decl.grammarOfWithin1 decl (Bool.andLeft within))
        (fileGrammarOfWithin1 rest (Bool.andRight within))

--| **Slice 1 (D3687).** For every source in slice 1's grammar, the formatter succeeds, giving `out`; the language's
--| own lexer and parser read both `source` and `out`, to trees that mean the same program; `out` is in the grammar
--| too; and formatting `out` gives `out` again.
--|
--| "The language's own" is `lex` then `parseFile` of the lexer's leaves, as `inGrammar1` reads a source: no step of
--| the formatter (comment placement, the tidy passes) is in it. "The same program" is `meaning`, which reads no comment, as in
--| `formatKeepsProgram1`; the trees themselves may differ, in comments, blank lines and a list's or tuple's last
--| comma, which the formatter drops.
--|
--| Proof idea: `formatAccepts1` gives `out`, and `formatIdempotent1` the second run. `formatKeepsProgram1` gives
--| equal meanings for the trees the driver parses (after comment placement). Comment placement keeps every token (`settledOnceTokens`), so a
--| parse of either side's leaves is the other side's but for comments (`settledParses1` for the source,
--| `parseKeepsTokens1` for `out`, whose driver tree is within the slice and so of the grammar), and `meaning` ignores
--| comments (`meaningBlanksFirst`). The second run's leaf test gives `out`'s alphabet.
theorem slice1Formats ∀ (source: Text)
    (inGrammar: inGrammar1 source = True):
    ∃ (out: Text) (lexed lexedOut: Lexed) (file fileOut: SourceFile) => formatWithin1 source = Ok out
      ∧ lex source = Ok lexed
      ∧ parseFile lexed = Ok file
      ∧ lex out = Ok lexedOut
      ∧ parseFile lexedOut = Ok fileOut
      ∧ fileOut.meaning = file.meaning
      ∧ inGrammar1 out = True
      ∧ formatWithin1 out = Ok out :=
  let (out, formats) := formatAccepts1 source inGrammar
  let again := formatIdempotent1 source out formats
  let (before, after, parse1Source, parse1Out, _, means) := formatKeepsProgram1 source out formats
  match lexes: lex source, inGrammar with
    | Ok lexed, inGrammar =>
      match parses: parseFile lexed, inGrammar with
        | Err message, inGrammar => (Bool.falseNotTrue (Bool.andRight inGrammar)).impossible
        | Ok file, inGrammar =>
          let (settled, settles, alike, _) := settledParses1 lexed file parses (Bool.andRight inGrammar)
          let settledBefore: settled = before := Result.okInjective (Eq.trans settles.flipped parse1Source)
          let (lexedOut, parsedOut, accepted) := formatsOf out out again
          let (lexesOut, leavesOut, parsesOut, withinOut, _) := accepted
          let afterIs: after = parsedOut :=
            Result.okInjective (Eq.trans (rewrite lexesOut at parse1Out then parse1Out).flipped parsesOut)
          let (fileOut, outParses, outAlike, outGrammar) :=
            parseKeepsTokens1 lexedOut.settledOnce lexedOut parsedOut
              (settledOnceTokens lexedOut)
              parsesOut
              (fileGrammarOfWithin1 parsedOut.decls withinOut)
          let meaningOut: fileOut.meaning = file.meaning := calc fileOut.meaning
            _ = fileOut.withoutComments.meaning := (meaningBlanksFirst fileOut).flipped
            _ = parsedOut.withoutComments.meaning := rewrite outAlike
            _ = parsedOut.meaning := meaningBlanksFirst parsedOut
            _ = after.meaning := rewrite afterIs
            _ = before.meaning := means
            _ = settled.meaning := rewrite settledBefore
            _ = settled.withoutComments.meaning := (meaningBlanksFirst settled).flipped
            _ = file.withoutComments.meaning := rewrite alike
            _ = file.meaning := meaningBlanksFirst file
          let outInGrammar: inGrammar1 out = True :=
            rewrite lexesOut, outParses then
              Bool.andIntro (leavesAlphabetOfWithin1 lexedOut.leaves (Bool.andLeft leavesOut)) outGrammar
          (
            out,
            lexed,
            lexedOut,
            file,
            fileOut,
            formats,
            byComputing,
            parses,
            lexesOut,
            outParses,
            meaningOut,
            outInGrammar,
            again
          )

-- A source the theorems apply to (D3684).

--| A source with comments above, after and at the end of declarations, a value after a comment on the `:=` (so on the
--| next line), a tuple, a list, a call, a sign and an arrow.
def witnessSource: Text :=
  "-- top\ndef d: A -> B := f (a, -b) [1, 2] -- end\n\n\ndef e: C := -- after\n  g x\n-- last\n"

def witnessOut: Text := "-- top\ndef d: A -> B := f (a, -b) [1, 2] -- end\n\ndef e: C := -- after\n  g x\n-- last\n"

--| The top theorems' one hypothesis holds of `witnessSource`.
theorem witnessFormats: formatWithin1 witnessSource = Ok witnessOut := byComputing

--| `slice1Formats`' one hypothesis holds of `witnessSource`.
theorem witnessInGrammar: inGrammar1 witnessSource = True := byComputing

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
      && file.shaped
      && file.settled
      && file.lexical
      && file.commaFree
      && file.unreturned
      && file.decls.all Decl.unreturned
      && file.calmTop.within1
      && file.calmTop.commaFree
      && file.calmTop.printed1 == file.printed1
      && readsBack file.lexed.settled file

--| The layers' hypotheses and conclusions hold of `witnessSource`'s printed tree.
theorem witnessGoals: goalsHoldOn witnessSource = True := byComputing

--| `tidiedUnreturned1`'s and `tidiedDeclsUnreturned1`'s hypotheses hold of `witnessSource` (its `Formats1`), and so do
--| their conclusions.
theorem witnessUnreturned: ∃ (lexed: Lexed) (parsed: SourceFile) => parsed.tidy1.unreturned = True
      ∧ parsed.tidy1.decls.all Decl.unreturned = True :=
  match formatsOf witnessSource witnessOut witnessFormats with
    | Witness lexed (Witness parsed (lexes, leaves, parses, within, _)) =>
      Witness lexed
        (Witness parsed (
          tidiedUnreturned1 witnessSource lexed parsed lexes leaves parses within,
          tidiedDeclsUnreturned1 witnessSource lexed parsed lexes leaves parses within
        ))
