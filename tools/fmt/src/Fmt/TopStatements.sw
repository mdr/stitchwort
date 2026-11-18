--| Slice 1's two top theorems (SW-4079; docs/reviews/SW-4078-slice1-stock-take.md, recommendation 1), about the
--| driver `formatWithin1`:
--|
--| - `formatKeepsProgram1`: what it prints parses back, to `calmTop` of the tree it printed, with the source's
--|   `meaning`.
--| - `formatIdempotent1`: formatting what it prints gives the same text.
--|
--| Both are proved from the layers' theorems, with every piece not yet proved stated as an open goal: here
--| (`declElementsOneLine1`, `tidiedDeclsUnreturned1`, `printedSpelledPlain1` and the `calmTop` facts),
--| in `Fmt.TopReadBack` (read-back), and `tidiedUnreturned1` in `Fmt.SettleOutputProofs`. `stitchwort goal` lists what
--| is left. One of them, `printedSplit1`, is false today of a declaration with a binary operator, which read-back
--| doesn't read yet (SW-4071).
--|
--| What slice 1 covers: files of `def name: Type := value` with no parameters, the type and value names, numerals,
--| brackets, tuples, lists, calls, `-`, `!`, `¬`, binary operators and `->`, with comments and blank lines; the
--| driver refuses anything else, and (D3685, for now) a declaration that doesn't print on one line.

namespace Fmt.TopStatements
import Std (Bool, Eq, List, Nat, Option, Result, Text, Void)
import Syntax (..)
import Fmt (..)
import Fmt.Driver1 (..)
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
import Fmt.DeclFactsProofs (DeclElements, declHangsOf, printedHangs1)
import Fmt.OneLineStatements (edgeElements1, edgeQuietOneLine1)
import Fmt.TreeJoinProofs (lexKind, printLexes1Tree)
import Fmt.TokenProofs (declRealOfLexical)
import Fmt.SpellProofs (declSoundOfSettled)
import Syntax.ParseWalk (parseLexical1, parseShaped1)
import Syntax.ParseWalkOthers (frameRest, parseSettledSourceProved)
import Syntax.GoodItemProofs (settledGood, spelledPlain1)
import Syntax.SettleProofs (alphabet1, plain1, settledKeepsTokens, tokens)
import Syntax.SettleBareProofs (settledOnceNone)

-- Open goals beyond read-back.

--| `declElementsOneLine1` (open; the stock take's U5 and SW-4058, for one-line declarations): a slice 1 declaration
--| that prints on one line meets `DeclElements`, the element facts `printedHangs` and `printedStands1` take.
--| `quietElements` gives them when the type and value hold no comment (`DeclQuiet`); on one line they may still hold
--| a trailing comment on the type's last token (the `:=` then starts the next line), one above the value's first
--| token (or after the `:=`) and one after the value's last. "Last" counts no closers: a comment after the last
--| other word, with only closers after it in the type or value, prints after them on the line (`def x: F (a -- c\n)
--| := b` prints `def x: F (a) -- c\n  :=\n  b`; test in `Fmt.Tests`), so the type's `ElHangs` and the value's
--| `BodyLays` must allow a comment held across closers (SW-4088 report).
theorem declElementsOneLine1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (oneLine: decl.oneLine1 = True):
    DeclElements lexKind decl :=
  edgeElements1 decl within shaped settled lexical (edgeQuietOneLine1 decl within shaped settled lexical oneLine)

--| `tidiedDeclsUnreturned1` (open; the stock take's U6): no comment of the tree the driver prints ends in a carriage
--| return or a space, above or after any word of any declaration. `printedStands1` takes it. Its route is
--| `tidiedUnreturned1`'s: the lexer strips both, rule N and the parser move comments without changing their texts,
--| and the passes keep every word's comments.
theorem tidiedDeclsUnreturned1 ∀ (source: Text) (lexed: Lexed) (tidied: Tidied)
    (lexes: lex source = Ok lexed)
    (tidy: lexed.tidied = Ok tidied):
    tidied.fourth.decls.all Decl.unreturned1 = True :=
  ?

--| `printedSpelledPlain1` (open; **not in the stock take's map**): the output's names and numerals are spelled
--| plainly, so the second run passes the driver's `spelledPlain1` test. From `printedTokens1` (each printed token's
--| text is a word's, its kind the lexer's) and `lexical1` with `within1` (each name or numeral of the tree is spelled
--| plainly, `textSpells1`).
theorem printedSpelledPlain1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped1 = True)
    (settled: file.settled1 = True)
    (lexical: file.lexical1 = True):
    spelledPlain1 file.lexed1.leaves = True :=
  ?

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

-- `calmTop` keeps `calm`'s facts: `calmTopWithin`, `calmTopCommaFree`, `calmTopOneLine`, `calmTopPrints` and
-- `calmTopMeans` are in `Fmt.CalmTopProofs`.

-- The driver, both ways.

--| What `formatWithin1` accepting a source says: it lexes, its leaves pass the tests, it parses to a tree within the
--| slice, that tree's tidied form prints on one line, and the output is that form printed.
def Formats1 (source out: Text) (lexed: Lexed) (parsed: SourceFile): Prop :=
  lex source = Ok lexed
    ∧ leavesWithin1 lexed.leaves = True
    ∧ parseFile lexed.settledOnce = Ok parsed
    ∧ parsed.within1 = True
    ∧ parsed.tidy1.oneLine1 = True
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
                | True, formats =>
                  match oneLine: parsed.tidy1.oneLine1, formats with
                    | False, formats => (Result.errNotOk formats).impossible
                    | True, formats =>
                      (lexed, parsed, lexes, leaves, parses, within, oneLine, (Result.okInjective formats).flipped)

theorem formatsFrom ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (leaves: leavesWithin1 lexed.leaves = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (within: parsed.within1 = True)
    (oneLine: parsed.tidy1.oneLine1 = True):
    formatWithin1 source = Ok parsed.tidy1.printed1 :=
  rewrite lexes, leaves, parses, within, oneLine

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
  let spelled := Bool.andLeft (Bool.andRight leaves)
  let plain := Bool.andRight (Bool.andRight leaves)
  let good := settledGood source lexed lexes alphabet spelled plain
  let shaped := parseShaped1 frameRest lexed.settledOnce parsed good parses within
  let lexical := parseLexical1 frameRest lexed.settledOnce parsed good parses within
  let settled := parseSettledSourceProved source lexed parsed lexes alphabet spelled plain parses within
  rewrite tidyComma1 parsed within then
    (
      commaKeepsWithin parsed within,
      rewrite commaKeepsShaped parsed within then shaped,
      rewrite commaKeepsSettled parsed within then settled,
      rewrite commaKeepsLexical parsed within then lexical,
      commaBare parsed within
    )

-- Line breaks and comments of the printed declarations.

theorem declHangsOneLine ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (oneLine: decl.oneLine1 = True):
    hangs decl.leaves1 = True ∧ (decl.unreturned1 = True → decl.stands1 = True) :=
  let sound := declSoundOfSettled decl within settled (declRealOfLexical decl within lexical)
  let elements := declElementsOneLine1 decl within shaped settled lexical oneLine
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
    (oneLine: decls.all Decl.oneLine1 = True)
    (unreturned: decls.all Decl.unreturned1 = True)
    (each: ∀ (decl: Decl) => decl.within1 = True
      → decl.shaped1 = True
      → decl.settled1 = True
      → decl.lexical1 = True
      → decl.oneLine1 = True
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
          (Bool.andLeft oneLine)
          (Bool.andLeft unreturned))
        (declsAll rest p
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight settled)
          (Bool.andRight lexical)
          (Bool.andRight oneLine)
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
    (oneLine: file.oneLine1 = True)
    (declsUnreturned: file.decls.all Decl.unreturned1 = True)
    (unreturned: file.unreturned1 = True):
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
      oneLine
      declsUnreturned
      (decl w s t l o u => (declHangsOneLine decl w s t l o).left)
  let stood: file.stood1 = True :=
    declsAll file.decls Decl.stands1 within shaped declsSettled lexical oneLine declsUnreturned (decl w s t l o u =>
      (declHangsOneLine decl w s t l o).right u)
  let once := settledOnceNone file.lexed1 (printedNoLast1 file within shaped settled lexical)
  let (words, ends) := printedSettle1 file within shaped settled lexical hung stood unreturned
  (
    printedFileLexes1 file within shaped settled lexical,
    rewrite once then
      readsBackFile1 file file.lexed1.settled within shaped settled lexical commaFree oneLine hung
        (settledKeepsTokens file.lexed1)
        words
        ends
        declsReadBack
  )

--| The facts of the tree the driver prints for an accepted source.
def Printed1 (source: Text) (lexed: Lexed) (parsed: SourceFile): Prop :=
  TreeFacts parsed.tidy1
    ∧ parsed.tidy1.oneLine1 = True
    ∧ lex parsed.tidy1.printed1 = Ok parsed.tidy1.lexed1
    ∧ parseFile parsed.tidy1.lexed1.settledOnce = Ok parsed.tidy1.calmTop

theorem printedOf ∀ (source out: Text) (lexed: Lexed) (parsed: SourceFile)
    (formats: Formats1 source out lexed parsed):
    Printed1 source lexed parsed :=
  let (lexes, leaves, parses, within, oneLine, _) := formats
  let facts := tidiedFacts source lexed parsed lexes leaves parses within
  let tidied: Tidied := {
    first = parsed.withForall,
    second = parsed.withForall.withoutTrailingCommas,
    third = parsed.withForall.withoutTrailingCommas.withoutSpareBrackets,
    fourth = parsed.tidy1
  }
  let tidy: lexed.tidied = Ok tidied := rewrite parses
  let unreturned := tidiedUnreturned1 source lexed tidied lexes tidy
  let declsUnreturned := tidiedDeclsUnreturned1 source lexed tidied lexes tidy
  let (lexOut, parseOut) := outputParses1 parsed.tidy1 facts oneLine declsUnreturned unreturned
  (facts, oneLine, lexOut, parseOut)

-- The top theorems.

--| **The same program.** If slice 1's driver formats `source` to `out`, then both parse (as the driver parses: lexed,
--| settled once, `parseFile`), `out` to `calmTop` of the tidied tree of `source`, and the two trees have the same
--| `meaning`.
--|
--| `calmTop` is `calm` (each word's blank-line flag kept only where the rules print a blank line) with the file's first
--| flag cleared; it changes comments' flags only, so `meaning`, which reads no comment, is kept. Slice 1 excludes
--| everything `formatWithin1` refuses: a token outside the slice's alphabet, a name or numeral not spelled plainly, a
--| source that isn't `plain1`, one that doesn't lex or parse, a tree outside `within1`, and (D3685, for now) a
--| declaration that doesn't print on one line.
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
  let (lexes, leaves, parses, within, oneLine, outIs) := accepted
  let (facts, _, lexOut, parseOut) := printedOf source out lexed parsed accepted
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
--| Proof idea: the second run lexes `out` to the printed tree's leaves, which pass the alphabet
--| (`printedAlphabet1`), are spelled plainly (`printedSpelledPlain1`) and are `plain1` (`printedPlain1`), and parse
--| to `calmTop` of the printed tree (`printedOf`); that tree is within the slice and has no last comma, so tidying
--| changes nothing (`tidySame1`); it prints on one line, and prints `out` (`calmTopPrints`).
theorem formatIdempotent1 ∀ (source out: Text) (formats: formatWithin1 source = Ok out): formatWithin1 out = Ok out :=
  let (lexed, parsed, accepted) := formatsOf source out formats
  let (_, _, _, _, oneLine, outIs) := accepted
  let (facts, _, lexOut, parseOut) := printedOf source out lexed parsed accepted
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
      oneLine
      (tidiedDeclsUnreturnedOf source out lexed parsed accepted)
      (decl w s t l o u => (declHangsOneLine decl w s t l o).left)
  let leaves: leavesWithin1 file.lexed1.leaves = True :=
    Bool.andIntro
      (printedAlphabet1 file within shaped settled lexical)
      (Bool.andIntro
        (printedSpelledPlain1 file within shaped settled lexical)
        (printedPlain1 file within shaped settled lexical hung))
  let topWithin := calmTopWithin file within
  let same := tidySame1 file.calmTop topWithin (calmTopCommaFree file within commaFree)
  let topOneLine: file.calmTop.tidy1.oneLine1 = True := rewrite same then calmTopOneLine file within lexical oneLine
  let again := formatsFrom out file.lexed1 file.calmTop (rewrite outIs then lexOut) leaves parseOut topWithin topOneLine
  rewrite same, calmTopPrints file within lexical at again then
    Eq.trans again (Eq.cong (text => (Ok text: Result Text Text)) outIs.flipped)

--| The declarations' comments of an accepted source's printed tree end in neither a carriage return nor a space.
theorem tidiedDeclsUnreturnedOf ∀ (source out: Text) (lexed: Lexed) (parsed: SourceFile)
    (formats: Formats1 source out lexed parsed):
    parsed.tidy1.decls.all Decl.unreturned1 = True :=
  let (lexes, _, parses, _, _, _) := formats
  let tidied: Tidied := {
    first = parsed.withForall,
    second = parsed.withForall.withoutTrailingCommas,
    third = parsed.withForall.withoutTrailingCommas.withoutSpareBrackets,
    fourth = parsed.tidy1
  }
  tidiedDeclsUnreturned1 source lexed tidied lexes (rewrite parses)

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

--| What the open goals take and give, run on a source's printed tree: the tree facts and one-line test their
--| hypotheses ask, and each conclusion that is a test (the `calmTop` facts, the comments without returns, the output
--| spelled plainly, and read-back in file form, compared as `OutputStatements.readsBack` does).
def goalsHoldOn (source: Text): Bool := match tidiedOf source with
  | None => False
  | Some file =>
    file.within1
      && file.shaped1
      && file.settled1
      && file.lexical1
      && file.commaFree
      && file.oneLine1
      && file.unreturned1
      && file.decls.all Decl.unreturned1
      && spelledPlain1 file.lexed1.leaves
      && file.calmTop.within1
      && file.calmTop.commaFree
      && file.calmTop.oneLine1
      && file.calmTop.printed1 == file.printed1
      && readsBack file.lexed1.settled file

--| The open goals' hypotheses and conclusions hold of `witnessSource`'s printed tree.
theorem witnessGoals: goalsHoldOn witnessSource = True := byComputing
