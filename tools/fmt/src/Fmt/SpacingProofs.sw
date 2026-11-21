--| `printedSpacing1` from what the declaration's document says touches (SW-4076, step 4 of tools/fmt/NOTES.md,
--| "Printed spacing"): `Std.Doc`'s `printTouches` takes the document's touches to the printed pieces, and
--| `Fmt.GlueProofs.printedGlued` takes those to the lexer's items.

namespace Fmt.SpacingProofs
import Std (Bool, Doc, Eq, List, Nat, Option, Text, byDecision)
import Std.Doc (..)
import Std.Doc.Proofs (Begun, Seam, Touch, Touches, printTouches, printedJoins, printedPieces, touchesOf)
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Item, Tok, Word, items)
import Syntax.LexProofs (Laid)
import Fmt (..)
import Fmt.GlueProofs (codeTouching, printedGlued)
import Fmt.JoinProofs (doc1Passes)
import Fmt.PrintLexProofs (AllGood, Follows, Printable, chronoOfPairs, goodOfChrono, pieceFold)
import Fmt.PrintHangProofs (pairsEnd)
import Fmt.SpellProofs (declSoundOfSettled, doc1Spells)
import Fmt.TreeJoinProofs (declJoins, declOperators, declPrintable, lexKind)
import Fmt.TokenProofs (declRealOfLexical)
import Fmt.OutputStatements (..)
import Fmt.GlueProofs (codeTouchingAppend)
import Fmt.JoinProofs (DeclJoins, WordJoins, Joinable)
import Fmt.CalmProofs (lambdaHugNone, matchedNone, plainDef, plainDefIs, valueElPlain)
import Fmt.TouchSteps (..)
import Fmt.TouchSeq (HugSteps, SeqSteps, eachAppend, hugFrom, spacedHugSteps, spacedSteps)
import Fmt.TouchProofs (ElSteps, callHugSteps, elFree, elSteps, wordLeafSteps)

theorem spacingAdmitsGlue ∀ (spacing: List Spacing) (found: List Item):
    spacingAdmits spacing found = admitsGlue spacing (found.map (item => item.glued)) :=
  match spacing, found with
    | [], [] | [_, .._] => byComputing
    | [first, ..rest], [] => byComputing
    | [first, ..rest], [item, ..later] => rewrite spacingAdmitsGlue rest later

--| Step 2's goal for one declaration: from the start of a line, its document lists its words touching as
--| `Decl.spacing` asks of its code words.
def SpacedTouches (decl: Decl) (doc: Doc): Prop :=
  Touches doc Begun [] (seam trace => admitsGlue decl.spacing (codeTouching (trace ++ seam.ending)) = True)

theorem allGoodAppend ∀ (kinds: Text → Syntax.Tok) (front back: List Text)
    (good: AllGood kinds front)
    (later: AllGood kinds back):
    AllGood kinds (front ++ back) :=
  match front, good with
    | [], _ => later
    | [text, ..rest], (first, others) => (first, allGoodAppend kinds rest back others later)

theorem allGoodReverse ∀ (kinds: Text → Syntax.Tok) (texts: List Text)
    (good: AllGood kinds texts):
    AllGood kinds texts.reverse :=
  match texts, good with
    | [], _ => byComputing
    | [text, ..rest], (first, others) =>
      rewrite List.reverseCons text rest then
        allGoodAppend kinds rest.reverse [text] (allGoodReverse kinds rest others) (first, byComputing)

--| A slice 1 declaration's printed items are spaced as `Decl.spacing` says, given that its document touches as the
--| spacing asks (`SpacedTouches`, step 2).
--|
--| Proof idea: `printTouches` gives the spacing of the printed pieces' touches; `printedJoins`, from `doc1Passes`
--| and `declPrintable` as `printLexes1` has them, gives that no text follows a comment on its line (`pairsEnd`) and
--| that every text is good (`goodOfChrono`), so `printedGlued` makes the items' glue those touches.
theorem printedSpacingOfTouches ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True)
    (spaced: ∀ (doc: Doc) => decl.doc1 = Some doc → SpacedTouches decl doc):
    spacingAdmits decl.spacing (items decl.leaves) = True :=
  match shows: decl.doc1 with
    | Some doc =>
      let sound := declSoundOfSettled decl within settled (declRealOfLexical decl within lexical)
      let (uniform, _, words) := doc1Spells decl doc within sound shows
      let joins :=
        doc1Passes lexKind decl doc within
          (declJoins decl within shaped sound lexical (declOperators decl within))
          shows
      let printable := declPrintable decl within sound lexical (declOperators decl within)
      let (_, every, pairs) :=
        printedJoins (Follows lexKind) (Printable lexKind) doc width uniform joins (rewrite words then printable)
      let texts := printedPieces doc width
      let chrono := chronoOfPairs (Follows lexKind) texts.reverse pairs
      let ordered := rewrite List.reverseReverse texts at chrono then chrono
      let good := goodOfChrono lexKind texts ordered every
      let touched: admitsGlue decl.spacing (codeTouching (touchesOf texts.reverse)) = True :=
        printTouches (touches => admitsGlue decl.spacing (codeTouching touches) = True) doc width (spaced doc shows)
      let glued := printedGlued lexKind texts (pairsEnd lexKind texts.reverse pairs) (allGoodReverse lexKind texts good)
      rewrite spacingAdmitsGlue decl.spacing (items (laidOf doc).leaves.reverse), glued then touched
    | None =>
      match decl, within, shows with
        | Definition [] header (Assigned colonEq value), _, never => cases

-- The definition's document.

--| A token that is no closer, free, then the printer stands after it.
theorem wordEndsSteps ∀ [word: Word] (around: Around) (key: Nat)
    (joins: WordJoins word):
    Steps (word.leaf around key) (Fits True Free) [Free] (Ends True) :=
  stepsTo (wordLeafSteps word around key Free joins (Inl byComputing)) (seam closed =>
    endsWeaker word.trails True (_ => byComputing) seam (closedEnds word.trails seam closed))

--| What follows a `:=`: the value below, or one of the layouts that keep its start on the line, each spacing the
--| value's words as `spacing` says.
--|
--| Proof idea: as `Fmt.JoinProofs.bodyAfterPasses`: `matchedNone`, `valueElPlain` and `lambdaHugNone` leave the
--| value's element; each option is it after a space or a line break (`OneLineBelow` included), or the call's hug
--| after a space (`callHugSteps`).
theorem bodySteps ∀ (value: Expr) (assign: Word) (around: Around) (semi: Bool)
    (within: value.within1 = True)
    (shaped: value.shaped = True)
    (lexical: value.lexical = True)
    (joinable: Joinable lexKind value)
    (steps: ElSteps value):
    Steps (bodyAfter value assign around semi).fst (Ends True) (value.spacing False) (Ends value.trails)
      ∧ Steps (bodyAfter value assign around semi).snd (Ends True) (value.spacing False) (Ends value.trails) :=
  let inside: Around := { around | hoisted = True }
  let spacing := value.spacing False
  let post := Ends value.trails
  let element: Steps (value.el around) (Fits True Free) spacing post :=
    elFree value around steps within shaped lexical joinable
  let afterGap: Steps (value.el around) (Gapped True) spacing post :=
    stepsFrom element (seam gapped => gappedFits byComputing gapped)
  let spacedStep: Steps (Doc.concat [Doc.text " ", value.el around]) (Ends True) spacing post :=
    stepsConcat _ (stepsTwo (Doc.text " ") (Ends True) (Gapped True) post (stepsSpace True) afterGap)
  let below: Steps (Nest 2 (Doc.concat [HardLine, value.el around])) (Ends True) spacing post :=
    stepsNest 2 _
      (stepsConcat _
        (stepsTwo HardLine
          (Ends True)
          (Fits True Free)
          post
          (stepsHard _ (seam ended => endsQuiet True seam ended) byComputing)
          element))
  let lowered: Steps (OneLineBelow (value.el around)) (Ends True) spacing post :=
    stepsOneLineBelow (Ends True) post (seam ended => endsQuiet True seam ended) byComputing element
  let hugs: HugSteps (value.callHug inside) (Gapped True) spacing post :=
    hugFrom
      (value.callHug inside)
      (Fits True Free)
      (Gapped True)
      spacing
      post
      (callHugSteps value inside within shaped lexical joinable)
      (seam gapped => gappedFits byComputing gapped)
  rewrite matchedNone value inside within,
      valueElPlain value around semi within,
      lambdaHugNone value semi inside (value.el around) within then
    match plain: assign.trails || value.noted || value.isBlock with
      | True => (below, below)
      | False => (
        below,
        stepsChoice (Flatten (Doc.concat [Doc.text " ", value.el around])) _ (Ends True) (
          stepsFlatten _ spacedStep,
          eachAppend
            (Ends True)
            spacing
            post
            (if value.opensBracket || (value.callHug inside).isSome then [OneLineBelow (value.el around)] else [])
            ((if value.opensBracket then [Doc.concat [Doc.text " ", value.el around]]
              else optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open])))
              ++ [Nest 2 (Doc.concat [HardLine, value.el around])])
            (match value.opensBracket || (value.callHug inside).isSome with
              | True => (lowered, byComputing)
              | False => byComputing)
            (eachAppend
              (Ends True)
              spacing
              post
              (if value.opensBracket then [Doc.concat [Doc.text " ", value.el around]]
               else optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open])))
              [Nest 2 (Doc.concat [HardLine, value.el around])]
              (match value.opensBracket with
                | True => (spacedStep, byComputing)
                | False => spacedHugSteps (value.callHug inside) spacing post hugs)
              (below, byComputing))
        )
      )

--| A definition's type: below the `:` if a comment follows it, else after a space.
theorem typedSteps ∀ (trails: Bool) (typeDoc: Doc) (spacing: List Spacing)
    (typeSteps: Steps typeDoc (Fits True Free) spacing (Ends True)):
    StepsAll
      (if trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc])
      (Ends True)
      spacing
      (Ends True) :=
  match trails with
    | True =>
      stepsLast
        (stepsNest 4 _
          (stepsConcat _
            (stepsTwo HardLine
              (Ends True)
              (Fits True Free)
              (Ends True)
              (stepsHard _ (seam ended => endsQuiet True seam ended) byComputing)
              typeSteps)))
    | False =>
      stepsTwo
        (Doc.text " ")
        (Ends True)
        (Gapped True)
        (Ends True)
        (stepsSpace True)
        (stepsNest 4 _ (stepsFrom typeSteps (seam gapped => gappedFits byComputing gapped)))

--| A plain definition: `def`, the name, `:`, the type, `:=` and the value, from where a free word may start, each
--| token free but as the type's and value's `spacing` say.
--|
--| Proof idea: as `Fmt.JoinProofs.plainDefPasses`: the header's tokens each after the one before (`spacedSteps`),
--| the type after a space or a line break (`typedSteps`), then the `:=` after a space and the body in either of
--| `IfBroken`'s forms (`bodySteps`).
theorem plainDefSteps ∀ (keyword: Comments) (name: Word) (colon: Comments) (result: Expr)
    (colonEq: Comments) (value: Expr)
    (resultWithin: result.within1 = True)
    (resultShaped: result.shaped = True)
    (resultLexical: result.lexical = True)
    (valueWithin: value.within1 = True)
    (valueShaped: value.shaped = True)
    (valueLexical: value.lexical = True)
    (keywordJoins: WordJoins (fixedWord "def" keyword))
    (nameJoins: WordJoins name)
    (colonJoins: WordJoins (fixedWord ":" colon))
    (resultJoins: Joinable lexKind result)
    (assignJoins: WordJoins (fixedWord ":=" colonEq))
    (valueJoins: Joinable lexKind value) (elements: ∀ (expr: Expr) => ElSteps expr):
    Steps
      (plainDef keyword name colon result colonEq value)
      (Fits True Free)
      ([Free, Free, Free] ++ result.spacing False ++ [Free] ++ value.spacing False)
      (Ends value.trails) :=
  let start: Around := { before = False, hoisted = True, item = False, at = 0, inArm = False }
  let keywordWord := fixedWord "def" keyword
  let colonWord := fixedWord ":" colon
  let assign := fixedWord ":=" colonEq
  let colonAround := start.next (trailsBack [name, keywordWord]) 2
  let typeDoc := result.el (start.next colonWord.trails 3)
  let headDoc := spaced (headDocs start [keywordWord, name])
  let typed := if colonWord.trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc]
  let headerDoc := Doc.concat ([headDoc, colonWord.leaf colonAround 2] ++ typed)
  let typeSteps: Steps typeDoc (Fits True Free) (result.spacing False) (Ends True) :=
    stepsTo
      (elFree result
        (start.next colonWord.trails 3)
        (elements result)
        resultWithin
        resultShaped
        resultLexical
        resultJoins)
      (seam ended => endsWeaker result.trails True (_ => byComputing) seam ended)
  let headSteps: Steps headDoc (Fits True Free) [Free, Free] (Ends True) :=
    spacedSteps
      [keywordWord.leaf start 0, name.leaf (start.next keywordWord.trails 1) 1]
      [[Free], [Free]]
      (Fits True Free)
      (Ends True)
      (
        wordEndsSteps start 0 keywordJoins,
        stepsFrom (wordEndsSteps (start.next keywordWord.trails 1) 1 nameJoins) (seam gapped =>
          gappedFits byComputing gapped)
      )
  let colonSteps: Steps (colonWord.leaf colonAround 2) (Ends True) [Free] (Ends True) :=
    stepsFrom (wordEndsSteps colonAround 2 colonJoins) (seam ended => endsFits True seam ended)
  let headerSteps: Steps headerDoc (Fits True Free) [Free, Free, Free, ..result.spacing False] (Ends True) :=
    stepsConcat _
      (stepsCons headDoc
        [colonWord.leaf colonAround 2, ..typed]
        (Fits True Free)
        (Ends True)
        (Ends True)
        headSteps
        (stepsCons
          (colonWord.leaf colonAround 2)
          typed
          (Ends True)
          (Ends True)
          (Ends True)
          colonSteps
          (typedSteps colonWord.trails typeDoc (result.spacing False) typeSteps)))
  let around := start.next assign.trails (4 + result.size)
  let body := bodyAfter value assign around False
  let (belowSteps, choiceSteps) :=
    bodySteps value assign around False valueWithin valueShaped valueLexical valueJoins (elements value)
  let assignLeaf := assign.leaf (start.next result.trails (3 + result.size)) (3 + result.size)
  let headWords := [keywordWord, name]
  let inside :=
    (headWords.reverse.drop 1 |> .any Word.trails)
      || colonWord.trails
      || (result.words.reverse.drop 1 |> .any Word.trails)
      || (value.layoutBody && (lastCode headWords).trails)
  let breaks := headerDoc.forcesBreak || inside
  let assignSteps: Steps assignLeaf (Gapped True) [Free] (Ends True) :=
    stepsFrom (wordEndsSteps (start.next result.trails (3 + result.size)) (3 + result.size) assignJoins) (seam gapped =>
      gappedFits byComputing gapped)
  stepsSpacing byComputing
    (stepsConcat _
      (stepsCons
        (IdGroup 0 headerDoc breaks)
        [Doc.text " ", assignLeaf, IfBroken 0 body.fst body.snd]
        (Fits True Free)
        (Ends True)
        (Ends value.trails)
        (stepsIdGroup 0 breaks _ _ headerSteps)
        (stepsCons
          (Doc.text " ")
          [assignLeaf, IfBroken 0 body.fst body.snd]
          (Ends True)
          (Gapped True)
          (Ends value.trails)
          (stepsSpace True)
          (stepsTwo assignLeaf
            (Gapped True)
            (Ends True)
            (Ends value.trails)
            assignSteps
            (stepsIfBroken 0 _ _ belowSteps choiceSteps)))))

--| A document that steps from a line start to a seam where no code waits lists its words as the spacing asks.
theorem spacedOfSteps ∀ (decl: Decl) (doc: Doc) (post: Seam → Prop)
    (steps: Steps doc (Fits True Free) decl.spacing post) (quiet: ∀ (seam: Seam) => post seam → Quiet seam):
    SpacedTouches decl doc :=
  steps Begun []
    (seam trace => admitsGlue decl.spacing (codeTouching (trace ++ seam.ending)) = True)
    byComputing
    (after added ended admits =>
      let glue: admitsGlue decl.spacing (codeTouching (added ++ after.ending)) = True :=
        rewrite codeTouchingAppend added after.ending,
            endingQuiet after (quiet after ended),
            List.appendNil (codeTouching added) then
          admits
      glue)

--| A slice 1 definition's document touches as `Decl.spacing` asks, given that every expression's element does
--| (`elSteps`).
--|
--| Proof idea: `doc1` is `plainDef` (`plainDefIs`, as `Fmt.JoinProofs.doc1Passes` has it), which `plainDefSteps`
--| steps from a line start to where only a comment the value ends with may wait; `spacedOfSteps` takes that to the
--| touches.
theorem declSpacedTouches ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True)
    (elements: ∀ (expr: Expr) => ElSteps expr) (doc: Doc)
    (shows: decl.doc1 = Some doc):
    SpacedTouches decl doc :=
  let sound := declSoundOfSettled decl within settled (declRealOfLexical decl within lexical)
  let joins := declJoins decl within shaped sound lexical (declOperators decl within)
  match decl, joins with
    | Definition [] header (Assigned colonEq value), (keywordJoins, nameJoins, colonJoins, resultJoins, assignJoins,
        valueJoins) =>
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
          } =>
          rewrite <- Option.someInjective shows, plainDefIs keyword name colon result colonEq value then
            spacedOfSteps
              (Definition []
                {
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
                }
                (Assigned colonEq value))
              (plainDef keyword name colon result colonEq value)
              (Ends value.trails)
              (plainDefSteps keyword name colon result colonEq value
                (Bool.andRight (Bool.andLeft within))
                (Bool.andLeft shaped)
                (Bool.andLeft (Bool.andRight lexical))
                (Bool.andRight within)
                (Bool.andRight shaped)
                (Bool.andRight (Bool.andRight lexical))
                keywordJoins
                nameJoins
                colonJoins
                resultJoins
                assignJoins
                valueJoins
                elements)
              (seam ended => endsQuiet value.trails seam ended)

--| A slice 1 declaration's printed items are spaced as `Decl.spacing` says: each glued to the item before exactly
--| where its spacing is `Glued`, and apart where it is `Apart` (the statement `Fmt.OutputStatements` describes).
theorem printedSpacing1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True):
    spacingAdmits decl.spacing (items decl.leaves) = True :=
  printedSpacingOfTouches decl within shaped settled lexical (doc shows =>
    declSpacedTouches decl within shaped settled lexical elSteps doc shows)

--| `def d: A := f -x`.
def signDecl: Decl :=
  Definition []
    {
      exportKeyword = None,
      opaqueKeyword = None,
      kind = DefPlain,
      keyword = Comments.none,
      name = fixedWord "d" Comments.none,
      forallKeyword = None,
      params = [],
      colon = Comments.none,
      result = Atom Upper (fixedWord "A" Comments.none),
      decreasingClause = None,
      unfoldingClause = None
    }
    (Assigned Comments.none
      (App (Atom Lower (fixedWord "f" Comments.none)) [
        Prefix (fixedWord "-" Comments.none) (Atom Lower (fixedWord "x" Comments.none))
      ]))

theorem signSpacedTouches: SpacedTouches signDecl (signDecl.doc1.getOrElse Nothing) := byDecision

--| `printedSpacingOfTouches` applies: `f -x`'s sign apart from `f` and glued to `x`.
theorem printedSpacingExample: spacingAdmits signDecl.spacing (items signDecl.leaves) = True :=
  printedSpacingOfTouches signDecl byComputing byComputing byComputing byComputing (doc shows =>
    let same: signDecl.doc1.getOrElse Nothing = doc := Eq.cong (found => found.getOrElse Nothing) shows
    rewrite <- same then signSpacedTouches)
