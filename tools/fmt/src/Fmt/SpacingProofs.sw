--| `printedSpacing1` from what the declaration's document says touches (SW-4076, step 4 of tools/fmt/NOTES.md,
--| "Printed spacing"): `Std.Doc`'s `printTouches` takes the document's touches to the printed pieces, and
--| `Fmt.GlueProofs.printedGlued` takes those to the lexer's items.

namespace Fmt.SpacingProofs
import Std (Bool, Doc, Eq, List, Nat, Option, Text)
import Std.Doc.Proofs (Begun, Seam, Touch, Touches, printTouches, printedJoins, printedPieces, touchesOf)
import Syntax (Decl, DefBody, Item, items)
import Syntax.Proofs (Laid)
import Fmt (..)
import Fmt.GlueProofs (codeTouching, printedGlued)
import Fmt.JoinProofs (doc1Passes)
import Fmt.PrintLexProofs (AllGood, Follows, Printable, chronoOfPairs, goodOfChrono, pieceFold)
import Fmt.PrintHangProofs (pairsEnd)
import Fmt.SpellProofs (declSoundOfSettled, doc1Spells)
import Fmt.TreeJoinProofs (declJoins, declOperators, declPrintable, lexKind)
import Fmt.TokenProofs (declRealOfLexical)
import Fmt.OutputStatements (..)

--| Each glue as its spacing says, the two lists alike in length: `spacingAdmits` of the items' `glued`.
def admitsGlue: List Spacing → List Bool → Bool
  | [], [] => True
  | [spacing, ..rest], [glued, ..later] => spacing.admits glued && admitsGlue rest later
  | _, _ => False

theorem spacingAdmitsGlue ∀ (spacing: List Spacing) (found: List Item):
    spacingAdmits spacing found = admitsGlue spacing (found.map (item => item.glued)) :=
  match spacing, found with
    | [], [] => byComputing
    | [], [item, ..later] => byComputing
    | [first, ..rest], [] => byComputing
    | [first, ..rest], [item, ..later] => rewrite spacingAdmitsGlue rest later

--| Step 2's goal for one declaration: from the start of a line, its document lists its words touching as
--| `Decl.spacing1` asks of its code words.
def SpacedTouches (decl: Decl) (doc: Doc): Prop :=
  Touches doc Begun [] (seam trace => admitsGlue decl.spacing1 (codeTouching (trace ++ seam.ending)) = True)

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

--| A slice 1 declaration's printed items are spaced as `Decl.spacing1` says, given that its document touches as the
--| spacing asks (`SpacedTouches`, step 2).
--|
--| Proof idea: `printTouches` gives the spacing of the printed pieces' touches; `printedJoins`, from `doc1Passes`
--| and `declPrintable` as `printLexes1` has them, gives that no text follows a comment on its line (`pairsEnd`) and
--| that every text is good (`goodOfChrono`), so `printedGlued` makes the items' glue those touches.
theorem printedSpacingOfTouches ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (spaced: ∀ (doc: Doc) => decl.doc1 = Some doc → SpacedTouches decl doc):
    spacingAdmits decl.spacing1 (items decl.leaves1) = True :=
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
      let touched: admitsGlue decl.spacing1 (codeTouching (touchesOf texts.reverse)) = True :=
        printTouches (touches => admitsGlue decl.spacing1 (codeTouching touches) = True) doc width (spaced doc shows)
      let glued := printedGlued lexKind texts (pairsEnd lexKind texts.reverse pairs) (allGoodReverse lexKind texts good)
      rewrite spacingAdmitsGlue decl.spacing1 (items (laidOf doc).leaves.reverse), glued then touched
    | None =>
      match decl, within, shows with
        | Definition [] header (Assigned colonEq value), _, never => cases
