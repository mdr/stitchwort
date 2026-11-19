--| Trailing-comment facts of a slice 1 expression's tokens (SW-4099): the tokens' trails (`atomTrailsIs`, `infixTrails`,
--| `prefixTrails`, `lastTrailsIs`) and the lexical facts of the last token (`lastLexical`, `lastWithin`).

namespace Fmt.EdgeHangProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Syntax (Comments, Expr, InfixKind, Tok, Word)
import Std.Doc.Proofs (..)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.AppHangProofs (ArgsHang, HangsFor, appElHangs, argAround, lastArg)
import Fmt.ChainHangProofs (HangsAt, PairFacts, arrowChainHangs, binaryChainHangs)
import Fmt.BracketHangProofs (
  ItemsHang,
  bracketTrails,
  groupedBracketHangs,
  lastTrails,
  listHangs,
  tupleHangs,
  tupleTrails
)
import Fmt.ExprHangProofs (..)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (arrowListed, lexKind)
import Fmt.TrailsProofs (Coded, appTrails, itemsBack, parenTrails, trailsBackCoded)
import Fmt.DeclFactsProofs (leadNotCloser, notesOfWord, trailsOfSound)
import Fmt.OneLineStatements (..)
import Fmt.EdgeKeyProofs (..)

-- What an edge-quiet expression trails.

theorem codedSnocLead ∀ (front: List Word) (last: Word)
    (code: isCloserText last.text = False):
    Coded (front ++ [last]) = True :=
  match front with
    | [] => rewrite code
    | [word, ..rest] =>
      match isCloserText word.text with
        | True => codedSnocLead rest last code
        | False => byComputing

--| A slice 1 expression read back has a token that is no closer: its first.
theorem codedLex ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True):
    Coded expr.words.reverse = True :=
  let (rest, words) := wordsLead expr within
  rewrite words, List.reverseCons expr.lead rest then
    codedSnocLead rest.reverse expr.lead (leadNotCloser expr within lexical)

theorem atomTrailsIs ∀ (kind: Syntax.Tok) (word: Word): (Atom kind word).trails = word.trails :=
  rewrite Bool.andFalse (isCloserText word.text), Bool.orFalse word.trails

--| A chain trails as its right operand does.
theorem infixTrails ∀ (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr)
    (code: Coded right.words.reverse = True):
    (Infix kind left operator right).trails = right.trails :=
  rewrite List.reverseAppend left.words [operator, ..right.words],
      List.reverseCons operator right.words,
      List.appendAssoc right.words.reverse [operator] left.words.reverse,
      trailsBackCoded right.words.reverse ([operator] ++ left.words.reverse) code

--| A sign trails as its operand does.
theorem prefixTrails ∀ (operator: Word) (operand: Expr)
    (code: Coded operand.words.reverse = True):
    (Prefix operator operand).trails = operand.trails :=
  rewrite List.reverseCons operator operand.words, trailsBackCoded operand.words.reverse [operator] code

theorem lastWithin ∀ (argument: Expr) (rest: List Expr)
    (within: allWithin1 [argument, ..rest] = True):
    (lastArg argument rest).within1 = True :=
  match rest with
    | [] => Bool.andLeft within
    | [next, ..more] => lastWithin next more (Bool.andRight within)

theorem lastLexical ∀ (argument: Expr) (rest: List Expr)
    (lexical: allLexical1 [argument, ..rest] = True):
    (lastArg argument rest).lexical1 = True :=
  match rest with
    | [] => Bool.andLeft lexical
    | [next, ..more] => lastLexical next more (Bool.andRight lexical)

--| The last of items trails as the last item does.
theorem lastTrailsIs ∀ (seat: Bool) (item: Expr) (rest: List Expr):
    lastTrails seat [item, ..rest] = (lastArg item rest).trails :=
  match rest with
    | [] => byComputing
    | [next, ..more] => lastTrailsIs item.trails next more

--| The code before a slice 1 bracket's closer ends with a comment when its last item does, or its opener with none.
theorem edgeCloseBefore ∀ (open: Word) (items: List Expr) (close: Word)
    (opens: isCloserText open.text = False)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (trails: lastTrails open.trails items = True):
    (ListOf open items False close).trailsBeforeClose = True :=
  rewrite List.reverseSnoc [open, ..itemsWords items] close, List.reverseCons open (itemsWords items) then
    match items, within, lexical, trails with
      | [], _, _, trails => rewrite trails
      | [item, ..rest], within, lexical, trails =>
        let (front, back) := itemsBack item rest
        let code := codedLex (lastArg item rest) (lastWithin item rest within) (lastLexical item rest lexical)
        rewrite back,
            List.appendAssoc (lastArg item rest).words.reverse front [open],
            trailsBackCoded (lastArg item rest).words.reverse (front ++ [open]) code,
            <- lastTrailsIs open.trails item rest then
          trails

--| An element's facts, its trailing comment named by an equation.
theorem trailsSwap ∀ (kinds: Text → Tok) (doc: Doc) (indent column: Nat)
    (before from to: Bool) (start: Nat → Place → Option Nat)
    (same: from = to)
    (el: ElHangs kinds doc indent column before from start):
    ElHangs kinds doc indent column before to start :=
  rewrite <- same then el
