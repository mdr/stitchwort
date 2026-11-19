--| Each edge-quiet slice 1 expression (`Expr.edgeQuiet1`) hangs as an element (SW-4099): `leadFacts`' induction
--| (`Fmt.ExprHangProofs`) again, its invariant (`EdgeFacts`) trailing what the expression does, `expr.trails`, in
--| place of `False`. The rule-level lemmas already carry a part's trailing comment past the closers after it; what
--| is new is the last item's and last argument's facts (`edgeItemsHang`, `edgeArgsHang`, `edgeLastHangs`,
--| `edgeHugFacts`), the keys (`Fmt.EdgeKeyProofs.edgeKeys`), and the equations between what each rule says its node
--| trails and `Expr.trails` (`Fmt.TrailsProofs`, `infixTrails`, `prefixTrails`).
--|
--| A later token with comments above it (SW-4082) would add `startFor expr.noted` to the same invariant.

namespace Fmt.EdgeHangProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Syntax (Comments, Expr, InfixKind, Tok, Word)
import Std.Doc.Proofs (..)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.AppHangProofs (ArgsHang, Hangs, HangsFor, appElHangs, argAround, lastArg)
import Fmt.ChainHangProofs (HangsAt, LinkFacts, PairFacts, arrowChainHangs, binaryChainHangs, runFactsOf)
import Fmt.BracketHangProofs (
  ItemsHang,
  elItemHangs,
  bracketTrails,
  groupedBracketHangs,
  lastTrails,
  listHangs,
  parenElHangs,
  tupleHangs,
  tupleTrails
)
import Fmt.ExprHangProofs (..)
import Fmt.QuietKeyProofs (quietKeys)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (arrowListed, lexKind)
import Fmt.TrailsProofs (Coded, appTrails, itemsBack, parenTrails, trailsBackCoded)
import Fmt.DeclFactsProofs (leadNotCloser, notesOfWord, trailsOfSound)
import Fmt.OneLineStatements (..)
import Fmt.EdgeKeyProofs (..)

-- What an edge-quiet expression trails.

--| A token with no comment after it.
def Word.untrailed1 (word: Word): Bool := !word.trails

theorem untrailedAppend ∀ (front back: List Word)
    (first: front.all Word.untrailed1 = True)
    (second: back.all Word.untrailed1 = True):
    (front ++ back).all Word.untrailed1 = True :=
  match front with
    | [] => second
    | [word, ..rest] => rewrite Bool.andLeft first, untrailedAppend rest back (Bool.andRight first) second

theorem untrailedReverse ∀ (words: List Word)
    (all: words.all Word.untrailed1 = True):
    words.reverse.all Word.untrailed1 = True :=
  match words with
    | [] => byComputing
    | [word, ..rest] =>
      rewrite List.reverseCons word rest then
        untrailedAppend rest.reverse [word] (untrailedReverse rest (Bool.andRight all)) (rewrite Bool.andLeft all)

theorem quietUntrailed ∀ (words: List Word) (quiet: words.all Word.quiet1 = True): words.all Word.untrailed1 = True :=
  match words with
    | [] => byComputing
    | [word, ..rest] => rewrite quietNoTrail word (Bool.andLeft quiet), quietUntrailed rest (Bool.andRight quiet)

theorem trailsBackUntrailed ∀ (words: List Word) (all: words.all Word.untrailed1 = True): trailsBack words = False :=
  match words with
    | [] => byComputing
    | [word, ..rest] =>
      rewrite Bool.notTrue word.trails (Bool.andLeft all),
          trailsBackUntrailed rest (Bool.andRight all),
          Bool.andFalse (isCloserText word.text)

--| An edge-quiet expression that may not end with a comment has none after any token.
theorem edgeOffWords ∀ (expr: Expr) (lead: Bool)
    (edge: expr.edgeQuiet1 lead False = True):
    expr.words.all Word.untrailed1 = True :=
  match expr, edge with
    | Atom _ word, edge => rewrite edgeUntrailed word lead edge
    | Paren open inner close, edge =>
      untrailedAppend
        [open, ..inner.words]
        [close]
        (rewrite edgeUntrailed open lead (Bool.andLeft edge) then
          edgeOffWords inner False (Bool.andLeft (Bool.andRight edge)))
        (rewrite quietNoTrail close (Bool.andRight (Bool.andRight edge)))
    | Tuple open items _ close, edge =>
      untrailedAppend
        [open, ..itemsWords items]
        [close]
        (rewrite edgeUntrailed open lead (Bool.andLeft edge) then
          lastOffWords items (Bool.andLeft (Bool.andRight edge)))
        (rewrite quietNoTrail close (Bool.andRight (Bool.andRight edge)))
    | ListOf open items _ close, edge =>
      untrailedAppend
        [open, ..itemsWords items]
        [close]
        (rewrite edgeUntrailed open lead (Bool.andLeft edge) then
          lastOffWords items (Bool.andLeft (Bool.andRight edge)))
        (rewrite quietNoTrail close (Bool.andRight (Bool.andRight edge)))
    | App head arguments, edge =>
      untrailedAppend head.words
        (itemsWords arguments)
        (edgeOffWords head lead (Bool.andLeft (Bool.andRight edge)))
        (lastOffWords arguments (Bool.andRight (Bool.andRight edge)))
    | Infix _ left operator right, edge =>
      untrailedAppend left.words
        [operator, ..right.words]
        (edgeOffWords left lead (Bool.andLeft edge))
        (rewrite quietNoTrail operator (Bool.andLeft (Bool.andRight edge)) then
          edgeOffWords right False (Bool.andRight (Bool.andRight edge)))
    | Prefix operator operand, edge =>
      rewrite edgeUntrailed operator lead (Bool.andLeft edge) then edgeOffWords operand False (Bool.andRight edge)

theorem lastOffWords ∀ (items: List Expr)
    (edge: lastEdgeQuiet1 False items = True):
    (itemsWords items).all Word.untrailed1 = True :=
  match items with
    | [] => byComputing
    | [item] => untrailedAppend item.words [] (edgeOffWords item False edge) byComputing
    | [item, next, ..more] =>
      untrailedAppend item.words
        (itemsWords [next, ..more])
        (quietUntrailed item.words (quietWords item (Bool.andLeft edge)))
        (lastOffWords [next, ..more] (Bool.andRight edge))

--| An edge-quiet expression that may not end with a comment trails none.
theorem edgeOffTrails ∀ (expr: Expr) (lead: Bool) (edge: expr.edgeQuiet1 lead False = True): expr.trails = False :=
  trailsBackUntrailed expr.words.reverse (untrailedReverse expr.words (edgeOffWords expr lead edge))

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

-- The first token.

--| An edge-quiet expression's first token writes no own-line comments where they are written elsewhere or it has
--| none.
theorem edgeLeadLeading ∀ (expr: Expr) (around: Around) (key: Nat) (lead end: Bool)
    (edge: expr.edgeQuiet1 lead end = True)
    (bare: expr.bareAt around = True):
    expr.lead.leading around key = [] :=
  match expr, edge with
    | Atom _ word, edge => edgeLeading word around key lead end edge bare
    | Paren open _ _, edge => edgeLeading open around key lead False (Bool.andLeft edge) bare
    | Tuple open _ _ _, edge => edgeLeading open around key lead False (Bool.andLeft edge) bare
    | ListOf open items _ _, edge => edgeLeading open around key lead (end && items.isEmpty) (Bool.andLeft edge) bare
    | App head _, edge => edgeLeadLeading head around key lead False (Bool.andLeft (Bool.andRight edge)) bare
    | Infix _ left _ _, edge => edgeLeadLeading left around key lead False (Bool.andLeft edge) bare
    | Prefix operator _, edge => edgeLeading operator around key lead False (Bool.andLeft edge) bare

--| An edge-quiet expression that may not lead has no comments above its first token.
theorem edgeLeadUnnoted ∀ (expr: Expr) (end: Bool) (edge: expr.edgeQuiet1 False end = True): expr.lead.noted = False :=
  match expr, edge with
    | Atom _ word, edge => edgeUnnoted word end edge
    | Paren open _ _, edge => edgeUnnoted open False (Bool.andLeft edge)
    | Tuple open _ _ _, edge => edgeUnnoted open False (Bool.andLeft edge)
    | ListOf open items _ _, edge => edgeUnnoted open (end && items.isEmpty) (Bool.andLeft edge)
    | App head _, edge => edgeLeadUnnoted head False (Bool.andLeft (Bool.andRight edge))
    | Infix _ left _ _, edge => edgeLeadUnnoted left False (Bool.andLeft edge)
    | Prefix operator _, edge => edgeUnnoted operator False (Bool.andLeft edge)

theorem edgeOffBare ∀ (expr: Expr) (around: Around) (end: Bool)
    (edge: expr.edgeQuiet1 False end = True):
    expr.bareAt around = True :=
  rewrite edgeLeadUnnoted expr end edge then Bool.orTrue around.hoisted

-- The invariant.

--| What the induction carries: as `LeadFacts`, the element trailing what the expression does.
def EdgeFacts (expr: Expr): Prop :=
  (∀ (around: Around) => expr.bareAt around = True → HangsAt lexKind around.before expr.trails (expr.el around))
    ∧ (∀ (level: Option Nat) (first: Bool) (around: Around) => expr.bareAt around = True
      → LinkFacts lexKind level first expr around expr.trails)

theorem edgeHangsOf ∀ (expr: Expr)
    (facts: EdgeFacts expr) (around: Around)
    (bare: expr.bareAt around = True):
    HangsAt lexKind around.before expr.trails (expr.el around) :=
  let (hangs, _) := facts
  hangs around bare

theorem edgeLinksOf ∀ (expr: Expr)
    (facts: EdgeFacts expr)
    (level: Option Nat) (first: Bool) (around: Around)
    (bare: expr.bareAt around = True):
    LinkFacts lexKind level first expr around expr.trails :=
  let (_, links) := facts
  links level first around bare

-- Items and arguments.

--| Items, quiet but the last, which is edge-quiet, each hang after an opener that trails nothing.
theorem edgeItemsHang ∀ (items: List Expr) (inset: Nat) (bare arm: Bool) (at: Nat) (end: Bool)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (sound: allSound items = True)
    (edge: lastEdgeQuiet1 end items = True):
    ItemsHang lexKind inset bare arm False False at items :=
  match items with
    | [] => byComputing
    | [item] =>
      let facts := edgeFacts item False end (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound) edge
      (
        elItemHangs lexKind _ inset False item.trails
          (edgeHangsOf item facts
            (firstAround bare arm False at)
            (edgeOffBare item (firstAround bare arm False at) end edge)
            inset
            inset),
        byComputing
      )
    | [item, next, ..more] =>
      let quiet: item.quiet1 = True := Bool.andLeft edge
      let facts := leadFacts item (Bool.andLeft within) (Bool.andLeft lexical) (quietLead item quiet) quietKeys
      let quietItem := quietTrails item quiet
      let first: ElHangs lexKind (item.el (firstAround bare arm False at)) inset inset False item.trails wordStart :=
        rewrite quietItem then
          leadHangsOf item facts
            (firstAround bare arm False at)
            (quietBare item (firstAround bare arm False at) quiet)
            inset
            inset
      let later: ItemsHang lexKind inset False arm item.trails item.trails (at + item.size) [next, ..more] :=
        rewrite quietItem then
          edgeItemsHang
            [next, ..more]
            inset
            False
            arm
            (at + item.size)
            end
            (Bool.andRight within)
            (Bool.andRight lexical)
            (Bool.andRight sound)
            (Bool.andRight edge)
      (elItemHangs lexKind _ inset False item.trails first, later)

--| After a list's opener that trails a comment only when the list is empty.
theorem edgeOpenItems ∀ (open: Word) (items: List Expr) (inset: Nat) (bare arm: Bool) (at: Nat) (lead end: Bool)
    (openEdge: open.edge1 lead (end && items.isEmpty) = True)
    (hang: ItemsHang lexKind inset bare arm False False at items):
    ItemsHang lexKind inset bare arm open.trails open.trails at items :=
  match items, hang with
    | [], _ => byComputing
    | [item, ..rest], hang =>
      let off: open.edge1 lead False = True := match end, openEdge with
        | True, edge => edge
        | False, edge => edge
      rewrite edgeUntrailed open lead off then hang

--| An edge-quiet bracket hugged as a call's last argument: as `huggedBracket` writes it, and opened.
--|
--| Proof idea: `hugFacts`' route (framed by the opener), the items by `edgeItemsHang`, the keys by `edgeCellsKeys`
--| and `edgeBrokenKeys`, and the comment before the closer, if any, the last item's (`edgeCloseBefore`).
theorem edgeHugFacts ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around) (end: Bool)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (openSound: open.sound = True)
    (closeSound: close.sound = True)
    (bare: open.leading around around.at = [])
    (each: ∀ (inset: Nat) => ItemsHang lexKind inset
      (list && items.all Expr.plainItem)
      around.inArm
      open.trails
      open.trails
      (around.at + 1)
      items)
    (edge: lastEdgeQuiet1 end items = True)
    (closeQuiet: close.quiet1 = True)
    (isOpen: open.text = (if list then "[" else "("))
    (isClose: close.text = (if list then "]" else ")")):
    Hangs lexKind around.before
      (close.trails || (ListOf open items False close).trailsBeforeClose)
      (huggedBracket list open items close around).fst
      ∧ (∀ (opened: Doc) => (huggedBracket list open items close around).snd = Some opened
        → Hangs lexKind around.before (close.trails || (ListOf open items False close).trailsBeforeClose) opened) :=
  let opener: OpenerToken lexKind open.text := match list with
    | True => rewrite isOpen then openBracket
    | False => rewrite isOpen then openParen
  let opens: isCloserText open.text = False := match list with
    | True => rewrite isOpen
    | False => rewrite isOpen
  let closer: CloserToken lexKind close.text := match list with
    | True => rewrite isClose then closeBracket
    | False => rewrite isClose then closeParen
  let bareItems := list && items.all Expr.plainItem
  let lays: ∀ (hard: Bool) => Hangs lexKind around.before
    (close.trails || (ListOf open items False close).trailsBeforeClose)
    (framedBy open around (Group (bracketContent list open items close { around | hoisted = True }) hard)) :=
    hard inset =>
      framedHangs lexKind open around
        (Group (bracketContent list open items close { around | hoisted = True }) hard)
        inset
        inset _
        bare
        (indent seat =>
          groupedBracketHangs lexKind list open items close around hard indent seat opener
            (trailsOfSound open openSound)
            closer
            (notesOfWord close closeSound)
            (trailsOfSound close closeSound)
            byComputing
            (each (indent + 2))
            (edgeCellsKeys items
              (around.at + 1)
              bareItems
              around.inArm
              open.trails
              (around.at + 1)
              end
              within
              lexical
              edge)
            (edgeBrokenKeys items
              (around.at + 1)
              bareItems
              around.inArm
              True
              open.trails
              (around.at + 1)
              end
              within
              lexical
              edge)
            (edgeCloseBefore open items close opens within lexical))
  (
    lays (bracketContent list open items close { around | hoisted = True }).forcesBreak,
    opened same => rewrite <- Option.someInjective same then lays True
  )

--| An edge-quiet slice 1 call's last argument hangs, as it is and opened, after an element that trails nothing.
theorem edgeLastHangs ∀ (argument: Expr) (around: Around) (end: Bool)
    (quietBefore: around.before = False)
    (within: argument.within1 = True)
    (lexical: argument.lexical1 = True)
    (sound: argument.sound = True)
    (edge: argument.edgeQuiet1 False end = True):
    Hangs lexKind around.before argument.trails (lastArgument argument around).fst
      ∧ (∀ (opened: Doc) => (lastArgument argument around).snd = Some opened
        → Hangs lexKind around.before argument.trails opened) :=
  let facts := edgeFacts argument False end within lexical sound edge
  let plain: Hangs lexKind around.before argument.trails (argument.el around) := inset =>
    edgeHangsOf argument facts around (edgeOffBare argument around end edge) inset inset
  match argument, within with
    | Atom _ _, _ => (plain, opened never => cases)
    | Paren open inner close, within =>
      rewrite parenLast open inner close around within then (plain, opened never => cases)
    | App _ _, _ => (plain, opened never => cases)
    | Infix InfixBinary _ _ _, _ => (plain, opened never => cases)
    | Infix InfixArrow _ _ _, _ => (plain, opened never => cases)
    | Prefix _ _, _ => (plain, opened never => cases)
    | Tuple open items trailing close, within =>
      let isOpen: open.text = "(" := DecEq.sound (Bool.andLeft lexical)
      let isClose: close.text = ")" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let itemsLexical := Bool.andRight (Bool.andRight lexical)
      let openOff := edgeUntrailed open False (Bool.andLeft edge)
      let same := (tupleTrails open items trailing close (rewrite isClose)).flipped
      let (hug, opens) :=
        edgeHugFacts False open items close around end within itemsLexical
          (Bool.andLeft sound)
          (Bool.andRight (Bool.andRight sound))
          (edgeLeadingOff open around around.at False (Bool.andLeft edge))
          (inset =>
            rewrite openOff then
              edgeItemsHang items inset
                (False && items.all Expr.plainItem)
                around.inArm
                (around.at + 1)
                end
                within
                itemsLexical
                (Bool.andLeft (Bool.andRight sound))
                (Bool.andLeft (Bool.andRight edge)))
          (Bool.andLeft (Bool.andRight edge))
          (Bool.andRight (Bool.andRight edge))
          isOpen
          isClose
      (
        inset => trailsSwap lexKind _ inset inset around.before _ _ wordStart same (hug inset),
        opened opening inset =>
          trailsSwap lexKind _ inset inset around.before _ _ wordStart same (opens opened opening inset)
      )
    | ListOf open items trailing close, within =>
      let isOpen: open.text = "[" := DecEq.sound (Bool.andLeft lexical)
      let isClose: close.text = "]" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let itemsLexical := Bool.andRight (Bool.andRight lexical)
      let same := (bracketTrails open items trailing close (rewrite isClose)).flipped
      let (hug, opens) :=
        edgeHugFacts True open items close around end within itemsLexical
          (Bool.andLeft sound)
          (Bool.andRight (Bool.andRight sound))
          (edgeLeadingOff open around around.at (end && items.isEmpty) (Bool.andLeft edge))
          (inset =>
            edgeOpenItems open items inset
              (True && items.all Expr.plainItem)
              around.inArm
              (around.at + 1)
              False
              end
              (Bool.andLeft edge)
              (edgeItemsHang items inset
                (True && items.all Expr.plainItem)
                around.inArm
                (around.at + 1)
                end
                within
                itemsLexical
                (Bool.andLeft (Bool.andRight sound))
                (Bool.andLeft (Bool.andRight edge))))
          (Bool.andLeft (Bool.andRight edge))
          (Bool.andRight (Bool.andRight edge))
          isOpen
          isClose
      (
        inset => trailsSwap lexKind _ inset inset around.before _ _ wordStart same (hug inset),
        opened opening inset =>
          trailsSwap lexKind _ inset inset around.before _ _ wordStart same (opens opened opening inset)
      )

--| Arguments, quiet but the last, which is edge-quiet, each hang, the last as it is and opened, after an element
--| that trails nothing.
theorem edgeArgsHang ∀ (arm: Bool) (previous: Expr) (at: Nat) (arguments: List Expr) (end: Bool)
    (previousQuiet: previous.trails = False)
    (within: allWithin1 arguments = True)
    (lexical: allLexical1 arguments = True)
    (sound: allSound arguments = True)
    (edge: lastEdgeQuiet1 end arguments = True):
    ArgsHang lexKind arm previous at arguments :=
  match arguments with
    | [] => byComputing
    | [argument] =>
      let unnoted: argument.noted = False :=
        Eq.trans (Eq.cong Word.noted (firstWordLead argument (Bool.andLeft within))) (edgeLeadUnnoted argument end edge)
      rewrite unnoted then
        edgeLastHangs argument
          (argAround arm previous at)
          end
          previousQuiet
          (Bool.andLeft within)
          (Bool.andLeft lexical)
          (Bool.andLeft sound)
          edge
    | [argument, next, ..more] =>
      let quiet: argument.quiet1 = True := Bool.andLeft edge
      let argumentQuiet := quietTrails argument quiet
      let facts := leadFacts argument (Bool.andLeft within) (Bool.andLeft lexical) (quietLead argument quiet) quietKeys
      let unnoted: argument.noted = False :=
        Eq.trans (Eq.cong Word.noted (firstWordLead argument (Bool.andLeft within))) (quietUnnoted argument quiet)
      let first: HangsFor lexKind argument.noted previous.trails argument.trails
        (argument.el (argAround arm previous at)) :=
        rewrite argumentQuiet, unnoted then
          (inset =>
            leadHangsOf argument facts
              (argAround arm previous at)
              (quietBare argument (argAround arm previous at) quiet)
              inset
              inset)
      (
        first,
        edgeArgsHang arm argument
          (at + argument.size)
          [next, ..more]
          end
          argumentQuiet
          (Bool.andRight within)
          (Bool.andRight lexical)
          (Bool.andRight sound)
          (Bool.andRight edge)
      )

-- The induction.

--| Each edge-quiet slice 1 expression hangs as an element wherever it writes no comments above its first token
--| (`bareAt`), trailing what it does, and as a chain's operand.
--|
--| Proof idea: `leadFacts`' cases, each rule-level lemma taking the part's own trailing comment: a name or numeral
--| `plainLeafHangs`, its comment from `sound`; a sign `prefixHangs` on its operand's facts; a paren `parenElHangs` on
--| its inner's; a list or tuple `listHangs` or `tupleHangs` with `edgeItemsHang` (an empty list's opener may trail);
--| a call `appElHangs` with `edgeArgsHang`; a chain `binaryChainHangs` or `arrowChainHangs`, its left operand's
--| `LinkFacts` trailing nothing and its right's trailing what the chain does. Each lemma's trailing comment is the
--| node's `Expr.trails` by `atomTrailsIs`, `prefixTrails`, `parenTrails`, `bracketTrails`, `tupleTrails`,
--| `appTrails` and `infixTrails`, the words read back stopping at a token that is no closer (`codedLex`).
theorem edgeFacts ∀ (expr: Expr) (lead end: Bool)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (sound: expr.sound = True)
    (edge: expr.edgeQuiet1 lead end = True):
    EdgeFacts expr :=
  match expr, within with
    | Atom kind word, within =>
      let (plain, (notComment, solid, closer, comma)) := wordFacts kind word.text within
      let hangs: ∀ (around: Around) => (Atom kind word).bareAt around = True
        → HangsAt lexKind around.before (Atom kind word).trails ((Atom kind word).el around) :=
        around bare indent column =>
          rewrite atomTrailsIs kind word then
            plainLeafHangs lexKind word around around.at indent column plain notComment solid closer comma
              (edgeLeading word around around.at lead end edge bare)
              (trailsOfSound word sound)
      (hangs, level first around bare => hangs around bare)
    | Prefix operator operand, within =>
      let (plain, (notComment, solid, closer, comma)) := prefixToken operator.text (Bool.andRight within)
      let operandEdge: operand.edgeQuiet1 False end = True := Bool.andRight edge
      let operandWithin: operand.within1 = True := Bool.andLeft within
      let operandLexical: operand.lexical1 = True := Bool.andRight lexical
      let inner := edgeFacts operand False end operandWithin operandLexical (Bool.andRight sound) operandEdge
      let hangs: ∀ (around: Around) => (Prefix operator operand).bareAt around = True
        → HangsAt lexKind around.before (Prefix operator operand).trails ((Prefix operator operand).el around) :=
        around bare indent column =>
          rewrite prefixTrails operator operand (codedLex operand operandWithin operandLexical) then
            prefixHangs lexKind operator operand around indent column operand.trails plain notComment solid closer comma
              (edgeLeading operator around around.at lead False (Bool.andLeft edge) bare)
              (trailsOfSound operator (Bool.andLeft sound))
              (inset =>
                edgeHangsOf operand inner
                  (around.next operator.trails 1)
                  (edgeOffBare operand (around.next operator.trails 1) end operandEdge)
                  inset
                  inset)
      (hangs, level first around bare => hangs around bare)
    | Paren open inner close, within =>
      let isOpen: open.text = "(" := DecEq.sound (Bool.andLeft lexical)
      let isClose: close.text = ")" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let innerLexical: inner.lexical1 = True := Bool.andRight (Bool.andRight lexical)
      let openEdge: open.edge1 lead False = True := Bool.andLeft edge
      let innerEdge: inner.edgeQuiet1 False end = True := Bool.andLeft (Bool.andRight edge)
      let openOff := edgeUntrailed open lead openEdge
      let facts := edgeFacts inner False end within innerLexical (Bool.andLeft (Bool.andRight sound)) innerEdge
      let hangs: ∀ (around: Around) => (Paren open inner close).bareAt around = True
        → HangsAt lexKind around.before (Paren open inner close).trails ((Paren open inner close).el around) :=
        around bare indent column =>
          rewrite parenTrails open inner close (rewrite isClose) (Inl openOff) then
            parenElHangs lexKind open inner close around indent column
              (rewrite isOpen then openParen)
              (trailsOfSound open (Bool.andLeft sound))
              openOff
              (rewrite isClose then closeParen)
              (notesOfWord close (Bool.andRight (Bool.andRight sound)))
              (trailsOfSound close (Bool.andRight (Bool.andRight sound)))
              (edgeLeading open around around.at lead False openEdge bare)
              (parenInnerPlain inner (around.next open.trails 1) within)
              (inset =>
                rewrite openOff then
                  edgeHangsOf inner facts
                    (around.next False 1)
                    (edgeOffBare inner (around.next False 1) end innerEdge)
                    inset
                    inset)
              (edgeKeys inner (around.next open.trails 1) (around.at + 1) False end within innerLexical innerEdge)
      (hangs, level first around bare => hangs around bare)
    | ListOf open items trailing close, within =>
      let isOpen: open.text = "[" := DecEq.sound (Bool.andLeft lexical)
      let isClose: close.text = "]" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let itemsLexical: allLexical1 items = True := Bool.andRight (Bool.andRight lexical)
      let openEdge: open.edge1 lead (end && items.isEmpty) = True := Bool.andLeft edge
      let itemsEdge: lastEdgeQuiet1 end items = True := Bool.andLeft (Bool.andRight edge)
      let itemsSound: allSound items = True := Bool.andLeft (Bool.andRight sound)
      let closeSound: close.sound = True := Bool.andRight (Bool.andRight sound)
      let bareItems := True && items.all Expr.plainItem
      let opens: isCloserText open.text = False := rewrite isOpen
      let hangs: ∀ (around: Around) => (ListOf open items trailing close).bareAt around = True
        → HangsAt lexKind around.before
          (ListOf open items trailing close).trails
          ((ListOf open items trailing close).el around) :=
        around bare indent column =>
          trailsSwap lexKind _ indent column around.before _ _ wordStart
            (bracketTrails open items trailing close (rewrite isClose)).flipped
            (listHangs lexKind open items trailing close around indent column
              (rewrite isOpen then openBracket)
              (trailsOfSound open (Bool.andLeft sound))
              (rewrite isClose then closeBracket)
              (notesOfWord close closeSound)
              (trailsOfSound close closeSound)
              byComputing
              (edgeLeading open around around.at lead (end && items.isEmpty) openEdge bare)
              (deep =>
                edgeOpenItems open items
                  (deep + 2)
                  bareItems
                  around.inArm
                  (around.at + 1)
                  lead
                  end
                  openEdge
                  (edgeItemsHang items
                    (deep + 2)
                    bareItems
                    around.inArm
                    (around.at + 1)
                    end
                    within
                    itemsLexical
                    itemsSound
                    itemsEdge))
              (edgeCellsKeys items
                (around.at + 1)
                bareItems
                around.inArm
                open.trails
                (around.at + 1)
                end
                within
                itemsLexical
                itemsEdge)
              (edgeBrokenKeys items
                (around.at + 1)
                bareItems
                around.inArm
                True
                open.trails
                (around.at + 1)
                end
                within
                itemsLexical
                itemsEdge)
              (edgeCloseBefore open items close opens within itemsLexical))
      (hangs, level first around bare => hangs around bare)
    | Tuple open items trailing close, within =>
      let isOpen: open.text = "(" := DecEq.sound (Bool.andLeft lexical)
      let isClose: close.text = ")" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      let itemsLexical: allLexical1 items = True := Bool.andRight (Bool.andRight lexical)
      let openEdge: open.edge1 lead False = True := Bool.andLeft edge
      let itemsEdge: lastEdgeQuiet1 end items = True := Bool.andLeft (Bool.andRight edge)
      let itemsSound: allSound items = True := Bool.andLeft (Bool.andRight sound)
      let closeSound: close.sound = True := Bool.andRight (Bool.andRight sound)
      let openOff := edgeUntrailed open lead openEdge
      let opens: isCloserText open.text = False := rewrite isOpen
      let hangs: ∀ (around: Around) => (Tuple open items trailing close).bareAt around = True
        → HangsAt lexKind around.before
          (Tuple open items trailing close).trails
          ((Tuple open items trailing close).el around) :=
        around bare indent column =>
          trailsSwap lexKind _ indent column around.before _ _ wordStart
            (tupleTrails open items trailing close (rewrite isClose)).flipped
            (tupleHangs lexKind open items trailing close around indent column
              (rewrite isOpen then openParen)
              (trailsOfSound open (Bool.andLeft sound))
              (rewrite isClose then closeParen)
              (notesOfWord close closeSound)
              (trailsOfSound close closeSound)
              byComputing
              (edgeLeading open around around.at lead False openEdge bare)
              (deep =>
                rewrite openOff then
                  edgeItemsHang items
                    (deep + 2)
                    False
                    around.inArm
                    (around.at + 1)
                    end
                    within
                    itemsLexical
                    itemsSound
                    itemsEdge)
              (edgeCellsKeys items
                (around.at + 1)
                False
                around.inArm
                open.trails
                (around.at + 1)
                end
                within
                itemsLexical
                itemsEdge)
              (edgeBrokenKeys items
                (around.at + 1)
                False
                around.inArm
                True
                open.trails
                (around.at + 1)
                end
                within
                itemsLexical
                itemsEdge)
              (edgeCloseBefore open items close opens within itemsLexical))
      (hangs, level first around bare => hangs around bare)
    | App head arguments, within =>
      match arguments, edge with
        | [], never => (Bool.falseNotTrue never).impossible
        | [argument, ..rest], edge =>
          let headEdge: head.edgeQuiet1 lead False = True := Bool.andLeft edge
          let argumentsEdge: lastEdgeQuiet1 end [argument, ..rest] = True := Bool.andRight edge
          let headFacts :=
            edgeFacts head lead False (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound) headEdge
          let headTrails := edgeOffTrails head lead headEdge
          let code :=
            codedLex
              (lastArg argument rest)
              (lastWithin argument rest (Bool.andRight within))
              (lastLexical argument rest (Bool.andRight lexical))
          let hangs: ∀ (around: Around) => (App head [argument, ..rest]).bareAt around = True
            → HangsAt lexKind around.before
              (App head [argument, ..rest]).trails
              ((App head [argument, ..rest]).el around) :=
            around bare indent column =>
              rewrite appTrails head argument rest code then
                appElHangs lexKind head argument rest around indent column
                  (rewrite firstWordLead (App head [argument, ..rest]) within then
                    edgeLeadLeading head around around.at lead False headEdge bare)
                  (inset seat =>
                    elUnheld lexKind
                      (head.el { around | hoisted = True })
                      inset
                      seat
                      around.before
                      head.trails
                      wordStart
                      (edgeHangsOf head headFacts { around | hoisted = True } byComputing inset seat))
                  (edgeArgsHang around.inArm head
                    (around.at + head.size)
                    [argument, ..rest]
                    end
                    headTrails
                    (Bool.andRight within)
                    (Bool.andRight lexical)
                    (Bool.andRight sound)
                    argumentsEdge)
          (hangs, level first around bare => hangs around bare)
    | Infix InfixBinary left operator right, within =>
      let word := fixedWord operator.text Comments.none
      let leftEdge: left.edgeQuiet1 lead False = True := Bool.andLeft edge
      let rightEdge: right.edgeQuiet1 False end = True := Bool.andRight (Bool.andRight edge)
      let rightWithin: right.within1 = True := Bool.andLeft (Bool.andRight within)
      let rightLexical: right.lexical1 = True := Bool.andRight (Bool.andRight lexical)
      let leftFacts :=
        edgeFacts left lead False (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound) leftEdge
      let rightFacts :=
        edgeFacts right False end rightWithin rightLexical (Bool.andRight (Bool.andRight sound)) rightEdge
      let leftOff := edgeOffTrails left lead leftEdge
      let code := codedLex right rightWithin rightLexical
      let listed := Bool.andLeft (Bool.andRight (Bool.andRight within))
      let pair: ∀ (level: Option Nat) (first: Bool) (around: Around) => left.bareAt around = True
        → PairFacts lexKind level first left word right around False right.trails :=
        level first around bare =>
          let leftLinks := edgeLinksOf left leftFacts level first around bare
          (
            False,
            False,
            rewrite leftOff at leftLinks then leftLinks,
            runFactsOf lexKind False False _
              (quietRun operator.text
                (around.next left.trails left.size)
                (around.next left.trails left.size).at
                listed),
            chainRightPlain level right (around.next False (left.size + 1)) rightWithin,
            edgeLinksOf right rightFacts level False
              (around.next False (left.size + 1))
              (edgeOffBare right (around.next False (left.size + 1)) end rightEdge)
          )
      let hangs: ∀ (around: Around) => (Infix InfixBinary left word right).bareAt around = True
        → HangsAt lexKind around.before
          (Infix InfixBinary left word right).trails
          ((Infix InfixBinary left word right).el around) :=
        around bare indent column =>
          rewrite infixTrails InfixBinary left word right code then
            binaryChainHangs lexKind left word right around indent column False right.trails
              (rewrite firstWordLead (Infix InfixBinary left word right) within then
                edgeLeadLeading left around around.at lead False leftEdge bare)
              (opensNoArms left (Infix InfixBinary left word right).chainLevel (Bool.andLeft within))
              (pair (Infix InfixBinary left word right).chainLevel True { around | hoisted = True } byComputing)
      rewrite quietIs operator (Bool.andLeft (Bool.andRight edge)) then
        (
          hangs,
          level first around bare =>
            rewrite infixTrails InfixBinary left word right code then
              match chained: (Infix InfixBinary left word right).inChain level with
                | True =>
                  let (noted, next, leftLinks, run, rightDocs, rightLinks) := pair level first around bare
                  (False, noted, next, leftLinks, run, rightDocs, rightLinks)
                | False =>
                  let whole := hangs around bare
                  rewrite infixTrails InfixBinary left word right code at whole then whole
        )
    | Infix InfixArrow left operator right, within =>
      let word := fixedWord operator.text Comments.none
      let leftEdge: left.edgeQuiet1 lead False = True := Bool.andLeft edge
      let rightEdge: right.edgeQuiet1 False end = True := Bool.andRight (Bool.andRight edge)
      let rightWithin: right.within1 = True := Bool.andLeft (Bool.andRight within)
      let rightLexical: right.lexical1 = True := Bool.andRight (Bool.andRight lexical)
      let leftFacts :=
        edgeFacts left lead False (Bool.andLeft within) (Bool.andLeft lexical) (Bool.andLeft sound) leftEdge
      let rightFacts :=
        edgeFacts right False end rightWithin rightLexical (Bool.andRight (Bool.andRight sound)) rightEdge
      let leftOff := edgeOffTrails left lead leftEdge
      let code := codedLex right rightWithin rightLexical
      let listed := arrowListed operator.text (Bool.andRight (Bool.andRight within))
      let pair: ∀ (level: Option Nat) (first: Bool) (around: Around) => left.bareAt around = True
        → PairFacts lexKind level first left word right around False right.trails :=
        level first around bare =>
          let leftLinks := edgeLinksOf left leftFacts level first around bare
          (
            False,
            False,
            rewrite leftOff at leftLinks then leftLinks,
            runFactsOf lexKind False False _
              (quietRun operator.text
                (around.next left.trails left.size)
                (around.next left.trails left.size).at
                listed),
            chainRightPlain level right (around.next False (left.size + 1)) rightWithin,
            edgeLinksOf right rightFacts level False
              (around.next False (left.size + 1))
              (edgeOffBare right (around.next False (left.size + 1)) end rightEdge)
          )
      let hangs: ∀ (around: Around) => (Infix InfixArrow left word right).bareAt around = True
        → HangsAt lexKind around.before
          (Infix InfixArrow left word right).trails
          ((Infix InfixArrow left word right).el around) :=
        around bare indent column =>
          rewrite infixTrails InfixArrow left word right code then
            arrowChainHangs lexKind left word right around indent column False right.trails
              (rewrite firstWordLead (Infix InfixArrow left word right) within then
                edgeLeadLeading left around around.at lead False leftEdge bare)
              (opensNoArms left (Infix InfixArrow left word right).chainLevel (Bool.andLeft within))
              (pair (Infix InfixArrow left word right).chainLevel True { around | hoisted = True } byComputing)
      rewrite quietIs operator (Bool.andLeft (Bool.andRight edge)) then
        (
          hangs,
          level first around bare =>
            rewrite infixTrails InfixArrow left word right code then
              match chained: (Infix InfixArrow left word right).inChain level with
                | True =>
                  let (noted, next, leftLinks, run, rightDocs, rightLinks) := pair level first around bare
                  (False, noted, next, leftLinks, run, rightDocs, rightLinks)
                | False =>
                  let whole := hangs around bare
                  rewrite infixTrails InfixArrow left word right code at whole then whole
        )
