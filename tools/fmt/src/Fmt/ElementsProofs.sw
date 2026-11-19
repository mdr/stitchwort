--| `DeclElements` for every slice 1 declaration the driver parses (SW-4130, piece E of docs/reviews/SW-4119-slice1-review.md):
--| comments anywhere the grammar allows in the type and the value, kept blank lines, any layout. No one-line test.
--|
--| The route is `edgeFacts`' induction (`Fmt.EdgeHangProofs`) with no class: its invariant (`AnyFacts`, `EdgeFacts`
--| for the places where the element's first token writes nothing before it) holds of every expression with the
--| tree facts, one lemma per node kind (`atomAny`, `prefixAny`, `parenAny`, `tupleAny`, `listAny`, `appAny`,
--| `binaryAny`, `arrowAny`), each from its parts' facts. The declaration's parts follow as for the edge-quiet class
--| (`anyElHangs`, `anyType`, `anyBody`), with no `calm`: the facts hold of the tree as it is.
--|
--| `laysKinds` (`Fmt.LaysKinds`) is no route here: it drops columns, and `ElHangs` is about them (a line's start
--| against the block column in force, `Room`, `CloserRoom`).
--|
--| What `settled1` says that the rules' layout needs, node by node, is `Expr.homed1` (`Fmt.ElementsHomed`), which `homedOfSettled`
--| reads off `settled1`.

namespace Fmt.ElementsProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc.Proofs (..)
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Header, InfixKind, Note, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.ChainHangProofs (HangsAt, LinkFacts)
import Fmt.ExprHangProofs (prefixToken, wordFacts)
import Fmt.SpellProofs (..)
import Fmt.CalmProofs (headerResultWithin)
import Fmt.TreeJoinProofs (lexKind)
import Fmt.TokenProofs (declRealOfLexical)
import Fmt.DeclHangProofs (BodyLays, OnLine, atomDecl, declStart, plainBody)
import Fmt.DeclFactsProofs (DeclElements, HugOnLine, appDocsHug, leadNotCloser, notesOfWord, plainBodyEl, trailsOfSound)
import Fmt.EdgeHangProofs (atomTrailsIs, codedLex, lastLexical, lastWithin, prefixTrails, trailsSwap)
import Fmt.AppHangProofs (ArgsHang, appElHangs, lastArg)
import Fmt.TrailsProofs (appTrails)
import Fmt.EdgeDeclProofs (edgeNotedNodeHangs)
import Fmt.ElementsHomed (..)
import Fmt.ToldWordProofs (..)
import Fmt.StandsProofs (..)
import Fmt.OutputStatements (tidiedOf)
import Fmt.OneLineStatements (..)
import Fmt.Driver1 (..)
import Fmt.ElementsKeys (LedAt, anyKeys, ledItemHangs)
import Fmt.ElementsBlank (BlankLined, blankItemHangs)
import Fmt.ElementsParen (innerLowers, parenLedElHangs, parenPlainElHangs)
import Fmt.ExprHangProofs (closeParen, openParen, parenInnerPlain)
import Fmt.TrailsProofs (parenTrails)
import Fmt.ElementsApp (LastHangs, Led, argsLed, lastLed)

-- The invariant.

--| The element's first token writes nothing before itself where it stands: its comments are written by an enclosing
--| element, or it has none, and no blank line kept above it as an item (`Word.leadsLine`).
def Expr.plainAt (expr: Expr) (around: Around): Bool := !expr.lead.leadsLine around

--| What the induction carries: `EdgeFacts`, at the places where the first token writes nothing before itself.
def AnyFacts (expr: Expr): Prop :=
  (∀ (around: Around) => expr.plainAt around = True → HangsAt lexKind around.before expr.trails (expr.el around))
    ∧ (∀ (level: Option Nat) (first: Bool) (around: Around) => expr.plainAt around = True
      → LinkFacts lexKind level first expr around expr.trails)

def AllAnyFacts: List Expr → Prop
  | [] => True
  | [expr, ..rest] => AnyFacts expr ∧ AllAnyFacts rest

theorem anyHangsOf ∀ (expr: Expr)
    (facts: AnyFacts expr) (around: Around)
    (plain: expr.plainAt around = True):
    HangsAt lexKind around.before expr.trails (expr.el around) :=
  let (hangs, _) := facts
  hangs around plain

--| A token whose first line writes nothing before it has no leading documents.
theorem unledLeading ∀ (word: Word) (around: Around) (key: Nat)
    (plain: (!word.leadsLine around) = True):
    word.leading around key = [] :=
  match word, around with
    | { text, comments = { above, after, blankBefore } }, { before, hoisted, item, at, inArm } =>
      match hoisted, above with
        | True, _ => byComputing
        | False, [] =>
          match item, blankBefore, plain with
            | False, _, _ => byComputing
            | True, False, _ => byComputing
            | True, True, never => (Bool.falseNotTrue never).impossible
        | False, [note, ..rest] => (Bool.falseNotTrue plain).impossible

--| An element not an item, its first token with no comments above, writes nothing before it.
theorem unnotedPlain ∀ (expr: Expr) (around: Around)
    (unnoted: expr.lead.noted = False)
    (single: around.item = False):
    expr.plainAt around = True :=
  match lead: expr.lead, unnoted with
    | { text, comments = { above = [], after, blankBefore } }, _ =>
      match around, single with
        | { before, hoisted, item = False, at, inArm }, _ =>
          match hoisted with
            | True => byComputing
            | False => byComputing
    | { text, comments = { above = [note, ..rest], after, blankBefore } }, never => (Bool.trueNotFalse never).impossible

-- The node kinds.

--| A name or numeral (proved): its leaf, as `edgeFacts`' atom, with no comment before it where it stands plain.
theorem atomAny ∀ (kind: Tok) (word: Word)
    (within: (Atom kind word).within1 = True)
    (sound: (Atom kind word).sound = True):
    AnyFacts (Atom kind word) :=
  let (plain, (notComment, solid, closer, comma)) := wordFacts kind word.text within
  let hangs: ∀ (around: Around) => (Atom kind word).plainAt around = True
    → HangsAt lexKind around.before (Atom kind word).trails ((Atom kind word).el around) :=
    around bare indent column =>
      rewrite atomTrailsIs kind word then
        plainLeafHangs lexKind word around around.at indent column plain notComment solid closer comma
          (unledLeading word around around.at bare)
          (trailsOfSound word sound)
  (hangs, level first around bare => hangs around bare)

-- A later part whose first token has comments above it.

--| Where an element ended, one whose first token has own-line comments may start: its first word on the comment break
--| the `LineStart` before the comments makes, right of the line, so with room for it but for `->`'s glue.
theorem endedLedSeat ∀ (indent: Nat) (before: Bool) (state: HangState) (place: Place)
    (unglued: state.glue = False)
    (ended: Ended state before place)
    (clear: (inForce state.blocks state.top <= indent) = True):
    Seat indent indent before state place (leadStart indent place) :=
  match place, ended with
    | Mid at carry, (floor, left) => ((floor, left), Nat.leRefl indent, clear, (unglued, arithmetic))
    | Held at carry, (trails, floor, left) => ((trails, floor, left), Nat.leRefl indent, clear, (unglued, arithmetic))

--| An element after words is a part, its first token where `startFor` says: `elPart`, and the same from
--| `endedLedSeat` for an element whose first token has comments above it.
theorem elPartFor ∀ (kinds: Text → Tok) (doc: Doc) (indent: Nat) (before trails noted: Bool)
    (el: ElHangs kinds doc indent indent before trails (startFor noted)):
    PartHangs kinds doc indent before trails :=
  match noted with
    | False => elPart kinds doc indent before trails el
    | True => state entry quiet unglued =>
      let pre: Place → Hang → Prop := place hang =>
        place = entry
          ∧ hang = Hang.At state
          ∧ Ended state before entry
          ∧ (inForce state.blocks state.top <= indent) = True
      let opened := openedBy state (leadStart indent entry)
      hangsPost kinds doc indent pre
        (place hang => Ended opened trails place ∧ hang = Hang.At opened)
        (place hang => Ended state trails place ∧ hang = Hang.At state)
        (hangsPre kinds doc indent
          (Entered indent indent before state entry (leadStart indent entry))
          pre
          (place hang => Ended opened trails place ∧ hang = Hang.At opened)
          (el state entry)
          (place hang (isEntry, folded, ended, clear) =>
            (isEntry, folded, endedLedSeat indent before state entry unglued ended clear)))
        (place hang (ended, folded) =>
          let same: opened = state := openedQuiet state (leadStart indent entry) quiet unglued
          (rewrite same at ended then ended, rewrite same at folded then folded))

--| `prefixHangs`, the operand's first token where `startFor` says: after its own-line comments, if it has any.
theorem prefixLedHangs ∀ (kinds: Text → Tok) (operator: Word) (operand: Expr) (around: Around)
    (indent column: Nat) (trails: Bool)
    (plain: Fmt.HangProofs.Plain (kinds operator.text))
    (token: operator.text.startsWith "--" = False)
    (solid: isLayout operator.text = False)
    (closer: isCloserText operator.text = False)
    (comma: (operator.text == ",") = False)
    (bare: operator.leading around around.at = [])
    (trailed: TrailsComment operator)
    (operandHangs: ∀ (inset: Nat) => ElHangs kinds
      (operand.el (around.next operator.trails 1))
      inset
      inset
      operator.trails
      trails
      (startFor operand.noted)):
    ElHangs kinds (Expr.el (Prefix operator operand) around) indent column around.before trails wordStart :=
  let inside := { around | hoisted = True }
  framedHangs kinds operator around
    (Doc.concat [
      operator.leaf inside around.at,
      prefixGap operator operand,
      operand.el (around.next operator.trails 1)
    ])
    indent
    column
    trails
    bare
    (inset seat =>
      elGapThen kinds
        (operator.leaf inside around.at)
        (prefixGap operator operand)
        (operand.el (around.next operator.trails 1))
        inset
        seat
        operator.trails
        trails
        (elUnheld kinds
          (operator.leaf inside around.at)
          inset
          seat
          inside.before
          operator.trails
          wordStart
          (plainLeafHangs kinds operator inside around.at inset seat plain token solid closer comma byComputing
              trailed))
        (prefixGapIs operator operand)
        (elPartFor kinds
          (operand.el (around.next operator.trails 1))
          inset
          operator.trails
          trails
          operand.noted
          (operandHangs inset)))

--| A sign and its operand (proved, the pattern for the other nodes): the sign may have a comment after it, and the
--| operand comments above its first token, after which it starts its line (`ledHangs` from the operand's facts,
--| `prefixLedHangs`).
theorem prefixAny ∀ (operator: Word) (operand: Expr)
    (within: (Prefix operator operand).within1 = True)
    (lexical: (Prefix operator operand).lexical1 = True)
    (sound: (Prefix operator operand).sound = True)
    (homed: (Prefix operator operand).homed1 = True)
    (inner: AnyFacts operand):
    AnyFacts (Prefix operator operand) :=
  let (plain, (notComment, solid, closer, comma)) := prefixToken operator.text (Bool.andRight within)
  let operandWithin: operand.within1 = True := Bool.andLeft within
  let operandLexical: operand.lexical1 = True := Bool.andRight lexical
  let operandSound: operand.sound = True := Bool.andRight sound
  let hangs: ∀ (around: Around) => (Prefix operator operand).plainAt around = True
    → HangsAt lexKind around.before (Prefix operator operand).trails ((Prefix operator operand).el around) :=
    around bare indent column =>
      rewrite prefixTrails operator operand (codedLex operand operandWithin operandLexical) then
        prefixLedHangs lexKind operator operand around indent column operand.trails plain notComment solid closer comma
          (unledLeading operator around around.at bare)
          (trailsOfSound operator (Bool.andLeft sound))
          (inset =>
            ledHangs operand
              (around.next operator.trails 1)
              inset
              operandWithin
              operandLexical
              operandSound
              inner
              byComputing
              byComputing)
  (hangs, level first around bare => hangs around bare)

--| A paren (proved): any comments on its opener, what it holds and its closer. What it holds starts where it stands
--| (`parenPlainElHangs`), or on the line after own-line comments above its first token (`parenLedElHangs`).
theorem parenAny ∀ (open: Word) (inner: Expr) (close: Word)
    (within: (Paren open inner close).within1 = True)
    (lexical: (Paren open inner close).lexical1 = True)
    (sound: (Paren open inner close).sound = True)
    (homed: (Paren open inner close).homed1 = True)
    (facts: AnyFacts inner):
    AnyFacts (Paren open inner close) :=
  let isOpen: open.text = "(" := DecEq.sound (Bool.andLeft lexical)
  let isClose: close.text = ")" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
  let innerWithin: inner.within1 = True := within
  let innerLexical: inner.lexical1 = True := Bool.andRight (Bool.andRight lexical)
  let innerSound: inner.sound = True := Bool.andLeft (Bool.andRight sound)
  let closeSound: close.sound = True := Bool.andRight (Bool.andRight sound)
  let hangs: ∀ (around: Around) => (Paren open inner close).plainAt around = True
    → HangsAt lexKind around.before (Paren open inner close).trails ((Paren open inner close).el around) :=
    around bare indent column =>
      let innerAround := around.next open.trails 1
      let keys := anyKeys inner innerAround (around.at + 1) innerWithin (Nat.leRefl _)
      rewrite parenTrails open inner close (rewrite isClose) (Inr (codedLex inner innerWithin innerLexical)) then
        match above: inner.lead.comments.above with
          | [] =>
            let unnoted: inner.lead.noted = False := Eq.cong (notes => !notes.isEmpty) above
            parenPlainElHangs lexKind open inner close around indent column
              (rewrite isOpen then openParen)
              (trailsOfSound open (Bool.andLeft sound))
              (rewrite isClose then closeParen)
              (notesOfWord close closeSound)
              (trailsOfSound close closeSound)
              (unledLeading open around around.at bare)
              (parenInnerPlain inner innerAround innerWithin)
              (inset =>
                anyHangsOf inner facts innerAround (unnotedPlain inner innerAround unnoted byComputing) inset inset)
              (trails inset =>
                let (_, plainLowers) :=
                  innerLowers inner innerAround inset
                    (around.at + 1)
                    innerWithin
                    innerLexical
                    byComputing
                    byComputing
                    (Nat.leRefl _)
                plainLowers above trails)
              keys
          | [note, ..rest] =>
            let quiet: ∀ (entry: Place) => (plainStart entry && note.blankBefore && innerAround.item) = False :=
              entry => rewrite Bool.andFalse note.blankBefore then Bool.andFalse (plainStart entry)
            parenLedElHangs lexKind open inner close around indent column
              (rewrite isOpen then openParen)
              (trailsOfSound open (Bool.andLeft sound))
              (rewrite isClose then closeParen)
              (notesOfWord close closeSound)
              (trailsOfSound close closeSound)
              (unledLeading open around around.at bare)
              (parenInnerPlain inner innerAround innerWithin)
              (inset state entry =>
                ledAnyHangs inner innerAround inset state entry note rest innerWithin innerLexical innerSound facts
                    byComputing above
                    (quiet entry))
              (inset =>
                let (ledLowers, _) :=
                  innerLowers inner innerAround inset
                    (around.at + 1)
                    innerWithin
                    innerLexical
                    byComputing
                    byComputing
                    (Nat.leRefl _)
                ledLowers (rewrite above))
              keys
  (hangs, level first around bare => hangs around bare)

--| A tuple (open): comments and kept blank lines on any item, after any item, and on the brackets.
theorem tupleAny ∀ (open: Word) (items: List Expr) (trailing: Bool) (close: Word)
    (within: (Tuple open items trailing close).within1 = True)
    (lexical: (Tuple open items trailing close).lexical1 = True)
    (sound: (Tuple open items trailing close).sound = True)
    (homed: (Tuple open items trailing close).homed1 = True)
    (facts: AllAnyFacts items):
    AnyFacts (Tuple open items trailing close) :=
  ?

--| A list (open): as a tuple, filled or broken.
theorem listAny ∀ (open: Word) (items: List Expr) (trailing: Bool) (close: Word)
    (within: (ListOf open items trailing close).within1 = True)
    (lexical: (ListOf open items trailing close).lexical1 = True)
    (sound: (ListOf open items trailing close).sound = True)
    (homed: (ListOf open items trailing close).homed1 = True)
    (facts: AllAnyFacts items):
    AnyFacts (ListOf open items trailing close) :=
  ?

--| A call (open): comments above and after the function and any argument.
theorem appAny ∀ (head: Expr) (arguments: List Expr)
    (within: (App head arguments).within1 = True)
    (lexical: (App head arguments).lexical1 = True)
    (sound: (App head arguments).sound = True)
    (homed: (App head arguments).homed1 = True)
    (shaped: (App head arguments).shaped1 = True)
    (headFacts: AnyFacts head)
    (argumentFacts: AllAnyFacts arguments):
    AnyFacts (App head arguments) :=
  match arguments, within with
    | [], _ =>
      let never: False = True := Bool.andRight (Bool.andRight shaped)
      (Bool.falseNotTrue never).impossible
    | [argument, ..rest], within =>
      let code :=
        codedLex
          (lastArg argument rest)
          (lastWithin argument rest (Bool.andRight within))
          (lastLexical argument rest (Bool.andRight lexical))
      let led: Led AnyFacts := expr around inset facts exprWithin exprLexical exprSound hoisted item =>
        ledHangs expr around inset exprWithin exprLexical exprSound facts hoisted item
      let hangs: ∀ (around: Around) => (App head [argument, ..rest]).plainAt around = True
        → HangsAt lexKind around.before
          (App head [argument, ..rest]).trails
          ((App head [argument, ..rest]).el around) :=
        around plain indent column =>
          rewrite appTrails head argument rest code then
            appElHangs lexKind head argument rest around indent column
              (rewrite firstWordLead (App head [argument, ..rest]) within then
                unledLeading (App head [argument, ..rest]).lead around around.at plain)
              (inset seat =>
                elUnheld lexKind
                  (head.el { around | hoisted = True })
                  inset
                  seat
                  around.before
                  head.trails
                  wordStart
                  (anyHangsOf head headFacts { around | hoisted = True } byComputing inset seat))
              (argsLed AnyFacts AllAnyFacts
                (expr more both => both)
                led
                around.inArm
                (previous at last held lastWithin lastLexical lastSound =>
                  lastLed AnyFacts led around.inArm previous at last held lastWithin lastLexical lastSound (opens =>
                    -- A hugged tuple or list last argument after a comment break: waits for the `huggedBracket` layout fix
                    -- (it lays the bracket undisplaced, its seat right of its indentation).
                    ?))
                head
                (around.at + head.size)
                [argument, ..rest]
                (Bool.andRight within)
                (Bool.andRight lexical)
                (Bool.andRight sound)
                argumentFacts)
      (hangs, level first around plain => hangs around plain)

--| A binary operator's chain (open): comments above and after any operand and after the operator.
theorem binaryAny ∀ (left: Expr) (operator: Word) (right: Expr)
    (within: (Infix InfixBinary left operator right).within1 = True)
    (lexical: (Infix InfixBinary left operator right).lexical1 = True)
    (sound: (Infix InfixBinary left operator right).sound = True)
    (homed: (Infix InfixBinary left operator right).homed1 = True)
    (leftFacts: AnyFacts left)
    (rightFacts: AnyFacts right):
    AnyFacts (Infix InfixBinary left operator right) :=
  ?

--| An arrow's chain (open): as a binary chain, but `homed1` leaves no comment after `->` or above its right operand.
theorem arrowAny ∀ (left: Expr) (operator: Word) (right: Expr)
    (within: (Infix InfixArrow left operator right).within1 = True)
    (lexical: (Infix InfixArrow left operator right).lexical1 = True)
    (sound: (Infix InfixArrow left operator right).sound = True)
    (homed: (Infix InfixArrow left operator right).homed1 = True)
    (leftFacts: AnyFacts left)
    (rightFacts: AnyFacts right):
    AnyFacts (Infix InfixArrow left operator right) :=
  ?

-- The induction.

--| Every slice 1 expression with the tree facts hangs as an element where its first token writes nothing before it.
--| `shaped` gives each call its arguments: with none, `appFrom`'s broken layout would end at a line start.
theorem anyFacts ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (sound: expr.sound = True)
    (homed: expr.homed1 = True)
    (shaped: expr.shaped1 = True):
    AnyFacts expr :=
  match expr, within with
    | Atom kind word, within => atomAny kind word within sound
    | Prefix operator operand, within =>
      prefixAny operator operand within lexical sound homed
        (anyFacts operand
          (Bool.andLeft within)
          (Bool.andRight lexical)
          (Bool.andRight sound)
          homed
          (Bool.andLeft shaped))
    | Paren open inner close, within =>
      parenAny open inner close within lexical sound homed
        (anyFacts inner within
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andLeft homed)
          shaped)
    | Tuple open items trailing close, within =>
      tupleAny open items trailing close within lexical sound homed
        (allAnyFacts items within
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andLeft homed)
          (Bool.andRight shaped))
    | ListOf open items trailing close, within =>
      listAny open items trailing close within lexical sound homed
        (allAnyFacts items within
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andLeft (Bool.andRight sound))
          (Bool.andLeft homed)
          shaped)
    | App head arguments, within =>
      appAny head arguments within lexical sound homed shaped
        (anyFacts head
          (Bool.andLeft within)
          (Bool.andLeft lexical)
          (Bool.andLeft sound)
          (Bool.andLeft homed)
          (Bool.andLeft (Bool.andRight shaped)))
        (allAnyFacts arguments
          (Bool.andRight within)
          (Bool.andRight lexical)
          (Bool.andRight sound)
          (Bool.andRight homed)
          (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight shaped)))))
    | Infix InfixBinary left operator right, within =>
      binaryAny left operator right within lexical sound homed
        (anyFacts left
          (Bool.andLeft within)
          (Bool.andLeft lexical)
          (Bool.andLeft sound)
          (Bool.andLeft homed)
          (Bool.andLeft shaped))
        (anyFacts right
          (Bool.andLeft (Bool.andRight within))
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andRight (Bool.andRight sound))
          (Bool.andRight homed)
          (Bool.andLeft (Bool.andRight shaped)))
    | Infix InfixArrow left operator right, within =>
      arrowAny left operator right within lexical sound homed
        (anyFacts left
          (Bool.andLeft within)
          (Bool.andLeft lexical)
          (Bool.andLeft sound)
          (Bool.andLeft homed)
          (Bool.andLeft shaped))
        (anyFacts right
          (Bool.andLeft (Bool.andRight within))
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andRight (Bool.andRight sound))
          (Bool.andLeft (Bool.andRight homed))
          (Bool.andLeft (Bool.andRight shaped)))

theorem allAnyFacts ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (sound: allSound items = True)
    (homed: allHomed1 items = True)
    (shaped: allShaped1 items = True):
    AllAnyFacts items :=
  match items with
    | [] => byComputing
    | [item, ..rest] => (
      anyFacts item
        (Bool.andLeft within)
        (Bool.andLeft lexical)
        (Bool.andLeft sound)
        (Bool.andLeft homed)
        (Bool.andLeft shaped),
      allAnyFacts rest
        (Bool.andRight within)
        (Bool.andRight lexical)
        (Bool.andRight sound)
        (Bool.andRight homed)
        (Bool.andRight shaped)
    )

-- The declaration's parts.

--| A slice 1 expression with `AnyFacts`, standing where it writes the comments above its first token (not hoisted,
--| not an item), hangs as an element from its seat at the indentation, its first token where `startFor` says.
--|
--| Proof idea: `edgeElHangs`' cases from the facts: with no comments, the element where it is plain; with comments, a
--| name or numeral by `notedLeafHangs` and a node by `edgeNotedNodeHangs` from its hoisted form's facts.
theorem ledHangs ∀ (expr: Expr) (around: Around) (indent: Nat)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (sound: expr.sound = True)
    (facts: AnyFacts expr)
    (hoisted: around.hoisted = False)
    (item: around.item = False):
    ElHangs lexKind (expr.el around) indent indent around.before expr.trails (startFor expr.noted) :=
  let sameNoted: expr.noted = expr.lead.noted := Eq.cong Word.noted (firstWordLead expr within)
  let hoistedHangs: ∀ (inset: Nat) => ElHangs lexKind
    (expr.el { around | hoisted = True })
    inset
    inset
    around.before
    expr.trails
    wordStart :=
    inset => anyHangsOf expr facts { around | hoisted = True } byComputing inset inset
  let comments: NotesComment expr.lead.comments.above := notesOfWord expr.lead (leadSound expr sound)
  let closer := leadNotCloser expr within lexical
  rewrite sameNoted then
    match above: expr.lead.comments.above with
      | [] =>
        let unnoted: expr.lead.noted = False := Eq.cong (notes => !notes.isEmpty) above
        anyHangsOf expr facts around (unnotedPlain expr around unnoted item) indent indent
      | [note, ..rest] =>
        let quiet: (note.blankBefore && around.item) = False := rewrite item then Bool.andFalse note.blankBefore
        match expr, within with
          | Atom kind word, within =>
            let (plain, (notComment, solid, wordCloser, comma)) := wordFacts kind word.text within
            let el: ElHangs lexKind (word.leaf around around.at) indent indent around.before word.trails leadStart :=
              state entry =>
                notedLeafHangs lexKind word around around.at indent state entry note rest plain notComment solid
                    wordCloser comma hoisted above comments
                    (trailsOfSound word sound)
                    (unblankedAt (plainStart entry) note.blankBefore around.item quiet)
            trailsSwap lexKind _ indent indent around.before _ _ leadStart (atomTrailsIs kind word).flipped el
          | Paren open inner close, _ =>
            edgeNotedNodeHangs
              (Paren open inner close)
              open
              (at => parenDoc open inner close { at | hoisted = True })
              around
              indent
              (Paren open inner close).trails
              note
              rest
              (at => byComputing)
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs
          | Tuple open items trailing close, _ =>
            edgeNotedNodeHangs
              (Tuple open items trailing close)
              open
              (at => commaBracket (list := False) open items close { at | hoisted = True })
              around
              indent
              (Tuple open items trailing close).trails
              note
              rest
              (at => byComputing)
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs
          | ListOf open items trailing close, _ =>
            edgeNotedNodeHangs
              (ListOf open items trailing close)
              open
              (at => commaBracket (list := True) open items close { at | hoisted = True })
              around
              indent
              (ListOf open items trailing close).trails
              note
              rest
              (at => byComputing)
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs
          | App head arguments, within =>
            let node: Around → Doc := at => (appDocs head arguments { at | hoisted = True }).doc
            edgeNotedNodeHangs
              (App head arguments)
              head.lead
              node
              around
              indent
              (App head arguments).trails
              note
              rest
              (at =>
                let unfolded: (App head arguments).el at = framedBy (App head arguments).firstWord at (node at) :=
                  byComputing
                Eq.trans unfolded
                  (Eq.cong (word => framedBy word at (node at)) (firstWordLead (App head arguments) within)))
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs
          | Infix InfixBinary left operator right, within =>
            let expr := Infix InfixBinary left operator right
            let node: Around → Doc := at => chain expr.chainLevel left operator right { at | hoisted = True }
            edgeNotedNodeHangs expr left.lead node around indent expr.trails note rest
              (at =>
                let unfolded: expr.el at = framedBy expr.firstWord at (node at) := byComputing
                Eq.trans unfolded (Eq.cong (word => framedBy word at (node at)) (firstWordLead expr within)))
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs
          | Infix InfixArrow left operator right, within =>
            let expr := Infix InfixArrow left operator right
            let node: Around → Doc := at => chain expr.chainLevel left operator right { at | hoisted = True }
            edgeNotedNodeHangs expr left.lead node around indent expr.trails note rest
              (at =>
                let unfolded: expr.el at = framedBy expr.firstWord at (node at) := byComputing
                Eq.trans unfolded (Eq.cong (word => framedBy word at (node at)) (firstWordLead expr within)))
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs
          | Prefix operator operand, _ =>
            edgeNotedNodeHangs
              (Prefix operator operand)
              operator
              (at =>
                Doc.concat [
                  operator.leaf { at | hoisted = True } at.at,
                  prefixGap operator operand,
                  operand.el (at.next operator.trails 1)
                ])
              around
              indent
              (Prefix operator operand).trails
              note
              rest
              (at => byComputing)
              byComputing
              hoisted
              above
              closer
              comments
              quiet
              hoistedHangs

--| An expression with `AnyFacts` and own-line comments above its first token, standing where it writes them (not
--| hoisted; an item or not), hangs from its seat at any entry but a plain line start under a kept blank line, its
--| first token on the line after the comments (`ledItemHangs`, its hoisted form plain).
theorem ledAnyHangs ∀ (expr: Expr) (around: Around) (indent: Nat) (state: HangState) (entry: Place)
    (note: Note) (rest: List Note)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (sound: expr.sound = True)
    (facts: AnyFacts expr)
    (hoisted: around.hoisted = False)
    (noted: expr.lead.comments.above = [note, ..rest])
    (quiet: (plainStart entry && note.blankBefore && around.item) = False):
    LedAt lexKind (expr.el around) indent around.before expr.trails state entry :=
  ledItemHangs expr around indent state entry note rest within lexical sound hoisted noted quiet (inset =>
    anyHangsOf expr facts { around | hoisted = True } byComputing inset inset)

--| An item with `AnyFacts`, a kept blank line before its first token and no comments above it, hangs from its seat
--| at an entry that isn't a plain line start where `BlankLined` holds, its first token on the line after the blank
--| line (`blankItemHangs`, its hoisted form plain).
theorem blankAnyHangs ∀ (expr: Expr) (around: Around) (indent: Nat) (state: HangState) (entry: Place)
    (within: expr.within1 = True)
    (sound: expr.sound = True)
    (facts: AnyFacts expr)
    (hoisted: around.hoisted = False)
    (item: around.item = True)
    (unnoted: expr.lead.comments.above = [])
    (blank: expr.lead.comments.blankBefore = True)
    (fresh: plainStart entry = False)
    (seatLined: BlankLined indent around.before entry):
    LedAt lexKind (expr.el around) indent around.before expr.trails state entry :=
  blankItemHangs expr around indent state entry within sound hoisted item unnoted blank fresh seatLined (inset =>
    anyHangsOf expr facts { around | hoisted = True } byComputing inset inset)

--| `ledHangs` for every slice 1 expression with the tree facts.
theorem anyElHangs ∀ (expr: Expr) (around: Around) (indent: Nat)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (sound: expr.sound = True)
    (homed: expr.homed1 = True)
    (shaped: expr.shaped1 = True)
    (hoisted: around.hoisted = False)
    (item: around.item = False):
    ElHangs lexKind (expr.el around) indent indent around.before expr.trails (startFor expr.noted) :=
  ledHangs expr around indent within lexical sound (anyFacts expr within lexical sound homed shaped) hoisted item

--| A call value's hug, if it has one, hangs on the `:=`'s line (open; with `appAny`): the function and the
--| arguments before the last, then the last argument opened, whatever their comments.
theorem anyHug ∀ (value: Expr) (around: Around)
    (within: value.within1 = True)
    (lexical: value.lexical1 = True)
    (sound: value.sound = True)
    (homed: value.homed1 = True)
    (shaped: value.shaped1 = True):
    HugOnLine lexKind value around :=
  let inside := { around | hoisted = True }
  match value, within with
    | App head arguments, within => open same =>
      match arguments, within, same with
        | [], _, never => cases
        | [argument, ..rest], within, same =>
          let headFacts :=
            anyFacts head
              (Bool.andLeft within)
              (Bool.andLeft lexical)
              (Bool.andLeft sound)
              (Bool.andLeft homed)
              (Bool.andLeft (Bool.andRight shaped))
          let led: Led AnyFacts := expr at inset facts exprWithin exprLexical exprSound hoisted item =>
            ledHangs expr at inset exprWithin exprLexical exprSound facts hoisted item
          let facts: ArgsHang lexKind inside.inArm head (inside.at + head.size) [argument, ..rest] :=
            argsLed AnyFacts AllAnyFacts
              (expr more both => both)
              led
              inside.inArm
              (previous at last held lastWithin lastLexical lastSound =>
                lastLed AnyFacts led inside.inArm previous at last held lastWithin lastLexical lastSound (opens =>
                  -- A hugged tuple or list last argument after a comment break: waits for the `huggedBracket` layout fix
                  -- (it lays the bracket undisplaced, its seat right of its indentation).
                  ?))
              head
              (inside.at + head.size)
              [argument, ..rest]
              (Bool.andRight within)
              (Bool.andRight lexical)
              (Bool.andRight sound)
              (allAnyFacts
                [argument, ..rest]
                (Bool.andRight within)
                (Bool.andRight lexical)
                (Bool.andRight sound)
                (Bool.andRight homed)
                (Bool.andRight (Bool.andRight (Bool.andRight shaped))))
          let headHangs: ElHangs lexKind (head.el inside) 0 0 False head.trails wordStart :=
            elUnheld lexKind
              (head.el inside)
              0
              0
              inside.before
              head.trails
              wordStart
              (anyHangsOf head headFacts inside byComputing 0 0)
          ((lastArg argument rest).trails, appDocsHug lexKind head argument rest inside 0 0 headHangs facts open same)
    | Atom _ _, _ => open never => cases
    | Paren _ _ _, _ => open never => cases
    | Tuple _ _ _ _, _ => open never => cases
    | ListOf _ _ _ _, _ => open never => cases
    | Infix InfixBinary _ _ _, _ => open never => cases
    | Infix InfixArrow _ _ _, _ => open never => cases
    | Prefix _ _, _ => open never => cases

--| A slice 1 type hangs as `DeclElements` asks, where it stands in a declaration.
theorem anyType ∀ (result: Expr) (before: Bool) (at: Nat) (inArm: Bool)
    (within: result.within1 = True)
    (lexical: result.lexical1 = True)
    (sound: result.sound = True)
    (homed: result.homed1 = True)
    (shaped: result.shaped1 = True):
    ElHangs lexKind
      (result.el { before, hoisted = False, item = False, at, inArm })
      4
      4
      before
      result.trails
      (startFor result.noted) :=
  anyElHangs result
    { before, hoisted = False, item = False, at, inArm }
    4
    within
    lexical
    sound
    homed
    shaped
    byComputing
    byComputing

--| A slice 1 value with no comment waiting and none above its first token lays on the `:=`'s line, and so does its
--| hug, if it has one.
theorem anyOnLine ∀ (value: Expr) (at: Nat) (inArm: Bool)
    (within: value.within1 = True)
    (lexical: value.lexical1 = True)
    (sound: value.sound = True)
    (homed: value.homed1 = True)
    (shaped: value.shaped1 = True)
    (unnoted: value.noted = False):
    OnLine lexKind (plainBody value { before = False, hoisted = False, item = False, at, inArm })
      ∧ (∀ (open: Doc) => value.callHug { before = False, hoisted = True, item = False, at, inArm } = Some open
        → OnLine lexKind open) :=
  let around: Around := { before = False, hoisted = False, item = False, at, inArm }
  let facts := anyFacts value within lexical sound homed shaped
  let leadUnnoted: value.lead.noted = False := calc value.lead.noted
    _ = value.noted := (Eq.cong Word.noted (firstWordLead value within)).flipped
    _ = False := unnoted
  let line: ElHangs lexKind (value.el around) 0 0 False value.trails wordStart :=
    anyHangsOf value facts around (unnotedPlain value around leadUnnoted byComputing) 0 0
  (
    (value.trails, rewrite plainBodyEl value around then line),
    open same => anyHug value around within lexical sound homed shaped open same
  )

--| A slice 1 value lays as a body, below the `:=` and on its line when no comment waits and it has none above its
--| first token.
theorem anyBody ∀ (value: Expr) (before: Bool) (at: Nat) (inArm: Bool)
    (within: value.within1 = True)
    (lexical: value.lexical1 = True)
    (sound: value.sound = True)
    (homed: value.homed1 = True)
    (shaped: value.shaped1 = True):
    BodyLays lexKind value { before, hoisted = False, item = False, at, inArm } before :=
  let around: Around := { before, hoisted = False, item = False, at, inArm }
  (
    (
      value.trails,
      rewrite plainBodyEl value around then
        anyElHangs value around 2 within lexical sound homed shaped byComputing byComputing
    ),
    waiting unnoted =>
      match before, waiting with | False, _ => anyOnLine value at inArm within lexical sound homed shaped unnoted
  )

-- The declaration.

--| Every slice 1 declaration with the tree facts meets `DeclElements`, the element facts `printedHangs` and
--| `printedStands1` take, whatever its comments and layout. `unreturned` is not needed; it is one of the hypotheses
--| `declElementsOneLine1` had, less `oneLine`.
--|
--| Proof idea: the type's facts from `anyType`, the value's from `anyBody`, each part's tokens sound by `settled1`
--| (`declSoundOfSettled`) and homed by `homedOfSettled`.
theorem declElements1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True)
    (lexical: decl.lexical1 = True)
    (unreturned: decl.unreturned1 = True):
    DeclElements lexKind decl :=
  let homed := homedOfSettled decl within lexical settled
  match decl, homed with
    | Definition [] header (Assigned colonEq value), homed =>
      let sound := declSoundOfSettled _ within settled (declRealOfLexical _ within lexical)
      let typeWithin: header.result.within1 = True := headerResultWithin header (Bool.andLeft within)
      let valueWithin: value.within1 = True := Bool.andRight within
      let typeLexical: header.result.lexical1 = True := Bool.andLeft (Bool.andRight lexical)
      let valueLexical: value.lexical1 = True := Bool.andRight (Bool.andRight lexical)
      let rest := Bool.andRight (Bool.andRight (Bool.andRight sound))
      let typeSound: header.result.sound = True := Bool.andLeft rest
      let valueSound: value.sound = True := Bool.andRight (Bool.andRight rest)
      (
        (
          header.result.trails,
          anyType header.result header.colon.after.isSome
            (0 + 3)
            False
            typeWithin
            typeLexical
            typeSound
            (Bool.andLeft homed)
            (Bool.andLeft shaped)
        ),
        anyBody value colonEq.after.isSome
          (0 + (4 + header.result.size))
          False
          valueWithin
          valueLexical
          valueSound
          (Bool.andRight homed)
          (Bool.andRight shaped)
      )

-- Sources the conditions apply to (D3684).

--| The tree facts and `homed1` of each declaration of a source's tidied tree.
def homedHoldsOn (source: Text): Bool := match tidiedOf source with
  | None => False
  | Some file => file.decls.all (decl =>
    decl.within1 && decl.shaped1 && decl.settled1 && decl.lexical1 && decl.unreturned1 && decl.homed1)

--| Comments after an arrow's operand, after a list's opener, items and closer, above an item with a blank line kept,
--| after a sign's operand, and at the end of the file.
theorem insideHomed: homedHoldsOn
        "-- top\ndef d: A -> -- x\n  B := g [ -- open\n    a, -- first\n\n    -- above\n    b,\n  ] -- close\n\n\ndef e: C := -1 + f x -- end\n-- last\n"
      = True :=
  byComputing

--| Comments written after `->` (rule N moves them before it), after a sign, and after operands with closers after
--| them.
theorem arrowsHomed: (homedHoldsOn "def d: A -> -- c\n  B -> -- e\n  C := x\n"
      && homedHoldsOn "def d: - -- c\n  1 -> A := x\n"
      && homedHoldsOn "def d: (A -- c\n  ) -> [B -- e\n  ] := x\n")
      = True :=
  byComputing

--| A declaration with comments inside its type and value, over several lines: a comment above an argument, after
--| an argument that is not the last, and after a list's opener.
def insideDecl: Decl := match tidiedOf "def x: F a -- c\n  b := f a -- d\n  -- e\n  [ -- g\n    b,\n  ] c\n" with
  | Some file => file.decls.headOr atomDecl
  | None => atomDecl

theorem insideDeclFacts: (insideDecl.within1
      && insideDecl.shaped1
      && insideDecl.settled1
      && insideDecl.lexical1
      && insideDecl.unreturned1
      && !insideDecl.edgeQuiet1
      && !insideDecl.oneLine1)
      = True :=
  byComputing

--| `declElements1` applies to it.
theorem insideElements: DeclElements lexKind insideDecl :=
  let (within, shaped, settled, lexical, unreturned, _) := insideDeclFacts
  declElements1 insideDecl within shaped settled lexical unreturned

--| `insideDecl`'s value, a call with comments above and after its arguments.
def insideValue: Expr := match insideDecl with
  | Definition _ _ (Assigned _ value) => value
  | _ => Atom Lower Word.none

--| `anyFacts`' hypotheses, `shaped` among them, hold of a parsed call: it applies.
theorem insideValueFacts: (insideValue.within1
      && insideValue.lexical1
      && insideValue.sound
      && insideValue.homed1
      && insideValue.shaped1)
      = True :=
  byComputing

theorem insideValueAny: AnyFacts insideValue :=
  let (within, lexical, sound, homed, shaped) := insideValueFacts
  anyFacts insideValue within lexical sound homed shaped
