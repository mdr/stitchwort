--| `DeclElements` for every slice 1 declaration the driver parses (SW-4130, piece E of docs/reviews/SW-4119-slice1-review.md):
--| comments anywhere the grammar allows in the type and the value, kept blank lines, any layout. No one-line test.
--|
--| The route is an induction on the expression with no class: its invariant (`AnyFacts`) holds of every expression with the
--| tree facts, one lemma per node kind (`atomAny`, `prefixAny`, `parenAny`, `tupleAny`, `listAny`, `appAny`,
--| `binaryAny`, `arrowAny`), each from its parts' facts. The declaration's parts follow
--| (`anyElHangs`, `anyType`, `anyBody`), with no `calm`: the facts hold of the tree as it is.
--|
--| `laysKinds` (`Fmt.LaysKinds`) is no route here: it drops columns, and `ElHangs` is about them (a line's start
--| against the block column in force, `Room`, `CloserRoom`).
--|
--| What `settled` says that the rules' layout needs, node by node, is `Expr.homed` (`Fmt.ElementsHomed`), which `homedOfSettled`
--| reads off `settled`.

namespace Fmt.ElementsProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc.Proofs (..)
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Header, InfixKind, Note, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.ChainHangProofs (HangsAt, Links, arrowChainHangs, binaryChainHangs)
import Fmt.ElementsChain (LedEl, arrowPair, binaryPair, operandLinks, unledLeading)
import Fmt.ExprHangProofs (opensNoArms, prefixToken, wordFacts)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (lexKind)
import Fmt.TokenProofs (declRealOfLexical)
import Fmt.DeclHangProofs (BodyLays, OnLine, declStart, plainBody)
import Fmt.DeclFactsProofs (DeclElements, HugOnLine, appDocsHug, leadNotCloser, notesOfWord, plainBodyEl, trailsOfSound)
import Fmt.EdgeHangProofs (atomTrailsIs, codedLex, infixTrails, lastLexical, lastWithin, prefixTrails, trailsSwap)
import Fmt.AppHangProofs (ArgsHang, HangsFor, appElHangs, argAround, lastArg, partHangsFor)
import Fmt.TrailsProofs (appTrails)
import Fmt.EdgeDeclProofs (edgeNotedNodeHangs)
import Fmt.ElementsHomed (..)
import Fmt.ToldWordProofs (..)
import Fmt.StandsProofs (..)
import Fmt.OutputStatements (tidiedOf)
import Fmt.OneLineStatements (..)
import Fmt.Driver1 (..)
import Fmt.ElementsKeys (LedAt, anyKeys, ledItemHangs)
import Fmt.ElementsBlank (blankItemHangs)
import Fmt.ElementsParen (innerLowers, parenLedElHangs, parenPlainElHangs)
import Fmt.ExprHangProofs (closeParen, openParen, parenInnerPlain)
import Fmt.TrailsProofs (parenTrails)
import Fmt.ElementsApp (LastHangs, Led, argsLed, lastLed)
import Fmt.ElementsItems (itemsLed)
import Fmt.ElementsKeys (anyBrokenKeys, anyCellsKeys)
import Fmt.BracketHangProofs (bracketTrails, groupedBracketHangs, listHangs, tupleHangs, tupleTrails)
import Fmt.EdgeHangProofs (edgeCloseBefore)
import Fmt.ExprHangProofs (closeBracket, openBracket)
import Syntax.SharedFacts (headerResultWithin)

-- The invariant.

--| The element's first token writes nothing before itself where it stands: its comments are written by an enclosing
--| element, or it has none, and no blank line kept above it as an item (`Word.leadsLine`).
def Expr.plainAt (expr: Expr) (around: Around): Bool := !expr.lead.leadsLine around

--| What the induction carries: the element facts at the places where the first token writes nothing before itself; and a
--| chain of the level asked, not an item, as an operand (`Links`) whether it writes own-line comments above its first
--| token or not (`led`), as the right operand of a chain of its level may.
def AnyFacts (expr: Expr): Prop :=
  (∀ (around: Around) => expr.plainAt around = True → HangsAt lexKind around.before expr.trails (expr.el around))
    ∧ (∀ (level: Option Nat) (first: Bool) (around: Around) => ((expr.inChain level && !around.item)
      || expr.plainAt around)
      = True
      → Links lexKind (expr.inChain level && expr.lead.leadsLine around) level first expr around expr.trails)

def AllAnyFacts: List Expr → Prop
  | [] => True
  | [expr, ..rest] => AnyFacts expr ∧ AllAnyFacts rest

theorem anyHangsOf ∀ (expr: Expr)
    (facts: AnyFacts expr) (around: Around)
    (plain: expr.plainAt around = True):
    HangsAt lexKind around.before expr.trails (expr.el around) :=
  let (hangs, _) := facts
  hangs around plain

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

--| A name or numeral (proved): its leaf, with no comment before it where it stands plain.
theorem atomAny ∀ (kind: Tok) (word: Word)
    (within: (Atom kind word).within1 = True)
    (sound: (Atom kind word).sound = True):
    AnyFacts (Atom kind word) :=
  let (plain, (notComment, solid, closer, comma)) :=
    wordFacts kind word.text (Bool.andIntro (Bool.andLeft within) (Bool.andRight (Bool.andRight within)))
  let hangs: ∀ (around: Around) => (Atom kind word).plainAt around = True
    → HangsAt lexKind around.before (Atom kind word).trails ((Atom kind word).el around) :=
    around bare indent column =>
      rewrite atomTrailsIs kind word then
        plainLeafHangs lexKind word around around.at indent column plain notComment solid closer comma
          (unledLeading word around around.at bare)
          (trailsOfSound word sound)
  (hangs, level first around bare => hangs around bare)

--| The operand's first token where `startFor` says: after its own-line comments, if it has any.
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
        (partHangsFor kinds
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
    (lexical: (Prefix operator operand).lexical = True)
    (sound: (Prefix operator operand).sound = True)
    (homed: (Prefix operator operand).homed = True)
    (inner: AnyFacts operand):
    AnyFacts (Prefix operator operand) :=
  let (plain, (notComment, solid, closer, comma)) := prefixToken operator.text (Bool.andRight within)
  let operandWithin: operand.within1 = True := Bool.andLeft within
  let operandLexical: operand.lexical = True := Bool.andRight lexical
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
    (lexical: (Paren open inner close).lexical = True)
    (sound: (Paren open inner close).sound = True)
    (homed: (Paren open inner close).homed = True)
    (facts: AnyFacts inner):
    AnyFacts (Paren open inner close) :=
  let isOpen: open.text = "(" := DecEq.sound (Bool.andLeft lexical)
  let isClose: close.text = ")" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
  let innerWithin: inner.within1 = True := within
  let innerLexical: inner.lexical = True := Bool.andRight (Bool.andRight lexical)
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
                    byComputing above)
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

--| A tuple (proved): comments and kept blank lines on any item, after any item, and on the brackets. An item with
--| comments or a kept blank line above its first token starts the line after them (`itemsLed`).
theorem tupleAny ∀ (open: Word) (items: List Expr) (trailing: Bool) (close: Word)
    (within: (Tuple open items trailing close).within1 = True)
    (lexical: (Tuple open items trailing close).lexical = True)
    (sound: (Tuple open items trailing close).sound = True)
    (homed: (Tuple open items trailing close).homed = True)
    (facts: AllAnyFacts items):
    AnyFacts (Tuple open items trailing close) :=
  let isOpen: open.text = "(" := DecEq.sound (Bool.andLeft lexical)
  let isClose: close.text = ")" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
  let itemsLexical: allLexical items = True := Bool.andRight (Bool.andRight lexical)
  let itemsSound: allSound items = True := Bool.andLeft (Bool.andRight sound)
  let closeSound: close.sound = True := Bool.andRight (Bool.andRight sound)
  let opens: isCloserText open.text = False := rewrite isOpen
  let bare := False
  let hangs: ∀ (around: Around) => (Tuple open items trailing close).plainAt around = True
    → HangsAt lexKind around.before
      (Tuple open items trailing close).trails
      ((Tuple open items trailing close).el around) :=
    around plain indent column =>
      trailsSwap lexKind _ indent column around.before _ _ wordStart
        (tupleTrails open items trailing close (rewrite isClose)).flipped
        (tupleHangs lexKind open items trailing close around indent column
          (rewrite isOpen then openParen)
          (trailsOfSound open (Bool.andLeft sound))
          (rewrite isClose then closeParen)
          (notesOfWord close closeSound)
          (trailsOfSound close closeSound)
          byComputing
          (unledLeading open around around.at plain)
          (deep =>
            itemsLed AnyFacts AllAnyFacts
              (expr more both => both)
              (expr held => held.left)
              (deep + 2)
              bare
              around.inArm
              open.trails
              (around.at + 1)
              items
              within
              itemsLexical
              itemsSound
              facts)
          (anyCellsKeys items (around.at + 1) bare around.inArm open.trails (around.at + 1) within (Nat.leRefl _))
          (anyBrokenKeys items (around.at + 1) bare around.inArm True open.trails (around.at + 1) within (Nat.leRefl _))
          (edgeCloseBefore open items close opens within itemsLexical))
  (hangs, level first around plain => hangs around plain)

--| A list (proved): as a tuple, filled or broken.
theorem listAny ∀ (open: Word) (items: List Expr) (trailing: Bool) (close: Word)
    (within: (ListOf open items trailing close).within1 = True)
    (lexical: (ListOf open items trailing close).lexical = True)
    (sound: (ListOf open items trailing close).sound = True)
    (homed: (ListOf open items trailing close).homed = True)
    (facts: AllAnyFacts items):
    AnyFacts (ListOf open items trailing close) :=
  let isOpen: open.text = "[" := DecEq.sound (Bool.andLeft lexical)
  let isClose: close.text = "]" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
  let itemsLexical: allLexical items = True := Bool.andRight (Bool.andRight lexical)
  let itemsSound: allSound items = True := Bool.andLeft (Bool.andRight sound)
  let closeSound: close.sound = True := Bool.andRight (Bool.andRight sound)
  let opens: isCloserText open.text = False := rewrite isOpen
  let bare := True && items.all Expr.plainItem
  let hangs: ∀ (around: Around) => (ListOf open items trailing close).plainAt around = True
    → HangsAt lexKind around.before
      (ListOf open items trailing close).trails
      ((ListOf open items trailing close).el around) :=
    around plain indent column =>
      trailsSwap lexKind _ indent column around.before _ _ wordStart
        (bracketTrails open items trailing close (rewrite isClose)).flipped
        (listHangs lexKind open items trailing close around indent column
          (rewrite isOpen then openBracket)
          (trailsOfSound open (Bool.andLeft sound))
          (rewrite isClose then closeBracket)
          (notesOfWord close closeSound)
          (trailsOfSound close closeSound)
          byComputing
          (unledLeading open around around.at plain)
          (deep =>
            itemsLed AnyFacts AllAnyFacts
              (expr more both => both)
              (expr held => held.left)
              (deep + 2)
              bare
              around.inArm
              open.trails
              (around.at + 1)
              items
              within
              itemsLexical
              itemsSound
              facts)
          (anyCellsKeys items (around.at + 1) bare around.inArm open.trails (around.at + 1) within (Nat.leRefl _))
          (anyBrokenKeys items (around.at + 1) bare around.inArm True open.trails (around.at + 1) within (Nat.leRefl _))
          (edgeCloseBefore open items close opens within itemsLexical))
  (hangs, level first around plain => hangs around plain)

--| What a tuple or list carries for its hug as a call's last argument: its items' facts. Nothing for any other
--| expression.
def BracketFacts: Expr → Prop
  | Tuple _ items _ _ | ListOf _ items _ _ => AllAnyFacts items
  | _ => True

def AllBracketFacts: List Expr → Prop
  | [] => True
  | [expr, ..rest] => BracketFacts expr ∧ AllBracketFacts rest

--| What a call asks of each argument: its facts, and its items' if it can hug.
def ArgFacts (expr: Expr): Prop := AnyFacts expr ∧ BracketFacts expr

def AllArgFacts (exprs: List Expr): Prop := AllAnyFacts exprs ∧ AllBracketFacts exprs

--| A node framed by its first token, standing where it writes the comments above that token (not hoisted, not an
--| item), hangs from its seat at the indentation, its first word where `startFor` says, if its document hangs from
--| any seat with no comment waiting.
--|
--| Proof idea: with no comments above the token, `framedHangs`; with some, `notedFramedHangs`, whose hoisted frame is
--| the displaced document, which `framedHangs` gives as well.
theorem framedLedHangs ∀ (first: Word) (around: Around) (doc: Doc) (indent: Nat) (trails: Bool)
    (sound: first.sound = True)
    (closer: isCloserText first.text = False)
    (hoisted: around.hoisted = False)
    (item: around.item = False)
    (el: ∀ (inset seat: Nat) => ElHangs lexKind doc inset seat False trails wordStart):
    ElHangs lexKind (framedBy first around doc) indent indent around.before trails (startFor first.noted) :=
  match first with
    | { text, comments = { above = [], after, blankBefore } } =>
      framedHangs lexKind
        { text, comments = { above = [], after, blankBefore } }
        around
        doc
        indent
        indent
        trails
        (unledLeading { text, comments = { above = [], after, blankBefore } } around around.at (rewrite hoisted, item))
        el
    | { text, comments = { above = [note, ..rest], after, blankBefore } } =>
      let word := { text, comments = { above = [note, ..rest], after, blankBefore } }
      notedFramedHangs lexKind word around doc indent trails note rest hoisted byComputing closer
        (notesOfWord word sound)
        (inset => framedHangs lexKind word { around | hoisted = True } doc inset inset trails byComputing el)

--| A tuple or list as a call's last argument (`huggedBracket`), as it is and opened, whatever its comments: framed by
--| its opener (`framedLedHangs`), its parts in a group (`groupedBracketHangs`) whose items hang by their facts
--| (`itemsLed`).
theorem hugLastHangs ∀ (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around) (trails: Bool)
    (hoisted: around.hoisted = False)
    (item: around.item = False)
    (isOpen: open.text = (if list then "[" else "("))
    (isClose: close.text = (if list then "]" else ")"))
    (openSound: open.sound = True)
    (closeSound: close.sound = True)
    (within: allWithin1 items = True)
    (lexical: allLexical items = True)
    (sound: allSound items = True)
    (facts: AllAnyFacts items)
    (trailsIs: (close.trails || (ListOf open items False close).trailsBeforeClose) = trails):
    HangsFor lexKind open.noted around.before trails (huggedBracket list open items close around).fst
      ∧ (∀ (opened: Doc) => (huggedBracket list open items close around).snd = Some opened
        → HangsFor lexKind open.noted around.before trails opened) :=
  let opener: OpenerToken lexKind open.text := match list with
    | True => rewrite isOpen then openBracket
    | False => rewrite isOpen then openParen
  let opens: isCloserText open.text = False := match list with | True | False => rewrite isOpen
  let closer: CloserToken lexKind close.text := match list with
    | True => rewrite isClose then closeBracket
    | False => rewrite isClose then closeParen
  let bare := list && items.all Expr.plainItem
  let lays: ∀ (hard: Bool) => HangsFor lexKind open.noted around.before trails
    (framedBy open around (Group (bracketContent list open items close { around | hoisted = True }) hard)) :=
    hard inset =>
      framedLedHangs open around
        (Group (bracketContent list open items close { around | hoisted = True }) hard)
        inset
        trails
        openSound
        opens
        hoisted
        item
        (indent seat =>
          trailsSwap lexKind _ indent seat False _ _ wordStart trailsIs
            (groupedBracketHangs lexKind list open items close around hard indent seat opener
              (trailsOfSound open openSound)
              closer
              (notesOfWord close closeSound)
              (trailsOfSound close closeSound)
              byComputing
              (itemsLed AnyFacts AllAnyFacts
                (expr more both => both)
                (expr held => held.left)
                (indent + 2)
                bare
                around.inArm
                open.trails
                (around.at + 1)
                items
                within
                lexical
                sound
                facts)
              (anyCellsKeys items (around.at + 1) bare around.inArm open.trails (around.at + 1) within (Nat.leRefl _))
              (anyBrokenKeys items
                (around.at + 1)
                bare
                around.inArm
                True
                open.trails
                (around.at + 1)
                within
                (Nat.leRefl _))
              (edgeCloseBefore open items close opens within lexical)))
  (
    lays (bracketContent list open items close { around | hoisted = True }).forcesBreak,
    opened same => rewrite <- Option.someInjective same then lays True
  )

--| A call's last argument that can hug (a tuple or list) hangs as `lastArgument` writes it, and opened.
theorem bracketLastHangs ∀ (arm: Bool) (previous: Expr) (at: Nat) (argument: Expr)
    (facts: BracketFacts argument)
    (within: argument.within1 = True)
    (lexical: argument.lexical = True)
    (sound: argument.sound = True)
    (opens: argument.opensBracket = True):
    LastHangs arm previous at argument :=
  match argument, within, opens with
    | Atom _ _ | Paren _ _ _ | App _ _ | Infix InfixBinary _ _ _ | Infix InfixArrow _ _ _ | Prefix _ _, _, never =>
      (Bool.falseNotTrue never).impossible
    | Tuple open items trailing close, within, _ =>
      let isClose: close.text = ")" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      hugLastHangs False open items close
        (argAround arm previous at)
        (Tuple open items trailing close).trails
        byComputing
        byComputing
        (DecEq.sound (Bool.andLeft lexical))
        isClose
        (Bool.andLeft sound)
        (Bool.andRight (Bool.andRight sound))
        within
        (Bool.andRight (Bool.andRight lexical))
        (Bool.andLeft (Bool.andRight sound))
        facts
        (tupleTrails open items trailing close (rewrite isClose)).flipped
    | ListOf open items trailing close, within, _ =>
      let isClose: close.text = "]" := DecEq.sound (Bool.andLeft (Bool.andRight lexical))
      hugLastHangs True open items close
        (argAround arm previous at)
        (ListOf open items trailing close).trails
        byComputing
        byComputing
        (DecEq.sound (Bool.andLeft lexical))
        isClose
        (Bool.andLeft sound)
        (Bool.andRight (Bool.andRight sound))
        within
        (Bool.andRight (Bool.andRight lexical))
        (Bool.andLeft (Bool.andRight sound))
        facts
        (bracketTrails open items trailing close (rewrite isClose)).flipped

--| What a call's arguments ask, from their facts (`argsLed`): each led, the last as `lastArgument` writes it.
theorem appArgsHang ∀ (arm: Bool) (head: Expr) (at: Nat) (arguments: List Expr)
    (within: allWithin1 arguments = True)
    (lexical: allLexical arguments = True)
    (sound: allSound arguments = True)
    (facts: AllAnyFacts arguments)
    (brackets: AllBracketFacts arguments):
    ArgsHang lexKind arm head at arguments :=
  let led: Led ArgFacts := expr around inset held exprWithin exprLexical exprSound hoisted item =>
    ledHangs expr around inset exprWithin exprLexical exprSound held.left hoisted item
  argsLed ArgFacts AllArgFacts
    (expr more both => ((both.left.left, both.right.left), (both.left.right, both.right.right)))
    led
    arm
    (previous at last held lastWithin lastLexical lastSound =>
      lastLed ArgFacts led arm previous at last held lastWithin lastLexical lastSound (opens =>
        bracketLastHangs arm previous at last held.right lastWithin lastLexical lastSound opens))
    head
    at
    arguments
    within
    lexical
    sound
    (facts, brackets)

--| A call (proved): comments above and after the function and any argument; a last tuple or list hugs as
--| `hugLastHangs` lays it.
theorem appAny ∀ (head: Expr) (arguments: List Expr)
    (within: (App head arguments).within1 = True)
    (lexical: (App head arguments).lexical = True)
    (sound: (App head arguments).sound = True)
    (homed: (App head arguments).homed = True)
    (shaped: (App head arguments).shaped = True)
    (headFacts: AnyFacts head)
    (argumentFacts: AllAnyFacts arguments)
    (argumentBrackets: AllBracketFacts arguments):
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
              (appArgsHang around.inArm head
                (around.at + head.size)
                [argument, ..rest]
                (Bool.andRight within)
                (Bool.andRight lexical)
                (Bool.andRight sound)
                argumentFacts
                argumentBrackets)
      (hangs, level first around plain => hangs around plain)

--| A binary operator's chain (proved): comments above and after any operand and the operator. An operator or right
--| operand with own-line comments above it starts the line after them.
--|
--| Proof idea: as an element, `binaryChainHangs` from the chain's `PairLinks` where it writes nothing before its first
--| token (`binaryPair`); as an operand of a chain of its level, the same pair where it stands, its first operand `led`
--| as it writes its comments (`operandLinks`, from the operands' facts and `ledHangs`).
theorem binaryAny ∀ (left: Expr) (operator: Word) (right: Expr)
    (within: (Infix InfixBinary left operator right).within1 = True)
    (lexical: (Infix InfixBinary left operator right).lexical = True)
    (sound: (Infix InfixBinary left operator right).sound = True)
    (homed: (Infix InfixBinary left operator right).homed = True)
    (leftFacts: AnyFacts left)
    (rightFacts: AnyFacts right):
    AnyFacts (Infix InfixBinary left operator right) :=
  let leftWithin: left.within1 = True := Bool.andLeft within
  let rightWithin: right.within1 = True := Bool.andLeft (Bool.andRight within)
  let rightLexical: right.lexical = True := Bool.andRight (Bool.andRight lexical)
  let (_, leftLinks) := leftFacts
  let (_, rightLinks) := rightFacts
  let leftLed: LedEl left := at inset hoisted item =>
    ledHangs left at inset leftWithin (Bool.andLeft lexical) (Bool.andLeft sound) leftFacts hoisted item
  let rightLed: LedEl right := at inset hoisted item =>
    ledHangs right at inset rightWithin rightLexical (Bool.andRight (Bool.andRight sound)) rightFacts hoisted item
  let trailsIs := infixTrails InfixBinary left operator right (codedLex right rightWithin rightLexical)
  let hangs: ∀ (around: Around) => (Infix InfixBinary left operator right).plainAt around = True
    → HangsAt lexKind around.before
      (Infix InfixBinary left operator right).trails
      ((Infix InfixBinary left operator right).el around) :=
    around bare indent column =>
      let lifted := { around | hoisted = True }
      let level := (Infix InfixBinary left operator right).chainLevel
      let leftLinked: Links lexKind False level True left lifted left.trails :=
        operandLinks left level True lifted leftWithin leftLinks leftLed (Bool.orRight byComputing)
      rewrite trailsIs then
        binaryChainHangs lexKind left operator right around indent column left.trails right.trails
          (rewrite firstWordLead (Infix InfixBinary left operator right) within then
            unledLeading (Infix InfixBinary left operator right).lead around around.at bare)
          (opensNoArms left level leftWithin)
          (binaryPair False level True left operator right lifted within sound leftLinked rightLinks rightLed)
  (
    hangs,
    level first around cond =>
      match c: (Infix InfixBinary left operator right).inChain level with
        | False =>
          let plain: (Infix InfixBinary left operator right).plainAt around = True := cond
          hangs around plain
        | True =>
          let single: (!around.item || !left.lead.leadsLine around) = True := cond
          let leftLinked := operandLinks left level first around leftWithin leftLinks leftLed single
          rewrite trailsIs then
            (
              left.trails,
              binaryPair
                (left.lead.leadsLine around)
                level
                first
                left
                operator
                right
                around
                within
                sound
                leftLinked
                rightLinks
                rightLed
            )
  )

--| An arrow's chain (proved): as a binary chain, but `homed` leaves no comment after `->` or above its right operand;
--| `->` may have comments above it, and then starts the line after them, glued to its operand.
--|
--| Proof idea: `binaryAny`'s, with `arrowChainHangs` and `arrowPair`.
theorem arrowAny ∀ (left: Expr) (operator: Word) (right: Expr)
    (within: (Infix InfixArrow left operator right).within1 = True)
    (lexical: (Infix InfixArrow left operator right).lexical = True)
    (sound: (Infix InfixArrow left operator right).sound = True)
    (homed: (Infix InfixArrow left operator right).homed = True)
    (leftFacts: AnyFacts left)
    (rightFacts: AnyFacts right):
    AnyFacts (Infix InfixArrow left operator right) :=
  let leftWithin: left.within1 = True := Bool.andLeft within
  let rightWithin: right.within1 = True := Bool.andLeft (Bool.andRight within)
  let rightLexical: right.lexical = True := Bool.andRight (Bool.andRight lexical)
  let unled: operator.trails = False :=
    Bool.notTrue operator.trails (Bool.andLeft (Bool.andRight (Bool.andRight homed)))
  let unnoted: right.noted = False := Bool.notTrue right.noted (Bool.andRight (Bool.andRight (Bool.andRight homed)))
  let (_, leftLinks) := leftFacts
  let (_, rightLinks) := rightFacts
  let leftLed: LedEl left := at inset hoisted item =>
    ledHangs left at inset leftWithin (Bool.andLeft lexical) (Bool.andLeft sound) leftFacts hoisted item
  let rightLed: LedEl right := at inset hoisted item =>
    ledHangs right at inset rightWithin rightLexical (Bool.andRight (Bool.andRight sound)) rightFacts hoisted item
  let trailsIs := infixTrails InfixArrow left operator right (codedLex right rightWithin rightLexical)
  let hangs: ∀ (around: Around) => (Infix InfixArrow left operator right).plainAt around = True
    → HangsAt lexKind around.before
      (Infix InfixArrow left operator right).trails
      ((Infix InfixArrow left operator right).el around) :=
    around bare indent column =>
      let lifted := { around | hoisted = True }
      let level := (Infix InfixArrow left operator right).chainLevel
      let leftLinked: Links lexKind False level True left lifted left.trails :=
        operandLinks left level True lifted leftWithin leftLinks leftLed (Bool.orRight byComputing)
      rewrite trailsIs then
        arrowChainHangs lexKind left operator right around indent column left.trails right.trails
          (rewrite firstWordLead (Infix InfixArrow left operator right) within then
            unledLeading (Infix InfixArrow left operator right).lead around around.at bare)
          (opensNoArms left level leftWithin)
          (arrowPair False level True left operator right lifted within sound unled unnoted leftLinked rightLinks
              rightLed)
  (
    hangs,
    level first around cond =>
      match c: (Infix InfixArrow left operator right).inChain level with
        | False =>
          let plain: (Infix InfixArrow left operator right).plainAt around = True := cond
          hangs around plain
        | True =>
          let single: (!around.item || !left.lead.leadsLine around) = True := cond
          let leftLinked := operandLinks left level first around leftWithin leftLinks leftLed single
          rewrite trailsIs then
            (
              left.trails,
              arrowPair
                (left.lead.leadsLine around)
                level
                first
                left
                operator
                right
                around
                within
                sound
                unled
                unnoted
                leftLinked
                rightLinks
                rightLed
            )
  )

-- The induction.

--| Every slice 1 expression with the tree facts hangs as an element where its first token writes nothing before it.
--| `shaped` gives each call its arguments: with none, `appFrom`'s broken layout would end at a line start.
theorem anyFacts ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical = True)
    (sound: expr.sound = True)
    (homed: expr.homed = True)
    (shaped: expr.shaped = True):
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
        (allBracketFacts arguments
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
    (lexical: allLexical items = True)
    (sound: allSound items = True)
    (homed: allHomed items = True)
    (shaped: allShaped items = True):
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

--| A tuple's or list's items' facts, for its hug.
theorem bracketFacts ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical = True)
    (sound: expr.sound = True)
    (homed: expr.homed = True)
    (shaped: expr.shaped = True):
    BracketFacts expr :=
  match expr, within with
    | Atom _ _ | Prefix _ _ | Paren _ _ _, _ => byComputing
    | Tuple open items trailing close, within =>
      allAnyFacts items within
        (Bool.andRight (Bool.andRight lexical))
        (Bool.andLeft (Bool.andRight sound))
        (Bool.andLeft homed)
        (Bool.andRight shaped)
    | ListOf open items trailing close, within =>
      allAnyFacts items within
        (Bool.andRight (Bool.andRight lexical))
        (Bool.andLeft (Bool.andRight sound))
        (Bool.andLeft homed)
        shaped
    | App _ _ | Infix InfixBinary _ _ _ | Infix InfixArrow _ _ _, _ => byComputing

theorem allBracketFacts ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (lexical: allLexical items = True)
    (sound: allSound items = True)
    (homed: allHomed items = True)
    (shaped: allShaped items = True):
    AllBracketFacts items :=
  match items with
    | [] => byComputing
    | [item, ..rest] => (
      bracketFacts item
        (Bool.andLeft within)
        (Bool.andLeft lexical)
        (Bool.andLeft sound)
        (Bool.andLeft homed)
        (Bool.andLeft shaped),
      allBracketFacts rest
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
--| Proof idea: cases from the facts: with no comments, the element where it is plain; with comments, a
--| name or numeral by `notedLeafHangs` and a node by `edgeNotedNodeHangs` from its hoisted form's facts.
theorem ledHangs ∀ (expr: Expr) (around: Around) (indent: Nat)
    (within: expr.within1 = True)
    (lexical: expr.lexical = True)
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
        match expr, within with
          | Atom kind word, within =>
            let (plain, (notComment, solid, wordCloser, comma)) :=
              wordFacts kind word.text (Bool.andIntro (Bool.andLeft within) (Bool.andRight (Bool.andRight within)))
            let el: ElHangs lexKind (word.leaf around around.at) indent indent around.before word.trails leadStart :=
              state entry =>
                notedLeafHangs lexKind word around around.at indent state entry note rest plain notComment solid
                    wordCloser comma hoisted above comments
                    (trailsOfSound word sound)
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
              hoistedHangs

--| An expression with `AnyFacts` and own-line comments above its first token, standing where it writes them (not
--| hoisted; an item or not), hangs from its seat at any entry but a plain line start under a kept blank line, its
--| first token on the line after the comments (`ledItemHangs`, its hoisted form plain).
theorem ledAnyHangs ∀ (expr: Expr) (around: Around) (indent: Nat) (state: HangState) (entry: Place)
    (note: Note) (rest: List Note)
    (within: expr.within1 = True)
    (lexical: expr.lexical = True)
    (sound: expr.sound = True)
    (facts: AnyFacts expr)
    (hoisted: around.hoisted = False)
    (noted: expr.lead.comments.above = [note, ..rest]):
    LedAt lexKind (expr.el around) indent around.before expr.trails state entry :=
  ledItemHangs expr around indent state entry note rest within lexical sound hoisted noted (inset =>
    anyHangsOf expr facts { around | hoisted = True } byComputing inset inset)

--| `ledHangs` for every slice 1 expression with the tree facts.
theorem anyElHangs ∀ (expr: Expr) (around: Around) (indent: Nat)
    (within: expr.within1 = True)
    (lexical: expr.lexical = True)
    (sound: expr.sound = True)
    (homed: expr.homed = True)
    (shaped: expr.shaped = True)
    (hoisted: around.hoisted = False)
    (item: around.item = False):
    ElHangs lexKind (expr.el around) indent indent around.before expr.trails (startFor expr.noted) :=
  ledHangs expr around indent within lexical sound (anyFacts expr within lexical sound homed shaped) hoisted item

--| A call value's hug, if it has one, hangs on the `:=`'s line (proved): the function and the
--| arguments before the last, then the last argument opened, whatever their comments.
theorem anyHug ∀ (value: Expr) (around: Around)
    (within: value.within1 = True)
    (lexical: value.lexical = True)
    (sound: value.sound = True)
    (homed: value.homed = True)
    (shaped: value.shaped = True):
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
          let facts: ArgsHang lexKind inside.inArm head (inside.at + head.size) [argument, ..rest] :=
            appArgsHang inside.inArm head
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
              (allBracketFacts
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
    | Atom _ _ |
        Paren _ _ _ |
        Tuple _ _ _ _ |
        ListOf _ _ _ _ |
        Infix InfixBinary _ _ _ |
        Infix InfixArrow _ _ _ |
        Prefix _ _, _ => open never => cases

--| A slice 1 type hangs as `DeclElements` asks, where it stands in a declaration.
theorem anyType ∀ (result: Expr) (before: Bool) (at: Nat) (inArm: Bool)
    (within: result.within1 = True)
    (lexical: result.lexical = True)
    (sound: result.sound = True)
    (homed: result.homed = True)
    (shaped: result.shaped = True):
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
    (lexical: value.lexical = True)
    (sound: value.sound = True)
    (homed: value.homed = True)
    (shaped: value.shaped = True)
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
    (lexical: value.lexical = True)
    (sound: value.sound = True)
    (homed: value.homed = True)
    (shaped: value.shaped = True):
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
--| `printedStands1` take, whatever its comments and layout.
--|
--| Proof idea: the type's facts from `anyType`, the value's from `anyBody`, each part's tokens sound by `settled`
--| (`declSoundOfSettled`) and homed by `homedOfSettled`.
theorem declElements1 ∀ (decl: Decl)
    (within: decl.within1 = True)
    (shaped: decl.shaped = True)
    (settled: decl.settled = True)
    (lexical: decl.lexical = True)
    (unreturned: decl.unreturned = True):
    DeclElements lexKind decl :=
  let homed := homedOfSettled decl within lexical settled
  match decl, homed with
    | Definition [] header (Assigned colonEq value), homed =>
      let sound := declSoundOfSettled _ within settled (declRealOfLexical _ within lexical)
      let typeWithin: header.result.within1 = True := headerResultWithin header (Bool.andLeft within)
      let valueWithin: value.within1 = True := Bool.andRight within
      let typeLexical: header.result.lexical = True := Bool.andLeft (Bool.andRight lexical)
      let valueLexical: value.lexical = True := Bool.andRight (Bool.andRight lexical)
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
