--| The keys of an edge-quiet expression (`Expr.edgeQuiet1`, SW-4099): as for a quiet one (`Fmt.QuietKeyProofs`), its
--| document has no `Mark` or `CloserLine` below any floor. Only a closer with comments makes them, and an edge-quiet
--| expression's closers are quiet; its other tokens' comments (above the first, after the last that is no closer)
--| are text, line breaks and `LineSuffix`, which carry no key.

namespace Fmt.EdgeKeyProofs
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Syntax (Comments, Expr, InfixKind, Note, Word)
import Fmt (..)
import Fmt.HangProofs (Gap, prefixGapIs)
import Fmt.MarkProofs (allKeysFrom, keysFrom)
import Fmt.AppHangProofs (appDocsIs, argAround)
import Fmt.ExprHangProofs (..)
import Fmt.QuietKeyProofs (
  ArgKeys,
  allKeysAppend,
  allKeysIf,
  appFromKeys,
  argumentDocsCons,
  chainOfKeys,
  keysIf,
  leafKeys,
  pieceKeys,
  quietKeys,
  trailingKeys
)
import Fmt.SpellProofs (firstWordLead)
import Fmt.DeclFactsProofs (leadNotCloser)
import Fmt.OneLineStatements (..)

-- Tokens.

--| A token of an edge-quiet expression writes no own-line comments where they are written elsewhere or it has none.
theorem edgeLeading ∀ (word: Word) (around: Around) (key: Nat) (lead end: Bool)
    (edge: word.edge1 lead end = True)
    (bare: (around.hoisted || !word.noted) = True):
    word.leading around key = [] :=
  match word, edge with
    | { text, comments = { above, after, blankBefore } }, edge =>
      match hoisted: around.hoisted, above with
        | True, _ => byComputing
        | False, [] =>
          match blankBefore, lead, edge with
            | False, _, _ =>
              match around.item with
                | True => byComputing
                | False => byComputing
            | True, True, never => cases
            | True, False, never => cases

--| A token that may not lead has no own-line comments.
theorem edgeUnnoted ∀ (word: Word) (end: Bool) (edge: word.edge1 False end = True): word.noted = False :=
  match word, edge with
    | { text, comments = { above, after, blankBefore } }, edge =>
      match above, edge with
        | [], _ => byComputing
        | [note, ..rest], never => cases

--| A token that may not end trails no comment.
theorem edgeUntrailed ∀ (word: Word) (lead: Bool) (edge: word.edge1 lead False = True): word.trails = False :=
  match word.trails, edge with
    | False, _ => byComputing
    | True, never =>
      match lead, never with
        | True, never => cases
        | False, never => cases

--| A token that may not lead writes no own-line comments, wherever it stands.
theorem edgeLeadingOff ∀ (word: Word) (around: Around) (key: Nat) (end: Bool)
    (edge: word.edge1 False end = True):
    word.leading around key = [] :=
  edgeLeading word around key False end edge (rewrite edgeUnnoted word end edge then Bool.orTrue around.hoisted)

--| Own-line comments are text and line breaks.
theorem notesAboveKeys ∀ (low: Nat) (keep: Bool) (notes: List Note): allKeysFrom low (notesAbove keep notes) = True :=
  match notes with
    | [] => byComputing
    | [note, ..rest] =>
      allKeysAppend low _ _ (allKeysIf low _ [Blank] [] byComputing byComputing) (rewrite notesAboveKeys low True rest)

--| A token that is no closer writes no key before it, whatever its comments.
theorem leadingKeys ∀ (low key: Nat) (word: Word) (around: Around)
    (closer: isCloserText word.text = False):
    allKeysFrom low (word.leading around key) = True :=
  match word, closer with
    | { text, comments = { above, after, blankBefore } }, closer =>
      match hoisted: around.hoisted, above with
        | True, _ => byComputing
        | False, [] => allKeysIf low _ [BreakParent, LineStart, Blank] [] byComputing byComputing
        | False, [note, ..rest] =>
          rewrite closer then
            allKeysAppend low _ _
              (rewrite notesAboveKeys low around.item [note, ..rest])
              (allKeysIf low _ [Blank] [] byComputing byComputing)

--| A token that is no closer has no line of its own, so no `CloserLine`.
theorem leafKeysOpen ∀ (low key: Nat) (word: Word) (around: Around)
    (closer: isCloserText word.text = False):
    keysFrom low (word.leaf around key) = True :=
  let own: allKeysFrom low
    (if isCloserText word.text && !word.noted && around.before && word.trails then [CloserLine key] else [])
    = True :=
    rewrite closer
  keysConcat low _
    (allKeysAppend low _ _
      (leadingKeys low key word around closer)
      (allKeysAppend low _ _ own
        (allKeysAppend low [piece word.text] _ (rewrite pieceKeys low word.text) (trailingKeys low word))))

--| An opener before a quiet closer has no mark.
theorem openingKeysOpen ∀ (low: Nat) (word closer: Word) (around: Around)
    (opens: isCloserText word.text = False)
    (closerQuiet: closer.quiet1 = True):
    keysFrom low (word.opening around closer) = True :=
  let mark: allKeysFrom low (if closer.noted || closer.trails then [Mark around.at] else []) = True :=
    rewrite wordQuietUnnoted closer closerQuiet, quietNoTrail closer closerQuiet
  keysConcat low _
    (allKeysAppend low _ _
      (leadingKeys low around.at word around opens)
      (allKeysAppend low _ _ mark
        (allKeysAppend low [piece word.text] _ (rewrite pieceKeys low word.text) (trailingKeys low word))))

--| A node framed by a first token that is no closer keeps its contents' keys.
theorem framedKeysOpen ∀ (low: Nat) (first: Word) (around: Around) (doc: Doc)
    (opens: isCloserText first.text = False)
    (keys: keysFrom low doc = True):
    keysFrom low (framedBy first around doc) = True :=
  keysConcat low _
    (rewrite keysConcat low (first.leading around around.at) (leadingKeys low around.at first around opens),
        keysIf low _ (Displaced doc) doc keys keys)

theorem parenOpens ∀ (text: Text) (is: text = "("): isCloserText text = False := rewrite is

theorem bracketOpens ∀ (text: Text) (is: text = "["): isCloserText text = False := rewrite is

theorem parenOpensExample: isCloserText "(" = False := parenOpens "(" byComputing

theorem bracketOpensExample: isCloserText "[" = False := bracketOpens "[" byComputing

-- Brackets.

theorem edgeCellsKeys ∀ (items: List Expr) (low: Nat) (bare arm before: Bool) (at: Nat) (end: Bool)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (edge: lastEdgeQuiet1 end items = True):
    allKeysFrom low (cells bare arm before at items) = True :=
  match items with
    | [] => byComputing
    | [item] =>
      rewrite edgeKeys item
        (firstAround bare arm before at)
        low
        False
        end
        (Bool.andLeft within)
        (Bool.andLeft lexical)
        edge
    | [item, next, ..more] =>
      let one := quietKeys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft edge)
      rewrite keysConcat low [item.el (firstAround bare arm before at), Closing ","] (rewrite one),
          edgeCellsKeys
            [next, ..more]
            low
            False
            arm
            item.trails
            (at + item.size)
            end
            (Bool.andRight within)
            (Bool.andRight lexical)
            (Bool.andRight edge)

theorem edgeBrokenKeys ∀ (items: List Expr) (low: Nat) (bare arm first before: Bool) (at: Nat) (end: Bool)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (edge: lastEdgeQuiet1 end items = True):
    allKeysFrom low (brokenItems bare arm first before at items) = True :=
  match items with
    | [] => byComputing
    | [item] =>
      let one :=
        edgeKeys item (firstAround bare arm before at) low False end (Bool.andLeft within) (Bool.andLeft lexical) edge
      match first with
        | True => rewrite one
        | False => rewrite one
    | [item, next, ..more] =>
      let one := quietKeys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft edge)
      let rest :=
        edgeBrokenKeys
          [next, ..more]
          low
          False
          arm
          False
          item.trails
          (at + item.size)
          end
          (Bool.andRight within)
          (Bool.andRight lexical)
          (Bool.andRight edge)
      match first with
        | True => rewrite one, rest
        | False => rewrite one, rest

--| An edge-quiet bracket's parts, in any of `bracketContent`'s layouts.
theorem edgeContentKeys ∀ (low: Nat) (list: Bool) (open: Word) (items: List Expr) (close: Word)
    (around: Around) (end: Bool)
    (opens: isCloserText open.text = False)
    (closeQuiet: close.quiet1 = True)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (edge: lastEdgeQuiet1 end items = True):
    keysFrom low (bracketContent list open items close around) = True :=
  let prefix := openingKeysOpen low open close around opens closeQuiet
  let closer :=
    leafKeys low around.at close
      (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
      closeQuiet
  let bare := list && items.all Expr.plainItem
  let partsList := [
    open.opening around close,
    Nest 2 (Doc.concat (brokenItems bare around.inArm True open.trails (around.at + 1) items)),
    SoftLine,
    close.leaf
      (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
      around.at
  ]
  let parts: allKeysFrom low partsList = True :=
    rewrite prefix,
        keysConcat low _
          (edgeBrokenKeys items low bare around.inArm True open.trails (around.at + 1) end within lexical edge),
        closer
  keysIf low _ _ _
    (keysConcat low _ (rewrite prefix, closer))
    (keysIf low _ _ _
      (keysConcat low _
        (rewrite prefix,
            edgeCellsKeys items low bare around.inArm open.trails (around.at + 1) end within lexical edge,
            closer))
      (keysConcat low _
        (allKeysIf low _
          (partsList ++ [BreakParent])
          partsList
          (allKeysAppend low partsList [BreakParent] parts byComputing)
          parts)))

-- Calls.

--| An edge-quiet bracket hugged as a call's last argument keeps its keys, as it is and opened.
theorem edgeHugKeys ∀ (low: Nat) (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around) (end: Bool)
    (opens: isCloserText open.text = False)
    (closeQuiet: close.quiet1 = True)
    (within: allWithin1 items = True)
    (lexical: allLexical1 items = True)
    (edge: lastEdgeQuiet1 end items = True):
    keysFrom low (huggedBracket list open items close around).fst = True
      ∧ (∀ (opened: Doc) => (huggedBracket list open items close around).snd = Some opened
        → keysFrom low opened = True) :=
  let content :=
    edgeContentKeys low list open items close { around | hoisted = True } end opens closeQuiet within lexical edge
  (
    framedKeysOpen low open around
      (Group
        (bracketContent list open items close { around | hoisted = True })
        (bracketContent list open items close { around | hoisted = True }).forcesBreak)
      opens
      content,
    opened same =>
      rewrite <- Option.someInjective same then
        framedKeysOpen low open around
          (Group (bracketContent list open items close { around | hoisted = True }) True)
          opens
          content
  )

--| An edge-quiet slice 1 call's last argument keeps its keys, as it is and opened.
theorem edgeLastKeys ∀ (low: Nat) (argument: Expr) (around: Around) (end: Bool)
    (within: argument.within1 = True)
    (lexical: argument.lexical1 = True)
    (edge: argument.edgeQuiet1 False end = True):
    keysFrom low (lastArgument argument around).fst = True
      ∧ (∀ (open: Doc) => (lastArgument argument around).snd = Some open → keysFrom low open = True) :=
  let plain := edgeKeys argument around low False end within lexical edge
  match argument, within with
    | Atom _ _, _ => (plain, open never => cases)
    | Paren open inner close, within =>
      rewrite parenLast open inner close around within then (plain, opened never => cases)
    | App _ _, _ => (plain, open never => cases)
    | Infix InfixBinary _ _ _, _ => (plain, open never => cases)
    | Infix InfixArrow _ _ _, _ => (plain, open never => cases)
    | Prefix _ _, _ => (plain, open never => cases)
    | Tuple open items trailing close, within =>
      edgeHugKeys low False open items close around end
        (parenOpens open.text (DecEq.sound (Bool.andLeft lexical)))
        (Bool.andRight (Bool.andRight edge))
        within
        (Bool.andRight (Bool.andRight lexical))
        (Bool.andLeft (Bool.andRight edge))
    | ListOf open items trailing close, within =>
      edgeHugKeys low True open items close around end
        (bracketOpens open.text (DecEq.sound (Bool.andLeft lexical)))
        (Bool.andRight (Bool.andRight edge))
        within
        (Bool.andRight (Bool.andRight lexical))
        (Bool.andLeft (Bool.andRight edge))

theorem edgeArgumentKeys ∀ (low: Nat) (arm: Bool) (previous: Expr) (at: Nat) (arguments: List Expr) (end: Bool)
    (within: allWithin1 arguments = True)
    (lexical: allLexical1 arguments = True)
    (edge: lastEdgeQuiet1 end arguments = True):
    ArgKeys low (argumentDocs arm previous at arguments) :=
  match arguments with
    | [] => (byComputing, byComputing, open never => cases)
    | [argument] =>
      let (last, hug) :=
        edgeLastKeys low argument (argAround arm previous at) end (Bool.andLeft within) (Bool.andLeft lexical) edge
      (byComputing, last, hug)
    | [argument, next, ..more] =>
      let (docs, last, hug) :=
        edgeArgumentKeys low arm argument
          (at + argument.size)
          [next, ..more]
          end
          (Bool.andRight within)
          (Bool.andRight lexical)
          (Bool.andRight edge)
      let front: allKeysFrom low [
        argument.el (argAround arm previous at),
        ..(argumentDocs arm argument (at + argument.size) [next, ..more]).fst
      ]
        = True :=
        rewrite quietKeys argument (argAround arm previous at) low (Bool.andLeft within) (Bool.andLeft edge), docs
      (front, last, hug)

-- Chains.

theorem edgeLinkKeys ∀ (low: Nat) (level: Option Nat) (first: Bool) (expr: Expr) (around: Around) (lead end: Bool)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (edge: expr.edgeQuiet1 lead end = True):
    allKeysFrom low (linkDocs level first expr around) = True :=
  match expr, within with
    | Infix InfixBinary left operator right, within =>
      allKeysIf low _ _ _
        (edgePairKeys low level first left operator right around lead end
          (Bool.andLeft within)
          (Bool.andLeft (Bool.andRight within))
          (Bool.andLeft lexical)
          (Bool.andRight (Bool.andRight lexical))
          edge)
        (rewrite edgeKeys (Infix InfixBinary left operator right) around low lead end within lexical edge)
    | Infix InfixArrow left operator right, within =>
      allKeysIf low _ _ _
        (edgePairKeys low level first left operator right around lead end
          (Bool.andLeft within)
          (Bool.andLeft (Bool.andRight within))
          (Bool.andLeft lexical)
          (Bool.andRight (Bool.andRight lexical))
          edge)
        (rewrite edgeKeys (Infix InfixArrow left operator right) around low lead end within lexical edge)
    | Atom _ _, within => rewrite edgeKeys expr around low lead end within lexical edge
    | Paren _ _ _, within => rewrite edgeKeys expr around low lead end within lexical edge
    | Tuple _ _ _ _, within => rewrite edgeKeys expr around low lead end within lexical edge
    | ListOf _ _ _ _, within => rewrite edgeKeys expr around low lead end within lexical edge
    | App _ _, within => rewrite edgeKeys expr around low lead end within lexical edge
    | Prefix _ _, within => rewrite edgeKeys expr around low lead end within lexical edge

theorem edgePairKeys ∀ (low: Nat) (level: Option Nat) (first: Bool) (left: Expr) (operator: Word) (right: Expr)
    (around: Around) (lead end: Bool)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (leftLexical: left.lexical1 = True)
    (rightLexical: right.lexical1 = True)
    (edge: (left.edgeQuiet1 lead False && operator.quiet1 && right.edgeQuiet1 False end) = True):
    allKeysFrom low (chainLinks level first left operator right around) = True :=
  let rightAround := around.next operator.trails (left.size + 1)
  allKeysAppend low _ _
    (edgeLinkKeys low level first left around lead False leftWithin leftLexical (Bool.andLeft edge))
    (rewrite leafKeys low
          (around.next left.trails left.size).at
          operator
          (around.next left.trails left.size)
          (Bool.andLeft (Bool.andRight edge)),
        chainRightPlain level right rightAround rightWithin,
        edgeLinkKeys low level False right rightAround False end rightWithin rightLexical
          (Bool.andRight (Bool.andRight edge)))

-- The induction.

--| Every edge-quiet slice 1 expression's document has no keys below any floor.
--|
--| Proof idea: `quietKeys`' induction, each token that is no closer by `leafKeysOpen` (its own-line comments and its
--| trailing `LineSuffix` carry no key) and each closer, quiet, by `leafKeys`; the quiet items and arguments before
--| the last by `quietKeys`.
theorem edgeKeys ∀ (expr: Expr) (around: Around) (low: Nat) (lead end: Bool)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (edge: expr.edgeQuiet1 lead end = True):
    keysFrom low (expr.el around) = True :=
  let inside := { around | hoisted = True }
  let firstOpens: isCloserText expr.firstWord.text = False :=
    rewrite firstWordLead expr within then leadNotCloser expr within lexical
  match expr, within with
    | Atom kind word, within =>
      let (_, (_, _, closer, _)) := wordFacts kind word.text within
      leafKeysOpen low around.at word around closer
    | Prefix operator operand, within =>
      let (_, (_, _, closer, _)) := prefixToken operator.text (Bool.andRight within)
      let gap: keysFrom low (prefixGap operator operand) = True := match prefixGapIs operator operand with
        | Inl isNothing => rewrite isNothing
        | Inr isSpace => rewrite isSpace
      framedKeysOpen low operator around _ closer
        (keysConcat low _
          (rewrite leafKeysOpen low around.at operator inside closer,
              gap,
              edgeKeys operand
                (around.next operator.trails 1)
                low
                False
                end
                (Bool.andLeft within)
                (Bool.andRight lexical)
                (Bool.andRight edge)))
    | Paren open inner close, within =>
      let opens := parenOpens open.text (DecEq.sound (Bool.andLeft lexical))
      let closeQuiet: close.quiet1 = True := Bool.andRight (Bool.andRight edge)
      framedKeysOpen low open around _ opens
        (keysConcat low _
          (rewrite openingKeysOpen low open close inside opens closeQuiet,
              parenInnerPlain inner (inside.next open.trails 1) within,
              edgeKeys inner
                (inside.next open.trails 1)
                low
                False
                end
                within
                (Bool.andRight (Bool.andRight lexical))
                (Bool.andLeft (Bool.andRight edge)),
              leafKeys low inside.at close (inside.next inner.trails (1 + inner.size)) closeQuiet))
    | Tuple open items _ close, within =>
      framedKeysOpen low open around
        (commaBracket (list := False) open items close inside)
        (parenOpens open.text (DecEq.sound (Bool.andLeft lexical)))
        (edgeContentKeys low False open items close inside end
          (parenOpens open.text (DecEq.sound (Bool.andLeft lexical)))
          (Bool.andRight (Bool.andRight edge))
          within
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andLeft (Bool.andRight edge)))
    | ListOf open items _ close, within =>
      framedKeysOpen low open around
        (commaBracket (list := True) open items close inside)
        (bracketOpens open.text (DecEq.sound (Bool.andLeft lexical)))
        (edgeContentKeys low True open items close inside end
          (bracketOpens open.text (DecEq.sound (Bool.andLeft lexical)))
          (Bool.andRight (Bool.andRight edge))
          within
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andLeft (Bool.andRight edge)))
    | App head arguments, within =>
      let headEdge: head.edgeQuiet1 lead False = True := Bool.andLeft (Bool.andRight edge)
      let argumentsEdge: lastEdgeQuiet1 end arguments = True := Bool.andRight (Bool.andRight edge)
      let argumentDocsOf := argumentDocs inside.inArm head (inside.at + head.size) arguments
      let (docs, last, hug) :=
        edgeArgumentKeys low inside.inArm head
          (inside.at + head.size)
          arguments
          end
          (Bool.andRight within)
          (Bool.andRight lexical)
          argumentsEdge
      let lastDoc := (argumentDocsOf.snd.getOrElse (Nothing, None)).fst
      let lastAll: allKeysFrom low [lastDoc] = True := rewrite last
      let all := allKeysAppend low argumentDocsOf.fst [lastDoc] docs lastAll
      framedKeysOpen low
        (App head arguments).firstWord
        around
        (appDocs head arguments inside).doc
        firstOpens
        (rewrite appDocsIs head arguments inside then
          appFromKeys low _ _ _ _ _ _ _ _
            (rewrite edgeKeys head inside low lead False (Bool.andLeft within) (Bool.andLeft lexical) headEdge, all)
            hug)
    | Infix InfixBinary left operator right, within =>
      framedKeysOpen low
        (Infix InfixBinary left operator right).firstWord
        around _
        firstOpens
        (chainOfKeys low _ _
          (edgePairKeys low _ True left operator right inside lead end
            (Bool.andLeft within)
            (Bool.andLeft (Bool.andRight within))
            (Bool.andLeft lexical)
            (Bool.andRight (Bool.andRight lexical))
            edge))
    | Infix InfixArrow left operator right, within =>
      framedKeysOpen low
        (Infix InfixArrow left operator right).firstWord
        around _
        firstOpens
        (chainOfKeys low _ _
          (edgePairKeys low _ True left operator right inside lead end
            (Bool.andLeft within)
            (Bool.andLeft (Bool.andRight within))
            (Bool.andLeft lexical)
            (Bool.andRight (Bool.andRight lexical))
            edge))
