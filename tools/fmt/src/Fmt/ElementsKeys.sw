--| Two facts the node kinds of `Fmt.ElementsProofs` share (SW-4145, piece E2 of SW-4130's plan), for expressions with
--| comments anywhere inside:
--|
--| - `anyKeys`: every `Mark` and `CloserLine` of a slice 1 expression's document is keyed at or after the
--|   expression's own position (`around.at`), whatever its comments. A key belongs to a bracket pair and is its
--|   opener's position, and every opener of the expression stands at or after its first token; so `keysFrom` holds
--|   from any floor up to `around.at`. `Fmt.EdgeKeyProofs.edgeKeys` is the case with no keys at all.
--| - `ledItemHangs`: an expression with own-line comments above its first token, standing where it writes them as an
--|   item may (`around.item` either way), hangs from its seat with its first token on the line after them, at every
--|   entry but a plain line start under a kept blank line (`notedLeafHangs`' condition). A broken bracket's items
--|   enter after a line break or mid-line, never at a plain line start, so the condition holds of them.

namespace Fmt.ElementsKeys
import Std (Bool, DecEq, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Comments, Expr, InfixKind, Note, Tok, Word)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.MarkProofs (allKeysFrom, keysFrom)
import Fmt.AppHangProofs (appDocsIs, argAround)
import Fmt.ExprHangProofs (..)
import Fmt.QuietKeyProofs (ArgKeys, allKeysAppend, allKeysIf, appFromKeys, chainOfKeys, keysIf, pieceKeys)
import Fmt.EdgeKeyProofs (notesAboveKeys)
import Fmt.EdgeHangProofs (atomTrailsIs)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (lexKind)
import Fmt.DeclFactsProofs (leadNotCloser, notesOfWord, trailsOfSound)
import Fmt.BracketHangProofs (trailingKeys)

-- Keys.

theorem keysAbove ∀ (low at skipped: Nat) (floor: (low <= at) = True): (low <= at + skipped) = True :=
  Nat.leAddOfLeLeft low at skipped floor

theorem laterCloserNotesKeys ∀ (low: Nat) (notes: List Note): allKeysFrom low (laterCloserNotes notes) = True :=
  match notes with
    | [] => byComputing
    | [note, ..rest] =>
      allKeysAppend low
        [HardLine] _
        byComputing
        (allKeysAppend low _ _
          (allKeysIf low _ [Blank] [] byComputing byComputing)
          (rewrite laterCloserNotesKeys low rest))

--| Own-line comments before a closer are text and line breaks.
theorem closerNotesKeys ∀ (low: Nat) (notes: List Note): allKeysFrom low (closerNotes notes) = True := match notes with
  | [] => byComputing
  | [note, ..rest] =>
    allKeysAppend low _ _ (allKeysIf low _ [Blank] [] byComputing byComputing) (rewrite laterCloserNotesKeys low rest)

--| A token's own-line comments carry no key but a closer's `CloserLine`, at the key it is given.
theorem leadingKeysAt ∀ (low key: Nat) (word: Word) (around: Around)
    (floor: (low <= key) = True):
    allKeysFrom low (word.leading around key) = True :=
  match word with
    | { text, comments = { above, after, blankBefore } } =>
      match hoisted: around.hoisted, above with
        | True, _ => byComputing
        | False, [] => allKeysIf low _ [BreakParent, LineStart, Blank] [] byComputing byComputing
        | False, [note, ..rest] =>
          allKeysIf low _ _ _
            (rewrite keysConcat low
                  [LineStartHere, ..closerNotes [note, ..rest]]
                  (rewrite closerNotesKeys low [note, ..rest]),
                floor)
            (allKeysAppend low _ _
              (rewrite notesAboveKeys low [note, ..rest])
              (allKeysIf low _ [Blank] [] byComputing byComputing))

--| A token's keys are the one it is given.
theorem leafKeysAt ∀ (low key: Nat) (word: Word) (around: Around)
    (floor: (low <= key) = True):
    keysFrom low (word.leaf around key) = True :=
  let own: allKeysFrom low
    (if isCloserText word.text && !word.noted && around.before && word.trails then [CloserLine key] else [])
    = True :=
    allKeysIf low _ [CloserLine key] [] (rewrite floor) byComputing
  keysConcat low _
    (allKeysAppend low _ _
      (leadingKeysAt low key word around floor)
      (allKeysAppend low _ _ own
        (allKeysAppend low [piece word.text] _ (rewrite pieceKeys low word.text) (trailingKeys low word))))

--| An opener's keys are its own position, for its comments and its mark.
theorem openingKeysAt ∀ (low: Nat) (word closer: Word) (around: Around)
    (floor: (low <= around.at) = True):
    keysFrom low (word.opening around closer) = True :=
  let mark: allKeysFrom low (if closer.noted || closer.trails then [Mark around.at] else []) = True :=
    allKeysIf low _ [Mark around.at] [] (rewrite floor) byComputing
  keysConcat low _
    (allKeysAppend low _ _
      (leadingKeysAt low around.at word around floor)
      (allKeysAppend low _ _ mark
        (allKeysAppend low [piece word.text] _ (rewrite pieceKeys low word.text) (trailingKeys low word))))

--| A node framed by its first token keeps its contents' keys.
theorem framedKeysAt ∀ (low: Nat) (first: Word) (around: Around) (doc: Doc)
    (floor: (low <= around.at) = True)
    (keys: keysFrom low doc = True):
    keysFrom low (framedBy first around doc) = True :=
  keysConcat low _
    (rewrite keysConcat low (first.leading around around.at) (leadingKeysAt low around.at first around floor),
        keysIf low _ (Displaced doc) doc keys keys)

-- Brackets.

theorem anyCellsKeys ∀ (items: List Expr) (low: Nat) (bare arm before: Bool) (at: Nat)
    (within: allWithin1 items = True)
    (floor: (low <= at) = True):
    allKeysFrom low (cells bare arm before at items) = True :=
  match items with
    | [] => byComputing
    | [item] => rewrite anyKeys item (firstAround bare arm before at) low (Bool.andLeft within) floor
    | [item, next, ..more] =>
      let one := anyKeys item (firstAround bare arm before at) low (Bool.andLeft within) floor
      rewrite keysConcat low [item.el (firstAround bare arm before at), Closing ","] (rewrite one),
          anyCellsKeys
            [next, ..more]
            low
            False
            arm
            item.trails
            (at + item.size)
            (Bool.andRight within)
            (keysAbove low at item.size floor)

theorem anyBrokenKeys ∀ (items: List Expr) (low: Nat) (bare arm first before: Bool) (at: Nat)
    (within: allWithin1 items = True)
    (floor: (low <= at) = True):
    allKeysFrom low (brokenItems bare arm first before at items) = True :=
  match items with
    | [] => byComputing
    | [item] =>
      let one := anyKeys item (firstAround bare arm before at) low (Bool.andLeft within) floor
      match first with
        | True => rewrite one
        | False => rewrite one
    | [item, next, ..more] =>
      let one := anyKeys item (firstAround bare arm before at) low (Bool.andLeft within) floor
      let rest :=
        anyBrokenKeys
          [next, ..more]
          low
          False
          arm
          False
          item.trails
          (at + item.size)
          (Bool.andRight within)
          (keysAbove low at item.size floor)
      match first with
        | True => rewrite one, rest
        | False => rewrite one, rest

--| A bracket's parts, in any of `bracketContent`'s layouts.
theorem anyContentKeys ∀ (low: Nat) (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around)
    (floor: (low <= around.at) = True)
    (within: allWithin1 items = True):
    keysFrom low (bracketContent list open items close around) = True :=
  let prefix := openingKeysAt low open close around floor
  let closer :=
    leafKeysAt low around.at close
      (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
      floor
  let bare := list && items.all Expr.plainItem
  let partsList := [
    open.opening around close,
    Nest 2 (Doc.concat (brokenItems bare around.inArm True open.trails (around.at + 1) items)),
    SoftLine,
    close.leaf
      (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
      around.at
  ]
  let inner := keysAbove low around.at 1 floor
  let parts: allKeysFrom low partsList = True :=
    rewrite prefix,
        keysConcat low _ (anyBrokenKeys items low bare around.inArm True open.trails (around.at + 1) within inner),
        closer
  keysIf low _ _ _
    (keysConcat low _ (rewrite prefix, closer))
    (keysIf low _ _ _
      (keysConcat low _
        (rewrite prefix, anyCellsKeys items low bare around.inArm open.trails (around.at + 1) within inner, closer))
      (keysConcat low _
        (allKeysIf low _
          (partsList ++ [BreakParent])
          partsList
          (allKeysAppend low partsList [BreakParent] parts byComputing)
          parts)))

-- Calls.

--| A bracket hugged as a call's last argument keeps its keys, as it is and opened.
theorem anyHugKeys ∀ (low: Nat) (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around)
    (floor: (low <= around.at) = True)
    (within: allWithin1 items = True):
    keysFrom low (huggedBracket list open items close around).fst = True
      ∧ (∀ (opened: Doc) => (huggedBracket list open items close around).snd = Some opened
        → keysFrom low opened = True) :=
  let content := anyContentKeys low list open items close { around | hoisted = True } floor within
  (
    framedKeysAt low open around
      (Group
        (bracketContent list open items close { around | hoisted = True })
        (bracketContent list open items close { around | hoisted = True }).forcesBreak)
      floor
      content,
    opened same =>
      rewrite <- Option.someInjective same then
        framedKeysAt low open around
          (Group (bracketContent list open items close { around | hoisted = True }) True)
          floor
          content
  )

--| A slice 1 call's last argument keeps its keys, as it is and opened.
theorem anyLastKeys ∀ (low: Nat) (argument: Expr) (around: Around)
    (within: argument.within1 = True)
    (floor: (low <= around.at) = True):
    keysFrom low (lastArgument argument around).fst = True
      ∧ (∀ (open: Doc) => (lastArgument argument around).snd = Some open → keysFrom low open = True) :=
  let plain := anyKeys argument around low within floor
  match argument, within with
    | Atom _ _, _ => (plain, open never => cases)
    | Paren open inner close, within =>
      rewrite parenLast open inner close around within then (plain, opened never => cases)
    | App _ _ | Infix InfixBinary _ _ _ | Infix InfixArrow _ _ _ | Prefix _ _, _ => (plain, open never => cases)
    | Tuple open items trailing close, within => anyHugKeys low False open items close around floor within
    | ListOf open items trailing close, within => anyHugKeys low True open items close around floor within

theorem anyArgumentKeys ∀ (low: Nat) (arm: Bool) (previous: Expr) (at: Nat) (arguments: List Expr)
    (within: allWithin1 arguments = True)
    (floor: (low <= at) = True):
    ArgKeys low (argumentDocs arm previous at arguments) :=
  match arguments with
    | [] => (byComputing, byComputing, open never => cases)
    | [argument] =>
      let (last, hug) := anyLastKeys low argument (argAround arm previous at) (Bool.andLeft within) floor
      (byComputing, last, hug)
    | [argument, next, ..more] =>
      let (docs, last, hug) :=
        anyArgumentKeys low arm argument
          (at + argument.size)
          [next, ..more]
          (Bool.andRight within)
          (keysAbove low at argument.size floor)
      let front: allKeysFrom low [
        argument.el (argAround arm previous at),
        ..(argumentDocs arm argument (at + argument.size) [next, ..more]).fst
      ]
        = True :=
        rewrite anyKeys argument (argAround arm previous at) low (Bool.andLeft within) floor, docs
      (front, last, hug)

-- Chains.

theorem anyLinkKeys ∀ (low: Nat) (level: Option Nat) (first: Bool) (expr: Expr) (around: Around)
    (within: expr.within1 = True)
    (floor: (low <= around.at) = True):
    allKeysFrom low (linkDocs level first expr around) = True :=
  match expr, within with
    | Infix InfixBinary left operator right, within =>
      allKeysIf low _ _ _
        (anyPairKeys low level first left operator right around
          (Bool.andLeft within)
          (Bool.andLeft (Bool.andRight within))
          floor)
        (rewrite anyKeys (Infix InfixBinary left operator right) around low within floor)
    | Infix InfixArrow left operator right, within =>
      allKeysIf low _ _ _
        (anyPairKeys low level first left operator right around
          (Bool.andLeft within)
          (Bool.andLeft (Bool.andRight within))
          floor)
        (rewrite anyKeys (Infix InfixArrow left operator right) around low within floor)
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ | Prefix _ _, within =>
      rewrite anyKeys expr around low within floor

theorem anyPairKeys ∀ (low: Nat) (level: Option Nat) (first: Bool) (left: Expr) (operator: Word)
    (right: Expr) (around: Around)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (floor: (low <= around.at) = True):
    allKeysFrom low (chainLinks level first left operator right around) = True :=
  let rightAround := around.next operator.trails (left.size + 1)
  allKeysAppend low _ _
    (anyLinkKeys low level first left around leftWithin floor)
    (rewrite leafKeysAt low
          (around.next left.trails left.size).at
          operator
          (around.next left.trails left.size)
          (keysAbove low around.at left.size floor),
        chainRightPlain level right rightAround rightWithin,
        anyLinkKeys low level False right rightAround rightWithin (keysAbove low around.at (left.size + 1) floor))

-- The induction.

--| Every slice 1 expression's document keys its marks and closer lines at or after its own position, whatever its
--| comments: so `keysFrom` holds from any floor up to `around.at`.
--|
--| Proof idea: `edgeKeys`' induction, each token by `leafKeysAt` with the key it is given (its own position, or its
--| bracket's opener's for a closer), each opener by `openingKeysAt`; every part of a node stands at or after the
--| node's position (`around.next` adds to it), so the floor carries down.
theorem anyKeys ∀ (expr: Expr) (around: Around) (low: Nat)
    (within: expr.within1 = True)
    (floor: (low <= around.at) = True):
    keysFrom low (expr.el around) = True :=
  let inside := { around | hoisted = True }
  let after := keysAbove low around.at 1 floor
  match expr, within with
    | Atom kind word, within => leafKeysAt low around.at word around floor
    | Prefix operator operand, within =>
      let gap: keysFrom low (prefixGap operator operand) = True := match prefixGapIs operator operand with
        | Inl isNothing => rewrite isNothing
        | Inr isSpace => rewrite isSpace
      framedKeysAt low operator around _ floor
        (keysConcat low _
          (rewrite leafKeysAt low around.at operator inside floor,
              gap,
              anyKeys operand (around.next operator.trails 1) low (Bool.andLeft within) after))
    | Paren open inner close, within =>
      framedKeysAt low open around _ floor
        (keysConcat low _
          (rewrite openingKeysAt low open close inside floor,
              parenInnerPlain inner (inside.next open.trails 1) within,
              anyKeys inner (inside.next open.trails 1) low within after,
              leafKeysAt low inside.at close (inside.next inner.trails (1 + inner.size)) floor))
    | Tuple open items _ close, within =>
      framedKeysAt low open around
        (commaBracket (list := False) open items close inside)
        floor
        (anyContentKeys low False open items close inside floor within)
    | ListOf open items _ close, within =>
      framedKeysAt low open around
        (commaBracket (list := True) open items close inside)
        floor
        (anyContentKeys low True open items close inside floor within)
    | App head arguments, within =>
      let argumentDocsOf := argumentDocs inside.inArm head (inside.at + head.size) arguments
      let (docs, last, hug) :=
        anyArgumentKeys low inside.inArm head
          (inside.at + head.size)
          arguments
          (Bool.andRight within)
          (keysAbove low around.at head.size floor)
      let lastDoc := (argumentDocsOf.snd.getOrElse (Nothing, None)).fst
      let lastAll: allKeysFrom low [lastDoc] = True := rewrite last
      let all := allKeysAppend low argumentDocsOf.fst [lastDoc] docs lastAll
      framedKeysAt low
        (App head arguments).firstWord
        around
        (appDocs head arguments inside).doc
        floor
        (rewrite appDocsIs head arguments inside then
          appFromKeys low _ _ _ _ _ _ _ _ (rewrite anyKeys head inside low (Bool.andLeft within) floor, all) hug)
    | Infix InfixBinary left operator right, within =>
      framedKeysAt low
        (Infix InfixBinary left operator right).firstWord
        around _
        floor
        (chainOfKeys low _ _
          (anyPairKeys low _ True left operator right inside
            (Bool.andLeft within)
            (Bool.andLeft (Bool.andRight within))
            floor))
    | Infix InfixArrow left operator right, within =>
      framedKeysAt low
        (Infix InfixArrow left operator right).firstWord
        around _
        floor
        (chainOfKeys low _ _
          (anyPairKeys low _ True left operator right inside
            (Bool.andLeft within)
            (Bool.andLeft (Bool.andRight within))
            floor))

-- An item with comments above its first token.

--| What an element whose first token has own-line comments above it gives at one entry: laid from its seat there,
--| its first token at the start of the line after the comments (`leadStart`), it ends after words as one token.
def LedAt (kinds: Text → Tok) (doc: Doc) (indent: Nat) (before trails: Bool) (state: HangState) (entry: Place): Prop :=
  HangLays kinds doc indent (Entered indent indent before state entry (leadStart indent entry)) (place hang =>
    Ended (openedBy state (leadStart indent entry)) trails place
      ∧ hang = Hang.At (openedBy state (leadStart indent entry)))

--| `notedFramedHangs` at one entry, its blank-line condition `notedLeafHangs`': a blank line kept above the first
--| comment, before an item, is not at a plain line start, where it may print nothing.
theorem notedFramedAt ∀ (kinds: Text → Tok) (first: Word) (around: Around) (doc: Doc) (indent: Nat) (trails: Bool)
    (state: HangState) (entry: Place) (note: Note) (rest: List Note)
    (hoisted: around.hoisted = False)
    (noted: first.comments.above = [note, ..rest])
    (closer: isCloserText first.text = False)
    (comments: NotesComment [note, ..rest])
    (framed: ∀ (inset: Nat) => ElHangs kinds
      (Doc.concat [Doc.concat [], Displaced doc])
      inset
      inset
      around.before
      trails
      wordStart):
    LedAt kinds (framedBy first around doc) indent around.before trails state entry :=
  hangsBy (place trace next entered after =>
    match entered with
      | (_, _, (seated, _, _, room)) =>
        let column := leadColumn indent entry
        let opened := openedBy state (Some column)
        let pre := Entered indent indent around.before state entry (leadStart indent entry)
        let lined := LineAt indent column (Hang.At state)
        let post: Place → Hang → Prop := place hang => Ended opened trails place ∧ hang = Hang.At opened
        let leadingDocs := first.leading around around.at
        let leading :=
          hangsConcat
            (allHangsPre
              [weaker := pre]
              (leadingHangs kinds first around around.at indent around.before state entry note rest hoisted noted closer
                  comments
                  (leadFresh indent state entry room))
              (place hang (isEntry, folded, (seated, _, _, _)) => (isEntry, folded, seated)))
        let displaced :=
          linedDisplaced kinds doc indent column around.before trails state
            (leadDeep indent around.before state entry seated (leadFresh indent state entry room))
            room
            framed
        let isNoted: first.noted = True := rewrite noted
        let unframed: framedBy first around doc = Doc.concat [Doc.concat leadingDocs, Displaced doc] := rewrite isNoted
        rewrite unframed then
          hangsConcat (hangsTwo leading displaced) place _ trace next byComputing entered (hangsAfter after))

--| A node with own-line comments above its first token, at one entry (`edgeNotedNodeHangs` with `notedFramedAt`).
theorem notedNodeAt ∀ (expr: Expr) (word: Word) (node: Around → Doc) (around: Around) (indent: Nat) (trails: Bool)
    (state: HangState) (entry: Place) (note: Note) (rest: List Note)
    (elIs: ∀ (at: Around) => expr.el at = framedBy word at (node at))
    (same: node { around | hoisted = True } = node around)
    (hoisted: around.hoisted = False)
    (noted: word.comments.above = [note, ..rest])
    (closer: isCloserText word.text = False)
    (comments: NotesComment [note, ..rest])
    (hoistedHangs: ∀ (inset: Nat) => ElHangs lexKind
      (expr.el { around | hoisted = True })
      inset
      inset
      around.before
      trails
      wordStart):
    LedAt lexKind (expr.el around) indent around.before trails state entry :=
  let lifted := { around | hoisted = True }
  let isNoted: word.noted = True := rewrite noted
  let unwrapped: framedBy word lifted (node lifted) = Doc.concat [Doc.concat [], Displaced (node around)] :=
    rewrite isNoted, same
  rewrite elIs around then
    notedFramedAt lexKind word around
      (node around)
      indent
      trails
      state
      entry
      note
      rest
      hoisted
      noted
      closer
      comments
      (inset =>
        let fact := hoistedHangs inset
        rewrite elIs lifted, unwrapped at fact then fact)

--| A slice 1 expression with own-line comments above its first token, standing where it writes them (not hoisted;
--| an item or not), hangs from its seat at any entry but a plain line start under a kept blank line: its first token
--| starts the line after the comments. `hoistedHangs` is the expression with its comments written elsewhere, which
--| `AnyFacts` gives (`Fmt.ElementsProofs.anyHangsOf`, plain when hoisted).
--|
--| Proof idea: `ledHangs`' noted cases with the blank-line condition kept per entry: a name or numeral by
--| `notedLeafHangs`, a node by `notedNodeAt` from its hoisted form.
theorem ledItemHangs ∀ (expr: Expr) (around: Around) (indent: Nat) (state: HangState) (entry: Place)
    (note: Note) (rest: List Note)
    (within: expr.within1 = True)
    (lexical: expr.lexical = True)
    (sound: expr.sound = True)
    (hoisted: around.hoisted = False)
    (noted: expr.lead.comments.above = [note, ..rest])
    (hoistedHangs: ∀ (inset: Nat) => ElHangs lexKind
      (expr.el { around | hoisted = True })
      inset
      inset
      around.before
      expr.trails
      wordStart):
    LedAt lexKind (expr.el around) indent around.before expr.trails state entry :=
  let base := notesOfWord expr.lead (leadSound expr sound)
  let comments: NotesComment [note, ..rest] := rewrite noted at base then base
  let closer := leadNotCloser expr within lexical
  match expr, within with
    | Atom kind word, within =>
      let (plain, (notComment, solid, wordCloser, comma)) := wordFacts kind word.text within
      rewrite atomTrailsIs kind word then
        notedLeafHangs lexKind word around around.at indent state entry note rest plain notComment solid wordCloser
            comma hoisted noted comments
            (trailsOfSound word sound)
    | Paren open inner close, _ =>
      notedNodeAt
        (Paren open inner close)
        open
        (at => parenDoc open inner close { at | hoisted = True })
        around
        indent
        (Paren open inner close).trails
        state
        entry
        note
        rest
        (at => byComputing)
        byComputing
        hoisted
        noted
        closer
        comments
        hoistedHangs
    | Tuple open items trailing close, _ =>
      notedNodeAt
        (Tuple open items trailing close)
        open
        (at => commaBracket (list := False) open items close { at | hoisted = True })
        around
        indent
        (Tuple open items trailing close).trails
        state
        entry
        note
        rest
        (at => byComputing)
        byComputing
        hoisted
        noted
        closer
        comments
        hoistedHangs
    | ListOf open items trailing close, _ =>
      notedNodeAt
        (ListOf open items trailing close)
        open
        (at => commaBracket (list := True) open items close { at | hoisted = True })
        around
        indent
        (ListOf open items trailing close).trails
        state
        entry
        note
        rest
        (at => byComputing)
        byComputing
        hoisted
        noted
        closer
        comments
        hoistedHangs
    | App head arguments, within =>
      let node: Around → Doc := at => (appDocs head arguments { at | hoisted = True }).doc
      notedNodeAt
        (App head arguments)
        head.lead
        node
        around
        indent
        (App head arguments).trails
        state
        entry
        note
        rest
        (at =>
          let unfolded: (App head arguments).el at = framedBy (App head arguments).firstWord at (node at) := byComputing
          Eq.trans unfolded (Eq.cong (word => framedBy word at (node at)) (firstWordLead (App head arguments) within)))
        byComputing
        hoisted
        noted
        closer
        comments
        hoistedHangs
    | Infix InfixBinary left operator right, within =>
      let expr := Infix InfixBinary left operator right
      let node: Around → Doc := at => chain expr.chainLevel left operator right { at | hoisted = True }
      notedNodeAt expr left.lead node around indent expr.trails state entry note rest
        (at =>
          let unfolded: expr.el at = framedBy expr.firstWord at (node at) := byComputing
          Eq.trans unfolded (Eq.cong (word => framedBy word at (node at)) (firstWordLead expr within)))
        byComputing
        hoisted
        noted
        closer
        comments
        hoistedHangs
    | Infix InfixArrow left operator right, within =>
      let expr := Infix InfixArrow left operator right
      let node: Around → Doc := at => chain expr.chainLevel left operator right { at | hoisted = True }
      notedNodeAt expr left.lead node around indent expr.trails state entry note rest
        (at =>
          let unfolded: expr.el at = framedBy expr.firstWord at (node at) := byComputing
          Eq.trans unfolded (Eq.cong (word => framedBy word at (node at)) (firstWordLead expr within)))
        byComputing
        hoisted
        noted
        closer
        comments
        hoistedHangs
    | Prefix operator operand, _ =>
      notedNodeAt
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
        state
        entry
        note
        rest
        (at => byComputing)
        byComputing
        hoisted
        noted
        closer
        comments
        hoistedHangs
