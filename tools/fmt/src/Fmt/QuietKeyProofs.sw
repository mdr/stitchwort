--| `QuietKeys` (ticket 18h): a quiet slice 1 expression's document has no `Mark` or `CloserLine` below any key
--| floor, since only comments make them: a closer's line of its own needs a comment, an opener's mark a commented
--| closer. So `exprFacts` holds with no hypothesis beyond the expression's (`quietExprFacts`).

namespace Fmt.QuietKeyProofs
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Syntax (Comments, Expr, InfixKind, Word)
import Fmt (..)
import Fmt.HangProofs (Gap, prefixGapIs)
import Fmt.MarkProofs (allKeysFrom, keysFrom)
import Fmt.AppHangProofs (appDocsIs, argAround)
import Fmt.BracketHangProofs (huggedBracketIs)
import Fmt.ExprHangProofs (..)

-- Lists of documents.

theorem allKeysAppend ∀ (low: Nat) (front back: List Doc)
    (first: allKeysFrom low front = True)
    (second: allKeysFrom low back = True):
    allKeysFrom low (front ++ back) = True :=
  match front with
    | [] => second
    | [doc, ..rest] => rewrite Bool.andLeft first, allKeysAppend low rest back (Bool.andRight first) second

theorem allKeysFront ∀ (low: Nat) (front back: List Doc)
    (all: allKeysFrom low (front ++ back) = True):
    allKeysFrom low front = True :=
  match front with
    | [] => byComputing
    | [doc, ..rest] => rewrite Bool.andLeft all, allKeysFront low rest back (Bool.andRight all)

theorem allKeysTake ∀ (low: Nat) (docs: List Doc) (count: Nat)
    (all: allKeysFrom low docs = True):
    allKeysFrom low (docs.take count) = True :=
  match docs, count with
    | _, Zero => byComputing
    | [], Succ _ => byComputing
    | [doc, ..rest], Succ count => rewrite Bool.andLeft all, allKeysTake low rest count (Bool.andRight all)

theorem allKeysDrop ∀ (low: Nat) (docs: List Doc) (count: Nat)
    (all: allKeysFrom low docs = True):
    allKeysFrom low (docs.drop count) = True :=
  match docs, count with
    | _, Zero => all
    | [], Succ _ => byComputing
    | [doc, ..rest], Succ count => allKeysDrop low rest count (Bool.andRight all)

theorem allKeysHard ∀ (low: Nat) (docs: List Doc)
    (all: allKeysFrom low docs = True):
    allKeysFrom low (docs.concatMap (doc => [HardLine, doc])) = True :=
  match docs with
    | [] => byComputing
    | [doc, ..rest] => rewrite Bool.andLeft all, allKeysHard low rest (Bool.andRight all)

theorem joinedKeys ∀ (low: Nat) (docs: List Doc)
    (all: allKeysFrom low docs = True):
    allKeysFrom low (Doc.joinedWith (Doc.text " ") docs) = True :=
  match docs with
    | [] => byComputing
    | [only] => all
    | [doc, next, ..more] => rewrite Bool.andLeft all, joinedKeys low [next, ..more] (Bool.andRight all)

theorem keysSpaced ∀ (low: Nat) (docs: List Doc)
    (all: allKeysFrom low docs = True):
    keysFrom low (spaced docs) = True :=
  keysConcat low (Doc.joinedWith (Doc.text " ") docs) (joinedKeys low docs all)

theorem keysIf ∀ (low: Nat) (cond: Bool) (yes no: Doc)
    (first: keysFrom low yes = True)
    (second: keysFrom low no = True):
    keysFrom low (if cond then yes else no) = True :=
  match cond with
    | True => first
    | False => second

theorem allKeysIf ∀ (low: Nat) (cond: Bool) (yes no: List Doc)
    (first: allKeysFrom low yes = True)
    (second: allKeysFrom low no = True):
    allKeysFrom low (if cond then yes else no) = True :=
  match cond with
    | True => first
    | False => second

-- Tokens.

theorem quietNoted ∀ (word: Word) (quiet: word.quiet1 = True): word.noted = False := match word, quiet with
  | { text, comments = { above = [], after = None, blankBefore = False } }, _ => byComputing

theorem trailingKeys ∀ (low: Nat) (word: Word): allKeysFrom low word.trailing = True := match word.comments.after with
  | Some _ => byComputing
  | None => byComputing

theorem pieceKeys ∀ (low: Nat) (text: Text): keysFrom low (piece text) = True :=
  keysIf low _ (Closing text) (Doc.text text) byComputing byComputing

--| A quiet token has no line of its own, so no `CloserLine`.
theorem leafKeys ∀ (low key: Nat) (word: Word) (around: Around)
    (quiet: word.quiet1 = True):
    keysFrom low (word.leaf around key) = True :=
  let own: allKeysFrom low
    (if isCloserText word.text && !word.noted && around.before && word.trails then [CloserLine key] else [])
    = True :=
    rewrite quietNoTrail word quiet,
        Bool.andFalse around.before,
        Bool.andFalse (!word.noted),
        Bool.andFalse (isCloserText word.text)
  keysConcat low _
    (allKeysAppend low _ _
      (rewrite quietLeading word around key quiet)
      (allKeysAppend low _ _ own
        (allKeysAppend low [piece word.text] _ (rewrite pieceKeys low word.text) (trailingKeys low word))))

--| A quiet opener before a quiet closer has no mark.
theorem openingKeys ∀ (low: Nat) (word closer: Word) (around: Around)
    (quiet: word.quiet1 = True)
    (closerQuiet: closer.quiet1 = True):
    keysFrom low (word.opening around closer) = True :=
  let mark: allKeysFrom low (if closer.noted || closer.trails then [Mark around.at] else []) = True :=
    rewrite quietNoted closer closerQuiet, quietNoTrail closer closerQuiet
  keysConcat low _
    (allKeysAppend low _ _
      (rewrite quietLeading word around around.at quiet)
      (allKeysAppend low _ _ mark
        (allKeysAppend low [piece word.text] _ (rewrite pieceKeys low word.text) (trailingKeys low word))))

--| A node framed by a quiet first token keeps its contents' keys.
theorem framedKeys ∀ (low: Nat) (first: Word) (around: Around) (doc: Doc)
    (quiet: first.quiet1 = True)
    (keys: keysFrom low doc = True):
    keysFrom low (framedBy first around doc) = True :=
  keysConcat low _ (rewrite quietLeading first around around.at quiet, keysIf low _ (Displaced doc) doc keys keys)

-- Brackets.

--| A quiet bracket's items in cells keep their keys (`cellsKeys`, with the induction's own step).
theorem cellsQuiet ∀ (items: List Expr) (low: Nat) (bare arm before: Bool) (at: Nat)
    (within: allWithin1 items = True)
    (quiet: allQuiet1 items = True):
    allKeysFrom low (cells bare arm before at items) = True :=
  match items with
    | [] => byComputing
    | [item] => rewrite quietKeys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft quiet)
    | [item, next, ..more] =>
      let one := quietKeys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft quiet)
      rewrite keysConcat low [item.el (firstAround bare arm before at), Closing ","] (rewrite one),
          cellsQuiet [next, ..more] low False arm False (at + item.size) (Bool.andRight within) (Bool.andRight quiet)

--| A quiet bracket's items, one a line, keep their keys (`brokenKeys`, with the induction's own step).
theorem brokenQuiet ∀ (items: List Expr) (low: Nat) (bare arm first before: Bool) (at: Nat)
    (within: allWithin1 items = True)
    (quiet: allQuiet1 items = True):
    allKeysFrom low (brokenItems bare arm first before at items) = True :=
  match items with
    | [] => byComputing
    | [item] =>
      match first with
        | True => rewrite quietKeys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft quiet)
        | False =>
          rewrite quietKeys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft quiet)
    | [item, next, ..more] =>
      let rest :=
        brokenQuiet
          [next, ..more]
          low
          False
          arm
          False
          False
          (at + item.size)
          (Bool.andRight within)
          (Bool.andRight quiet)
      match first with
        | True =>
          rewrite quietKeys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft quiet), rest
        | False =>
          rewrite quietKeys item (firstAround bare arm before at) low (Bool.andLeft within) (Bool.andLeft quiet), rest

--| A quiet bracket's parts, in any of `bracketContent`'s layouts.
theorem contentKeys ∀ (low: Nat) (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around)
    (openQuiet: open.quiet1 = True)
    (closeQuiet: close.quiet1 = True)
    (within: allWithin1 items = True)
    (quiet: allQuiet1 items = True):
    keysFrom low (bracketContent list open items close around) = True :=
  let prefix := openingKeys low open close around openQuiet closeQuiet
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
        keysConcat low _ (brokenQuiet items low bare around.inArm True open.trails (around.at + 1) within quiet),
        closer
  keysIf low _ _ _
    (keysConcat low _ (rewrite prefix, closer))
    (keysIf low _ _ _
      (keysConcat low _
        (rewrite prefix, cellsQuiet items low bare around.inArm open.trails (around.at + 1) within quiet, closer))
      (keysConcat low _
        (allKeysIf low _
          (partsList ++ [BreakParent])
          partsList
          (allKeysAppend low partsList [BreakParent] parts byComputing)
          parts)))

-- Calls.

--| A call's layouts keep its elements' keys, and its hug's.
--|
--| Proof idea: every layout of `appFrom` is built from the elements (spaced, filled, flattened, taken, dropped, each
--| after a `HardLine`) and the hug, so each list lemma above keeps the keys.
theorem appFromKeys ∀ (low id keep: Nat) (between betweenFront: Bool) (headDoc: Doc) (front: List Doc)
    (lastDoc: Doc) (hug: Option Doc)
    (all: allKeysFrom low ([headDoc, ..front] ++ [lastDoc]) = True)
    (hugKeys: ∀ (open: Doc) => hug = Some open → keysFrom low open = True):
    keysFrom low (appFrom id keep between betweenFront headDoc front lastDoc hug).doc = True :=
  let docs := [headDoc, ..front] ++ [lastDoc]
  let flat := keysSpaced low docs all
  let frontKeys := allKeysFront low [headDoc, ..front] [lastDoc] all
  let hugged: allKeysFrom low
    (optionList (hug.map (open => Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", open])))
    = True :=
    match hug, hugKeys with
      | None, _ => byComputing
      | Some open, hugKeys =>
        rewrite keysConcat low
          [Flatten (spaced [headDoc, ..front]), Doc.text " ", open]
          (rewrite keysSpaced low [headDoc, ..front] frontKeys, hugKeys open byComputing)
  let kept := allKeysTake low docs keep all
  let rest := keysConcat low _ (allKeysHard low (docs.drop keep) (allKeysDrop low docs keep all))
  let restTail := Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))
  let filled: keysFrom low (IdGroup id (Nest 4 (Fill (docs.take keep))) False) = True := kept
  let frontDoc :=
    keysIf low
      (keep > 2 && !betweenFront)
      (IdGroup id (Nest 4 (Fill (docs.take keep))) False)
      (spaced (docs.take keep))
      filled
      (keysSpaced low (docs.take keep) kept)
  let restDoc :=
    keysIf low
      (keep > 2 && !betweenFront)
      (IfBroken id (Nest 4 restTail) (Nest 2 restTail))
      (Nest 2 restTail)
      (rewrite rest)
      rest
  let broken :=
    keysConcat low
      [
        if keep > 2 && !betweenFront then IdGroup id (Nest 4 (Fill (docs.take keep))) False
        else spaced (docs.take keep),
        if keep > 2 && !betweenFront then IfBroken id (Nest 4 restTail) (Nest 2 restTail) else Nest 2 restTail
      ]
      (rewrite frontDoc, restDoc)
  let chosen: allKeysFrom low
    ([Flatten (spaced docs)]
      ++ optionList (hug.map (open => Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", open]))
      ++ [
        Doc.concat [
          if keep > 2 && !betweenFront then IdGroup id (Nest 4 (Fill (docs.take keep))) False
          else spaced (docs.take keep),
          if keep > 2 && !betweenFront then
            IfBroken id
              (Nest 4 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
              (Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))))
          else Nest 2 (Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc])))
        ]
      ])
    = True :=
    allKeysAppend low _ _ (rewrite flat) (allKeysAppend low _ _ hugged (rewrite broken))
  match whole: keep == docs.length with
    | True =>
      match between with
        | True => flat
        | False => all
    | False => chosen

--| A quiet slice 1 call's last argument keeps its keys, as it is and opened.
theorem lastKeys ∀ (low: Nat) (argument: Expr) (around: Around)
    (within: argument.within1 = True)
    (quiet: argument.quiet1 = True):
    keysFrom low (lastArgument argument around).fst = True
      ∧ (∀ (open: Doc) => (lastArgument argument around).snd = Some open → keysFrom low open = True) :=
  let plain := quietKeys argument around low within quiet
  match argument, within with
    | Atom _ _, _ => (plain, open never => cases)
    | Paren open inner close, within =>
      rewrite parenLast open inner close around within then (plain, opened never => cases)
    | App _ _, _ => (plain, open never => cases)
    | Infix InfixBinary _ _ _, _ => (plain, open never => cases)
    | Infix InfixArrow _ _ _, _ => (plain, open never => cases)
    | Prefix _ _, _ => (plain, open never => cases)
    | Tuple open items trailing close, within =>
      hugKeys low False open items close around
        (Bool.andLeft quiet)
        (Bool.andRight (Bool.andRight quiet))
        within
        (Bool.andLeft (Bool.andRight quiet))
    | ListOf open items trailing close, within =>
      hugKeys low True open items close around
        (Bool.andLeft quiet)
        (Bool.andRight (Bool.andRight quiet))
        within
        (Bool.andLeft (Bool.andRight quiet))

--| A quiet bracket hugged as a call's last argument keeps its keys, as it is and opened.
theorem hugKeys ∀ (low: Nat) (list: Bool) (open: Word) (items: List Expr) (close: Word) (around: Around)
    (openQuiet: open.quiet1 = True)
    (closeQuiet: close.quiet1 = True)
    (within: allWithin1 items = True)
    (quiet: allQuiet1 items = True):
    keysFrom low (huggedBracket list open items close around).fst = True
      ∧ (∀ (opened: Doc) => (huggedBracket list open items close around).snd = Some opened
        → keysFrom low opened = True) :=
  let content := contentKeys low list open items close { around | hoisted = True } openQuiet closeQuiet within quiet
  rewrite huggedBracketIs list open items close around (quietLeading open around around.at openQuiet) then
    (content, opened same => rewrite <- Option.someInjective same then content)

--| What a call's arguments' documents keep: the documents before the last, the last's and its hug's.
def ArgKeys (low: Nat) (docs: (List Doc, Option (Doc, Option Doc))): Prop :=
  allKeysFrom low docs.fst = True
    ∧ keysFrom low (docs.snd.getOrElse (Nothing, None)).fst = True
    ∧ (∀ (open: Doc) => (docs.snd.getOrElse (Nothing, None)).snd = Some open → keysFrom low open = True)

theorem argumentDocsCons ∀ (arm: Bool) (previous: Expr) (at: Nat) (argument next: Expr) (more: List Expr):
    argumentDocs arm previous at [argument, next, ..more]
      = (
        [
          argument.el (argAround arm previous at),
          ..(argumentDocs arm argument (at + argument.size) [next, ..more]).fst
        ],
        (argumentDocs arm argument (at + argument.size) [next, ..more]).snd
      ) :=
  match pair: argumentDocs arm argument (at + argument.size) [next, ..more] with | (docs, last) => byComputing

theorem argumentKeys ∀ (low: Nat) (arm: Bool) (previous: Expr) (at: Nat) (arguments: List Expr)
    (within: allWithin1 arguments = True)
    (quiet: allQuiet1 arguments = True):
    ArgKeys low (argumentDocs arm previous at arguments) :=
  match arguments with
    | [] => (byComputing, byComputing, open never => cases)
    | [argument] =>
      let (last, hug) := lastKeys low argument (argAround arm previous at) (Bool.andLeft within) (Bool.andLeft quiet)
      (byComputing, last, hug)
    | [argument, next, ..more] =>
      let (docs, last, hug) :=
        argumentKeys low arm argument (at + argument.size) [next, ..more] (Bool.andRight within) (Bool.andRight quiet)
      let front: allKeysFrom low [
        argument.el (argAround arm previous at),
        ..(argumentDocs arm argument (at + argument.size) [next, ..more]).fst
      ]
        = True :=
        rewrite quietKeys argument (argAround arm previous at) low (Bool.andLeft within) (Bool.andLeft quiet), docs
      (front, last, hug)

-- Chains.

theorem chainOfKeys ∀ (low: Nat) (arms: Bool) (links: List Doc)
    (all: allKeysFrom low links = True):
    keysFrom low (chainOf arms links) = True :=
  match links with
    | [] => byComputing
    | [head, ..tail] =>
      rewrite keysConcat low
        [head, Nest (if arms then 0 else 2) (Doc.concat tail)]
        (rewrite Bool.andLeft all, keysConcat low tail (Bool.andRight all))

--| A quiet slice 1 chain's links keep their operands' and operators' keys.
theorem linkKeys ∀ (low: Nat) (level: Option Nat) (first: Bool) (expr: Expr) (around: Around)
    (within: expr.within1 = True)
    (quiet: expr.quiet1 = True):
    allKeysFrom low (linkDocs level first expr around) = True :=
  match expr, within with
    | Infix InfixBinary left operator right, within =>
      allKeysIf low _ _ _
        (pairKeys low level first left operator right around
          (Bool.andLeft within)
          (Bool.andLeft (Bool.andRight within))
          quiet)
        (rewrite quietKeys (Infix InfixBinary left operator right) around low within quiet)
    | Infix InfixArrow left operator right, within =>
      allKeysIf low _ _ _
        (pairKeys low level first left operator right around
          (Bool.andLeft within)
          (Bool.andLeft (Bool.andRight within))
          quiet)
        (rewrite quietKeys (Infix InfixArrow left operator right) around low within quiet)
    | Atom _ _, within => rewrite quietKeys expr around low within quiet
    | Paren _ _ _, within => rewrite quietKeys expr around low within quiet
    | Tuple _ _ _ _, within => rewrite quietKeys expr around low within quiet
    | ListOf _ _ _ _, within => rewrite quietKeys expr around low within quiet
    | App _ _, within => rewrite quietKeys expr around low within quiet
    | Prefix _ _, within => rewrite quietKeys expr around low within quiet

theorem pairKeys ∀ (low: Nat) (level: Option Nat) (first: Bool) (left: Expr) (operator: Word)
    (right: Expr) (around: Around)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (quiet: (left.quiet1 && operator.quiet1 && right.quiet1) = True):
    allKeysFrom low (chainLinks level first left operator right around) = True :=
  let rightAround := around.next operator.trails (left.size + 1)
  allKeysAppend low _ _
    (linkKeys low level first left around leftWithin (Bool.andLeft quiet))
    (rewrite leafKeys low
          (around.next left.trails left.size).at
          operator
          (around.next left.trails left.size)
          (Bool.andLeft (Bool.andRight quiet)),
        chainRightPlain level right rightAround rightWithin,
        linkKeys low level False right rightAround rightWithin (Bool.andRight (Bool.andRight quiet)))

-- The induction.

--| Every quiet slice 1 expression's document has no keys below any floor.
--|
--| Proof idea: by the expression, through its rule: a token (`leafKeys`), framed (`framedKeys`) around a prefix's
--| parts, a paren's or bracket's (`openingKeys`, `contentKeys`), a call's layouts (`appFromKeys` over `argumentKeys`
--| and `lastKeys`), or a chain's links (`chainOfKeys`, `pairKeys`).
theorem quietKeys: QuietKeys := expr around low within quiet =>
  let inside := { around | hoisted = True }
  match expr, within with
    | Atom _ word, _ => leafKeys low around.at word around quiet
    | Prefix operator operand, within =>
      let gap: keysFrom low (prefixGap operator operand) = True := match prefixGapIs operator operand with
        | Inl isNothing => rewrite isNothing
        | Inr isSpace => rewrite isSpace
      framedKeys low operator around _
        (Bool.andLeft quiet)
        (keysConcat low _
          (rewrite leafKeys low around.at operator inside (Bool.andLeft quiet),
              gap,
              quietKeys operand (around.next operator.trails 1) low (Bool.andLeft within) (Bool.andRight quiet)))
    | Paren open inner close, within =>
      framedKeys low open around _
        (Bool.andLeft quiet)
        (keysConcat low _
          (rewrite openingKeys low open close inside (Bool.andLeft quiet) (Bool.andRight (Bool.andRight quiet)),
              parenInnerPlain inner (inside.next open.trails 1) within,
              quietKeys inner (inside.next open.trails 1) low within (Bool.andLeft (Bool.andRight quiet)),
              leafKeys low inside.at close
                (inside.next inner.trails (1 + inner.size))
                (Bool.andRight (Bool.andRight quiet))))
    | Tuple open items _ close, within =>
      framedKeys low open around
        (commaBracket (list := False) open items close inside)
        (Bool.andLeft quiet)
        (contentKeys low False open items close inside
          (Bool.andLeft quiet)
          (Bool.andRight (Bool.andRight quiet))
          within
          (Bool.andLeft (Bool.andRight quiet)))
    | ListOf open items _ close, within =>
      framedKeys low open around
        (commaBracket (list := True) open items close inside)
        (Bool.andLeft quiet)
        (contentKeys low True open items close inside
          (Bool.andLeft quiet)
          (Bool.andRight (Bool.andRight quiet))
          within
          (Bool.andLeft (Bool.andRight quiet)))
    | App head arguments, within =>
      let headIsQuiet: head.quiet1 = True := Bool.andLeft (Bool.andRight quiet)
      let argumentsQuiet: allQuiet1 arguments = True := Bool.andRight (Bool.andRight quiet)
      let argumentDocsOf := argumentDocs inside.inArm head (inside.at + head.size) arguments
      let (docs, last, hug) :=
        argumentKeys low inside.inArm head (inside.at + head.size) arguments (Bool.andRight within) argumentsQuiet
      let lastDoc := (argumentDocsOf.snd.getOrElse (Nothing, None)).fst
      let lastAll: allKeysFrom low [lastDoc] = True := rewrite last
      let all := allKeysAppend low argumentDocsOf.fst [lastDoc] docs lastAll
      framedKeys low
        (App head arguments).firstWord
        around
        (appDocs head arguments inside).doc
        (headQuiet (App head arguments).words (quietWords (App head arguments) quiet))
        (rewrite appDocsIs head arguments inside then
          appFromKeys low _ _ _ _ _ _ _ _
            (rewrite quietKeys head inside low (Bool.andLeft within) headIsQuiet, all)
            hug)
    | Infix InfixBinary left operator right, within =>
      framedKeys low
        (Infix InfixBinary left operator right).firstWord
        around _
        (headQuiet
          (Infix InfixBinary left operator right).words
          (quietWords (Infix InfixBinary left operator right) quiet))
        (chainOfKeys low _ _
          (pairKeys low _ True left operator right inside
            (Bool.andLeft within)
            (Bool.andLeft (Bool.andRight within))
            quiet))
    | Infix InfixArrow left operator right, within =>
      framedKeys low
        (Infix InfixArrow left operator right).firstWord
        around _
        (headQuiet
          (Infix InfixArrow left operator right).words
          (quietWords (Infix InfixArrow left operator right) quiet))
        (chainOfKeys low _ _
          (pairKeys low _ True left operator right inside
            (Bool.andLeft within)
            (Bool.andLeft (Bool.andRight within))
            quiet))

--| Each quiet slice 1 expression hangs as an element wherever it stands, and as a chain's operand: `exprFacts` with
--| its keys.
theorem quietExprFacts ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical1 = True)
    (quiet: expr.quiet1 = True):
    ExprFacts expr :=
  exprFacts expr within lexical quiet quietKeys
