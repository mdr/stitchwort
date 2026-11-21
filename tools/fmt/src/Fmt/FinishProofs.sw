--| The end of a slice 1 declaration's document (SW-4066): whatever its layout, it finishes with its value's last
--| token, a word that is no layout and no comment, and after it only that token's trailing comment (`defFinishes`,
--| `Std.Doc`'s `Finishes`). Each rule's document finishes as its last element does, down to a leaf's `piece`
--| (`elFinishes`, an induction shaped as `JoinProofs`' `elPasses`); the tree's `Joinable` facts say what kind of
--| token each word is.

namespace Fmt.FinishProofs
import Std (Bool, Doc, Eq, List, Nat, Option, Text, Void)
import Std.Doc (..)
import Std.Doc.Proofs (..)
import Syntax (Comments, Expr, InfixKind, Tok, Word)
import Fmt (..)
import Fmt.SpellProofs (appDocsIsOneFirst)
import Fmt.JoinProofs (AllJoinable, CloserJoins, Joinable, Token, WordJoins, closerCloses, closesToken, keptShort)
import Fmt.CalmProofs (bracketFrom, bracketIs, lambdaHugNone, matchedNone, plainDef, valueElPlain)

-- Words.

--| A document's last word as slice 1 prints it: a token, no layout and no comment.
def Final (text: Text): Prop := isLayout text = False ∧ Token text

--| A last word is no layout.
theorem finalSolid ∀ (text: Text) (final: Final text): isLayout text = False := final.left

--| A token's text as a document finishes with it, a closer or not.
theorem pieceFinishes ∀ (text: Text) (final: Final text): Finishes Final (piece text) :=
  match closing: isCloserText text || text == "," with | True | False => final

--| A token's trailing comment writes nothing where it stands.
theorem trailingSilent ∀ (word: Word): AllSilent word.trailing := match after: word.comments.after with
  | Some comment => (byComputing, byComputing)
  | None => byComputing

--| A token on its own finishes with its text: its own-line comments come before it, its trailing comment after.
theorem leafFinishes ∀ [word: Word] (around: Around) (key: Nat)
    (final: Final word.text):
    Finishes Final (word.leaf around key) :=
  finishesConcat Final _
    (finishesAppend Final
      (word.leading around key) _
      (finishesAppend Final _ _ (Inr ((pieceFinishes word.text final), (trailingSilent word)))))

--| A token that is no closer or comma is a last word.
theorem wordFinal ∀ (word: Word) (joins: WordJoins word): Final word.text := match joins with
  | (sound, token, comma, notCloser) => (Bool.notTrue (isLayout word.text) (Bool.andLeft sound), token)

--| A closing bracket is a last word.
theorem closerFinal ∀ (word: Word) (joins: CloserJoins word): Final word.text := match joins with
  | (sound, closer) =>
    (Bool.notTrue (isLayout word.text) (Bool.andLeft sound), closesToken word.text (closerCloses word.text closer))

-- The rules.

--| A node's document with its first token's own-line comments before it finishes as the document does.
theorem framedFinishes ∀ (first: Word) (around: Around) (doc: Doc)
    (ends: Finishes Final doc):
    Finishes Final (framedBy first around doc) :=
  let placed: Finishes Final (if first.displaces around then Displaced doc else doc) :=
    match displaced: first.displaces around with | True | False => ends
  finishesConcat Final _ (Inl (Inr (placed, byComputing)))

--| `( … )` finishes with its closer.
theorem parenFinishes ∀ (open: Word) (inner: Expr) (close: Word) (around: Around)
    (closer: CloserJoins close):
    Finishes Final (parenDoc open inner close around) :=
  finishesConcat Final _ (Inl (Inl (Inr ((leafFinishes _ around.at (closerFinal close closer)), byComputing))))

--| Each of a bracket's layouts finishes with its closer.
theorem bracketFromFinishes ∀ (list empty plain holds: Bool) (prefix closer: Doc) (filled broken: List Doc)
    (ends: Finishes Final closer):
    Finishes Final (bracketFrom list empty plain holds prefix closer filled broken) :=
  match empty with
    | True => finishesConcat Final _ (Inl (Inr (ends, byComputing)))
    | False =>
      match fills: list && !holds && plain with
        | True => finishesConcat Final [prefix, Nest 2 (Fill filled), closer] (Inl (Inl (Inr (ends, byComputing))))
        | False =>
          match holds with
            | True => finishesConcat Final _ (Inl (Inl (Inl (Inr (ends, (byComputing, byComputing))))))
            | False => finishesConcat Final _ (Inl (Inl (Inl (Inr (ends, byComputing)))))

--| A tuple's or list's contents finish with its closer.
theorem bracketFinishes ∀ (list: Bool) (open: Word) (items: List Expr) [close: Word] (around: Around)
    (closer: CloserJoins close):
    Finishes Final (bracketContent list open items close around) :=
  rewrite bracketIs list open items close around then
    bracketFromFinishes list items.isEmpty
      (items.all Expr.plainItem)
      (ListOf open items False close).holdsTrailingComment
      (open.opening around close)
      (close.leaf
        (around.next (ListOf open items False close).trailsBeforeClose ((ListOf open items False close).size - 1))
        around.at)
      (cells (list && items.all Expr.plainItem) around.inArm open.trails (around.at + 1) items)
      (brokenItems (list && items.all Expr.plainItem) around.inArm True open.trails (around.at + 1) items)
      (leafFinishes _ around.at (closerFinal close closer))

--| A bracket as a call's last argument, as it stands and opened, finishes with its closer.
theorem huggedFinishes ∀ (list: Bool) (open: Word) (items: List Expr) [close: Word] (around: Around) (hard: Bool)
    (closer: CloserJoins close):
    Finishes Final
      (framedBy open around (Group (bracketContent list open items close { around | hoisted = True }) hard)) :=
  framedFinishes open around
    (Group (bracketContent list open items close { around | hoisted = True }) hard)
    (bracketFinishes list open items { around | hoisted = True } closer)

-- Calls.

--| A hug finishes with a word, if there is one.
def HugFinishes: Option Doc → Prop
  | None => True
  | Some open => Finishes Final open

--| The `count`th and later of docs whose last finishes with a word finish with it, short of all of them.
theorem dropFinishes ∀ (docs: List Doc) (count: Nat)
    (ends: FinishesLast Final docs)
    (short: count ≤ docs.length)
    (differs: (count == docs.length) = False):
    FinishesLast Final (docs.drop count) :=
  match docs, count, ends with
    | [], _, never => cases
    | [only], Zero, ends => ends
    | [only], Succ more, _ =>
      match more, differs with
        | Zero, never => cases
        | Succ less, _ => Void.impossible (arithmetic)
    | [doc, next, ..rest], Zero, ends => ends
    | [doc, next, ..rest], Succ more, ends => dropFinishes [next, ..rest] more ends (arithmetic) differs

--| Each doc after a line break: the last still finishes the docs.
theorem hardFinishes ∀ (docs: List Doc)
    (ends: FinishesLast Final docs):
    FinishesLast Final (docs.concatMap (doc => [HardLine, doc])) :=
  match docs, ends with
    | [], never => cases
    | [only], ends => ends
    | [doc, next, ..more], ends => finishesLastAppend Final [HardLine, doc] _ (hardFinishes [next, ..more] ends)

--| Each of the docs finishes with a word.
def EachFinishes: List Doc → Prop
  | [] => True
  | [doc, ..docs] => Finishes Final doc ∧ EachFinishes docs

--| Options that each finish with a word, before options that do, do.
theorem eachFinishesAppend ∀ (front back: List Doc)
    (first: EachFinishes front)
    (rest: FinishesEach Final back):
    FinishesEach Final (front ++ back) :=
  match front, first with
    | [], _ => rest
    | [doc, ..others], Both ends more =>
      let later := eachFinishesAppend others back more rest
      match tail: others ++ back with
        | [next, ..after] => (ends, later)

--| The spaced docs, whose last finishes with a word, finish with it.
theorem spacedFinishes ∀ (docs: List Doc) (ends: FinishesLast Final docs): Finishes Final (spaced docs) :=
  finishesConcat Final _ (finishesOfLast Final _ (joinedFinishes Final (Doc.text " ") docs ends))

--| A call's layouts (`appFrom`) each finish with its last argument.
--|
--| Proof idea: on one line or filled, the docs finish with the last argument's (`spacedFinishes`); split where the
--| kept elements end, the dropped ones each after a line break end with it too (`dropFinishes`, `hardFinishes`); the
--| hug finishes with the last argument opened.
theorem appFromFinishes ∀ (id keep: Nat) (between betweenFront: Bool) (headDoc lastDoc: Doc)
    (front: List Doc) (hug: Option Doc)
    (ends: Finishes Final lastDoc)
    (hugEnds: HugFinishes hug)
    (short: keep ≤ ([headDoc, ..front] ++ [lastDoc]).length):
    Finishes Final (appFrom id keep between betweenFront headDoc front lastDoc hug).doc
      ∧ HugFinishes (appFrom id keep between betweenFront headDoc front lastDoc hug).hug :=
  let docs := [headDoc, ..front] ++ [lastDoc]
  let lastOf: FinishesLast Final docs := finishesLastAppend Final [headDoc, ..front] [lastDoc] ends
  let all: Finishes Final (spaced docs) := spacedFinishes docs lastOf
  match full: keep == docs.length with
    | True =>
      match between with
        | True => (all, byComputing)
        | False => (lastOf, byComputing)
    | False =>
      let rest := Doc.concat (docs.drop keep |> .concatMap (doc => [HardLine, doc]))
      let restEnds: Finishes Final rest :=
        finishesConcat Final _
          (finishesOfLast Final _ (hardFinishes (docs.drop keep) (dropFinishes docs keep lastOf short full)))
      let fillFront := keep > 2 && !betweenFront
      let restDoc := if fillFront then IfBroken id (Nest 4 rest) (Nest 2 rest) else Nest 2 rest
      let restDocEnds: Finishes Final restDoc := match fillFront with
        | True => (restEnds, restEnds)
        | False => restEnds
      let frontDoc := if fillFront then IdGroup id (Nest 4 (Fill (docs.take keep))) False else spaced (docs.take keep)
      let broken: Finishes Final (Doc.concat [frontDoc, restDoc]) :=
        finishesConcat Final _ (Inl (Inr (restDocEnds, byComputing)))
      match hug, hugEnds with
        | None, _ => ((all, broken), byComputing)
        | Some open, opens =>
          let hugged: Finishes Final (Doc.concat [Flatten (spaced [headDoc, ..front]), Doc.text " ", open]) :=
            finishesConcat Final
              [Flatten (spaced [headDoc, ..front]), Doc.text " ", open]
              (Inl (Inl (Inr (opens, byComputing))))
          ((all, (hugged, broken)), hugged)

--| A call's last argument, as it stands and opened, finishes with its last token.
theorem lastArgumentFinishes ∀ (kinds: Text → Tok) (argument: Expr) (around: Around)
    (within: argument.within1 = True)
    (joinable: Joinable kinds argument):
    Finishes Final (lastArgument argument around).fst ∧ HugFinishes (lastArgument argument around).snd :=
  match argument, joinable with
    | Tuple open items comma close, (opener, closer, each) =>
      let content := bracketContent False open items close { around | hoisted = True }
      (
        huggedFinishes False open items around content.forcesBreak closer,
        huggedFinishes False open items around True closer
      )
    | ListOf open items comma close, (opener, closer, each) =>
      let content := bracketContent True open items close { around | hoisted = True }
      (
        huggedFinishes True open items around content.forcesBreak closer,
        huggedFinishes True open items around True closer
      )
    | Atom kind word, joins => (elFinishes kinds (Atom kind word) within joins around, byComputing)
    | App head arguments, joins => (elFinishes kinds (App head arguments) within joins around, byComputing)
    | Infix kind left operator right, joins =>
      (elFinishes kinds (Infix kind left operator right) within joins around, byComputing)
    | Prefix operator operand, joins => (elFinishes kinds (Prefix operator operand) within joins around, byComputing)
    | Paren open (Atom k w) close, joins =>
      (elFinishes kinds (Paren open (Atom k w) close) within joins around, byComputing)
    | Paren open (Paren o i c) close, joins =>
      (elFinishes kinds (Paren open (Paren o i c) close) within joins around, byComputing)
    | Paren open (Tuple o is m c) close, joins =>
      (elFinishes kinds (Paren open (Tuple o is m c) close) within joins around, byComputing)
    | Paren open (ListOf o is m c) close, joins =>
      (elFinishes kinds (Paren open (ListOf o is m c) close) within joins around, byComputing)
    | Paren open (App h xs) close, joins =>
      (elFinishes kinds (Paren open (App h xs) close) within joins around, byComputing)
    | Paren open (Infix k l o r) close, joins =>
      (elFinishes kinds (Paren open (Infix k l o r) close) within joins around, byComputing)
    | Paren open (Prefix o x) close, joins =>
      (elFinishes kinds (Paren open (Prefix o x) close) within joins around, byComputing)

--| A call's last argument and its hug finish with its last token, and there is one document before it for each
--| argument but one.
theorem argumentsFinish ∀ (kinds: Text → Tok) (arm: Bool) (previous: Expr) (at: Nat) (arguments: List Expr)
    (filled: arguments ≠ [])
    (within: allWithin1 arguments = True)
    (joinable: AllJoinable kinds arguments):
    Finishes Final ((argumentDocs arm previous at arguments).snd.getOrElse (Nothing, None)).fst
      ∧ HugFinishes ((argumentDocs arm previous at arguments).snd.getOrElse (Nothing, None)).snd
      ∧ (argumentDocs arm previous at arguments).fst.length + 1 = arguments.length :=
  match arguments, joinable with
    | [], _ => (filled byComputing).impossible
    | [argument], (joins, _) =>
      let place := { before = previous.trails, hoisted = False, item = False, at, inArm = arm }
      let (lastEnds, hugEnds) := lastArgumentFinishes kinds argument place (Bool.andLeft within) joins
      (lastEnds, hugEnds, byComputing)
    | [argument, next, ..more], (joins, rest) =>
      let (lastEnds, hugEnds, length) :=
        argumentsFinish kinds arm argument
          (at + argument.size)
          [next, ..more]
          (List.consNotNil next more)
          (Bool.andRight within)
          rest
      (lastEnds, hugEnds, arithmetic [length])

--| A call finishes with its last argument, in each layout and its hug.
theorem appFinishes ∀ (kinds: Text → Tok) (head: Expr) (arguments: List Expr) (around: Around)
    (within: allWithin1 arguments = True)
    (joinable: AllJoinable kinds arguments)
    (filled: arguments ≠ []):
    Finishes Final (appDocs head arguments around).doc ∧ HugFinishes (appDocs head arguments around).hug :=
  let results := argumentDocs around.inArm head (around.at + head.size) arguments
  let front := results.fst
  let lastDoc := (results.snd.getOrElse (Nothing, None)).fst
  let (lastEnds, hugEnds, length) :=
    argumentsFinish kinds around.inArm head (around.at + head.size) arguments filled within joinable
  let short: 1 + keptFront head arguments ≤ ([head.el around, ..front] ++ [lastDoc]).length :=
    rewrite List.lengthAppend front [lastDoc] then arithmetic [keptShort head arguments, length]
  rewrite appDocsIsOneFirst head arguments around then
    appFromFinishes
      (around.at + 1)
      (1 + keptFront head arguments)
      (commentBetween head arguments)
      (commentBetween head (arguments.take (1 + keptFront head arguments - 1)))
      (head.el around)
      lastDoc
      front
      (results.snd.getOrElse (Nothing, None)).snd
      lastEnds
      hugEnds
      short

-- Operator chains.

--| A chain's docs grouped, the lines after the first operand's nested, finish with its last.
theorem chainOfFinishes ∀ (arms: Bool) (links: List Doc)
    (ends: FinishesLast Final links)
    (long: 2 ≤ links.length):
    Finishes Final (chainOf arms links) :=
  match links, ends with
    | [head, next, ..more], ends =>
      let tail: Finishes Final (Doc.concat [next, ..more]) := finishesConcat Final _ (finishesOfLast Final _ ends)
      finishesConcat Final _ (Inl (Inr (tail, byComputing)))

--| What follows a chain's operator finishes with the operand.
theorem chainRightFinishes ∀ (kinds: Text → Tok) (level: Option Nat) (right: Expr) (place: Around)
    (within: right.within1 = True)
    (joinable: Joinable kinds right):
    FinishesLast Final (chainRight level right place) :=
  let spaced: FinishesLast Final [Doc.text " ", ..linkDocs level False right place] :=
    finishesLastAppend Final [Doc.text " "] _ (linkDocsFinish kinds level False right place within joinable)
  match right with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ | Infix _ _ _ _ | Prefix _ _ => spaced

--| A chain's links finish with its last operand.
theorem chainLinksFinish ∀ [kinds: Text → Tok] (level: Option Nat) (first: Bool) (left: Expr) (operator: Word)
    [right: Expr] (around: Around)
    (rightWithin: right.within1 = True)
    (rightJoins: Joinable kinds right):
    FinishesLast Final (chainLinks level first left operator right around) :=
  let operatorAround := around.next left.trails left.size
  let rightAround := around.next operator.trails (left.size + 1)
  let leaf := operator.leaf operatorAround operatorAround.at
  let after: FinishesLast Final [Line, leaf, ..chainRight level right rightAround] :=
    finishesLastAppend Final
      [Line, leaf]
      (chainRight level right rightAround)
      (chainRightFinishes kinds level right rightAround rightWithin rightJoins)
  finishesLastAppend Final (linkDocs level first left around) [Line, leaf, ..chainRight level right rightAround] after

--| A chain operand's documents finish with its last token.
theorem linkDocsFinish ∀ (kinds: Text → Tok) (level: Option Nat) (first: Bool) (expr: Expr) (around: Around)
    (within: expr.within1 = True)
    (joinable: Joinable kinds expr):
    FinishesLast Final (linkDocs level first expr around) :=
  let element: FinishesLast Final [expr.el around] := elFinishes kinds expr within joinable around
  match expr, joinable with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ | Prefix _ _, _ => element
    | Infix kind left operator right, (leftJoins, operatorJoins, rightJoins) =>
      match kind with
        | InfixBinary =>
          match inChain: (Infix InfixBinary left operator right).inChain level with
            | True => chainLinksFinish level first left operator around (Bool.andLeft (Bool.andRight within)) rightJoins
            | False => element
        | InfixArrow =>
          match inChain: (Infix InfixArrow left operator right).inChain level with
            | True => chainLinksFinish level first left operator around (Bool.andLeft (Bool.andRight within)) rightJoins
            | False => element
        | _ => cases

--| An operator chain finishes with its last operand.
theorem chainFinishes ∀ (kinds: Text → Tok) (level: Option Nat) (left: Expr) (operator: Word)
    (right: Expr) (around: Around)
    (rightWithin: right.within1 = True)
    (rightJoins: Joinable kinds right):
    Finishes Final (chain level left operator right around) :=
  let links := chainLinks level True left operator right around
  chainOfFinishes
    (left.opensArms level)
    links
    (chainLinksFinish level True left operator around rightWithin rightJoins)
    (List.twoLeLengthAppend (linkDocs level True left around) Line (operator.leaf _ _) _)

-- The induction.

--| Wherever an expression stands, its element finishes with its last token, in every layout.
--|
--| Proof idea: Induction on the expression, as `elPasses`: a token is a leaf (`leafFinishes`); brackets finish with
--| their closer; a call with its last argument, a chain with its last operand, a prefix operator with its operand,
--| each by the induction; and the node's own-line comments come before it (`framedFinishes`).
theorem elFinishes ∀ (kinds: Text → Tok) (expr: Expr)
    (within: expr.within1 = True)
    (joinable: Joinable kinds expr) (around: Around):
    Finishes Final (expr.el around) :=
  let inside := { around | hoisted = True }
  match expr, joinable with
    | Atom kind word, joins => leafFinishes around around.at (wordFinal word joins)
    | Paren open inner close, (opener, closer, innerJoins) =>
      framedFinishes
        (Paren open inner close).firstWord
        around
        (parenDoc open inner close inside)
        (parenFinishes open inner close inside closer)
    | Tuple open items comma close, (opener, closer, each) =>
      framedFinishes
        (Tuple open items comma close).firstWord
        around
        (commaBracket False open items close inside)
        (bracketFinishes False open items inside closer)
    | ListOf open items comma close, (opener, closer, each) =>
      framedFinishes
        (ListOf open items comma close).firstWord
        around
        (commaBracket True open items close inside)
        (bracketFinishes True open items inside closer)
    | App head arguments, (headJoins, each, filled) =>
      framedFinishes
        (App head arguments).firstWord
        around
        (appDocs head arguments inside).doc
        (appFinishes kinds head arguments inside (Bool.andRight within) each filled).left
    | Infix kind left operator right, (leftJoins, operatorJoins, rightJoins) =>
      match kind with
        | InfixBinary =>
          framedFinishes
            (Infix InfixBinary left operator right).firstWord
            around
            (chain (Infix InfixBinary left operator right).chainLevel left operator right inside)
            (chainFinishes kinds
              (Infix InfixBinary left operator right).chainLevel
              left
              operator
              right
              inside
              (Bool.andLeft (Bool.andRight within))
              rightJoins)
        | InfixArrow =>
          framedFinishes
            (Infix InfixArrow left operator right).firstWord
            around
            (chain (Infix InfixArrow left operator right).chainLevel left operator right inside)
            (chainFinishes kinds
              (Infix InfixArrow left operator right).chainLevel
              left
              operator
              right
              inside
              (Bool.andLeft (Bool.andRight within))
              rightJoins)
        | _ => cases
    | Prefix operator operand, (joins, operandJoins, glue) =>
      framedFinishes
        (Prefix operator operand).firstWord
        around
        (Doc.concat [
          operator.leaf inside around.at,
          prefixGap operator operand,
          operand.el (around.next operator.trails 1)
        ])
        (finishesConcat Final _
          (Inl
            (Inl
              (Inr (
                (elFinishes kinds operand (Bool.andLeft within) operandJoins (around.next operator.trails 1)),
                byComputing
              )))))

-- The declaration.

--| A call's hug finishes with its last argument opened.
theorem callHugFinishes ∀ (kinds: Text → Tok) (value: Expr) (inside: Around)
    (within: value.within1 = True)
    (joinable: Joinable kinds value):
    HugFinishes (value.callHug inside) :=
  match value, joinable with
    | App head arguments, (headJoins, each, filled) =>
      (appFinishes kinds head arguments inside (Bool.andRight within) each filled).right
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | Infix _ _ _ _ | Prefix _ _, _ => byComputing

--| The hug after a space, if there is one, finishes with a word.
theorem spacedHugsFinish ∀ (hug: Option Doc)
    (hugEnds: HugFinishes hug):
    EachFinishes (optionList (hug.map (open => Doc.concat [Doc.text " ", open]))) :=
  match hug, hugEnds with
    | None, _ => byComputing
    | Some open, opens => ((finishesConcat Final _ (Inl (Inr (opens, byComputing)))), byComputing)

--| What follows a `:=` finishes with the value's last token, below or in each layout that keeps its start on the
--| line.
--|
--| Proof idea: `matchedNone`, `valueElPlain` and `lambdaHugNone` leave the value's element; each option is it after
--| a space or a line break, or the call's hug after a space (`callHugFinishes`).
theorem bodyFinishes ∀ (kinds: Text → Tok) (value: Expr) (assign: Word) (around: Around) (semi: Bool)
    (within: value.within1 = True)
    (joinable: Joinable kinds value):
    Finishes Final (bodyAfter value assign around semi).fst ∧ Finishes Final (bodyAfter value assign around semi).snd :=
  let inside: Around := { around | hoisted = True }
  let element := elFinishes kinds value within joinable around
  let spacedEnds: Finishes Final (Doc.concat [Doc.text " ", value.el around]) :=
    finishesConcat Final _ (Inl (Inr (element, byComputing)))
  let below: Finishes Final (Nest 2 (Doc.concat [HardLine, value.el around])) :=
    finishesConcat Final _ (Inl (Inr (element, byComputing)))
  let hugs := callHugFinishes kinds value inside within joinable
  rewrite matchedNone value inside within,
      valueElPlain value around semi within,
      lambdaHugNone value semi inside (value.el around) within then
    match plain: assign.trails || value.noted || value.isBlock with
      | True => (below, below)
      | False => (
        below,
        eachFinishesAppend
          [Flatten (Doc.concat [Doc.text " ", value.el around])] _
          (spacedEnds, byComputing)
          (eachFinishesAppend
            (if value.opensBracket || (value.callHug inside).isSome then [OneLineBelow (value.el around)] else []) _
            (match value.opensBracket || (value.callHug inside).isSome with
              | True => (element, byComputing)
              | False => byComputing)
            (eachFinishesAppend
              (if value.opensBracket then [Doc.concat [Doc.text " ", value.el around]]
               else optionList ((value.callHug inside).map (open => Doc.concat [Doc.text " ", open])))
              [Nest 2 (Doc.concat [HardLine, value.el around])]
              (match value.opensBracket with
                | True => (spacedEnds, byComputing)
                | False => spacedHugsFinish (value.callHug inside) hugs)
              below))
      )

--| A definition's document finishes as its body does, in both of its forms.
theorem defFromFinishes ∀ (headerDoc: Doc) (breaks: Bool) (assignDoc below choice: Doc)
    (ends: Finishes Final below ∧ Finishes Final choice):
    Finishes Final (defFrom headerDoc breaks assignDoc below choice) :=
  let quiet: AllSilent [] := byComputing
  finishesConcat Final
    [IdGroup 0 headerDoc breaks, Doc.text " ", assignDoc, IfBroken 0 below choice]
    (Inl (Inl (Inl (Inr (ends, quiet)))))

--| A slice 1 definition's document finishes with its value's last token, in every layout.
theorem defFinishes ∀ (kinds: Text → Tok) (keyword: Comments) (name: Word) (colon: Comments) (result: Expr)
    (colonEq: Comments) (value: Expr)
    (within: value.within1 = True)
    (joinable: Joinable kinds value):
    Finishes Final (plainDef keyword name colon result colonEq value) :=
  let start: Around := { before = False, hoisted = True, item = False, at = 0, inArm = False }
  let keywordWord := fixedWord "def" keyword
  let colonWord := fixedWord ":" colon
  let assign := fixedWord ":=" colonEq
  let headWords := [keywordWord, name]
  let colonAround := start.next (trailsBack headWords.reverse) 2
  let typeDoc := result.el (start.next colonWord.trails 3)
  let headDoc := spaced (headDocs start headWords)
  let typed := if colonWord.trails then [Nest 4 (Doc.concat [HardLine, typeDoc])] else [Doc.text " ", Nest 4 typeDoc]
  let headerDoc := Doc.concat ([headDoc, colonWord.leaf colonAround 2] ++ typed)
  let inside :=
    (headWords.reverse.drop 1 |> .any Word.trails)
      || colonWord.trails
      || (result.words.reverse.drop 1 |> .any Word.trails)
      || (value.layoutBody && (lastCode headWords).trails)
  let around := start.next assign.trails (4 + result.size)
  let body := bodyAfter value assign around False
  defFromFinishes headerDoc
    (headerDoc.forcesBreak || inside)
    (assign.leaf (start.next result.trails (3 + result.size)) (3 + result.size))
    body.fst
    body.snd
    (bodyFinishes kinds value assign around False within joinable)
