--| Toward `printedSplit1` (SW-4077): what the items of a printed declaration's group share with the items of the
--| declaration's own printed leaves. `items` reads only tokens for every field but the leaf (`glued`, `afterOperand`,
--| depth, index), and the group has the printed leaves' tokens, so the printed spacing (`printedSpacing1`) holds of
--| the group's items too.

namespace Fmt.SplitProofs
import Std (Bool, Eq, List, Nat, Option, Text, Void)
import Syntax (Comments, Decl, Expr, InfixKind, Leaf, Token, Word, items, itemsAfter)
import Syntax.SettleProofs (tokens)
import Fmt (..)
import Fmt.OutputStatements (..)
import Fmt.GlueProofs (gluedAfter, itemsGlued)
import Fmt.SpacingProofs (printedSpacing1, spacingAdmitsGlue)
import Fmt.TopReadBack (..)
import Fmt.SpellProofs (..)
import Fmt.PrefixHeadSplit (prefixHeadDecl, prefixHeadPrinted)

--| Each leaf's `glued` depends on the tokens alone.
theorem gluedSameTokens ∀ (before: Option Token) (first second: List Leaf)
    (same: tokens first = tokens second):
    gluedAfter before first = gluedAfter before second :=
  match first, second, same with
    | [], [], _ => byComputing
    | [leaf, ..rest], [other, ..others], same =>
      let head: leaf.token = other.token := List.consInjectiveHead _ _ _ _ same
      let tail: tokens rest = tokens others := Eq.cong (.drop 1) same
      rewrite head, gluedSameTokens (Some other.token) rest others tail
    | [], [other, ..others], never => (List.nilNotCons other.token (tokens others) never).impossible
    | [leaf, ..rest], [], never => (List.nilNotCons leaf.token (tokens rest) never.flipped).impossible

--| Leaves with the same tokens have items glued alike.
theorem itemsGluedSame ∀ (first second: List Leaf)
    (same: tokens first = tokens second):
    (items first).map (item => item.glued) = (items second).map (item => item.glued) :=
  rewrite itemsGlued None 0 0 0 first, itemsGlued None 0 0 0 second, gluedSameTokens None first second same

--| A printed declaration's group is spaced as `Decl.spacing1` says: `printedSpacing1`, carried over the shared
--| tokens.
theorem groupSpacing ∀ (decl read: Decl) (group: List Leaf)
    (printed: PrintedGroup decl read group):
    spacingAdmits decl.spacing1 (items group) = True :=
  let (within, shaped, settled, lexical, _, _, sameTokens, _, _) := printed
  rewrite spacingAdmitsGlue decl.spacing1 (items group),
      itemsGluedSame group decl.leaves1 sameTokens,
      <- spacingAdmitsGlue decl.spacing1 (items decl.leaves1) then
    printedSpacing1 decl within shaped settled lexical

--| `groupSpacing` applies to `def d: A := -1 n`, the `1` glued to the `-`.
theorem groupSpacingExample: spacingAdmits prefixHeadDecl.spacing1 (items prefixHeadDecl.leaves1) = True :=
  groupSpacing prefixHeadDecl (prefixHeadDecl.calmAt True) prefixHeadDecl.leaves1 prefixHeadPrinted

-- The code texts of an expression: its tokens' texts with the comments dropped, commas kept.

--| A token's text is no comment, and its comments are comments: the spelling's comments are the ones dropped.
def Word.clean1 (word: Word): Bool := notComment word.text && word.comments.texts.all commentText

--| An expression's tokens' texts, a comma between a bracket's items: what `printedTokens1` says the printed leaves
--| are, without the comments.
def Expr.codeTexts1: Expr → List Text
  | Atom _ word => [word.text]
  | Paren open inner close => [open.text, ..inner.codeTexts1] ++ [close.text]
  | Tuple open items _ close => [open.text, ..commaTexts1 items] ++ [close.text]
  | ListOf open items _ close => [open.text, ..commaTexts1 items] ++ [close.text]
  | App head arguments => head.codeTexts1 ++ argumentTexts1 arguments
  | Infix _ left operator right => left.codeTexts1 ++ [operator.text, ..right.codeTexts1]
  | Prefix operator operand => [operator.text, ..operand.codeTexts1]
  | _ => []

def commaTexts1: List Expr → List Text
  | [] => []
  | [item] => item.codeTexts1
  | [item, ..rest] => item.codeTexts1 ++ [","] ++ commaTexts1 rest

def argumentTexts1: List Expr → List Text
  | [] => []
  | [argument, ..rest] => argument.codeTexts1 ++ argumentTexts1 rest

theorem textsAllAppend ∀ (xs ys: List Text) (p: Text → Bool): (xs ++ ys).all p = (xs.all p && ys.all p) := match xs with
  | [] => byComputing
  | [first, ..rest] =>
    match p first with
      | True => textsAllAppend rest ys p
      | False => byComputing

theorem allCons ∀ (x: a) (xs: List a) (p: a → Bool) (all: [x, ..xs].all p = True): p x = True ∧ xs.all p = True :=
  match holds: p x, all with
    | True, all => (byComputing, all)
    | False, never => (Bool.falseNotTrue never).impossible

theorem wordsAppendAll ∀ (xs ys: List Word) (p: Word → Bool)
    (all: (xs ++ ys).all p = True):
    xs.all p = True ∧ ys.all p = True :=
  match xs, all with
    | [], all => (byComputing, all)
    | [first, ..rest], all =>
      let (head, tail) := allCons first (rest ++ ys) p all
      let (front, back) := wordsAppendAll rest ys p tail
      (rewrite head then front, back)

--| Comments filtered out leave nothing.
theorem commentsDropped ∀ (texts: List Text) (all: texts.all commentText = True): texts.filter notComment = [] :=
  match texts, all with
    | [], _ => byComputing
    | [text, ..rest], all =>
      let (isComment, others) := allCons text rest commentText all
      rewrite commentsApart text isComment, commentsDropped rest others

--| A clean token's spelling, comments filtered out, is its text.
theorem wordDropsComments ∀ (word: Word) (hoisted: Bool)
    (clean: word.clean1 = True):
    (word.spelledAt hoisted).filter notComment = [word.text] :=
  let comments: word.comments.texts.all commentText = True := Bool.andRight clean
  let both: ((word.comments.above.map (note => note.text)).all commentText
    && word.comments.after.toList.all commentText)
    = True :=
    rewrite <- textsAllAppend (word.comments.above.map (note => note.text)) word.comments.after.toList commentText then
      comments
  let aboveDrop := commentsDropped (word.comments.above.map (note => note.text)) (Bool.andLeft both)
  let afterDrop := commentsDropped word.comments.after.toList (Bool.andRight both)
  let textKept: [word.text].filter notComment = [word.text] := rewrite Bool.andLeft clean
  match hoisted with
    | True => rewrite List.filterAppend ([] ++ [word.text]) word.comments.after.toList notComment, afterDrop, textKept
    | False =>
      rewrite List.filterAppend
            (word.comments.above.map (note => note.text))
            ([word.text] ++ word.comments.after.toList)
            notComment,
          List.filterAppend [word.text] word.comments.after.toList notComment,
          aboveDrop,
          afterDrop,
          textKept

--| A slice 1 expression's spelling, comments filtered out, is its code texts.
--|
--| Proof idea: by induction on the expression and its brackets' items, filtering each part of the spelling
--| (`List.filterAppend`): a clean token leaves its text (`wordDropsComments`), a comma itself.
theorem codeTextsOf ∀ (expr: Expr) (hoisted: Bool)
    (within: expr.within1 = True)
    (clean: expr.words.all Word.clean1 = True):
    (expr.spelt hoisted).filter notComment = expr.codeTexts1 :=
  match expr, within with
    | Atom _ word, _ => wordDropsComments word hoisted (allCons word [] Word.clean1 clean).left
    | Paren open inner close, within =>
      let (front, back) := wordsAppendAll [open, ..inner.words] [close] Word.clean1 clean
      let (openClean, innerClean) := allCons open inner.words Word.clean1 front
      rewrite List.filterAppend (open.spelledAt hoisted) (inner.spelt False ++ close.spelledAt False) notComment,
          List.filterAppend (inner.spelt False) (close.spelledAt False) notComment,
          wordDropsComments open hoisted openClean,
          codeTextsOf inner False within innerClean,
          wordDropsComments close False (allCons close [] Word.clean1 back).left
    | Tuple open items _ close, within =>
      let (front, back) := wordsAppendAll [open, ..itemsWords items] [close] Word.clean1 clean
      let (openClean, itemsClean) := allCons open (itemsWords items) Word.clean1 front
      rewrite List.filterAppend (open.spelledAt hoisted) (commaSpelt items ++ close.spelledAt False) notComment,
          List.filterAppend (commaSpelt items) (close.spelledAt False) notComment,
          wordDropsComments open hoisted openClean,
          commaTextsOf items within itemsClean,
          wordDropsComments close False (allCons close [] Word.clean1 back).left
    | ListOf open items _ close, within =>
      let (front, back) := wordsAppendAll [open, ..itemsWords items] [close] Word.clean1 clean
      let (openClean, itemsClean) := allCons open (itemsWords items) Word.clean1 front
      rewrite List.filterAppend (open.spelledAt hoisted) (commaSpelt items ++ close.spelledAt False) notComment,
          List.filterAppend (commaSpelt items) (close.spelledAt False) notComment,
          wordDropsComments open hoisted openClean,
          commaTextsOf items within itemsClean,
          wordDropsComments close False (allCons close [] Word.clean1 back).left
    | App head arguments, within =>
      let (headClean, argumentsClean) := wordsAppendAll head.words (itemsWords arguments) Word.clean1 clean
      rewrite List.filterAppend (head.spelt hoisted) (argumentsSpelt arguments) notComment,
          codeTextsOf head hoisted (Bool.andLeft within) headClean,
          argumentTextsOf arguments (Bool.andRight within) argumentsClean
    | Infix InfixBinary left operator right, within =>
      infixTextsOf InfixBinary left operator right hoisted
        (Bool.andLeft within)
        (Bool.andLeft (Bool.andRight within))
        clean
    | Infix InfixArrow left operator right, within =>
      infixTextsOf InfixArrow left operator right hoisted
        (Bool.andLeft within)
        (Bool.andLeft (Bool.andRight within))
        clean
    | Prefix operator operand, within =>
      let (operatorClean, operandClean) := allCons operator operand.words Word.clean1 clean
      rewrite List.filterAppend (operator.spelledAt hoisted) (operand.spelt False) notComment,
          wordDropsComments operator hoisted operatorClean,
          codeTextsOf operand False (Bool.andLeft within) operandClean
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible
    | other, never => (Bool.falseNotTrue never).impossible

theorem infixTextsOf ∀ (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr) (hoisted: Bool)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (clean: (Infix kind left operator right).words.all Word.clean1 = True):
    ((Infix kind left operator right).spelt hoisted).filter notComment = (Infix kind left operator right).codeTexts1 :=
  let (leftClean, restClean) := wordsAppendAll left.words [operator, ..right.words] Word.clean1 clean
  let (operatorClean, rightClean) := allCons operator right.words Word.clean1 restClean
  rewrite List.filterAppend (left.spelt hoisted) (operator.spelledAt False ++ right.spelt False) notComment,
      List.filterAppend (operator.spelledAt False) (right.spelt False) notComment,
      codeTextsOf left hoisted leftWithin leftClean,
      wordDropsComments operator False operatorClean,
      codeTextsOf right False rightWithin rightClean

theorem commaTextsOf ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (clean: (itemsWords items).all Word.clean1 = True):
    (commaSpelt items).filter notComment = commaTexts1 items :=
  match items with
    | [] => byComputing
    | [item] => codeTextsOf item False (Bool.andLeft within) (wordsAppendAll item.words [] Word.clean1 clean).left
    | [item, next, ..rest] =>
      let (itemClean, restClean) := wordsAppendAll item.words (itemsWords [next, ..rest]) Word.clean1 clean
      rewrite List.filterAppend (item.spelt False) ([","] ++ commaSpelt [next, ..rest]) notComment,
          List.filterAppend [","] (commaSpelt [next, ..rest]) notComment,
          codeTextsOf item False (Bool.andLeft within) itemClean,
          commaTextsOf [next, ..rest] (Bool.andRight within) restClean

theorem argumentTextsOf ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True)
    (clean: (itemsWords arguments).all Word.clean1 = True):
    (argumentsSpelt arguments).filter notComment = argumentTexts1 arguments :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      let (argumentClean, restClean) := wordsAppendAll argument.words (itemsWords rest) Word.clean1 clean
      rewrite List.filterAppend (argument.spelt False) (argumentsSpelt rest) notComment,
          codeTextsOf argument False (Bool.andLeft within) argumentClean,
          argumentTextsOf rest (Bool.andRight within) restClean
