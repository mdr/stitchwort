--| Toward `printedSplit1` (SW-4077): what the items of a printed declaration's group share with the items of the
--| declaration's own printed leaves. `items` reads only tokens for every field but the leaf (`glued`, `afterOperand`,
--| depth, index), and the group has the printed leaves' tokens, so the printed spacing (`printedSpacing1`) holds of
--| the group's items too.

namespace Fmt.SplitProofs
import Std (Bool, Eq, List, Nat, Option, Text, Void)
import Syntax (Comments, Decl, Expr, InfixKind, Item, Leaf, Tok, Token, Word, items, itemsAfter)
import Syntax.SettleProofs (tokens)
import Fmt (..)
import Fmt.OutputStatements (..)
import Fmt.GlueProofs (gluedAfter, itemsGlued)
import Fmt.SpacingProofs (printedSpacing1, spacingAdmitsGlue)
import Fmt.TopReadBack (..)
import Fmt.SpellProofs (..)
import Fmt.CalmProofs (calmAllEmpty, numeralCalm)
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

-- `afterOperand`, item by item.

--| Each item's `afterOperand` says whether the item before it closes an operand: how `items` sets it, which a call's
--| argument (`argumentGlue`) and a head's `-` (`negativeNumeral`) read.
def Chained: List Item → Bool
  | [first, second, ..rest] => (second.afterOperand == first.kind.closesOperand) && Chained [second, ..rest]
  | _ => True

theorem boolEqSelf ∀ (b: Bool): (b == b) = True := match b with
  | True => byComputing
  | False => byComputing

theorem itemsChained ∀ (before: Option Token) (index depth lineIndent: Nat) (leaves: List Leaf):
    Chained (itemsAfter before index depth lineIndent leaves) = True :=
  match leaves with
    | [] => byComputing
    | [_] => byComputing
    | [leaf, next, ..rest] =>
      rewrite itemsChained
            (Some leaf.token)
            (index + 1)
            (if leaf.token.kind.isOpener then depth + 1
             else if leaf.token.kind.isCloser then depth - 1
             else depth)
            (if leaf.token.lineStart then leaf.token.column else lineIndent)
            [next, ..rest],
          boolEqSelf leaf.token.kind.closesOperand

--| A group's items are chained.
theorem groupChained ∀ (group: List Leaf): Chained (items group) = True := itemsChained None 0 0 0 group

-- `calm` keeps the spacing: it changes only blank-line flags, and `signQuiet` reads whether comments are there.

--| `calm` keeps a slice 1 expression's first token, its flags calmed.
theorem leadCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).lead = expr.lead.kept item False :=
  match expr, within with
    | Atom _ _, _ => byComputing
    | Paren _ _ _, _ => byComputing
    | Tuple _ _ _ _, _ => byComputing
    | ListOf _ _ _ _, _ => byComputing
    | App head _, within => leadCalm head item (Bool.andLeft within)
    | Infix InfixBinary left _ _, within => leadCalm left item (Bool.andLeft within)
    | Infix InfixArrow left _ _, within => leadCalm left item (Bool.andLeft within)
    | Prefix _ _, _ => byComputing
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible
    | other, never => (Bool.falseNotTrue never).impossible

theorem numeralOneCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).numeral1 = expr.numeral1 :=
  match expr, within with
    | Atom Num _, _ => byComputing
    | Atom Float _, _ => byComputing
    | Atom Lower _, _ => byComputing
    | Atom Upper _, _ => byComputing
    | Atom _ _, never => (Bool.falseNotTrue never).impossible
    | Paren _ _ _, _ => byComputing
    | Tuple _ _ _ _, _ => byComputing
    | ListOf _ _ _ _, _ => byComputing
    | App _ _, _ => byComputing
    | Infix InfixBinary _ _ _, _ => byComputing
    | Infix InfixArrow _ _ _, _ => byComputing
    | Prefix _ _, _ => byComputing
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible
    | other, never => (Bool.falseNotTrue never).impossible

--| Whether comments sit between a sign and its operand is kept by `calm`.
theorem signQuietCalm ∀ (operator: Word) (operand: Expr) (item: Bool)
    (within: operand.within1 = True):
    signQuiet (operator.kept item False) (operand.calm False) = signQuiet operator operand :=
  rewrite leadCalm operand False within then
    match operator.comments.after, operand.lead.comments.above with
      | None, [] => byComputing
      | None, [_, .._] => byComputing
      | Some _, [] => byComputing
      | Some _, [_, .._] => byComputing

theorem operandSpacingCalm ∀ (argument: Bool) (operator: Word) (operand: Expr) (item: Bool)
    (within: operand.within1 = True):
    operandSpacing argument (operator.kept item False) (operand.calm False)
      = operandSpacing argument operator operand :=
  rewrite numeralCalm operand False within,
      signQuietCalm operator operand item within,
      numeralOneCalm operand False within

--| `calm` keeps the spacing `Spelt` reads.
--|
--| Proof idea: by induction on the expression and its brackets' items; a prefix's operand spacing reads the
--| operator's text, whether comments sit between it and its operand, and the operand's numeral tests, all kept.
theorem spacingCalm ∀ (expr: Expr) (item argument: Bool)
    (within: expr.within1 = True):
    (expr.calm item).spacing1 argument = expr.spacing1 argument :=
  match expr, within with
    | Atom _ _, _ => byComputing
    | Paren _ inner _, within => rewrite spacingCalm inner False False within
    | Tuple _ items _ _, within => rewrite commaSpacingCalmAll items True within
    | ListOf _ items _ _, within =>
      match items.all Expr.plainItem with
        | True => rewrite commaSpacingCalmLead items within
        | False => rewrite commaSpacingCalmAll items True within
    | App head arguments, within =>
      rewrite spacingCalm head item False (Bool.andLeft within), argumentsSpacingCalm arguments (Bool.andRight within)
    | Infix InfixBinary left _ right, within =>
      rewrite spacingCalm left item False (Bool.andLeft within),
          spacingCalm right False False (Bool.andLeft (Bool.andRight within))
    | Infix InfixArrow left _ right, within =>
      rewrite spacingCalm left item False (Bool.andLeft within),
          spacingCalm right False False (Bool.andLeft (Bool.andRight within))
    | Prefix operator operand, within =>
      rewrite operandSpacingCalm argument operator operand item (Bool.andLeft within) then
        match operandSpacing argument operator operand with
          | Some _ => rewrite spacingCalm operand False False (Bool.andLeft within)
          | None => rewrite spacingCalm operand False False (Bool.andLeft within)
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible
    | other, never => (Bool.falseNotTrue never).impossible

theorem commaSpacingCalmAll ∀ (items: List Expr) (item: Bool)
    (within: allWithin1 items = True):
    commaSpacing1 (calmAll item items) = commaSpacing1 items :=
  match items with
    | [] => byComputing
    | [one] => rewrite spacingCalm one item False (Bool.andLeft within)
    | [one, next, ..rest] =>
      rewrite spacingCalm one item False (Bool.andLeft within),
          commaSpacingCalmAll [next, ..rest] item (Bool.andRight within)

theorem commaSpacingCalmLead ∀ (items: List Expr)
    (within: allWithin1 items = True):
    commaSpacing1 (calmLead items) = commaSpacing1 items :=
  match items with
    | [] => byComputing
    | [one] => rewrite spacingCalm one False False (Bool.andLeft within)
    | [one, next, ..rest] =>
      rewrite spacingCalm one False False (Bool.andLeft within),
          commaSpacingCalmAll [next, ..rest] True (Bool.andRight within)

theorem argumentsSpacingCalm ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True):
    argumentsSpacing1 (calmAll False arguments) = argumentsSpacing1 arguments :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      rewrite spacingCalm argument False True (Bool.andLeft within), argumentsSpacingCalm rest (Bool.andRight within)

-- `calm` keeps the shape: it changes no constructor, text or atom kind.

theorem levelCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).level = expr.level :=
  match expr, within with
    | Atom _ _, _ => byComputing
    | Paren _ _ _, _ => byComputing
    | Tuple _ _ _ _, _ => byComputing
    | ListOf _ _ _ _, _ => byComputing
    | App _ _, _ => byComputing
    | Infix InfixBinary _ _ _, _ => byComputing
    | Infix InfixArrow _ _ _, _ => byComputing
    | Prefix _ _, _ => byComputing
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible
    | other, never => (Bool.falseNotTrue never).impossible

theorem atomicCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).atomic1 = expr.atomic1 :=
  match expr, within with
    | Atom _ _, _ => byComputing
    | Paren _ _ _, _ => byComputing
    | Tuple _ _ _ _, _ => byComputing
    | ListOf _ _ _ _, _ => byComputing
    | App _ _, _ => byComputing
    | Infix InfixBinary _ _ _, _ => byComputing
    | Infix InfixArrow _ _ _, _ => byComputing
    | Prefix _ _, _ => byComputing
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible
    | other, never => (Bool.falseNotTrue never).impossible

theorem numberAtomCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).numberAtom1 = expr.numberAtom1 :=
  match expr, within with
    | Atom Tok.Num _, _ => byComputing
    | Atom Tok.Float _, _ => byComputing
    | Atom Tok.Lower _, _ => byComputing
    | Atom Tok.Upper _, _ => byComputing
    | Atom _ _, never => (Bool.falseNotTrue never).impossible
    | Paren _ _ _, _ => byComputing
    | Tuple _ _ _ _, _ => byComputing
    | ListOf _ _ _ _, _ => byComputing
    | App _ _, _ => byComputing
    | Infix InfixBinary _ _ _, _ => byComputing
    | Infix InfixArrow _ _ _, _ => byComputing
    | Prefix _ _, _ => byComputing
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible
    | other, never => (Bool.falseNotTrue never).impossible

theorem headCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).head1 = expr.head1 :=
  match expr, within with
    | Prefix _ operand, within => rewrite numberAtomCalm operand False (Bool.andLeft within)
    | Atom _ _, _ => byComputing
    | Paren _ _ _, _ => byComputing
    | Tuple _ _ _ _, _ => byComputing
    | ListOf _ _ _ _, _ => byComputing
    | App _ _, _ => byComputing
    | Infix InfixBinary _ _ _, _ => byComputing
    | Infix InfixArrow _ _ _, _ => byComputing
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible
    | other, never => (Bool.falseNotTrue never).impossible

theorem argumentCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).argument1 = expr.argument1 :=
  match expr, within with
    | Prefix _ operand, within => rewrite atomicCalm operand False (Bool.andLeft within)
    | Atom _ _, _ => byComputing
    | Paren _ _ _, _ => byComputing
    | Tuple _ _ _ _, _ => byComputing
    | ListOf _ _ _ _, _ => byComputing
    | App _ _, _ => byComputing
    | Infix InfixBinary _ _ _, _ => byComputing
    | Infix InfixArrow _ _ _, _ => byComputing
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible
    | other, never => (Bool.falseNotTrue never).impossible

theorem argumentsCalm ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True):
    (calmAll False arguments).all Expr.argument1 = arguments.all Expr.argument1 :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      rewrite argumentCalm argument False (Bool.andLeft within), argumentsCalm rest (Bool.andRight within)

theorem calmAllLength ∀ (items: List Expr) (item: Bool): (calmAll item items).length = items.length := match items with
  | [] => byComputing
  | [_, ..rest] => Eq.cong Succ (calmAllLength rest item)

--| `calm` keeps the parser's shape.
--|
--| Proof idea: by induction on the expression and its brackets' items: `calm` keeps every constructor, text, atom
--| kind and list length, so each test of `shaped1` (levels, heads, arguments) comes out the same.
theorem shapedCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).shaped1 = expr.shaped1 :=
  match expr, within with
    | Atom _ _, _ => byComputing
    | Paren _ inner _, within => shapedCalm inner False within
    | Tuple _ items _ _, within => rewrite calmAllLength items True, shapedAllCalm items True within
    | ListOf _ items _ _, within =>
      match items.all Expr.plainItem with
        | True => shapedLeadCalm items within
        | False => shapedAllCalm items True within
    | App head arguments, within =>
      rewrite headCalm head item (Bool.andLeft within),
          shapedCalm head item (Bool.andLeft within),
          calmAllEmpty arguments False,
          argumentsCalm arguments (Bool.andRight within),
          shapedAllCalm arguments False (Bool.andRight within)
    | Infix InfixBinary left _ right, within =>
      rewrite shapedCalm left item (Bool.andLeft within),
          shapedCalm right False (Bool.andLeft (Bool.andRight within)),
          levelCalm left item (Bool.andLeft within),
          levelCalm right False (Bool.andLeft (Bool.andRight within))
    | Infix InfixArrow left _ right, within =>
      rewrite shapedCalm left item (Bool.andLeft within),
          shapedCalm right False (Bool.andLeft (Bool.andRight within)),
          levelCalm left item (Bool.andLeft within),
          levelCalm right False (Bool.andLeft (Bool.andRight within))
    | Prefix _ operand, within =>
      rewrite shapedCalm operand False (Bool.andLeft within), levelCalm operand False (Bool.andLeft within)
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible
    | other, never => (Bool.falseNotTrue never).impossible

theorem shapedAllCalm ∀ (items: List Expr) (item: Bool)
    (within: allWithin1 items = True):
    allShaped1 (calmAll item items) = allShaped1 items :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      rewrite shapedCalm first item (Bool.andLeft within), shapedAllCalm rest item (Bool.andRight within)

theorem shapedLeadCalm ∀ (items: List Expr)
    (within: allWithin1 items = True):
    allShaped1 (calmLead items) = allShaped1 items :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      rewrite shapedCalm first False (Bool.andLeft within), shapedAllCalm rest True (Bool.andRight within)

--| `calm` keeps how the tokens lex: it changes no text.
theorem lexicalCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).lexical1 = expr.lexical1 :=
  match expr, within with
    | Atom _ _, _ => byComputing
    | Paren _ inner _, within => rewrite lexicalCalm inner False within
    | Tuple _ items _ _, within => rewrite lexicalAllCalm items True within
    | ListOf _ items _ _, within =>
      match items.all Expr.plainItem with
        | True => rewrite lexicalLeadCalm items within
        | False => rewrite lexicalAllCalm items True within
    | App head arguments, within =>
      rewrite lexicalCalm head item (Bool.andLeft within), lexicalAllCalm arguments False (Bool.andRight within)
    | Infix InfixBinary left _ right, within =>
      rewrite lexicalCalm left item (Bool.andLeft within), lexicalCalm right False (Bool.andLeft (Bool.andRight within))
    | Infix InfixArrow left _ right, within =>
      rewrite lexicalCalm left item (Bool.andLeft within), lexicalCalm right False (Bool.andLeft (Bool.andRight within))
    | Prefix _ operand, within => rewrite lexicalCalm operand False (Bool.andLeft within)
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible
    | other, never => (Bool.falseNotTrue never).impossible

theorem lexicalAllCalm ∀ (items: List Expr) (item: Bool)
    (within: allWithin1 items = True):
    allLexical1 (calmAll item items) = allLexical1 items :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      rewrite lexicalCalm first item (Bool.andLeft within), lexicalAllCalm rest item (Bool.andRight within)

theorem lexicalLeadCalm ∀ (items: List Expr)
    (within: allWithin1 items = True):
    allLexical1 (calmLead items) = allLexical1 items :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      rewrite lexicalCalm first False (Bool.andLeft within), lexicalAllCalm rest True (Bool.andRight within)
