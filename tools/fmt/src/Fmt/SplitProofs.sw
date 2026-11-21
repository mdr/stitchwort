--| Toward `printedSplit1` (SW-4077): what the items of a printed declaration's group share with the items of the
--| declaration's own printed leaves. `items` reads only tokens for every field but the leaf (`glued`, `afterOperand`,
--| depth, index), and the group has the printed leaves' tokens, so the printed spacing (`printedSpacing1`) holds of
--| the group's items too.

namespace Fmt.SplitProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Text, Void)
import Syntax (Comments, Decl, Expr, InfixKind, Item, Leaf, Tok, Token, Word, items, itemsAfter)
import Syntax.SettleProofs (tokens)
import Fmt (..)
import Fmt.OutputStatements (..)
import Fmt.GlueProofs (gluedAfter, itemsGlued)
import Fmt.SpacingProofs (printedSpacing1, spacingAdmitsGlue)
import Fmt.GroupFacts (..)
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
      let head: leaf.token = other.token := List.consInjectiveHead same
      let tail: tokens rest = tokens others := Eq.cong (.drop 1) same
      rewrite head, gluedSameTokens (Some other.token) rest others tail
    | [], [other, ..others], never => (List.nilNotCons other.token (tokens others) never).impossible
    | [leaf, ..rest], [], never => (List.nilNotCons leaf.token (tokens rest) never.flipped).impossible

--| Leaves with the same tokens have items glued alike.
theorem itemsGluedSame ∀ (first second: List Leaf)
    (same: tokens first = tokens second):
    (items first).map (item => item.glued) = (items second).map (item => item.glued) :=
  rewrite itemsGlued None 0 0 0 first, itemsGlued None 0 0 0 second, gluedSameTokens None first second same

--| A printed declaration's group is spaced as `Decl.spacing` says: `printedSpacing1`, carried over the shared
--| tokens.
theorem groupSpacing ∀ (decl read: Decl) (group: List Leaf)
    (printed: PrintedGroup decl read group):
    spacingAdmits decl.spacing (items group) = True :=
  let (within, shaped, settled, lexical, _, _, sameTokens, _, _) := printed
  rewrite spacingAdmitsGlue decl.spacing (items group),
      itemsGluedSame group decl.leaves sameTokens,
      <- spacingAdmitsGlue decl.spacing (items decl.leaves) then
    printedSpacing1 decl within shaped settled lexical

--| `groupSpacing` applies to `def d: A := -1 n`, the `1` glued to the `-`.
theorem groupSpacingExample: spacingAdmits prefixHeadDecl.spacing (items prefixHeadDecl.leaves) = True :=
  groupSpacing prefixHeadDecl (prefixHeadDecl.calmAt True) prefixHeadDecl.leaves prefixHeadPrinted

-- The code texts of an expression: its tokens' texts with the comments dropped, commas kept.

--| A token's text is no comment, and its comments are comments: the spelling's comments are the ones dropped.
def Word.clean (word: Word): Bool := notComment word.text && word.comments.texts.all commentText

--| An expression's tokens' texts, a comma between a bracket's items: what `printedTokens1` says the printed leaves
--| are, without the comments.
def Expr.codeTexts: Expr → List Text
  | Atom _ word => [word.text]
  | Paren open inner close => [open.text, ..inner.codeTexts] ++ [close.text]
  | Tuple open items _ close | ListOf open items _ close => [open.text, ..commaTexts items] ++ [close.text]
  | App head arguments => head.codeTexts ++ argumentTexts arguments
  | Infix _ left operator right => left.codeTexts ++ [operator.text, ..right.codeTexts]
  | Prefix operator operand => [operator.text, ..operand.codeTexts]
  | _ => []

def commaTexts: List Expr → List Text
  | [] => []
  | [item] => item.codeTexts
  | [item, ..rest] => item.codeTexts ++ [","] ++ commaTexts rest

def argumentTexts: List Expr → List Text
  | [] => []
  | [argument, ..rest] => argument.codeTexts ++ argumentTexts rest

--| Comments filtered out leave nothing.
theorem commentsDropped ∀ (texts: List Text) (all: texts.all commentText = True): texts.filter notComment = [] :=
  match texts, all with
    | [], _ => byComputing
    | [text, ..rest], all =>
      let (isComment, others) := List.allConsElim text rest commentText all
      rewrite commentsApart text isComment, commentsDropped rest others

--| A clean token's spelling, comments filtered out, is its text.
theorem wordDropsComments ∀ (word: Word) (hoisted: Bool)
    (clean: word.clean = True):
    (word.spelledAt hoisted).filter notComment = [word.text] :=
  let comments: word.comments.texts.all commentText = True := Bool.andRight clean
  let both: ((word.comments.above.map (note => note.text)).all commentText
    && word.comments.after.toList.all commentText)
    = True :=
    rewrite <- List.allAppendAnd
          (word.comments.above.map (note => note.text))
          word.comments.after.toList
          commentText then
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
    (clean: expr.words.all Word.clean = True):
    (expr.spelt hoisted).filter notComment = expr.codeTexts :=
  match expr, within with
    | Atom _ word, _ => wordDropsComments word hoisted (List.allConsElim word [] Word.clean clean).left
    | Paren open inner close, within =>
      let (front, back) := allSplitBool [open, ..inner.words] [close] Word.clean clean
      let (openClean, innerClean) := List.allConsElim open inner.words Word.clean front
      rewrite List.filterAppend (open.spelledAt hoisted) (inner.spelt False ++ close.spelledAt False) notComment,
          List.filterAppend (inner.spelt False) (close.spelledAt False) notComment,
          wordDropsComments open hoisted openClean,
          codeTextsOf inner False within innerClean,
          wordDropsComments close False (List.allConsElim close [] Word.clean back).left
    | Tuple open items _ close | ListOf open items _ close, within =>
      let (front, back) := allSplitBool [open, ..itemsWords items] [close] Word.clean clean
      let (openClean, itemsClean) := List.allConsElim open (itemsWords items) Word.clean front
      rewrite List.filterAppend (open.spelledAt hoisted) (commaSpelt items ++ close.spelledAt False) notComment,
          List.filterAppend (commaSpelt items) (close.spelledAt False) notComment,
          wordDropsComments open hoisted openClean,
          commaTextsOf items within itemsClean,
          wordDropsComments close False (List.allConsElim close [] Word.clean back).left
    | App head arguments, within =>
      let (headClean, argumentsClean) := allSplitBool head.words (itemsWords arguments) Word.clean clean
      rewrite List.filterAppend (head.spelt hoisted) (argumentsSpelt arguments) notComment,
          codeTextsOf head hoisted (Bool.andLeft within) headClean,
          argumentTextsOf arguments (Bool.andRight within) argumentsClean
    | Infix kind left operator right, within =>
      cases kind then infixTextsOf kind left operator right hoisted
        (Bool.andLeft within)
        (Bool.andLeft (Bool.andRight within))
        clean
    | Prefix operator operand, within =>
      let (operatorClean, operandClean) := List.allConsElim operator operand.words Word.clean clean
      rewrite List.filterAppend (operator.spelledAt hoisted) (operand.spelt False) notComment,
          wordDropsComments operator hoisted operatorClean,
          codeTextsOf operand False (Bool.andLeft within) operandClean
    | _, never => (Bool.falseNotTrue never).impossible

theorem infixTextsOf ∀ (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr) (hoisted: Bool)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (clean: (Infix kind left operator right).words.all Word.clean = True):
    ((Infix kind left operator right).spelt hoisted).filter notComment = (Infix kind left operator right).codeTexts :=
  let (leftClean, restClean) := allSplitBool left.words [operator, ..right.words] Word.clean clean
  let (operatorClean, rightClean) := List.allConsElim operator right.words Word.clean restClean
  rewrite List.filterAppend (left.spelt hoisted) (operator.spelledAt False ++ right.spelt False) notComment,
      List.filterAppend (operator.spelledAt False) (right.spelt False) notComment,
      codeTextsOf left hoisted leftWithin leftClean,
      wordDropsComments operator False operatorClean,
      codeTextsOf right False rightWithin rightClean

theorem commaTextsOf ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (clean: (itemsWords items).all Word.clean = True):
    (commaSpelt items).filter notComment = commaTexts items :=
  match items with
    | [] => byComputing
    | [item] => codeTextsOf item False (Bool.andLeft within) (allSplitBool item.words [] Word.clean clean).left
    | [item, next, ..rest] =>
      let (itemClean, restClean) := allSplitBool item.words (itemsWords [next, ..rest]) Word.clean clean
      rewrite List.filterAppend (item.spelt False) ([","] ++ commaSpelt [next, ..rest]) notComment,
          List.filterAppend [","] (commaSpelt [next, ..rest]) notComment,
          codeTextsOf item False (Bool.andLeft within) itemClean,
          commaTextsOf [next, ..rest] (Bool.andRight within) restClean

theorem argumentTextsOf ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True)
    (clean: (itemsWords arguments).all Word.clean = True):
    (argumentsSpelt arguments).filter notComment = argumentTexts arguments :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      let (argumentClean, restClean) := allSplitBool argument.words (itemsWords rest) Word.clean clean
      rewrite List.filterAppend (argument.spelt False) (argumentsSpelt rest) notComment,
          codeTextsOf argument False (Bool.andLeft within) argumentClean,
          argumentTextsOf rest (Bool.andRight within) restClean

-- `afterOperand`, item by item.

--| Each item's `afterOperand` says whether the item before it closes an operand: how `items` sets it, which a call's
--| argument (`argumentGlue`) and a head's `-` (`negativeNumeral`) read.
def Chained: List Item → Bool
  | [first, second, ..rest] => (second.afterOperand == first.kind.closesOperand) && Chained [second, ..rest]
  | _ => True

theorem itemsChained ∀ (before: Option Token) (index depth lineIndent: Nat) (leaves: List Leaf):
    Chained (itemsAfter before index depth lineIndent leaves) = True :=
  match leaves with
    | [] | [_] => byComputing
    | [leaf, next, ..rest] =>
      rewrite itemsChained
            (Some leaf.token)
            (index + 1)
            (if leaf.token.kind.isOpener then depth + 1
             else if leaf.token.kind.isCloser then depth - 1
             else depth)
            (if leaf.token.lineStart then leaf.token.column else lineIndent)
            [next, ..rest],
          DecEq.refl leaf.token.kind.closesOperand

--| A group's items are chained.
theorem groupChained ∀ (group: List Leaf): Chained (items group) = True := itemsChained None 0 0 0 group

-- `calm` keeps the spacing: it changes only blank-line flags, and `signQuiet` reads whether comments are there.

--| `calm` keeps a slice 1 expression's first token, its flags calmed.
theorem leadCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).lead = expr.lead.kept item False :=
  match expr, within with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _, _ => byComputing
    | App head _ | Infix InfixBinary head _ _ | Infix InfixArrow head _ _, within =>
      leadCalm head item (Bool.andLeft within)
    | Prefix _ _, _ => byComputing
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

theorem numeralOneCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).numeral1 = expr.numeral1 :=
  match expr, within with
    | Atom Num _ | Atom Float _ | Atom Lower _ | Atom Upper _, _ => byComputing
    | Atom _ _, never => (Bool.falseNotTrue never).impossible
    | Paren _ _ _ |
        Tuple _ _ _ _ |
        ListOf _ _ _ _ |
        App _ _ |
        Infix InfixBinary _ _ _ |
        Infix InfixArrow _ _ _ |
        Prefix _ _, _ => byComputing
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

--| Whether comments sit between a sign and its operand is kept by `calm`.
theorem signQuietCalm ∀ (operator: Word) (operand: Expr) (item: Bool)
    (within: operand.within1 = True):
    signQuiet (operator.kept item False) (operand.calm False) = signQuiet operator operand :=
  rewrite leadCalm operand False within then
    match operator.comments.after, operand.lead.comments.above with | None | Some _, [] | [_, .._] => byComputing

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
    (expr.calm item).spacing argument = expr.spacing argument :=
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
    | Infix InfixBinary left _ right | Infix InfixArrow left _ right, within =>
      rewrite spacingCalm left item False (Bool.andLeft within),
          spacingCalm right False False (Bool.andLeft (Bool.andRight within))
    | Prefix operator operand, within =>
      rewrite operandSpacingCalm argument operator operand item (Bool.andLeft within) then
        match operandSpacing argument operator operand with
          | Some _ | None => rewrite spacingCalm operand False False (Bool.andLeft within)
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

theorem commaSpacingCalmAll ∀ (items: List Expr) (item: Bool)
    (within: allWithin1 items = True):
    commaSpacing (calmAll item items) = commaSpacing items :=
  match items with
    | [] => byComputing
    | [one] => rewrite spacingCalm one item False (Bool.andLeft within)
    | [one, next, ..rest] =>
      rewrite spacingCalm one item False (Bool.andLeft within),
          commaSpacingCalmAll [next, ..rest] item (Bool.andRight within)

theorem commaSpacingCalmLead ∀ (items: List Expr)
    (within: allWithin1 items = True):
    commaSpacing (calmLead items) = commaSpacing items :=
  match items with
    | [] => byComputing
    | [one] => rewrite spacingCalm one False False (Bool.andLeft within)
    | [one, next, ..rest] =>
      rewrite spacingCalm one False False (Bool.andLeft within),
          commaSpacingCalmAll [next, ..rest] True (Bool.andRight within)

theorem argumentsSpacingCalm ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True):
    argumentsSpacing (calmAll False arguments) = argumentsSpacing arguments :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      rewrite spacingCalm argument False True (Bool.andLeft within), argumentsSpacingCalm rest (Bool.andRight within)

-- `calm` keeps the shape: it changes no constructor, text or atom kind.

theorem levelCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).level = expr.level :=
  match expr, within with
    | Atom _ _ |
        Paren _ _ _ |
        Tuple _ _ _ _ |
        ListOf _ _ _ _ |
        App _ _ |
        Infix InfixBinary _ _ _ |
        Infix InfixArrow _ _ _ |
        Prefix _ _, _ => byComputing
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

theorem atomicCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).primary = expr.primary :=
  match expr, within with
    | Atom _ _ |
        Paren _ _ _ |
        Tuple _ _ _ _ |
        ListOf _ _ _ _ |
        App _ _ |
        Infix InfixBinary _ _ _ |
        Infix InfixArrow _ _ _ |
        Prefix _ _, _ => byComputing
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

theorem numberAtomCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).numberAtom = expr.numberAtom :=
  match expr, within with
    | Atom Tok.Num _ | Atom Tok.Float _ | Atom Tok.Lower _ | Atom Tok.Upper _, _ => byComputing
    | Atom _ _, never => (Bool.falseNotTrue never).impossible
    | Paren _ _ _ |
        Tuple _ _ _ _ |
        ListOf _ _ _ _ |
        App _ _ |
        Infix InfixBinary _ _ _ |
        Infix InfixArrow _ _ _ |
        Prefix _ _, _ => byComputing
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

theorem headCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).callHead = expr.callHead :=
  match expr, within with
    | Prefix operator operand, within =>
      rewrite numberAtomCalm operand False (Bool.andLeft within),
          signQuietCalm operator operand item (Bool.andLeft within)
    | Atom _ _ |
        Paren _ _ _ |
        Tuple _ _ _ _ |
        ListOf _ _ _ _ |
        App _ _ |
        Infix InfixBinary _ _ _ |
        Infix InfixArrow _ _ _, _ => byComputing
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

theorem argumentCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).callArgument = expr.callArgument :=
  match expr, within with
    | Prefix operator operand, within =>
      rewrite atomicCalm operand False (Bool.andLeft within), signQuietCalm operator operand item (Bool.andLeft within)
    | Atom _ _ |
        Paren _ _ _ |
        Tuple _ _ _ _ |
        ListOf _ _ _ _ |
        App _ _ |
        Infix InfixBinary _ _ _ |
        Infix InfixArrow _ _ _, _ => byComputing
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

theorem argumentsCalm ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True):
    (calmAll False arguments).all Expr.callArgument = arguments.all Expr.callArgument :=
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
--| kind and list length, so each test of `shaped` (levels, heads, arguments) comes out the same.
theorem shapedCalm ∀ (expr: Expr) (item: Bool) (within: expr.within1 = True): (expr.calm item).shaped = expr.shaped :=
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
    | Infix InfixBinary left _ right | Infix InfixArrow left _ right, within =>
      rewrite shapedCalm left item (Bool.andLeft within),
          shapedCalm right False (Bool.andLeft (Bool.andRight within)),
          levelCalm left item (Bool.andLeft within),
          levelCalm right False (Bool.andLeft (Bool.andRight within))
    | Prefix _ operand, within =>
      rewrite shapedCalm operand False (Bool.andLeft within), levelCalm operand False (Bool.andLeft within)
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

theorem shapedAllCalm ∀ (items: List Expr) (item: Bool)
    (within: allWithin1 items = True):
    allShaped (calmAll item items) = allShaped items :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      rewrite shapedCalm first item (Bool.andLeft within), shapedAllCalm rest item (Bool.andRight within)

theorem shapedLeadCalm ∀ (items: List Expr)
    (within: allWithin1 items = True):
    allShaped (calmLead items) = allShaped items :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      rewrite shapedCalm first False (Bool.andLeft within), shapedAllCalm rest True (Bool.andRight within)

--| `calm` keeps how the tokens lex: it changes no text.
theorem lexicalCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).lexical = expr.lexical :=
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
    | Infix InfixBinary left _ right | Infix InfixArrow left _ right, within =>
      rewrite lexicalCalm left item (Bool.andLeft within), lexicalCalm right False (Bool.andLeft (Bool.andRight within))
    | Prefix _ operand, within => rewrite lexicalCalm operand False (Bool.andLeft within)
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

theorem lexicalAllCalm ∀ (items: List Expr) (item: Bool)
    (within: allWithin1 items = True):
    allLexical (calmAll item items) = allLexical items :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      rewrite lexicalCalm first item (Bool.andLeft within), lexicalAllCalm rest item (Bool.andRight within)

theorem lexicalLeadCalm ∀ (items: List Expr)
    (within: allWithin1 items = True):
    allLexical (calmLead items) = allLexical items :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      rewrite lexicalCalm first False (Bool.andLeft within), lexicalAllCalm rest True (Bool.andRight within)
