--| `printedSplit1` (SW-4077): a printed declaration's group of leaves splits into the items read-back reads, the
--| type's and value's spelt by theirs. The group's tokens are the printed leaves' (`PrintedGroup`), whose texts are
--| the declaration's code texts (`printedTokens1`, `codeTextsOf`) and whose kinds the lexer's (`Leaf.kinded`); its
--| code words are the read declaration's. A comma's text lexes as a comma and no word's does, so the items fill the
--| declaration's slots (`slotsFromTexts`), and `speltSlots` spells each part from its items.

namespace Fmt.GroupSlots
import Std (Bool, DecEq, Eq, List, Nat, Option, Text, Void)
import Syntax (..)
import Syntax.ParseCarries (codeWords, itemWords, wordWithinNotComma)
import Fmt (..)
import Fmt.OutputStatements (..)
import Fmt.TreeJoinProofs (
  OperatorSpells,
  PrefixSpells,
  infixListed,
  lexKind,
  nameKinded,
  operatorSpellsOf,
  prefixSpellsOf,
  spellsNotComment,
  spellsOfText1
)
import Fmt.SpellProofs (..)
import Fmt.SplitProofs (..)
import Fmt.SpeltSlots (..)
import Fmt.GroupFacts (..)
import Fmt.PassProofs (..)
import Fmt.TokenProofs (printedTokens1)
import Fmt.CalmProofs (withinCalm)
import Fmt.CalmTopProofs (exprCalmCommaFree)
import Syntax.ParseCarriesFile (itemWordsOfGroup, itemsLeaves)
import Syntax.SettleProofs (tokens)
import Syntax.ReadBackLine (Spelt)
import Syntax.ReadBackRuns (plainHeader)
import Syntax.ReadBackLine (infixTok, signKind)

-- Lists.

-- Clean words: a token's text is no comment.

theorem wordClean ∀ (word: Word)
    (plain: word.text.startsWith "--" = False)
    (commented: Fmt.SpellProofs.Word.commented word = True):
    word.clean = True :=
  Bool.andIntro (rewrite plain) commented

theorem fixedClean ∀ (text: Text) (comments: Comments)
    (plain: text.startsWith "--" = False)
    (commented: Fmt.SpellProofs.Word.commented (fixedWord text comments) = True):
    (fixedWord text comments).clean = True :=
  wordClean (fixedWord text comments) plain commented

theorem operatorNotComment ∀ (text: Text) (listed: operatorText1 text = True): text.startsWith "--" = False :=
  let (kind, spells, _) := operatorSpellsOf text listed
  spellsNotComment kind text spells

theorem prefixNotComment ∀ (text: Text) (listed: prefixText1 text = True): text.startsWith "--" = False :=
  match prefixSpellsOf text listed with | Inl minus | Inr (Inl minus) | Inr (Inr minus) => rewrite minus

theorem textPlain ∀ (text expected: Text)
    (is: (text == expected) = True)
    (plain: expected.startsWith "--" = False):
    text.startsWith "--" = False :=
  rewrite DecEq.sound is then plain

--| A slice 1 expression's words are clean when their comments are comments.
--|
--| Proof idea: by induction on the expression; a name or numeral is spelled as its kind (`spellsOfText1`), an
--| operator as a token of the alphabet, a bracket as itself, and no such text starts a comment (`spellsNotComment`).
theorem wordsClean ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical = True)
    (commented: expr.words.all Fmt.SpellProofs.Word.commented = True):
    expr.words.all Word.clean = True :=
  match expr, within with
    | Atom kind word, within =>
      Bool.andIntro
        (wordClean word
          (spellsNotComment kind word.text (spellsOfText1 kind word.text (Bool.andRight within)))
          (Bool.andLeft commented))
        byComputing
    | Paren open inner close, within =>
      let (front, back) := allSplitBool [open, ..inner.words] [close] Fmt.SpellProofs.Word.commented commented
      let (openCommented, innerCommented) := List.allConsElim open inner.words Fmt.SpellProofs.Word.commented front
      List.allAppendTrue
        [open, ..inner.words]
        [close]
        Word.clean
        (Bool.andIntro
          (wordClean open (textPlain open.text "(" (Bool.andLeft lexical) byComputing) openCommented)
          (wordsClean inner within (Bool.andRight (Bool.andRight lexical)) innerCommented))
        (Bool.andIntro
          (wordClean close
            (textPlain close.text ")" (Bool.andLeft (Bool.andRight lexical)) byComputing)
            (Bool.andLeft back))
          byComputing)
    | Tuple open items comma close, within =>
      let (front, back) := allSplitBool [open, ..itemsWords items] [close] Fmt.SpellProofs.Word.commented commented
      let (openCommented, itemsCommented) :=
        List.allConsElim open (itemsWords items) Fmt.SpellProofs.Word.commented front
      List.allAppendTrue
        [open, ..itemsWords items]
        [close]
        Word.clean
        (Bool.andIntro
          (wordClean open (textPlain open.text "(" (Bool.andLeft lexical) byComputing) openCommented)
          (itemsClean items within (Bool.andRight (Bool.andRight lexical)) itemsCommented))
        (Bool.andIntro
          (wordClean close
            (textPlain close.text ")" (Bool.andLeft (Bool.andRight lexical)) byComputing)
            (Bool.andLeft back))
          byComputing)
    | ListOf open items comma close, within =>
      let (front, back) := allSplitBool [open, ..itemsWords items] [close] Fmt.SpellProofs.Word.commented commented
      let (openCommented, itemsCommented) :=
        List.allConsElim open (itemsWords items) Fmt.SpellProofs.Word.commented front
      List.allAppendTrue
        [open, ..itemsWords items]
        [close]
        Word.clean
        (Bool.andIntro
          (wordClean open (textPlain open.text "[" (Bool.andLeft lexical) byComputing) openCommented)
          (itemsClean items within (Bool.andRight (Bool.andRight lexical)) itemsCommented))
        (Bool.andIntro
          (wordClean close
            (textPlain close.text "]" (Bool.andLeft (Bool.andRight lexical)) byComputing)
            (Bool.andLeft back))
          byComputing)
    | App head arguments, within =>
      let (headCommented, argumentsCommented) :=
        allSplitBool head.words (itemsWords arguments) Fmt.SpellProofs.Word.commented commented
      List.allAppendTrue head.words
        (itemsWords arguments)
        Word.clean
        (wordsClean head (Bool.andLeft within) (Bool.andLeft lexical) headCommented)
        (itemsClean arguments (Bool.andRight within) (Bool.andRight lexical) argumentsCommented)
    | Infix InfixBinary left operator right, within =>
      infixClean InfixBinary left operator right within
        (Bool.andLeft within)
        (Bool.andLeft (Bool.andRight within))
        lexical
        commented
    | Infix InfixArrow left operator right, within =>
      infixClean InfixArrow left operator right within
        (Bool.andLeft within)
        (Bool.andLeft (Bool.andRight within))
        lexical
        commented
    | Prefix operator operand, within =>
      let (operatorCommented, operandCommented) :=
        List.allConsElim operator operand.words Fmt.SpellProofs.Word.commented commented
      Bool.andIntro
        (wordClean operator (prefixNotComment operator.text (Bool.andRight within)) operatorCommented)
        (wordsClean operand (Bool.andLeft within) (Bool.andRight lexical) operandCommented)
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible

theorem infixClean ∀ (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr)
    (within: (Infix kind left operator right).within1 = True)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (lexical: (Infix kind left operator right).lexical = True)
    (commented: (Infix kind left operator right).words.all Fmt.SpellProofs.Word.commented = True):
    (Infix kind left operator right).words.all Word.clean = True :=
  let (leftCommented, restCommented) :=
    allSplitBool left.words [operator, ..right.words] Fmt.SpellProofs.Word.commented commented
  let (operatorCommented, rightCommented) :=
    List.allConsElim operator right.words Fmt.SpellProofs.Word.commented restCommented
  List.allAppendTrue left.words
    [operator, ..right.words]
    Word.clean
    (wordsClean left leftWithin (Bool.andLeft lexical) leftCommented)
    (Bool.andIntro
      (wordClean operator
        (operatorNotComment operator.text (infixListed kind left operator right within))
        operatorCommented)
      (wordsClean right rightWithin (Bool.andRight (Bool.andRight lexical)) rightCommented))

theorem itemsClean ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (lexical: allLexical items = True)
    (commented: (itemsWords items).all Fmt.SpellProofs.Word.commented = True):
    (itemsWords items).all Word.clean = True :=
  match items with
    | [] => byComputing
    | [item, ..rest] =>
      let (itemCommented, restCommented) :=
        allSplitBool item.words (itemsWords rest) Fmt.SpellProofs.Word.commented commented
      List.allAppendTrue item.words
        (itemsWords rest)
        Word.clean
        (wordsClean item (Bool.andLeft within) (Bool.andLeft lexical) itemCommented)
        (itemsClean rest (Bool.andRight within) (Bool.andRight lexical) restCommented)

-- Slots, read as texts and words.

--| A slot's text: its word's, or a comma's.
def slotText: Option Word → Text
  | Some word => word.text
  | None => ","

--| The words of the slots, commas left out.
def someWords: List (Option Word) → List Word
  | [] => []
  | [Some word, ..rest] => [word, ..someWords rest]
  | [None, ..rest] => someWords rest

theorem someWordsAppend ∀ (xs ys: List (Option Word)): someWords (xs ++ ys) = someWords xs ++ someWords ys :=
  match xs with
    | [] => byComputing
    | [Some word, ..rest] => rewrite someWordsAppend rest ys
    | [None, ..rest] => someWordsAppend rest ys

--| An expression's slots read as texts are its code texts.
theorem slotTexts ∀ (expr: Expr) (within: expr.within1 = True): expr.slots.map slotText = expr.codeTexts :=
  match expr, within with
    | Atom _ _, _ => byComputing
    | Paren open inner close, within =>
      rewrite List.mapAppend [Some open, ..inner.slots] [Some close] slotText, slotTexts inner within
    | Tuple open items _ close | ListOf open items _ close, within =>
      rewrite List.mapAppend [Some open, ..commaSlots items] [Some close] slotText, commaSlotTexts items within
    | App head arguments, within =>
      rewrite List.mapAppend head.slots (argumentSlots arguments) slotText,
          slotTexts head (Bool.andLeft within),
          argumentSlotTexts arguments (Bool.andRight within)
    | Infix InfixBinary left operator right | Infix InfixArrow left operator right, within =>
      rewrite List.mapAppend left.slots [Some operator, ..right.slots] slotText,
          slotTexts left (Bool.andLeft within),
          slotTexts right (Bool.andLeft (Bool.andRight within))
    | Prefix operator operand, within => rewrite slotTexts operand (Bool.andLeft within)
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

theorem commaSlotTexts ∀ (items: List Expr)
    (within: allWithin1 items = True):
    (commaSlots items).map slotText = commaTexts items :=
  match items with
    | [] => byComputing
    | [one] => slotTexts one (Bool.andLeft within)
    | [one, next, ..rest] =>
      rewrite List.mapAppend one.slots ([None] ++ commaSlots [next, ..rest]) slotText,
          slotTexts one (Bool.andLeft within),
          commaSlotTexts [next, ..rest] (Bool.andRight within)

theorem argumentSlotTexts ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True):
    (argumentSlots arguments).map slotText = argumentTexts arguments :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      rewrite List.mapAppend argument.slots (argumentSlots rest) slotText,
          slotTexts argument (Bool.andLeft within),
          argumentSlotTexts rest (Bool.andRight within)

--| An expression's slots' words are its words.
theorem slotWords ∀ (expr: Expr) (within: expr.within1 = True): someWords expr.slots = expr.words :=
  match expr, within with
    | Atom _ _, _ => byComputing
    | Paren open inner close, within =>
      rewrite someWordsAppend [Some open, ..inner.slots] [Some close], slotWords inner within
    | Tuple open items _ close | ListOf open items _ close, within =>
      rewrite someWordsAppend [Some open, ..commaSlots items] [Some close], commaSlotWords items within
    | App head arguments, within =>
      rewrite someWordsAppend head.slots (argumentSlots arguments),
          slotWords head (Bool.andLeft within),
          argumentSlotWords arguments (Bool.andRight within)
    | Infix InfixBinary left operator right | Infix InfixArrow left operator right, within =>
      rewrite someWordsAppend left.slots [Some operator, ..right.slots],
          slotWords left (Bool.andLeft within),
          slotWords right (Bool.andLeft (Bool.andRight within))
    | Prefix operator operand, within => rewrite slotWords operand (Bool.andLeft within)
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

theorem commaSlotWords ∀ (items: List Expr)
    (within: allWithin1 items = True):
    someWords (commaSlots items) = itemsWords items :=
  match items with
    | [] => byComputing
    | [one] => rewrite slotWords one (Bool.andLeft within), List.appendNil one.words
    | [one, next, ..rest] =>
      rewrite someWordsAppend one.slots ([None] ++ commaSlots [next, ..rest]),
          slotWords one (Bool.andLeft within),
          commaSlotWords [next, ..rest] (Bool.andRight within)

theorem argumentSlotWords ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True):
    someWords (argumentSlots arguments) = itemsWords arguments :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      rewrite someWordsAppend argument.slots (argumentSlots rest),
          slotWords argument (Bool.andLeft within),
          argumentSlotWords rest (Bool.andRight within)

-- `calm` keeps the code texts.

theorem codeTextsCalm ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True):
    (expr.calm item).codeTexts = expr.codeTexts :=
  match expr, within with
    | Atom _ _, _ => byComputing
    | Paren _ inner _, within => rewrite codeTextsCalm inner False within
    | Tuple _ items _ _, within => rewrite commaTextsCalmAll items True within
    | ListOf _ items _ _, within =>
      match items.all Expr.plainItem with
        | True => rewrite commaTextsCalmLead items within
        | False => rewrite commaTextsCalmAll items True within
    | App head arguments, within =>
      rewrite codeTextsCalm head item (Bool.andLeft within), argumentTextsCalm arguments (Bool.andRight within)
    | Infix InfixBinary left _ right | Infix InfixArrow left _ right, within =>
      rewrite codeTextsCalm left item (Bool.andLeft within),
          codeTextsCalm right False (Bool.andLeft (Bool.andRight within))
    | Prefix _ operand, within => rewrite codeTextsCalm operand False (Bool.andLeft within)
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

theorem commaTextsCalmAll ∀ (items: List Expr) (item: Bool)
    (within: allWithin1 items = True):
    commaTexts (calmAll item items) = commaTexts items :=
  match items with
    | [] => byComputing
    | [one] => rewrite codeTextsCalm one item (Bool.andLeft within)
    | [one, next, ..rest] =>
      rewrite codeTextsCalm one item (Bool.andLeft within), commaTextsCalmAll [next, ..rest] item (Bool.andRight within)

theorem commaTextsCalmLead ∀ (items: List Expr)
    (within: allWithin1 items = True):
    commaTexts (calmLead items) = commaTexts items :=
  match items with
    | [] => byComputing
    | [one] => rewrite codeTextsCalm one False (Bool.andLeft within)
    | [one, next, ..rest] =>
      rewrite codeTextsCalm one False (Bool.andLeft within),
          commaTextsCalmAll [next, ..rest] True (Bool.andRight within)

theorem argumentTextsCalm ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True):
    argumentTexts (calmAll False arguments) = argumentTexts arguments :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      rewrite codeTextsCalm argument False (Bool.andLeft within), argumentTextsCalm rest (Bool.andRight within)

-- No word is a comma.

--| A slot for a word holds no comma's text, as the lexer reads it.
def slotCode: Option Word → Bool
  | Some word => !(lexKind word.text == Comma)
  | None => True

theorem infixNotComma ∀ (kind: InfixKind) (tok: Tok) (is: infixTok kind tok = True): (tok == Comma) = False :=
  match kind, is with
    | InfixArrow, is => rewrite DecEq.sound is
    | InfixBinary, is =>
      match tok, is with
        | Star, _ => byComputing
        | Slash, _ => byComputing
        | Percent, _ => byComputing
        | Plus, _ => byComputing
        | Minus, _ => byComputing
        | PlusPlus, _ => byComputing
        | Equals, _ => byComputing
        | EqEq, _ => byComputing
        | NotEq, _ => byComputing
        | Lt, _ => byComputing
        | Le, _ => byComputing
        | Gt, _ => byComputing
        | Ge, _ => byComputing
        | AndAnd, _ => byComputing
        | OrOr, _ => byComputing

theorem signNotComma ∀ (tok: Tok) (sign: signKind tok = True): (tok == Comma) = False := match tok, sign with
  | Minus | Bang, _ => byComputing

theorem bracketCode ∀ (word: Word) (expected: Text)
    (is: (word.text == expected) = True)
    (code: (lexKind expected == Comma) = False):
    slotCode (Some word) = True :=
  rewrite DecEq.sound is, code

--| No word of a slice 1 expression lexes as a comma.
theorem slotsCode ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical = True):
    expr.slots.all slotCode = True :=
  match expr, within with
    | Atom kind word, within =>
      Bool.andIntro
        (rewrite lexKindOfLexes word.text kind lexical, wordWithinNotComma kind (Bool.andLeft within))
        byComputing
    | Paren open inner close, within =>
      List.allAppendTrue
        [Some open, ..inner.slots]
        [Some close]
        slotCode
        (Bool.andIntro
          (bracketCode open "(" (Bool.andLeft lexical) byComputing)
          (slotsCode inner within (Bool.andRight (Bool.andRight lexical))))
        (Bool.andIntro (bracketCode close ")" (Bool.andLeft (Bool.andRight lexical)) byComputing) byComputing)
    | Tuple open items _ close, within =>
      List.allAppendTrue
        [Some open, ..commaSlots items]
        [Some close]
        slotCode
        (Bool.andIntro
          (bracketCode open "(" (Bool.andLeft lexical) byComputing)
          (commaSlotsCode items within (Bool.andRight (Bool.andRight lexical))))
        (Bool.andIntro (bracketCode close ")" (Bool.andLeft (Bool.andRight lexical)) byComputing) byComputing)
    | ListOf open items _ close, within =>
      List.allAppendTrue
        [Some open, ..commaSlots items]
        [Some close]
        slotCode
        (Bool.andIntro
          (bracketCode open "[" (Bool.andLeft lexical) byComputing)
          (commaSlotsCode items within (Bool.andRight (Bool.andRight lexical))))
        (Bool.andIntro (bracketCode close "]" (Bool.andLeft (Bool.andRight lexical)) byComputing) byComputing)
    | App head arguments, within =>
      List.allAppendTrue head.slots
        (argumentSlots arguments)
        slotCode
        (slotsCode head (Bool.andLeft within) (Bool.andLeft lexical))
        (argumentSlotsCode arguments (Bool.andRight within) (Bool.andRight lexical))
    | Infix InfixBinary left operator right, within =>
      let (isTok, _) := infixFacts InfixBinary operator.text (Bool.andRight (Bool.andRight within))
      List.allAppendTrue left.slots
        [Some operator, ..right.slots]
        slotCode
        (slotsCode left (Bool.andLeft within) (Bool.andLeft lexical))
        (Bool.andIntro
          (rewrite infixNotComma InfixBinary (lexKind operator.text) isTok)
          (slotsCode right (Bool.andLeft (Bool.andRight within)) (Bool.andRight (Bool.andRight lexical))))
    | Infix InfixArrow left operator right, within =>
      let (isTok, _) := infixFacts InfixArrow operator.text (Bool.andRight (Bool.andRight within))
      List.allAppendTrue left.slots
        [Some operator, ..right.slots]
        slotCode
        (slotsCode left (Bool.andLeft within) (Bool.andLeft lexical))
        (Bool.andIntro
          (rewrite infixNotComma InfixArrow (lexKind operator.text) isTok)
          (slotsCode right (Bool.andLeft (Bool.andRight within)) (Bool.andRight (Bool.andRight lexical))))
    | Prefix operator operand, within =>
      Bool.andIntro
        (rewrite signNotComma (lexKind operator.text) (prefixFacts operator.text (Bool.andRight within)).left)
        (slotsCode operand (Bool.andLeft within) (Bool.andRight lexical))
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible

theorem commaSlotsCode ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (lexical: allLexical items = True):
    (commaSlots items).all slotCode = True :=
  match items with
    | [] => byComputing
    | [one] => slotsCode one (Bool.andLeft within) (Bool.andLeft lexical)
    | [one, next, ..rest] =>
      List.allAppendTrue one.slots
        ([None] ++ commaSlots [next, ..rest])
        slotCode
        (slotsCode one (Bool.andLeft within) (Bool.andLeft lexical))
        (Bool.andIntro byComputing (commaSlotsCode [next, ..rest] (Bool.andRight within) (Bool.andRight lexical)))

theorem argumentSlotsCode ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True)
    (lexical: allLexical arguments = True):
    (argumentSlots arguments).all slotCode = True :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      List.allAppendTrue argument.slots
        (argumentSlots rest)
        slotCode
        (slotsCode argument (Bool.andLeft within) (Bool.andLeft lexical))
        (argumentSlotsCode rest (Bool.andRight within) (Bool.andRight lexical))

-- Items from texts.

--| Items whose texts are the slots' texts, of the lexer's kinds, whose code words are the slots' words, fill the slots
--| one by one, when no word's text lexes as a comma.
theorem slotsFromTexts ∀ (read: List Item) (slots: List (Option Word))
    (texts: read.map Item.text = slots.map slotText)
    (kinded: read.all (item => item.leaf.token.kind == lexKind item.leaf.token.text) = True)
    (words: itemWords read = someWords slots)
    (code: slots.all slotCode = True):
    List.All2 SlotMatch read slots :=
  match read, slots with
    | [], [] => Trivial
    | [item, ..rest], [Some word, ..more] =>
      let textIs: item.leaf.token.text = word.text := List.consInjectiveHead texts
      let kindLex: item.leaf.token.kind = lexKind item.leaf.token.text := DecEq.sound (Bool.andLeft kinded)
      let kindIs: item.leaf.token.kind = lexKind word.text := rewrite textIs at kindLex then kindLex
      let notComma: (lexKind word.text == Comma) = False :=
        Bool.notTrue (lexKind word.text == Comma) (Bool.andLeft code)
      let joined: [item.leaf.word, ..itemWords rest] = [word, ..someWords more] :=
        rewrite kindIs, notComma at words then words
      (
        (List.consInjectiveHead joined, kindIs),
        slotsFromTexts rest more
          (List.consTailEq _ _ _ _ texts)
          (Bool.andRight kinded)
          (List.consTailEq _ _ _ _ joined)
          (Bool.andRight code)
      )
    | [item, ..rest], [None, ..more] =>
      let textIs: item.leaf.token.text = "," := List.consInjectiveHead texts
      let kindLex: item.leaf.token.kind = lexKind item.leaf.token.text := DecEq.sound (Bool.andLeft kinded)
      let kindIs: item.leaf.token.kind = Comma := rewrite textIs at kindLex then kindLex
      let tail: itemWords rest = someWords more := rewrite kindIs at words then words
      (kindIs, slotsFromTexts rest more (List.consTailEq _ _ _ _ texts) (Bool.andRight kinded) tail code)

-- The declaration's parts.

--| The slots of `def name: result := value`, from its keyword's comments on.
def partSlots (keyword: Comments) (name: Word) (colon colonEq: Comments) (result value: Expr): List (Option Word) :=
  [Some (fixedWord "def" keyword), Some name, Some (fixedWord ":" colon)]
    ++ result.slots
    ++ [Some (fixedWord ":=" colonEq), ..value.slots]

--| The definition `def name: result := value` with nothing else in its header.
def plainDecl (keyword: Comments) (name: Word) (colon colonEq: Comments) (result value: Expr): Decl :=
  Definition []
    {
      exportKeyword = None,
      opaqueKeyword = None,
      kind = DefPlain,
      keyword,
      name,
      forallKeyword = None,
      params = [],
      colon,
      result,
      decreasingClause = None,
      unfoldingClause = None
    }
    (Assigned colonEq value)

--| What `speltSlots` asks of an expression's tree.
def SlotTree (expr: Expr): Prop :=
  expr.within1 = True ∧ expr.shaped = True ∧ expr.lexical = True ∧ expr.commaFree = True

theorem plainHeaderOf ∀ (keyword name colon: Item) (result: Expr):
    plainHeader keyword name colon result
      = {
        exportKeyword = None,
        opaqueKeyword = None,
        kind = DefPlain,
        keyword = keyword.leaf.word.comments,
        name = name.leaf.word,
        forallKeyword = None,
        params = [],
        colon = colon.leaf.word.comments,
        result,
        decreasingClause = None,
        unfoldingClause = None
      } :=
  byComputing

--| The items of `def name: result := value` split as `GroupSplit` says, from facts of the parts: their texts and the
--| lexer's kinds, their code words, their spacing, and the expressions' trees.
--|
--| Proof idea: the items fill the declaration's slots (`slotsFromTexts`), which split at the `:` and the `:=`
--| (`List.all2AppendSplit`), and so do the spacing (`admitsSplit`) and the chaining (`chainedSplit`); `speltSlots` spells each
--| expression from its items, which follow a `:` or `:=`, neither of which closes an operand (`chainedAfter`).
theorem splitOfParts ∀ (group: List Leaf) (keyword: Comments) (name: Word)
    (colon colonEq: Comments) (result value: Expr)
    (resultTree: SlotTree result)
    (valueTree: SlotTree value)
    (lower: lexKind name.text = Lower ∨ lexKind name.text = Upper)
    (texts: (items group).map Item.text = ["def", name.text, ":"] ++ result.codeTexts ++ [":=", ..value.codeTexts])
    (kinded: (items group).all (item => item.leaf.token.kind == lexKind item.leaf.token.text) = True)
    (words: itemWords (items group)
      = [fixedWord "def" keyword, name, fixedWord ":" colon] ++ result.words ++ [fixedWord ":=" colonEq, ..value.words])
    (spacing: spacingAdmits ([Free, Free, Free] ++ result.spacing False ++ [Free] ++ value.spacing False) (items group)
      = True):
    ∃ (keywordItem nameItem colonItem colonEqItem: Item) (typeRead valueRead: List Item) => GroupSplit group
      (plainDecl keyword name colon colonEq result value)
      keywordItem
      nameItem
      colonItem
      colonEqItem
      typeRead
      valueRead
      result
      value :=
  let (resultWithin, resultShaped, resultLexical, resultFree) := resultTree
  let (valueWithin, valueShaped, valueLexical, valueFree) := valueTree
  let slots := partSlots keyword name colon colonEq result value
  let slotTextsAre: slots.map slotText = ["def", name.text, ":"] ++ result.codeTexts ++ [":=", ..value.codeTexts] :=
    rewrite List.mapAppend result.slots [Some (fixedWord ":=" colonEq), ..value.slots] slotText,
        slotTexts result resultWithin,
        slotTexts value valueWithin
  let slotWordsAre: someWords slots
    = [fixedWord "def" keyword, name, fixedWord ":" colon] ++ result.words ++ [fixedWord ":=" colonEq, ..value.words] :=
    rewrite someWordsAppend result.slots [Some (fixedWord ":=" colonEq), ..value.slots],
        slotWords result resultWithin,
        slotWords value valueWithin
  let nameCode: slotCode (Some name) = True := match lower with | Inl same | Inr same => rewrite same
  let code: slots.all slotCode = True :=
    Bool.andIntro byComputing
      (Bool.andIntro nameCode
        (Bool.andIntro byComputing
          (List.allAppendTrue result.slots
            [Some (fixedWord ":=" colonEq), ..value.slots]
            slotCode
            (slotsCode result resultWithin resultLexical)
            (Bool.andIntro byComputing (slotsCode value valueWithin valueLexical)))))
  let filled: List.All2 SlotMatch (items group) slots :=
    slotsFromTexts
      (items group)
      slots
      (Eq.trans texts slotTextsAre.flipped)
      kinded
      (Eq.trans words slotWordsAre.flipped)
      code
  let (front, rest, isItems, frontFilled, restFilled) :=
    List.all2AppendSplit SlotMatch
      (items group)
      [Some (fixedWord "def" keyword), Some name, Some (fixedWord ":" colon)]
      (result.slots ++ [Some (fixedWord ":=" colonEq), ..value.slots])
      filled
  let (typeRead, tail, isRest, typeFilled, tailFilled) :=
    List.all2AppendSplit SlotMatch rest result.slots [Some (fixedWord ":=" colonEq), ..value.slots] restFilled
  splitFilled group keyword name colon colonEq result value resultTree valueTree lower spacing front typeRead tail
    (rewrite isItems, isRest)
    frontFilled
    typeFilled
    tailFilled

theorem splitFilled ∀ (group: List Leaf) (keyword: Comments) (name: Word) (colon colonEq: Comments) (result value: Expr)
    (resultTree: SlotTree result)
    (valueTree: SlotTree value)
    (lower: lexKind name.text = Lower ∨ lexKind name.text = Upper)
    (spacing: spacingAdmits ([Free, Free, Free] ++ result.spacing False ++ [Free] ++ value.spacing False) (items group)
      = True) (front typeRead tail: List Item)
    (isItems: items group = front ++ typeRead ++ tail)
    (frontFilled: List.All2 SlotMatch front [Some (fixedWord "def" keyword), Some name, Some (fixedWord ":" colon)])
    (typeFilled: List.All2 SlotMatch typeRead result.slots)
    (tailFilled: List.All2 SlotMatch tail [Some (fixedWord ":=" colonEq), ..value.slots]):
    ∃ (keywordItem nameItem colonItem colonEqItem: Item) (typeRead valueRead: List Item) => GroupSplit group
      (plainDecl keyword name colon colonEq result value)
      keywordItem
      nameItem
      colonItem
      colonEqItem
      typeRead
      valueRead
      result
      value :=
  match front, tail, isItems, frontFilled, tailFilled with
    | [keywordItem, nameItem, colonItem], [colonEqItem, ..valueRead], isItems, (
        (keywordWord, keywordKind),
        (nameWord, nameKind),
        (colonWord, colonKind),
        _
      ), ((colonEqWord, colonEqKind), valueFilled) =>
      let (resultWithin, resultShaped, resultLexical, resultFree) := resultTree
      let (valueWithin, valueShaped, valueLexical, valueFree) := valueTree
      let isDef: keywordItem.kind = KwDef := rewrite keywordKind
      let isLower: nameItem.kind = Lower ∨ nameItem.kind = Upper := match lower with
        | Inl same => Inl (rewrite nameKind, same)
        | Inr same => Inr (rewrite nameKind, same)
      let isColon: colonItem.kind = Colon := rewrite colonKind
      let isColonEq: colonEqItem.kind = ColonEq := rewrite colonEqKind
      let spaced: spacingAdmits
        ([Free, Free, Free] ++ result.spacing False ++ [Free] ++ value.spacing False)
        ([keywordItem, nameItem, colonItem] ++ typeRead ++ [colonEqItem, ..valueRead])
        = True :=
        rewrite isItems at spacing then spacing
      let (_, restSpaced) :=
        admitsSplit
          [Free, Free, Free]
          (result.spacing False ++ [Free] ++ value.spacing False)
          [keywordItem, nameItem, colonItem]
          (typeRead ++ [colonEqItem, ..valueRead])
          byComputing
          spaced
      let (typeSpaced, tailSpaced) :=
        admitsSplit
          (result.spacing False)
          ([Free] ++ value.spacing False)
          typeRead
          [colonEqItem, ..valueRead]
          (lengthOf result False typeRead resultWithin typeFilled)
          restSpaced
      let valueSpaced: spacingAdmits (value.spacing False) valueRead = True := Bool.andRight tailSpaced
      let chained: Chained ([keywordItem, nameItem, colonItem] ++ typeRead ++ [colonEqItem, ..valueRead]) = True :=
        let groupChain := groupChained group
        rewrite isItems at groupChain then groupChain
      let (_, restChained) :=
        chainedSplit [keywordItem, nameItem, colonItem] (typeRead ++ [colonEqItem, ..valueRead]) chained
      let (typeChained, tailChained) := chainedSplit typeRead [colonEqItem, ..valueRead] restChained
      let (_, valueChained) := chainedSplit [colonEqItem] valueRead tailChained
      let typeLeadAll := chainedAfter [keywordItem, nameItem] colonItem (typeRead ++ [colonEqItem, ..valueRead]) chained
      let typeLead: leadAfter typeRead False = True :=
        rewrite isColon at typeLeadAll then leadFront typeRead [colonEqItem, ..valueRead] False typeLeadAll
      let valueLeadAll := chainedAfter ([keywordItem, nameItem, colonItem] ++ typeRead) colonEqItem valueRead chained
      let valueLead: leadAfter valueRead False = True := rewrite isColonEq at valueLeadAll then valueLeadAll
      let noRole: False = True → result.callArgument = True := never => (Bool.falseNotTrue never).impossible
      let noValueRole: False = True → value.callArgument = True := never => (Bool.falseNotTrue never).impossible
      let keywordComments: keywordItem.leaf.word.comments = keyword := rewrite keywordWord
      let colonComments: colonItem.leaf.word.comments = colon := rewrite colonWord
      let colonEqComments: colonEqItem.leaf.word.comments = colonEq := rewrite colonEqWord
      (
        keywordItem,
        nameItem,
        colonItem,
        colonEqItem,
        typeRead,
        valueRead,
        isItems,
        (rewrite plainHeaderOf keywordItem nameItem colonItem result,
            keywordComments,
            nameWord,
            colonComments,
            colonEqComments),
        isDef,
        isLower,
        isColon,
        isColonEq,
        speltSlots result False typeRead resultWithin resultShaped resultLexical resultFree noRole typeFilled typeSpaced
            typeChained typeLead,
        speltSlots value False valueRead valueWithin valueShaped valueLexical valueFree noValueRole valueFilled
            valueSpaced valueChained valueLead,
        resultWithin,
        valueWithin
      )
    | [_], _, _, (_, never), _ => never.impossible
    | [_, _], _, _, (_, (_, never)), _ => never.impossible
    | [_, _, _, _, .._], _, _, (_, (_, (_, never))), _ => never.impossible

-- The printed declaration.

theorem textsOfTokens ∀ (first second: List Leaf)
    (same: tokens first = tokens second):
    tokenTexts first = tokenTexts second :=
  let firstTexts := List.mapMap first ((token: Token) => token.text) ((leaf: Leaf) => leaf.token)
  let secondTexts := List.mapMap second ((token: Token) => token.text) ((leaf: Leaf) => leaf.token)
  let alike: (tokens first).map (token => token.text) = (tokens second).map (token => token.text) := rewrite same
  rewrite <- firstTexts, <- secondTexts then alike

theorem kindedOfTokens ∀ (first second: List Leaf)
    (same: tokens first = tokens second)
    (kinded: second.all Leaf.kinded = True):
    first.all Leaf.kinded = True :=
  let firstKinds :=
    List.allMapBool first ((token: Token) => token.kind == lexKind token.text) ((leaf: Leaf) => leaf.token)
  let secondKinds :=
    List.allMapBool second ((token: Token) => token.kind == lexKind token.text) ((leaf: Leaf) => leaf.token)
  let alike: (tokens first).all (token => token.kind == lexKind token.text)
    = (tokens second).all (token => token.kind == lexKind token.text) :=
    rewrite same
  let alikeLeaves: first.all Leaf.kinded = second.all Leaf.kinded := rewrite <- firstKinds, <- secondKinds then alike
  rewrite alikeLeaves then kinded

theorem itemTexts ∀ (group: List Leaf): (items group).map Item.text = tokenTexts group :=
  let texts := List.mapMap (items group) ((leaf: Leaf) => leaf.token.text) Item.leaf
  rewrite itemsLeaves group at texts then texts.flipped

theorem itemsKinded ∀ (group: List Leaf)
    (kinded: group.all Leaf.kinded = True):
    (items group).all (item => item.leaf.token.kind == lexKind item.leaf.token.text) = True :=
  let kinds := List.allMapBool (items group) Leaf.kinded Item.leaf
  rewrite itemsLeaves group at kinds then rewrite <- kinds then kinded

--| A slice 1 definition's spelling, comments filtered out: `def`, its name, `:`, its type's code texts, `:=` and its
--| value's.
theorem declCodeTexts ∀ (keyword: Comments) (name: Word) (colon colonEq: Comments) (result value: Expr)
    (within: (plainDecl keyword name colon colonEq result value).within1 = True)
    (lexical: (plainDecl keyword name colon colonEq result value).lexical = True)
    (commented: (plainDecl keyword name colon colonEq result value).words.all Fmt.SpellProofs.Word.commented = True):
    (plainDecl keyword name colon colonEq result value).spelt.filter notComment
      = ["def", name.text, ":"] ++ result.codeTexts ++ [":=", ..value.codeTexts] :=
  let headerWithin: (name.nameWithin1 && result.within1) = True := Bool.andLeft within
  let valueWithin: value.within1 = True := Bool.andRight within
  let nameWithin: name.nameWithin1 = True := Bool.andLeft headerWithin
  let resultWithin: result.within1 = True := Bool.andRight headerWithin
  let resultLexical: result.lexical = True := Bool.andLeft (Bool.andRight lexical)
  let valueLexical: value.lexical = True := Bool.andRight (Bool.andRight lexical)
  let (keywordCommented, afterKeyword) :=
    List.allConsElim
      (fixedWord "def" keyword)
      ([name, fixedWord ":" colon] ++ result.words ++ [fixedWord ":=" colonEq] ++ value.words)
      Fmt.SpellProofs.Word.commented
      commented
  let (nameCommented, afterName) :=
    List.allConsElim name
      ([fixedWord ":" colon] ++ result.words ++ [fixedWord ":=" colonEq] ++ value.words)
      Fmt.SpellProofs.Word.commented
      afterKeyword
  let (colonCommented, afterColon) :=
    List.allConsElim
      (fixedWord ":" colon)
      (result.words ++ [fixedWord ":=" colonEq] ++ value.words)
      Fmt.SpellProofs.Word.commented
      afterName
  let (resultCommented, afterResult) :=
    allSplitBool result.words ([fixedWord ":=" colonEq] ++ value.words) Fmt.SpellProofs.Word.commented afterColon
  let (colonEqCommented, valueCommented) :=
    List.allConsElim (fixedWord ":=" colonEq) value.words Fmt.SpellProofs.Word.commented afterResult
  let nameClean: name.clean = True :=
    wordClean name
      (let (nameKind, nameSpelled, _, _) := nameKinded name nameWithin; spellsNotComment nameKind name.text nameSpelled)
      nameCommented
  rewrite List.filterAppend
        (((fixedWord "def" keyword).spelledAt True ++ name.spelledAt False)
          ++ (fixedWord ":" colon).spelledAt False
          ++ result.spelt False)
        ((fixedWord ":=" colonEq).spelledAt False ++ value.spelt False)
        notComment,
      List.filterAppend
        ((fixedWord "def" keyword).spelledAt True ++ name.spelledAt False)
        ((fixedWord ":" colon).spelledAt False ++ result.spelt False)
        notComment,
      List.filterAppend ((fixedWord "def" keyword).spelledAt True) (name.spelledAt False) notComment,
      List.filterAppend ((fixedWord ":" colon).spelledAt False) (result.spelt False) notComment,
      List.filterAppend ((fixedWord ":=" colonEq).spelledAt False) (value.spelt False) notComment,
      wordDropsComments (fixedWord "def" keyword) True (fixedClean "def" keyword byComputing keywordCommented),
      wordDropsComments name False nameClean,
      wordDropsComments (fixedWord ":" colon) False (fixedClean ":" colon byComputing colonCommented),
      codeTextsOf result False resultWithin (wordsClean result resultWithin resultLexical resultCommented),
      wordDropsComments (fixedWord ":=" colonEq) False (fixedClean ":=" colonEq byComputing colonEqCommented),
      codeTextsOf value False valueWithin (wordsClean value valueWithin valueLexical valueCommented)

--| `splitOfParts` for a declaration read as the plain definition of the parts.
theorem splitOfRead ∀ (group: List Leaf) (read: Decl) (keyword: Comments) (name: Word)
    (colon colonEq: Comments) (result value: Expr)
    (isRead: read = plainDecl keyword name colon colonEq result value)
    (resultTree: SlotTree result)
    (valueTree: SlotTree value)
    (lower: lexKind name.text = Lower ∨ lexKind name.text = Upper)
    (texts: (items group).map Item.text = ["def", name.text, ":"] ++ result.codeTexts ++ [":=", ..value.codeTexts])
    (kinded: (items group).all (item => item.leaf.token.kind == lexKind item.leaf.token.text) = True)
    (words: itemWords (items group)
      = [fixedWord "def" keyword, name, fixedWord ":" colon] ++ result.words ++ [fixedWord ":=" colonEq, ..value.words])
    (spacing: spacingAdmits ([Free, Free, Free] ++ result.spacing False ++ [Free] ++ value.spacing False) (items group)
      = True):
    ∃ (keywordItem nameItem colonItem colonEqItem: Item) (typeRead valueRead: List Item) (result value: Expr) =>
      GroupSplit group read keywordItem nameItem colonItem colonEqItem typeRead valueRead result value :=
  let (keywordItem, nameItem, colonItem, colonEqItem, typeRead, valueRead, split) :=
    splitOfParts group keyword name colon colonEq result value resultTree valueTree lower texts kinded words spacing
  (keywordItem, nameItem, colonItem, colonEqItem, typeRead, valueRead, result, value, (rewrite isRead then split))

--| `calmAt` of a plain definition is a plain definition, its keyword's comments topped or not.
def keywordAt (keyword: Comments) (top: Bool): Comments := if top then keyword.topped else keyword

theorem calmShape ∀ (keyword: Comments) (name: Word) (colon colonEq: Comments) (result value: Expr) (top: Bool):
    (plainDecl keyword name colon colonEq result value).calmAt top
      = plainDecl
        (keywordAt keyword top)
        (name.kept False False)
        (colon.kept False False)
        (colonEq.kept False False)
        (result.calm False)
        (value.calm False) :=
  match top with | True | False => byComputing

--| `printedSplit1` for a definition of slice 1's shape.
--|
--| Proof idea: `read` is the calmed definition (`calmAt`), whose parts have the printed parts' trees, code texts and
--| spacing (`withinCalm`, `shapedCalm`, `lexicalCalm`, `codeTextsCalm`, `spacingCalm`); the group's texts and kinds
--| are the printed leaves' (`printedTokens1`), its words `read`'s, and its spacing the printed one (`groupSpacing`),
--| which is what `splitOfParts` takes.
theorem lexKindOfNameLexes ∀ (name: Word)
    (lexes: (name.lexesAs Lower || name.lexesAs Upper) = True):
    lexKind name.text = Lower ∨ lexKind name.text = Upper :=
  match (Bool.orReads _ _).forward lexes with
    | Inl lower => Inl (lexKindOfLexes name.text Lower lower)
    | Inr upper => Inr (lexKindOfLexes name.text Upper upper)

theorem printedSplitParts ∀ (keyword: Comments) (name: Word) (colon colonEq: Comments) (result value: Expr)
    (read: Decl) (group: List Leaf)
    (printed: PrintedGroup (plainDecl keyword name colon colonEq result value) read group):
    ∃ (keywordItem nameItem colonItem colonEqItem: Item) (typeRead valueRead: List Item) (result value: Expr) =>
      GroupSplit group read keywordItem nameItem colonItem colonEqItem typeRead valueRead result value :=
  let decl := plainDecl keyword name colon colonEq result value
  let (within, shaped, settled, lexical, commaFree, _, sameTokens, words, calmed) := printed
  let (top, isRead) := calmed
  let calmKeyword := keywordAt keyword top
  let isCalm := Eq.trans isRead (calmShape keyword name colon colonEq result value top)
  let headerWithin: (name.nameWithin1 && result.within1) = True := Bool.andLeft within
  let valueWithin: value.within1 = True := Bool.andRight within
  let resultWithin: result.within1 = True := Bool.andRight headerWithin
  let nameLexes: (name.lexesAs Lower || name.lexesAs Upper) = True := Bool.andLeft lexical
  let resultLexical: result.lexical = True := Bool.andLeft (Bool.andRight lexical)
  let valueLexical: value.lexical = True := Bool.andRight (Bool.andRight lexical)
  let resultTree: SlotTree (result.calm False) := (
    withinCalm result False resultWithin,
    (rewrite shapedCalm result False resultWithin then Bool.andLeft shaped),
    (rewrite lexicalCalm result False resultWithin then resultLexical),
    (rewrite exprCalmCommaFree result False then Bool.andLeft commaFree)
  )
  let valueTree: SlotTree (value.calm False) := (
    withinCalm value False valueWithin,
    (rewrite shapedCalm value False valueWithin then Bool.andRight shaped),
    (rewrite lexicalCalm value False valueWithin then valueLexical),
    (rewrite exprCalmCommaFree value False then Bool.andRight commaFree)
  )
  let printedTokens := printedTokens1 decl within shaped settled lexical
  let commented: decl.words.all Fmt.SpellProofs.Word.commented = True := Bool.andRight (Bool.andRight settled)
  let texts: (items group).map Item.text
    = ["def", name.text, ":"] ++ (result.calm False).codeTexts ++ [":=", ..(value.calm False).codeTexts] :=
    rewrite itemTexts group,
        textsOfTokens group decl.leaves sameTokens,
        printedTokens.left,
        codeTextsCalm result False resultWithin,
        codeTextsCalm value False valueWithin then
      declCodeTexts keyword name colon colonEq result value within lexical commented
  let readWords: read.words
    = [fixedWord "def" calmKeyword, name.kept False False, fixedWord ":" (colon.kept False False)]
      ++ (result.calm False).words
      ++ [fixedWord ":=" (colonEq.kept False False), ..(value.calm False).words] :=
    rewrite isCalm
  let spacing := groupSpacing decl read group printed
  splitOfRead group read calmKeyword
    (name.kept False False)
    (colon.kept False False)
    (colonEq.kept False False)
    (result.calm False)
    (value.calm False)
    isCalm
    resultTree
    valueTree
    (lexKindOfNameLexes name nameLexes)
    texts
    (itemsKinded group (kindedOfTokens group decl.leaves sameTokens printedTokens.right))
    (rewrite itemWordsOfGroup group, words then readWords)
    (rewrite spacingCalm result False False resultWithin, spacingCalm value False False valueWithin then spacing)

--| A printed declaration's group splits into the items `Syntax.ReadBackHungTop.readsBackHung` reads, with `read`'s
--| type and value spelt by them.
--|
--| Proof idea: the declaration is slice 1's `def name: type := value` (`within1`), and `printedSplitParts` splits its
--| group. The group's tokens are the printed ones, their kinds the lexer's and their texts the rules' spelling
--| (`printedTokens1`), so its items fill the declaration's slots (`slotsFromTexts`); the printed spacing
--| (`printedSpacing1`) and the items' chaining give `speltSlots` what it needs. An infix's kind is the one its
--| operator's token reads as (`within1`: `arrowText1`, `binaryText1`).
theorem printedSplit1 ∀ (decl read: Decl) (group: List Leaf)
    (printed: PrintedGroup decl read group):
    ∃ (keyword name colon colonEq: Item) (typeRead valueRead: List Item) (result value: Expr) => GroupSplit group read
        keyword name colon colonEq typeRead valueRead result value :=
  match decl, printed with
    | Definition
        []
        {
          exportKeyword = None,
          opaqueKeyword = None,
          kind = DefPlain,
          keyword,
          name,
          forallKeyword = None,
          params = [],
          colon,
          result,
          decreasingClause = None,
          unfoldingClause = None
        }
        (Assigned colonEq value), printed =>
      printedSplitParts keyword name colon colonEq result value read group printed
    | Definition _ _ Primitive | Definition _ _ (Arms _) | _, (never, _) => (Bool.falseNotTrue never).impossible

theorem operatorNotCommentExample: "+".startsWith "--" = False := operatorNotComment "+" byComputing
