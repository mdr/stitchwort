--| Toward `printedSplit1` (SW-4077): `Spelt` of a slice 1 expression from items that match its tokens one by one.
--| `slots` lists an expression's tokens, a comma between a bracket's items; `SlotMatch` says an item carries a
--| slot's word, lexed as the lexer does, or is a comma. With the printed spacing and the items' chaining, that is all
--| `Spelt` reads (`speltSlots`).

namespace Fmt.SpeltSlots
import Std (Bool, DecEq, Eq, Finite, List, Nat, Option, Parse, Text, Void)
import Syntax (Expr, InfixKind, Item, Leaf, Tok, Token, Word, lex, negativeNumeral)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackRuns (commaReads)
import Fmt (..)
import Fmt.OperatorList (operators1, operatorListed)
import Fmt.OutputStatements (..)
import Fmt.TreeJoinProofs (lexKind)
import Fmt.SplitProofs (Chained)
import Fmt.PassProofs (..)
import Fmt.TouchProofs (spacingFree)

-- Slots.

--| An expression's tokens in order: `Some` word for each, `None` for the comma between a bracket's items.
def Expr.slots: Expr → List (Option Word)
  | Atom _ word => [Some word]
  | Paren open inner close => [Some open, ..inner.slots] ++ [Some close]
  | Tuple open items _ close | ListOf open items _ close => [Some open, ..commaSlots items] ++ [Some close]
  | App head arguments => head.slots ++ argumentSlots arguments
  | Infix _ left operator right => left.slots ++ [Some operator, ..right.slots]
  | Prefix operator operand => [Some operator, ..operand.slots]
  | _ => []

def commaSlots: List Expr → List (Option Word)
  | [] => []
  | [item] => item.slots
  | [item, ..rest] => item.slots ++ [None] ++ commaSlots rest

def argumentSlots: List Expr → List (Option Word)
  | [] => []
  | [argument, ..rest] => argument.slots ++ argumentSlots rest

--| An item fills a slot: it carries the slot's word, of the kind the lexer gives its text, or it is a comma.
def SlotMatch (item: Item) (slot: Option Word): Prop := match slot with
  | Some word => item.leaf.word = word ∧ item.kind = lexKind word.text
  | None => item.kind = Comma

--| Whether the first item comes after an operand exactly when the expression is a call's argument: what `items`
--| sets for an argument's sign after the call's head, and for any other expression's first token after an opener, a
--| comma, an operator or a sign.
def leadAfter: List Item → Bool → Bool
  | [first, .._], argument => first.afterOperand == argument
  | [], _ => True

-- Lexing.

--| A text that lexes as one token of a kind is of that kind to `lexKind`.
theorem lexKindOfLexes ∀ (text: Text) (kind: Tok) (lexes: textLexesAs text kind = True): lexKind text = kind :=
  match lex text, lexes with
    | Ok lexed, lexes =>
      match lexed.leaves, lexes with
        | [leaf], lexes => DecEq.sound (Bool.andRight lexes)
        | [], never => (Bool.falseNotTrue never).impossible
        | [leaf, next, ..rest], never => (Bool.falseNotTrue never).impossible
    | Err _, never => (Bool.falseNotTrue never).impossible

--| The kind of infix a text is the operator of, in slice 1.
def infixText (kind: InfixKind) (text: Text): Bool := match kind with
  | InfixArrow => arrowText1 text
  | InfixBinary => binaryText1 text
  | _ => False

--| What `Spelt` asks of an infix's operator item, from its text: the token `infixTok` takes and the level
--| `tokLevel` gives.
def InfixFacts (kind: InfixKind) (text: Text): Prop :=
  infixTok kind (lexKind text) = True ∧ infixLevel kind text = tokLevel (lexKind text)

theorem arrowFacts ∀ (text: Text) (arrow: arrowText1 text = True): InfixFacts InfixArrow text :=
  match a0: text == "->" with
    | True => rewrite DecEq.sound a0 then (byComputing, byComputing)
    | False =>
      match a1: text == "→" with
        | True => rewrite DecEq.sound a1 then (byComputing, byComputing)

def binaryOperatorFacts: List.All (text => arrowText1 text = False → InfixFacts InfixBinary text) operators1 := (
  same => (Bool.trueNotFalse same).impossible,
  same => (Bool.trueNotFalse same).impossible,
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  _ => (byComputing, byComputing),
  Trivial
)

theorem binaryFacts ∀ (text: Text) (binary: binaryText1 text = True): InfixFacts InfixBinary text :=
  let notArrow: arrowText1 text = False := Bool.notTrue (arrowText1 text) (Bool.andRight binary)
  List.allMem
    (x => arrowText1 x = False → InfixFacts InfixBinary x)
    text
    operators1
    binaryOperatorFacts
    (operatorListed text (Bool.andLeft binary))
    notArrow

--| The operator of an infix in slice 1 is the token `Spelt` asks for, at its level.
theorem infixFacts ∀ (kind: InfixKind) (text: Text) (fits: infixText kind text = True): InfixFacts kind text :=
  match kind with
    | InfixArrow => arrowFacts text fits
    | InfixBinary => binaryFacts text fits

--| A sign of slice 1 is a sign token, `-` exactly when it is a `Minus`.
def SignFacts (text: Text): Prop := signKind (lexKind text) = True ∧ (lexKind text = Minus → text = "-")

theorem prefixFacts ∀ (text: Text) (listed: prefixText1 text = True): SignFacts text := match minus: text == "-" with
  | True => rewrite DecEq.sound minus then (byComputing, same => byComputing)
  | False =>
    match bang: text == "!" with
      | True =>
        rewrite DecEq.sound bang then
          (byComputing, never => (DecEq.soundFalse (lexKind "!") Minus byComputing never).impossible)
      | False =>
        match not: text == "¬" with
          | True =>
            rewrite DecEq.sound not then
              (byComputing, never => (DecEq.soundFalse (lexKind "¬") Minus byComputing never).impossible)

-- Splitting the spacing and the chaining with the items.

--| Spacing that admits joined items admits each part, split where the items split.
theorem admitsSplit ∀ (front back: List Spacing) (first second: List Item)
    (long: first.length = front.length)
    (admits: spacingAdmits (front ++ back) (first ++ second) = True):
    spacingAdmits front first = True ∧ spacingAdmits back second = True :=
  match front, first, long with
    | [], [], _ => (byComputing, admits)
    | [spacing, ..rest], [item, ..later], long =>
      let (restAdmits, backAdmits) := admitsSplit rest back later second (Nat.succInjective long) (Bool.andRight admits)
      (Bool.andIntro (Bool.andLeft admits) restAdmits, backAdmits)
    | [], [item, ..later], long => (Nat.succNotZero later.length long).impossible
    | [spacing, ..rest], [], long => (Nat.succNotZero rest.length long.flipped).impossible

--| Chained joined items are chained in each part.
theorem chainedSplit ∀ (first second: List Item)
    (chained: Chained (first ++ second) = True):
    Chained first = True ∧ Chained second = True :=
  match first with
    | [] => (byComputing, chained)
    | [item] =>
      match second with
        | [] => (byComputing, byComputing)
        | [next, ..rest] => (byComputing, Bool.andRight chained)
    | [item, next, ..rest] =>
      let (restChained, secondChained) := chainedSplit [next, ..rest] second (Bool.andRight chained)
      (Bool.andIntro (Bool.andLeft chained) restChained, secondChained)

--| In chained items, the item after another comes after an operand exactly when that one closes one.
theorem chainedAfter ∀ (front: List Item) (item: Item) (rest: List Item)
    (chained: Chained (front ++ [item, ..rest]) = True):
    leadAfter rest item.kind.closesOperand = True :=
  match front with
    | [] =>
      match rest with
        | [] => byComputing
        | [next, ..later] => Bool.andLeft chained
    | [first, ..others] => chainedAfter others item rest (chainedSplit [first] (others ++ [item, ..rest]) chained).right

-- The spacing's shape.

theorem spacedFirstLength ∀ (spacing: Spacing) (inner: List Spacing):
    (spacedFirst spacing inner).length = inner.length :=
  match inner with | [] | [_, .._] => byComputing

--| An expression's spacing has a place for each of its slots.
theorem spacingLength ∀ (expr: Expr) (argument: Bool)
    (within: expr.within1 = True):
    (expr.spacing argument).length = expr.slots.length :=
  match expr, within with
    | Atom _ _, _ => byComputing
    | Paren open inner close, within =>
      rewrite List.lengthAppend [Free, ..inner.spacing False] [Free],
          List.lengthAppend [Some open, ..inner.slots] [Some close],
          spacingLength inner False within
    | Tuple open items _ close | ListOf open items _ close, within =>
      rewrite List.lengthAppend [Free, ..commaSpacing items] [Free],
          List.lengthAppend [Some open, ..commaSlots items] [Some close],
          commaSpacingLength items within
    | App head arguments, within =>
      rewrite List.lengthAppend (head.spacing False) (argumentsSpacing arguments),
          List.lengthAppend head.slots (argumentSlots arguments),
          spacingLength head False (Bool.andLeft within),
          argumentsSpacingLength arguments (Bool.andRight within)
    | Infix InfixBinary left operator right | Infix InfixArrow left operator right, within =>
      rewrite List.lengthAppend (left.spacing False) [Free, ..spacedFirst Apart (right.spacing False)],
          List.lengthAppend left.slots [Some operator, ..right.slots],
          spacingLength left False (Bool.andLeft within),
          spacedFirstLength Apart (right.spacing False),
          spacingLength right False (Bool.andLeft (Bool.andRight within))
    | Prefix operator operand, within =>
      match operandSpacing argument operator operand with
        | Some spacing =>
          rewrite spacedFirstLength spacing (operand.spacing False), spacingLength operand False (Bool.andLeft within)
        | None => rewrite spacingLength operand False (Bool.andLeft within)
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

theorem commaSpacingLength ∀ (items: List Expr)
    (within: allWithin1 items = True):
    (commaSpacing items).length = (commaSlots items).length :=
  match items with
    | [] => byComputing
    | [item] => spacingLength item False (Bool.andLeft within)
    | [item, next, ..rest] =>
      rewrite List.lengthAppend (item.spacing False) ([Free] ++ commaSpacing [next, ..rest]),
          List.lengthAppend item.slots ([None] ++ commaSlots [next, ..rest]),
          spacingLength item False (Bool.andLeft within),
          commaSpacingLength [next, ..rest] (Bool.andRight within)

theorem argumentsSpacingLength ∀ (arguments: List Expr)
    (within: allWithin1 arguments = True):
    (argumentsSpacing arguments).length = (argumentSlots arguments).length :=
  match arguments with
    | [] => byComputing
    | [argument, ..rest] =>
      rewrite List.lengthAppend (argument.spacing True) (argumentsSpacing rest),
          List.lengthAppend argument.slots (argumentSlots rest),
          spacingLength argument True (Bool.andLeft within),
          argumentsSpacingLength rest (Bool.andRight within)

--| Spacing whose first place is set over a free one admits what the free one does, and the first item fits the
--| set place.
theorem admitsSpacedFirst ∀ (spacing: Spacing) (rest: List Spacing) (read: List Item)
    (admits: spacingAdmits (spacedFirst spacing [Free, ..rest]) read = True):
    spacingAdmits [Free, ..rest] read = True ∧ firstAdmits spacing read = True :=
  match read with | [item, ..later] => (Bool.andIntro byComputing (Bool.andRight admits), Bool.andLeft admits)

--| The first item fits the spacing.
def firstAdmits (spacing: Spacing): List Item → Bool
  | [item, .._] => spacing.admits item.glued
  | [] => True

-- Reading slots off the items.

--| The items of one slot.
theorem slotOne ∀ (read: List Item) (word: Word)
    (slots: List.All2 SlotMatch read [Some word]):
    ∃ (item: Item) => read = [item] ∧ item.leaf.word = word ∧ item.kind = lexKind word.text :=
  match read, slots with
    | [item], ((sameWord, sameKind), _) => (item, byComputing, sameWord, sameKind)
    | [], never => Void.impossible never
    | [item, next, ..rest], (_, never) => Void.impossible never

--| The items of a bracket's slots: its opener, the inside, its closer.
def BracketRead (read: List Item) (open close: Word) (inside: List (Option Word)) (first: Item)
    (middle: List Item) (last: Item):
    Prop :=
  read = [first, ..middle ++ [last]]
    ∧ first.leaf.word = open
    ∧ first.kind = lexKind open.text
    ∧ List.All2 SlotMatch middle inside
    ∧ last.leaf.word = close
    ∧ last.kind = lexKind close.text

theorem bracketSlots ∀ (read: List Item) (open close: Word) (inside: List (Option Word))
    (slots: List.All2 SlotMatch read ([Some open, ..inside] ++ [Some close])):
    ∃ (first: Item) (middle: List Item) (last: Item) => BracketRead read open close inside first middle last :=
  let (front, back, isRead, frontSlots, backSlots) :=
    List.all2AppendSplit SlotMatch read [Some open, ..inside] [Some close] slots
  let (last, isBack, lastWord, lastKind) := slotOne back close backSlots
  match front, frontSlots with
    | [first, ..middle], ((firstWord, firstKind), middleSlots) =>
      (first, middle, last, (rewrite isRead, isBack), firstWord, firstKind, middleSlots, lastWord, lastKind)

--| A token of a name or numeral closes an operand.
theorem wordCloses ∀ (kind: Tok) (within: kind.wordWithin1 = True): kind.closesOperand = True := match kind, within with
  | Lower | Upper | Num | Float, _ => byComputing
  | other, never => (Bool.falseNotTrue never).impossible

--| The last item closes an operand.
def EndsClosed (read: List Item): Prop :=
  ∃ (front: List Item) (last: Item) => read = front ++ [last] ∧ last.kind.closesOperand = True

theorem readCloserEnds ∀ (read: List Item) (open close: Word) (inside: List (Option Word)) (first: Item)
    (middle: List Item) (last: Item)
    (bracket: BracketRead read open close inside first middle last)
    (closer: lexKind close.text = RParen ∨ lexKind close.text = RBracket):
    EndsClosed read :=
  let (isRead, _, _, _, _, lastKind) := bracket
  match closer with | Inl paren | Inr paren => ([first, ..middle], last, (rewrite isRead), (rewrite lastKind, paren))

theorem parenLexCloser ∀ (close: Word)
    (is: (close.text == ")") = True):
    lexKind close.text = RParen ∨ lexKind close.text = RBracket :=
  Inl (rewrite DecEq.sound is)

theorem bracketLexCloser ∀ (close: Word)
    (is: (close.text == "]") = True):
    lexKind close.text = RParen ∨ lexKind close.text = RBracket :=
  Inr (rewrite DecEq.sound is)

--| A slice 1 expression's items end with one that closes an operand: a name, a numeral or a closer.
--|
--| Proof idea: by induction on the expression; the last slot is an atom's word, a bracket's closer, or the last of a
--| call's last argument, an infix's right operand or a sign's operand.
theorem lastCloses ∀ (expr: Expr) (read: List Item)
    (within: expr.within1 = True)
    (shaped: expr.shaped = True)
    (lexical: expr.lexical = True)
    (slots: List.All2 SlotMatch read expr.slots):
    EndsClosed read :=
  match expr, within with
    | Atom kind word, within =>
      let (item, isRead, _, itemKind) := slotOne read word slots
      (
        [],
        item,
        isRead,
        rewrite itemKind, lexKindOfLexes word.text kind lexical then wordCloses kind (Bool.andLeft within)
      )
    | Paren open inner close, within =>
      let (first, middle, last, bracket) := bracketSlots read open close inner.slots slots
      readCloserEnds read open close inner.slots first middle last bracket
        (parenLexCloser close (Bool.andLeft (Bool.andRight lexical)))
    | Tuple open items _ close, within =>
      let (first, middle, last, bracket) := bracketSlots read open close (commaSlots items) slots
      readCloserEnds read open close
        (commaSlots items)
        first
        middle
        last
        bracket
        (parenLexCloser close (Bool.andLeft (Bool.andRight lexical)))
    | ListOf open items _ close, within =>
      let (first, middle, last, bracket) := bracketSlots read open close (commaSlots items) slots
      readCloserEnds read open close
        (commaSlots items)
        first
        middle
        last
        bracket
        (bracketLexCloser close (Bool.andLeft (Bool.andRight lexical)))
    | App head arguments, within =>
      let (headRead, argsRead, isRead, _, argsSlots) :=
        List.all2AppendSplit SlotMatch read head.slots (argumentSlots arguments) slots
      let (front, last, isArgs, closes) :=
        argumentsLast arguments argsRead
          (Bool.andLeft (Bool.andRight (Bool.andRight shaped)))
          (Bool.andRight within)
          (Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight shaped))))
          (Bool.andRight lexical)
          argsSlots
      (headRead ++ front, last, (rewrite isRead, isArgs, List.appendAssoc headRead front [last]), closes)
    | Infix InfixBinary left operator right, within =>
      infixLast InfixBinary left operator right read
        (Bool.andLeft (Bool.andRight within))
        (Bool.andLeft (Bool.andRight shaped))
        (Bool.andRight (Bool.andRight lexical))
        slots
    | Infix InfixArrow left operator right, within =>
      infixLast InfixArrow left operator right read
        (Bool.andLeft (Bool.andRight within))
        (Bool.andLeft (Bool.andRight shaped))
        (Bool.andRight (Bool.andRight lexical))
        slots
    | Prefix operator operand, within =>
      match read, slots with
        | [sign, ..more], (_, moreSlots) =>
          let (front, last, isMore, closes) :=
            lastCloses operand more (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andRight lexical) moreSlots
          ([sign, ..front], last, (rewrite isMore), closes)
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible

theorem infixLast ∀ (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr) (read: List Item)
    (within: right.within1 = True)
    (shaped: right.shaped = True)
    (lexical: right.lexical = True)
    (slots: List.All2 SlotMatch read (Infix kind left operator right).slots):
    EndsClosed read :=
  let (leftRead, rest, isRead, _, restSlots) :=
    List.all2AppendSplit SlotMatch read left.slots [Some operator, ..right.slots] slots
  match rest, restSlots with
    | [op, ..rightRead], (_, rightSlots) =>
      let (front, last, isRight, closes) := lastCloses right rightRead within shaped lexical rightSlots
      (
        leftRead ++ [op, ..front],
        last,
        (rewrite isRead, isRight, List.appendAssoc leftRead [op, ..front] [last]),
        closes
      )

theorem argumentsLast ∀ (arguments: List Expr) (read: List Item)
    (some: (!arguments.isEmpty) = True)
    (within: allWithin1 arguments = True)
    (shaped: allShaped arguments = True)
    (lexical: allLexical arguments = True)
    (slots: List.All2 SlotMatch read (argumentSlots arguments)):
    EndsClosed read :=
  match arguments with
    | [argument, ..rest] =>
      let (first, second, isRead, firstSlots, secondSlots) :=
        List.all2AppendSplit SlotMatch read argument.slots (argumentSlots rest) slots
      match rest, second, secondSlots with
        | [], [], _ =>
          let (front, last, isFirst, closes) :=
            lastCloses argument first (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft lexical) firstSlots
          (front, last, (rewrite isRead, isFirst, List.appendNil (front ++ [last])), closes)
        | [next, ..others], second, secondSlots =>
          let (front, last, isSecond, closes) :=
            argumentsLast
              [next, ..others]
              second
              byComputing
              (Bool.andRight within)
              (Bool.andRight shaped)
              (Bool.andRight lexical)
              secondSlots
          (first ++ front, last, (rewrite isRead, isSecond, List.appendAssoc first front [last]), closes)

-- Tokens.

theorem tokLevelLow ∀ (tok: Tok): (18 <= tokLevel tok) = False :=
  let checked := Finite.check (kind => !(18 <= tokLevel kind)) byComputing tok
  Bool.notTrue (18 <= tokLevel tok) checked

--| An infix's operator closes no operand.
theorem infixOpens ∀ (kind: InfixKind) (tok: Tok) (is: infixTok kind tok = True): tok.closesOperand = False :=
  match kind, is with
    | InfixArrow, is => rewrite DecEq.sound is
    | InfixBinary, is =>
      match tok, is with
        | Star |
            Slash |
            Percent |
            Plus |
            Minus |
            PlusPlus |
            Equals |
            EqEq |
            NotEq |
            Lt |
            Le |
            Gt |
            Ge |
            AndAnd |
            OrOr, _ => byComputing
        | other, never => (Bool.falseNotTrue never).impossible
    | other, never => (Bool.falseNotTrue never).impossible

--| A sign closes no operand, and is no numeral.
theorem signOpens ∀ (tok: Tok)
    (sign: signKind tok = True):
    tok.closesOperand = False ∧ (tok == Num || tok == Float) = False :=
  match tok, sign with
    | Minus | Bang, _ => (byComputing, byComputing)
    | other, never => (Bool.falseNotTrue never).impossible

--| A name or numeral is no sign.
theorem wordNoSign ∀ (kind: Tok) (within: kind.wordWithin1 = True): signKind kind = False := match kind, within with
  | Lower | Upper | Num | Float, _ => byComputing
  | other, never => (Bool.falseNotTrue never).impossible

-- The first token.

--| The kind of an expression's first token.
def Expr.firstKind: Expr → Tok
  | Atom kind _ => kind
  | Paren _ _ _ | Tuple _ _ _ _ => LParen
  | ListOf _ _ _ _ => LBracket
  | App head _ | Infix _ head _ _ => head.firstKind
  | Prefix operator _ => lexKind operator.text
  | _ => Lower

--| The first item is of the kind.
def firstKindIs: List Item → Tok → Bool
  | [first, .._], kind => first.kind == kind
  | [], _ => True

theorem slotsSome ∀ (expr: Expr)
    (within: expr.within1 = True):
    ∃ (slot: Option Word) (rest: List (Option Word)) => expr.slots = [slot, ..rest] :=
  match expr, within with
    | Atom _ word, _ => (Some word, [], byComputing)
    | Paren open inner close, _ => (Some open, inner.slots ++ [Some close], byComputing)
    | Tuple open items _ close | ListOf open items _ close, _ =>
      (Some open, commaSlots items ++ [Some close], byComputing)
    | App head arguments, within =>
      let (slot, rest, starts) := slotsSome head (Bool.andLeft within)
      (slot, rest ++ argumentSlots arguments, rewrite starts)
    | Infix InfixBinary left operator right | Infix InfixArrow left operator right, within =>
      let (slot, rest, starts) := slotsSome left (Bool.andLeft within)
      (slot, rest ++ [Some operator, ..right.slots], rewrite starts)
    | Prefix operator operand, _ => (Some operator, operand.slots, byComputing)
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

--| The first of joined items is the first of the front part when that has items.
theorem frontFirst ∀ (front back: List Item) (slots: List (Option Word)) (slot: Option Word) (rest: List (Option Word))
    (starts: slots = [slot, ..rest])
    (matched: List.All2 SlotMatch front slots) (kind: Tok)
    (first: firstKindIs front kind = True):
    firstKindIs (front ++ back) kind = True :=
  match front, slots, matched with
    | [item, ..later], _, _ => first
    | [], [], _ => (List.nilNotCons slot rest starts).impossible

--| An expression's first item is of the kind of its first token.
theorem firstKindOf ∀ (expr: Expr) (read: List Item)
    (within: expr.within1 = True)
    (lexical: expr.lexical = True)
    (slots: List.All2 SlotMatch read expr.slots):
    firstKindIs read expr.firstKind = True :=
  match expr, within with
    | Atom kind word, _ =>
      let (item, isRead, _, itemKind) := slotOne read word slots
      rewrite isRead, itemKind, lexKindOfLexes word.text kind lexical then DecEq.refl kind
    | Paren open inner close, _ =>
      let (first, middle, last, (isRead, _, firstKind, _, _, _)) := bracketSlots read open close inner.slots slots
      rewrite isRead, firstKind, DecEq.sound (Bool.andLeft lexical)
    | Tuple open items _ close | ListOf open items _ close, _ =>
      let (first, middle, last, (isRead, _, firstKind, _, _, _)) :=
        bracketSlots read open close (commaSlots items) slots
      rewrite isRead, firstKind, DecEq.sound (Bool.andLeft lexical)
    | App head arguments, within =>
      let (headRead, argsRead, isRead, headSlots, _) :=
        List.all2AppendSplit SlotMatch read head.slots (argumentSlots arguments) slots
      let (slot, rest, starts) := slotsSome head (Bool.andLeft within)
      rewrite isRead then
        frontFirst headRead argsRead head.slots slot rest starts headSlots head.firstKind
          (firstKindOf head headRead (Bool.andLeft within) (Bool.andLeft lexical) headSlots)
    | Infix InfixBinary left operator right | Infix InfixArrow left operator right, within =>
      let (leftRead, rightRead, isRead, leftSlots, _) :=
        List.all2AppendSplit SlotMatch read left.slots [Some operator, ..right.slots] slots
      let (slot, rest, starts) := slotsSome left (Bool.andLeft within)
      rewrite isRead then
        frontFirst leftRead rightRead left.slots slot rest starts leftSlots left.firstKind
          (firstKindOf left leftRead (Bool.andLeft within) (Bool.andLeft lexical) leftSlots)
    | Prefix operator operand, _ =>
      match read, slots with
        | [sign, ..more], ((_, signKindIs), _) => rewrite signKindIs then DecEq.refl (lexKind operator.text)
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible

def isNumber (tok: Tok): Bool := tok == Num || tok == Float

--| A slice 1 expression outside an infix that starts with a numeral is one, or a call of one.
theorem numberLead ∀ (expr: Expr)
    (within: expr.within1 = True)
    (shaped: expr.shaped = True)
    (unary: expr.unary = True)
    (number: isNumber expr.firstKind = True):
    expr.numeral1 = True ∨ expr.numeralApplication = True :=
  match expr, within, number with
    | Atom Num _ | Atom Float _, _, _ => Inl byComputing
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _, _, never => (Bool.falseNotTrue never).impossible
    | Prefix operator _, within, number =>
      let notNumber := (signOpens (lexKind operator.text) (prefixFacts operator.text (Bool.andRight within)).left).right
      (Bool.falseNotTrue (rewrite notNumber at number then number)).impossible
    | App head arguments, within, number =>
      match head, Bool.andLeft shaped, number with
        | Atom Num _, _, _ => Inr byComputing
        | Atom Float _, _, _ => Inr byComputing
        | Atom other _, _, never => (Bool.falseNotTrue never).impossible
        | Paren _ _ _, _, never => (Bool.falseNotTrue never).impossible
        | Tuple _ _ _ _, _, never => (Bool.falseNotTrue never).impossible
        | ListOf _ _ _ _, _, never => (Bool.falseNotTrue never).impossible
        | Prefix operator _, head, number =>
          (Bool.falseNotTrue (rewrite DecEq.sound (Bool.andLeft head) at number then number)).impossible

--| An operand at a sign's level is no infix.
theorem unaryOfLevel ∀ (expr: Expr)
    (within: expr.within1 = True)
    (high: (18 <= expr.level) = True):
    expr.unary = True :=
  match expr, within with
    | Infix InfixBinary left operator right, within =>
      let (_, level) := infixFacts InfixBinary operator.text (Bool.andRight (Bool.andRight within))
      (Bool.falseNotTrue (rewrite level, tokLevelLow (lexKind operator.text) at high then high)).impossible
    | Infix InfixArrow _ _ _, _ => (Bool.falseNotTrue high).impossible
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ | Prefix _ _, _ => byComputing
    | Infix _ _ _ _ | _, never => (Bool.falseNotTrue never).impossible

--| An atom or bracket starts with no sign, and is no numeral's call.
theorem atomicFacts ∀ (expr: Expr)
    (within: expr.within1 = True)
    (atomic: expr.primary = True):
    signKind expr.firstKind = False ∧ expr.numeralApplication = False :=
  match expr, atomic with
    | Atom kind _, _ => (wordNoSign kind (Bool.andLeft within), byComputing)
    | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _, _ => (byComputing, byComputing)
    | other, never => (Bool.falseNotTrue never).impossible

-- Pieces of the induction.

theorem leadFront ∀ (front back: List Item) (argument: Bool)
    (lead: leadAfter (front ++ back) argument = True):
    leadAfter front argument = True :=
  match front with
    | [] => byComputing
    | [first, ..rest] => lead

theorem apartOperand ∀ (read: List Item) (apart: firstAdmits Apart read = True): operandApart read = True :=
  match read with
    | [] => byComputing
    | [first, ..rest] => apart

--| Items matching an expression's slots are as many as its spacing's places.
theorem lengthOf ∀ (expr: Expr) (argument: Bool) (read: List Item)
    (within: expr.within1 = True)
    (slots: List.All2 SlotMatch read expr.slots):
    read.length = (expr.spacing argument).length :=
  Eq.trans (List.all2Length SlotMatch read expr.slots slots) (spacingLength expr argument within).flipped

theorem noRole ∀ (expr: Expr) (never: False = True): expr.callArgument = True := (Bool.falseNotTrue never).impossible

--| A bracket's inside: spaced, chained and led as an expression outside a call's arguments.
theorem bracketInner ∀ (read: List Item) (open close: Word) (inside: List (Option Word)) (first: Item)
    (middle: List Item) (last: Item) (spacingInside: List Spacing)
    (bracket: BracketRead read open close inside first middle last)
    (long: inside.length = spacingInside.length)
    (spacing: spacingAdmits ([Free, ..spacingInside] ++ [Free]) read = True)
    (chained: Chained read = True)
    (opens: (lexKind open.text).closesOperand = False):
    spacingAdmits spacingInside middle = True ∧ Chained middle = True ∧ leadAfter middle False = True :=
  let (isRead, _, firstKind, middleSlots, _, _) := bracket
  let readAdmits: spacingAdmits ([Free, ..spacingInside] ++ [Free]) [first, ..middle ++ [last]] = True :=
    rewrite isRead at spacing then spacing
  let readChained: Chained [first, ..middle ++ [last]] = True := rewrite isRead at chained then chained
  let afterFirst := chainedAfter [] first (middle ++ [last]) readChained
  let firstOpens: first.kind.closesOperand = False := rewrite firstKind then opens
  (
    (admitsSplit spacingInside
      [Free]
      middle
      [last]
      (Eq.trans (List.all2Length SlotMatch middle inside middleSlots) long)
      (Bool.andRight readAdmits)).left,
    (chainedSplit middle [last] (chainedSplit [first] (middle ++ [last]) readChained).right).left,
    leadFront middle [last] False (rewrite firstOpens at afterFirst then afterFirst)
  )

--| A sign read with a numeral glued after it is a sign on a numeral: an operand that starts with one is the numeral
--| itself or a call of it, and before a call of one the sign is spaced apart.
theorem signNumeral ∀ (operator: Word) (operand: Expr) (argument: Bool) (sign: Item) (more: List Item)
    (within: operand.within1 = True)
    (shaped: operand.shaped = True)
    (lexical: operand.lexical = True)
    (unary: operand.unary = True)
    (minusText: lexKind operator.text = Minus → operator.text = "-")
    (signKindIs: sign.kind = lexKind operator.text)
    (moreSlots: List.All2 SlotMatch more operand.slots)
    (firstFits: ∀ (spacing: Spacing) => operandSpacing argument operator operand = Some spacing
      → firstAdmits spacing more = True)
    (negative: negativeNumeral [sign, ..more] = True):
    operand.numeral1 = True :=
  match more, moreSlots, negative with
    | [number, ..later], moreSlots, negative =>
      let isMinus: sign.kind = Minus := DecEq.sound (Bool.andLeft negative)
      let text: operator.text = "-" := minusText (rewrite <- signKindIs then isMinus)
      let isNum: (number.kind == Num || number.kind == Float) = True := Bool.andLeft (Bool.andRight negative)
      let glued: number.glued = True := Bool.andLeft (Bool.andRight (Bool.andRight negative))
      let firstIs: number.kind = operand.firstKind :=
        DecEq.sound (firstKindOf operand [number, ..later] within lexical moreSlots)
      let starts: isNumber operand.firstKind = True := rewrite firstIs at isNum then isNum
      match numberLead operand within shaped unary starts with
        | Inl numeral => numeral
        | Inr call =>
          let apart: operandSpacing argument operator operand = Some Apart := rewrite text, call
          let notGlued: (!number.glued) = True := firstFits Apart apart
          (Bool.falseNotTrue (rewrite glued at notGlued then notGlued)).impossible
    | [], _, never => (Bool.falseNotTrue never).impossible

--| A call's argument glues as `argumentGlue` reads it: an atom or bracket starts with no sign, and a sign on one is
--| apart from the head before it, after an operand, and glued to what it signs.
theorem argumentFitsOf ∀ (argument: Expr) (read: List Item)
    (within: argument.within1 = True)
    (lexical: argument.lexical = True)
    (isArgument: argument.callArgument = True)
    (slots: List.All2 SlotMatch read argument.slots)
    (spacing: spacingAdmits (argument.spacing True) read = True)
    (lead: leadAfter read True = True):
    argumentFits argument read = True :=
  match argument with
    | Prefix operator operand =>
      let atomic: operand.primary = True := Bool.andLeft isArgument
      let quiet: signQuiet operator operand = True := Bool.andRight isArgument
      let (_, noCall) := atomicFacts operand (Bool.andLeft within) atomic
      let glued: operandSpacing True operator operand = Some Glued := match minus: operator.text == "-" with
        | True => rewrite noCall, quiet
        | False => rewrite quiet
      match read, slots with
        | [sign, ..more], (_, moreSlots) =>
          let (rest, starts) := spacingFree operand (Bool.andLeft within)
          let signSpaced: spacingAdmits [Apart, ..spacedFirst Glued (operand.spacing False)] [sign, ..more] = True :=
            rewrite glued at spacing then spacing
          let tail: spacingAdmits (spacedFirst Glued [Free, ..rest]) more = True :=
            rewrite starts at signSpaced then Bool.andRight signSpaced
          let (_, nextGlued) := admitsSpacedFirst Glued rest more tail
          let apart: (!sign.glued) = True := Bool.andLeft signSpaced
          let after: sign.afterOperand = True := DecEq.sound lead
          match more, nextGlued with
            | [next, ..later], nextGlued =>
              Bool.andIntro atomic (Bool.orRight (rewrite after, Bool.notTrue sign.glued apart, nextGlued))
    | Atom kind word => Bool.andIntro isArgument (atomicGlue (Atom kind word) read within lexical isArgument slots)
    | Paren open inner close =>
      Bool.andIntro isArgument (atomicGlue (Paren open inner close) read within lexical isArgument slots)
    | Tuple open items comma close =>
      Bool.andIntro isArgument (atomicGlue (Tuple open items comma close) read within lexical isArgument slots)
    | ListOf open items comma close =>
      Bool.andIntro isArgument (atomicGlue (ListOf open items comma close) read within lexical isArgument slots)

theorem atomicGlue ∀ (argument: Expr) (read: List Item)
    (within: argument.within1 = True)
    (lexical: argument.lexical = True)
    (atomic: argument.primary = True)
    (slots: List.All2 SlotMatch read argument.slots):
    argumentGlue read = True :=
  match read with
    | [first, next, ..rest] =>
      let firstIs: first.kind = argument.firstKind :=
        DecEq.sound (firstKindOf argument [first, next, ..rest] within lexical slots)
      rewrite firstIs, (atomicFacts argument within atomic).left
    | [_] | [] => byComputing

--| A call's head is read as `headFits` asks: an atom or bracket, or `-` glued to a numeral, which the parser reads
--| as a negative numeral since nothing before it closes an operand.
theorem headFitsOf ∀ (head: Expr) (read: List Item)
    (within: head.within1 = True)
    (lexical: head.lexical = True)
    (fits: head.callHead = True)
    (slots: List.All2 SlotMatch read head.slots)
    (spacing: spacingAdmits (head.spacing False) read = True)
    (lead: leadAfter read False = True):
    headFits head read = True :=
  match head with
    | Prefix operator operand =>
      let number: operand.numberAtom = True := Bool.andLeft (Bool.andRight fits)
      match operand, number with
        | Atom Num word, _ =>
          negativeHead operator Num word read byComputing byComputing (Bool.andRight lexical) fits slots spacing lead
        | Atom Float word, _ =>
          negativeHead operator Float word read byComputing byComputing (Bool.andRight lexical) fits slots spacing lead
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ => Bool.orLeft fits

theorem negativeHead ∀ (operator: Word) (kind: Tok) (word: Word) (read: List Item)
    (isNumber: (kind == Num || kind == Float) = True)
    (numeral: (Atom kind word).numeral1 = True)
    (lexical: word.lexesAs kind = True)
    (fits: (Prefix operator (Atom kind word)).callHead = True)
    (slots: List.All2 SlotMatch read [Some operator, Some word])
    (spacing: spacingAdmits ((Prefix operator (Atom kind word)).spacing False) read = True)
    (lead: leadAfter read False = True):
    headFits (Prefix operator (Atom kind word)) read = True :=
  let minus: operator.text = "-" := DecEq.sound (Bool.andLeft fits)
  let quiet: signQuiet operator (Atom kind word) = True := Bool.andRight (Bool.andRight fits)
  let glued: operandSpacing False operator (Atom kind word) = Some Glued := rewrite minus, quiet, numeral
  match read, slots with
    | [sign, number], ((_, signKindIs), ((_, numberKindIs), _)) =>
      let spaced: spacingAdmits [Free, Glued] [sign, number] = True := rewrite glued at spacing then spacing
      let numberGlued: number.glued = True := match g: number.glued with
        | True => byComputing
      let after: sign.afterOperand = False := DecEq.sound lead
      rewrite signKindIs, minus, numberKindIs, lexKindOfLexes word.text kind lexical, isNumber, numberGlued, after
    | [], never => Void.impossible never
    | [sign], (_, never) => Void.impossible never
    | [sign, number, next, ..rest], (_, (_, never)) => Void.impossible never

-- The induction.

--| A slice 1 expression is `Spelt` by items that fill its slots, spaced as the printer spaces it, chained as `items`
--| chains them, with the first after an operand exactly when the expression is a call's argument.
--|
--| Proof idea: by induction on the expression, its brackets' items and its call's arguments. The items split with
--| the slots (`List.all2AppendSplit`), and the spacing and chaining with them (`admitsSplit`, `chainedSplit`); each token's kind
--| is the lexer's for its text (`lexKindOfLexes`, `infixFacts`, `prefixFacts`). A part after an opener, a comma, an
--| operator or a sign comes after no operand (`chainedAfter`); an argument comes after its call's head or the argument
--| before it, which end with a closing token (`lastCloses`). The glue `Spelt` reads comes from the spacing:
--| `headFitsOf`, `argumentFitsOf`, an infix's right operand set apart, and a sign before a numeral's call set apart
--| (`signNumeral`).
theorem speltSlots ∀ (expr: Expr) (argument: Bool) (read: List Item)
    (within: expr.within1 = True)
    (shaped: expr.shaped = True)
    (lexical: expr.lexical = True)
    (free: expr.commaFree = True)
    (role: argument = True → expr.callArgument = True)
    (slots: List.All2 SlotMatch read expr.slots)
    (spacing: spacingAdmits (expr.spacing argument) read = True)
    (chained: Chained read = True)
    (lead: leadAfter read argument = True):
    Spelt expr read :=
  match expr, within with
    | Atom kind word, within =>
      let (item, isRead, itemWord, itemKind) := slotOne read word slots
      (item, isRead, (rewrite itemKind then lexKindOfLexes word.text kind lexical), itemWord, Bool.andLeft within)
    | Paren open inner close, within =>
      let (first, middle, last, bracket) := bracketSlots read open close inner.slots slots
      let (isRead, firstWord, firstKind, middleSlots, lastWord, lastKind) := bracket
      let opener: (open.text == "(") = True := Bool.andLeft lexical
      let closer: (close.text == ")") = True := Bool.andLeft (Bool.andRight lexical)
      let (innerAdmits, innerChained, innerLead) :=
        bracketInner read open close inner.slots first middle last
          (inner.spacing False)
          bracket
          (spacingLength inner False within).flipped
          spacing
          chained
          (rewrite DecEq.sound opener)
      (
        first,
        middle,
        last,
        isRead,
        (rewrite firstKind, DecEq.sound opener),
        firstWord,
        (rewrite lastKind, DecEq.sound closer),
        lastWord,
        speltSlots inner False middle within shaped
          (Bool.andRight (Bool.andRight lexical))
          free
          (noRole inner)
          middleSlots
          innerAdmits
          innerChained
          innerLead
      )
    | Tuple open items comma close, within =>
      let (first, middle, last, bracket) := bracketSlots read open close (commaSlots items) slots
      let (isRead, firstWord, firstKind, middleSlots, lastWord, lastKind) := bracket
      let opener: (open.text == "(") = True := Bool.andLeft lexical
      let closer: (close.text == ")") = True := Bool.andLeft (Bool.andRight lexical)
      let (innerAdmits, innerChained, innerLead) :=
        bracketInner read open close
          (commaSlots items)
          first
          middle
          last
          (commaSpacing items)
          bracket
          (commaSpacingLength items within).flipped
          spacing
          chained
          (rewrite DecEq.sound opener)
      let commas :=
        speltCommas items middle within
          (Bool.andRight shaped)
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andRight free)
          middleSlots
          innerAdmits
          innerChained
          innerLead
      let two: (items.length >= 2) = True := Bool.andLeft shaped
      match items, two, commas with
        | [one, second, ..others], _, (
            oneRead,
            steps,
            isMiddle,
            oneSpelt,
            (separator, secondRead, later, isSteps, isSeparator, secondSpelt, othersSpelt)
          ) => (
          first,
          oneRead,
          separator,
          secondRead,
          later,
          last,
          (rewrite isRead,
              isMiddle,
              isSteps,
              List.appendAssoc oneRead [separator, ..secondRead ++ commaReads later] [last],
              List.appendAssoc secondRead (commaReads later) [last]),
          Bool.notTrue comma (Bool.andLeft free),
          (rewrite firstKind, DecEq.sound opener),
          firstWord,
          isSeparator,
          (rewrite lastKind, DecEq.sound closer),
          lastWord,
          oneSpelt,
          secondSpelt,
          othersSpelt
        )
    | ListOf open items comma close, within =>
      let (first, middle, last, bracket) := bracketSlots read open close (commaSlots items) slots
      let (isRead, firstWord, firstKind, middleSlots, lastWord, lastKind) := bracket
      let opener: (open.text == "[") = True := Bool.andLeft lexical
      let closer: (close.text == "]") = True := Bool.andLeft (Bool.andRight lexical)
      let (innerAdmits, innerChained, innerLead) :=
        bracketInner read open close
          (commaSlots items)
          first
          middle
          last
          (commaSpacing items)
          bracket
          (commaSpacingLength items within).flipped
          spacing
          chained
          (rewrite DecEq.sound opener)
      let commas :=
        speltCommas items middle within shaped
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andRight free)
          middleSlots
          innerAdmits
          innerChained
          innerLead
      match items, commas with
        | [], isMiddle => (
          first,
          last,
          (rewrite isRead, isMiddle),
          Bool.notTrue comma (Bool.andLeft free),
          (rewrite firstKind, DecEq.sound opener),
          firstWord,
          (rewrite lastKind, DecEq.sound closer),
          lastWord
        )
        | [one, ..others], (oneRead, steps, isMiddle, oneSpelt, othersSpelt) => (
          first,
          oneRead,
          steps,
          last,
          (rewrite isRead, isMiddle, List.appendAssoc oneRead (commaReads steps) [last]),
          Bool.notTrue comma (Bool.andLeft free),
          (rewrite firstKind, DecEq.sound opener),
          firstWord,
          (rewrite lastKind, DecEq.sound closer),
          lastWord,
          oneSpelt,
          othersSpelt
        )
    | App head arguments, within =>
      match argument, role with
        | True, role => (Bool.falseNotTrue (role byComputing)).impossible
        | False, _ => speltApp head arguments read within shaped lexical free slots spacing chained lead
    | Infix InfixBinary left operator right, within =>
      match argument, role with
        | False, _ =>
          speltInfix InfixBinary left operator right read
            (Bool.andLeft within)
            (Bool.andLeft (Bool.andRight within))
            (Bool.andRight (Bool.andRight within))
            shaped
            lexical
            free
            slots
            spacing
            chained
            lead
        | True, role => (Bool.falseNotTrue (role byComputing)).impossible
    | Infix InfixArrow left operator right, within =>
      match argument, role with
        | False, _ =>
          speltInfix InfixArrow left operator right read
            (Bool.andLeft within)
            (Bool.andLeft (Bool.andRight within))
            (Bool.andRight (Bool.andRight within))
            shaped
            lexical
            free
            slots
            spacing
            chained
            lead
        | True, role => (Bool.falseNotTrue (role byComputing)).impossible
    | Prefix operator operand, within =>
      match read, slots with
        | [sign, ..more], ((signWord, signKindIs), moreSlots) =>
          let (isSign, minusText) := prefixFacts operator.text (Bool.andRight within)
          let signIs: signKind sign.kind = True := rewrite signKindIs then isSign
          let operandWithin: operand.within1 = True := Bool.andLeft within
          let operandLexical: operand.lexical = True := Bool.andRight lexical
          let unary := unaryOfLevel operand operandWithin (Bool.andRight shaped)
          let (rest, starts) := spacingFree operand operandWithin
          let moreChained := (chainedSplit [sign] more chained).right
          let afterSign := chainedAfter [] sign more chained
          let moreLead: leadAfter more False = True :=
            rewrite (signOpens sign.kind signIs).left at afterSign then afterSign
          match spaced: operandSpacing argument operator operand with
            | Some chosen =>
              let tail: spacingAdmits (spacedFirst chosen [Free, ..rest]) more = True :=
                rewrite starts at spacing then Bool.andRight spacing
              let (moreAdmits0, firstFits) := admitsSpacedFirst chosen rest more tail
              let moreAdmits: spacingAdmits (operand.spacing False) more = True := rewrite starts then moreAdmits0
              (
                sign,
                more,
                byComputing,
                signIs,
                signWord,
                signNumeral operator operand argument sign more operandWithin
                  (Bool.andLeft shaped)
                  operandLexical
                  unary
                  minusText
                  signKindIs
                  moreSlots
                  (other same => rewrite <- Option.someInjective (Eq.trans spaced.flipped same) then firstFits),
                unary,
                speltSlots operand False more operandWithin
                  (Bool.andLeft shaped)
                  operandLexical
                  free
                  (noRole operand)
                  moreSlots
                  moreAdmits
                  moreChained
                  moreLead
              )
            | None =>
              let moreAdmits: spacingAdmits (operand.spacing False) more = True := Bool.andRight spacing
              (
                sign,
                more,
                byComputing,
                signIs,
                signWord,
                signNumeral operator operand argument sign more operandWithin
                  (Bool.andLeft shaped)
                  operandLexical
                  unary
                  minusText
                  signKindIs
                  moreSlots
                  (other same => (Option.noneNotSome other (Eq.trans spaced.flipped same)).impossible),
                unary,
                speltSlots operand False more operandWithin
                  (Bool.andLeft shaped)
                  operandLexical
                  free
                  (noRole operand)
                  moreSlots
                  moreAdmits
                  moreChained
                  moreLead
              )
        | [], never => Void.impossible never
    | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible

theorem speltInfix ∀ (kind: InfixKind) (left: Expr) (operator: Word) (right: Expr) (read: List Item)
    (leftWithin: left.within1 = True)
    (rightWithin: right.within1 = True)
    (fits: infixText kind operator.text = True)
    (shaped: (Infix kind left operator right).shaped = True)
    (lexical: (Infix kind left operator right).lexical = True)
    (free: (Infix kind left operator right).commaFree = True)
    (slots: List.All2 SlotMatch read (Infix kind left operator right).slots)
    (spacing: spacingAdmits ((Infix kind left operator right).spacing False) read = True)
    (chained: Chained read = True)
    (lead: leadAfter read False = True):
    Spelt (Infix kind left operator right) read :=
  let (leftRead, rest, isRead, leftSlots, restSlots) :=
    List.all2AppendSplit SlotMatch read left.slots [Some operator, ..right.slots] slots
  match rest, restSlots with
    | [op, ..rightRead], ((opWord, opKind), rightSlots) =>
      let (isTok, level) := infixFacts kind operator.text fits
      let readAdmits: spacingAdmits
        (left.spacing False ++ [Free, ..spacedFirst Apart (right.spacing False)])
        (leftRead ++ [op, ..rightRead])
        = True :=
        rewrite isRead at spacing then spacing
      let (leftAdmits, restAdmits) :=
        admitsSplit
          (left.spacing False)
          [Free, ..spacedFirst Apart (right.spacing False)]
          leftRead
          [op, ..rightRead]
          (lengthOf left False leftRead leftWithin leftSlots)
          readAdmits
      let (others, starts) := spacingFree right rightWithin
      let tail: spacingAdmits (spacedFirst Apart [Free, ..others]) rightRead = True :=
        rewrite starts at restAdmits then restAdmits
      let (rightAdmits0, apart) := admitsSpacedFirst Apart others rightRead tail
      let rightAdmits: spacingAdmits (right.spacing False) rightRead = True := rewrite starts then rightAdmits0
      let readChained: Chained (leftRead ++ [op, ..rightRead]) = True := rewrite isRead at chained then chained
      let (leftChained, restChained) := chainedSplit leftRead [op, ..rightRead] readChained
      let rightChained := (chainedSplit [op] rightRead restChained).right
      let afterOp := chainedAfter leftRead op rightRead readChained
      let opens: op.kind.closesOperand = False := rewrite opKind then infixOpens kind (lexKind operator.text) isTok
      let rightLead: leadAfter rightRead False = True := rewrite opens at afterOp then afterOp
      let leftLead := leadFront leftRead [op, ..rightRead] False (rewrite isRead at lead then lead)
      (
        leftRead,
        op,
        rightRead,
        isRead,
        (rewrite opKind then isTok),
        opWord,
        (rewrite opKind then level),
        Bool.andLeft (Bool.andRight (Bool.andRight shaped)),
        Bool.andRight (Bool.andRight (Bool.andRight shaped)),
        apartOperand rightRead apart,
        speltSlots left False leftRead leftWithin
          (Bool.andLeft shaped)
          (Bool.andLeft lexical)
          (Bool.andLeft free)
          (noRole left)
          leftSlots
          leftAdmits
          leftChained
          leftLead,
        speltSlots right False rightRead rightWithin
          (Bool.andLeft (Bool.andRight shaped))
          (Bool.andRight (Bool.andRight lexical))
          (Bool.andRight free)
          (noRole right)
          rightSlots
          rightAdmits
          rightChained
          rightLead
      )
    | [], never => Void.impossible never

theorem speltApp ∀ (head: Expr) (arguments: List Expr) (read: List Item)
    (within: (App head arguments).within1 = True)
    (shaped: (App head arguments).shaped = True)
    (lexical: (App head arguments).lexical = True)
    (free: (App head arguments).commaFree = True)
    (slots: List.All2 SlotMatch read (App head arguments).slots)
    (spacing: spacingAdmits ((App head arguments).spacing False) read = True)
    (chained: Chained read = True)
    (lead: leadAfter read False = True):
    Spelt (App head arguments) read :=
  let (headRead, argsRead, isRead, headSlots, argsSlots) :=
    List.all2AppendSplit SlotMatch read head.slots (argumentSlots arguments) slots
  let headWithin: head.within1 = True := Bool.andLeft within
  let headLexical: head.lexical = True := Bool.andLeft lexical
  let fitsHead: head.callHead = True := Bool.andLeft shaped
  let headShaped: head.shaped = True := Bool.andLeft (Bool.andRight shaped)
  let some: (!arguments.isEmpty) = True := Bool.andLeft (Bool.andRight (Bool.andRight shaped))
  let argsArgument: arguments.all Expr.callArgument = True :=
    Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight shaped)))
  let argsShaped: allShaped arguments = True := Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight shaped)))
  let readAdmits: spacingAdmits (head.spacing False ++ argumentsSpacing arguments) (headRead ++ argsRead) = True :=
    rewrite isRead at spacing then spacing
  let (headAdmits, argsAdmits) :=
    admitsSplit
      (head.spacing False)
      (argumentsSpacing arguments)
      headRead
      argsRead
      (lengthOf head False headRead headWithin headSlots)
      readAdmits
  let readChained: Chained (headRead ++ argsRead) = True := rewrite isRead at chained then chained
  let (headChained, argsChained) := chainedSplit headRead argsRead readChained
  let headLead := leadFront headRead argsRead False (rewrite isRead at lead then lead)
  let (front, last, isHead, closes) := lastCloses head headRead headWithin headShaped headLexical headSlots
  let joined: Chained (front ++ [last, ..argsRead]) = True :=
    rewrite isHead, List.appendAssoc front [last] argsRead at readChained then readChained
  let afterHead := chainedAfter front last argsRead joined
  let argsLead: leadAfter argsRead True = True := rewrite closes at afterHead then afterHead
  let (steps, isArgs, speltArgs) :=
    speltArguments arguments argsRead
      (Bool.andRight within)
      argsShaped
      argsArgument
      (Bool.andRight lexical)
      (Bool.andRight free)
      argsSlots
      argsAdmits
      argsChained
      argsLead
  let headSpelt :=
    speltSlots head False headRead headWithin headShaped headLexical
      (Bool.andLeft free)
      (noRole head)
      headSlots
      headAdmits
      headChained
      headLead
  let headFitting := headFitsOf head headRead headWithin headLexical fitsHead headSlots headAdmits headLead
  match arguments, some, speltArgs with
    | [first, ..more], _, (argRead, later, isSteps, argFits, argSpelt, moreSpelt) => (
      headRead,
      argRead,
      later,
      (rewrite isRead, isArgs, isSteps),
      headFitting,
      argFits,
      headSpelt,
      argSpelt,
      moreSpelt
    )

--| A call's arguments are spelt by their items, each after the head or the argument before it.
theorem speltArguments ∀ (arguments: List Expr) (read: List Item)
    (within: allWithin1 arguments = True)
    (shaped: allShaped arguments = True)
    (args: arguments.all Expr.callArgument = True)
    (lexical: allLexical arguments = True)
    (free: allCommaFree arguments = True)
    (slots: List.All2 SlotMatch read (argumentSlots arguments))
    (spacing: spacingAdmits (argumentsSpacing arguments) read = True)
    (chained: Chained read = True)
    (lead: leadAfter read True = True):
    ∃ (steps: List (List Item, Expr)) => read = Parse.loopReads [] steps ∧ SpeltArgs arguments steps :=
  match arguments with
    | [] =>
      match read, slots with
        | [], _ => ([], byComputing, byComputing)
    | [argument, ..rest] =>
      let (argRead, restRead, isRead, argSlots, restSlots) :=
        List.all2AppendSplit SlotMatch read argument.slots (argumentSlots rest) slots
      let argWithin: argument.within1 = True := Bool.andLeft within
      let argLexical: argument.lexical = True := Bool.andLeft lexical
      let isArgument: argument.callArgument = True := Bool.andLeft args
      let readAdmits: spacingAdmits (argument.spacing True ++ argumentsSpacing rest) (argRead ++ restRead) = True :=
        rewrite isRead at spacing then spacing
      let (argAdmits, restAdmits) :=
        admitsSplit
          (argument.spacing True)
          (argumentsSpacing rest)
          argRead
          restRead
          (lengthOf argument True argRead argWithin argSlots)
          readAdmits
      let readChained: Chained (argRead ++ restRead) = True := rewrite isRead at chained then chained
      let (argChained, restChained) := chainedSplit argRead restRead readChained
      let argLead := leadFront argRead restRead True (rewrite isRead at lead then lead)
      let (front, last, isArg, closes) :=
        lastCloses argument argRead argWithin (Bool.andLeft shaped) argLexical argSlots
      let joined: Chained (front ++ [last, ..restRead]) = True :=
        rewrite isArg, List.appendAssoc front [last] restRead at readChained then readChained
      let afterArg := chainedAfter front last restRead joined
      let restLead: leadAfter restRead True = True := rewrite closes at afterArg then afterArg
      let (later, isRest, restSpelt) :=
        speltArguments rest restRead
          (Bool.andRight within)
          (Bool.andRight shaped)
          (Bool.andRight args)
          (Bool.andRight lexical)
          (Bool.andRight free)
          restSlots
          restAdmits
          restChained
          restLead
      (
        [(argRead, argument), ..later],
        (rewrite isRead, isRest),
        (
          argRead,
          later,
          byComputing,
          argumentFitsOf argument argRead argWithin argLexical isArgument argSlots argAdmits argLead,
          speltSlots argument True argRead argWithin
            (Bool.andLeft shaped)
            argLexical
            (Bool.andLeft free)
            (_ => isArgument)
            argSlots
            argAdmits
            argChained
            argLead,
          restSpelt
        )
      )

--| A bracket's items spelt by theirs, commas between: the first item's read, then a step for each later one.
def CommaSpelt: List Expr → List Item → Prop
  | [], read => read = []
  | [one, ..rest], read =>
    ∃ (oneRead: List Item) (steps: List (Item, List Item, Expr)) => read = oneRead ++ commaReads steps
      ∧ Spelt one oneRead
      ∧ SpeltSteps rest steps

theorem speltCommas ∀ (items: List Expr) (read: List Item)
    (within: allWithin1 items = True)
    (shaped: allShaped items = True)
    (lexical: allLexical items = True)
    (free: allCommaFree items = True)
    (slots: List.All2 SlotMatch read (commaSlots items))
    (spacing: spacingAdmits (commaSpacing items) read = True)
    (chained: Chained read = True)
    (lead: leadAfter read False = True):
    CommaSpelt items read :=
  match items with
    | [] =>
      match read, slots with
        | [], _ => byComputing
    | [one] => (
      read,
      [],
      (List.appendNil read).flipped,
      speltSlots one False read
        (Bool.andLeft within)
        (Bool.andLeft shaped)
        (Bool.andLeft lexical)
        (Bool.andLeft free)
        (noRole one)
        slots
        spacing
        chained
        lead,
      byComputing
    )
    | [one, two, ..others] =>
      let (oneRead, restRead, isRead, oneSlots, restSlots) :=
        List.all2AppendSplit SlotMatch read one.slots ([None] ++ commaSlots [two, ..others]) slots
      match restRead, restSlots with
        | [comma, ..twoRead], (isComma, twoSlots) =>
          let readAdmits: spacingAdmits
            (one.spacing False ++ ([Free] ++ commaSpacing [two, ..others]))
            (oneRead ++ [comma, ..twoRead])
            = True :=
            rewrite isRead at spacing then spacing
          let (oneAdmits, restAdmits) :=
            admitsSplit
              (one.spacing False)
              ([Free] ++ commaSpacing [two, ..others])
              oneRead
              [comma, ..twoRead]
              (lengthOf one False oneRead (Bool.andLeft within) oneSlots)
              readAdmits
          let twoAdmits: spacingAdmits (commaSpacing [two, ..others]) twoRead = True := restAdmits
          let readChained: Chained (oneRead ++ [comma, ..twoRead]) = True := rewrite isRead at chained then chained
          let (oneChained, restChained) := chainedSplit oneRead [comma, ..twoRead] readChained
          let twoChained := (chainedSplit [comma] twoRead restChained).right
          let oneLead := leadFront oneRead [comma, ..twoRead] False (rewrite isRead at lead then lead)
          let afterComma := chainedAfter oneRead comma twoRead readChained
          let twoLead: leadAfter twoRead False = True := rewrite isComma at afterComma then afterComma
          let (twoRead1, steps, isTwo, twoSpelt, othersSpelt) :=
            speltCommas
              [two, ..others]
              twoRead
              (Bool.andRight within)
              (Bool.andRight shaped)
              (Bool.andRight lexical)
              (Bool.andRight free)
              twoSlots
              twoAdmits
              twoChained
              twoLead
          (
            oneRead,
            [(comma, twoRead1, two), ..steps],
            (rewrite isRead, isTwo),
            speltSlots one False oneRead
              (Bool.andLeft within)
              (Bool.andLeft shaped)
              (Bool.andLeft lexical)
              (Bool.andLeft free)
              (noRole one)
              oneSlots
              oneAdmits
              oneChained
              oneLead,
            (comma, twoRead1, steps, byComputing, isComma, twoSpelt, othersSpelt)
          )
        | [], never => Void.impossible never

-- Closed examples: the hypotheses of the token facts hold.

theorem arrowFactsExample: InfixFacts InfixArrow "→" := arrowFacts "→" byComputing

theorem binaryFactsExample: InfixFacts InfixBinary "++" := binaryFacts "++" byComputing

theorem closerExample: lexKind ")" = RParen ∨ lexKind ")" = RBracket :=
  parenLexCloser (fixedWord ")" Word.none.comments) byComputing

theorem bracketLexCloserExample: lexKind "]" = RParen ∨ lexKind "]" = RBracket :=
  bracketLexCloser (fixedWord "]" Word.none.comments) byComputing

theorem infixFactsExample: InfixFacts InfixBinary "+" := infixFacts InfixBinary "+" byComputing
