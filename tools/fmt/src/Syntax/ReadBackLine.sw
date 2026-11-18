--| Slice 1's read-back on one line (tickets 17d and 17e): a declaration whose type and value are words,
--| parentheses, tuples, lists and calls of these, the type on the `def`'s line and the value on it or on a line of its own, parses to
--| that declaration (`readsBackLine`).
--|
--| The items are related to the tree by `Spelt` (each node's tokens in order, each item carrying the node's word, a
--| comma between bracket items and none after the last); the look-aheads are discharged by `Syntax.ReadBackEnds`
--| from the item kinds (`lineAll`: words, brackets, commas and `:=`) and from what follows each node. In `Quiet` modes
--| only a line start stops a reading, so within a line nothing does; a value starting its own line is a block of that
--| one line, whose modes allow its first item (`fullAnyLine`). A call reads its head, then each argument at the
--| depth below (`appLine`). No list may start with `auto` on a type's name (`Expr.autoFree1`), which reads as an
--| implicit binder. A prefix `-` or `!` reads its operand at the unary level (`unaryLine`), and `-` glued to a numeral
--| reads as one atom, as `Spelt` says the parser sees it. A sign may start a call's argument (`f -x !b -1`), glued
--| to its atom and spaced from what precedes it (`argumentGlue`); not a call's head (`-1 n`). An arrow `A -> B` whose
--| left side has no infix reads its right side in full (`arrowLine`), so arrows nest to the right. Other infix
--| operators and lines starting inside an expression are not here yet.

namespace Syntax.ReadBackLine
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Void)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackRuns (plainHeader)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackEnds (..)

theorem notTrueFalse ∀ (b: Bool) (no: (!b) = True): b = False := match b, no with
  | False, _ => byComputing
  | True, never => (Bool.falseNotTrue never).impossible

--| Modes in which nothing but a line start stops a reading: no guard, `calc` or `rewrite` rule, as in a declaration's
--| type and body, inside their brackets, and in a block's line.
type Quiet (modes: Modes): Prop = {
  noGuard: modes.guard = False,
  noCalc: modes.inCalc = False,
  noRule: modes.rewriteRule = None
}

--| In quiet modes, no item that doesn't start a line stops a reading.
theorem quietStops ∀ (modes: Modes) (item: Item)
    (quiet: Quiet modes)
    (inLine: item.leaf.token.lineStart = False):
    modes.stops item = False :=
  match limit: modes.limit with
    | None => rewrite quiet.noGuard, quiet.noCalc, quiet.noRule
    | Some column =>
      rewrite quiet.noGuard, quiet.noCalc, quiet.noRule, inLine then
        andFalseMiddle
          (modes.allow != Some item.index)
          (item.leaf.token.column <= column
            && !((item.kind == Comma || item.kind.isCloser) && item.depth > 0)
            && !(item.leaf.token.column == column && item.kind.isInfixOnly))

--| Whether the first item, if any, doesn't stop a reading: what follows an expression lets it end.
def openHead (modes: Modes): List Item → Bool
  | [] => True
  | [next, .._] => !modes.stops next

theorem openHeadOf ∀ (modes: Modes) (item: Item) (later: List Item)
    (open: modes.stops item = False):
    openHead modes [item, ..later] = True :=
  rewrite open

theorem openHeadStops ∀ (modes: Modes) (item: Item) (later: List Item)
    (open: openHead modes [item, ..later] = True):
    modes.stops item = False :=
  notTrueFalse _ open

theorem quietPeekSecond ∀ (modes: Modes) (first second: Item) (later: List Item)
    (open1: modes.stops first = False)
    (open2: modes.stops second = False):
    peekIn modes 1 [first, second, ..later] = Some second.kind :=
  rewrite open1, open2

theorem quietBrackets ∀ (modes: Modes) (quiet: Quiet modes): Quiet modes.inBrackets :=
  { noGuard = byComputing, noCalc = quiet.noCalc, noRule = quiet.noRule }

--| The kinds of a one-line declaration's items from its type on, in this part: words, signs, brackets, commas and
--| `:=`.
def lineKind: Tok → Bool
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | Minus => True
  | Bang => True
  | Arrow => True
  | ColonEq => True
  | LParen => True
  | RParen => True
  | LBracket => True
  | RBracket => True
  | Comma => True
  | _ => False

def lineAll: List Item → Bool
  | [] => True
  | [item, ..rest] => lineKind item.kind && lineAll rest

--| The kinds an expression of this part starts with.
def startKind: Tok → Bool
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | LParen => True
  | LBracket => True
  | _ => False

--| The signs a prefix of this part is written with.
def signKind: Tok → Bool
  | Minus => True
  | Bang => True
  | _ => False

--| The kinds any expression of this part starts with: an atom's or a sign.
def leadKind: Tok → Bool
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | LParen => True
  | LBracket => True
  | Minus => True
  | Bang => True
  | _ => False

--| A numeral: what `-` glued to it reads as one atom with.
def Expr.numeral1: Expr → Bool
  | Atom Num _ => True
  | Atom Float _ => True
  | _ => False

--| An expression that starts with a sign: a prefix, or an arrow whose left side does.
def Expr.signed1: Expr → Bool
  | Prefix _ _ => True
  | Infix _ left _ _ => left.signed1
  | _ => False

--| No infix operator at the top: what `unary` reads whole.
def Expr.unary1: Expr → Bool
  | Infix _ _ _ _ => False
  | _ => True

--| `read` spells `expr`: the node's tokens in order, each an item of the token's kind carrying the node's word, a
--| comma between each two bracket items and none after the last (`comma = False`); a tuple has two items or more. A
--| prefix is its sign and its operand, no infix, the two read as a negative numeral exactly when the operand is a
--| numeral after `-`: the glue the printer gives, which the parser's `negativeNumeral` reads. An arrow is its left
--| side, `->` and its right side; its left side has no infix at the top (other operators are not here yet).
def Spelt: Expr → List Item → Prop
  | Atom kind word, read =>
    ∃ (item: Item) => read = [item] ∧ item.kind = kind ∧ item.leaf.word = word ∧ kind.wordWithin1 = True
  | Paren open inner close, read =>
    ∃ (first: Item) (inside: List Item) (last: Item) => read = [first, ..inside ++ [last]]
      ∧ first.kind = LParen
      ∧ first.leaf.word = open
      ∧ last.kind = RParen
      ∧ last.leaf.word = close
      ∧ Spelt inner inside
  | Tuple open [one, two, ..others] comma close, read =>
    ∃ (first: Item) (read1: List Item) (separator: Item) (read2: List Item) (steps: List (Item, List Item, Expr)) (last: Item) =>
      read = [first, ..read1 ++ ([separator, ..read2] ++ (commaReads steps ++ [last]))]
        ∧ comma = False
        ∧ first.kind = LParen
        ∧ first.leaf.word = open
        ∧ separator.kind = Comma
        ∧ last.kind = RParen
        ∧ last.leaf.word = close
        ∧ Spelt one read1
        ∧ Spelt two read2
        ∧ SpeltSteps others steps
  | ListOf open [] comma close, read =>
    ∃ (first last: Item) => read = [first, last]
      ∧ comma = False
      ∧ first.kind = LBracket
      ∧ first.leaf.word = open
      ∧ last.kind = RBracket
      ∧ last.leaf.word = close
  | ListOf open [one, ..others] comma close, read =>
    ∃ (first: Item) (read1: List Item) (steps: List (Item, List Item, Expr)) (last: Item) => read
      = [first, ..read1 ++ (commaReads steps ++ [last])]
      ∧ comma = False
      ∧ first.kind = LBracket
      ∧ first.leaf.word = open
      ∧ last.kind = RBracket
      ∧ last.leaf.word = close
      ∧ Spelt one read1
      ∧ SpeltSteps others steps
  | App head [argument, ..more], read =>
    ∃ (headRead argRead: List Item) (steps: List (List Item, Expr)) => read
      = headRead ++ (argRead ++ Parse.loopReads [] steps)
      ∧ head.atomic1 = True
      ∧ argumentFits argument argRead = True
      ∧ Spelt head headRead
      ∧ Spelt argument argRead
      ∧ SpeltArgs more steps
  | Prefix operator operand, read =>
    ∃ (sign: Item) (more: List Item) => read = [sign, ..more]
      ∧ signKind sign.kind = True
      ∧ sign.leaf.word = operator
      ∧ negativeNumeral [sign, ..more] = (sign.kind == Minus && operand.numeral1)
      ∧ operand.unary1 = True
      ∧ Spelt operand more
  | Infix InfixArrow left operator right, read =>
    ∃ (leftRead: List Item) (arrow: Item) (rightRead: List Item) => read = leftRead ++ [arrow, ..rightRead]
      ∧ arrow.kind = Arrow
      ∧ arrow.leaf.word = operator
      ∧ left.unary1 = True
      ∧ Spelt left leftRead
      ∧ Spelt right rightRead
  | _, _ => Void

--| A call's arguments after the first, as `arguments`' rounds: each an atom, a bracket or a sign on one, spelt by its
--| read.
def SpeltArgs: List Expr → List (List Item, Expr) → Prop
  | [], steps => steps = []
  | [argument, ..more], steps =>
    ∃ (read: List Item) (later: List (List Item, Expr)) => steps = [(read, argument), ..later]
      ∧ argumentFits argument read = True
      ∧ Spelt argument read
      ∧ SpeltArgs more later

--| A call's argument in this part: an atom or a bracket, or a sign on one.
def Expr.signArg1: Expr → Bool
  | Prefix _ operand => operand.atomic1
  | other => other.atomic1

--| A sign starting an argument is glued to what follows it and not to what precedes it, which ends an operand: the
--| spacing `argumentPrefix` asks of `f -x`.
def argumentGlue: List Item → Bool
  | [first, next, .._] => !signKind first.kind || (first.afterOperand && (!first.glued && next.glued))
  | _ => True

--| An argument of this part, its sign (if any) spaced as an argument's.
def argumentFits (argument: Expr) (read: List Item): Bool := argument.signArg1 && argumentGlue read

--| A call of `auto` on a type's name, `auto Ord …`: first in a list, `[auto Ord]` reads as an implicit binder
--| (`namelessAutoAt`), not as a list.
def Expr.autoCall1: Expr → Bool
  | App (Atom headKind word) [Atom argumentKind _, .._] =>
    headKind == Lower && word.text == "auto" && argumentKind == Upper
  | Infix _ left _ _ => left.autoCall1
  | _ => False

--| No list in the expression starts with an `auto` call (`autoCall1`), at any depth.
def Expr.autoFree1: Expr → Bool
  | Paren _ inner _ => inner.autoFree1
  | Tuple _ items _ _ => autoFreeAll items
  | ListOf _ [] _ _ => True
  | ListOf _ [one, ..others] _ _ => !one.autoCall1 && one.autoFree1 && autoFreeAll others
  | App head arguments => head.autoFree1 && autoFreeAll arguments
  | Prefix _ operand => operand.autoFree1
  | Infix _ left _ right => left.autoFree1 && right.autoFree1
  | _ => True

def autoFreeAll: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.autoFree1 && autoFreeAll rest

theorem lowerOf ∀ (kind: Tok) (lower: (kind == Lower) = True): kind = Lower := cases

--| No slice 1 call is an `auto` call: `within1` refuses the name `auto` (SW-4027).
theorem autoCallWithin1 ∀ (expr: Expr) (within: expr.within1 = True): expr.autoCall1 = False := match expr, within with
  | App (Atom headKind word) [Atom argumentKind _, .._], within =>
    let headWithin: (Atom headKind word).within1 = True := Bool.andLeft within
    match lower: headKind == Lower with
      | False => byComputing
      | True =>
        let isLower := lowerOf headKind lower
        let headSpells: textSpells1 headKind word.text = True := Bool.andRight headWithin
        let spells: textSpells1 Lower word.text = True :=
          Eq.trans (Eq.cong (kind => textSpells1 kind word.text) isLower).flipped headSpells
        rewrite notTrueFalse _ (Bool.andRight spells)
  | Infix InfixBinary left _ _, within => autoCallWithin1 left (Bool.andLeft within)
  | Infix InfixArrow left _ _, within => autoCallWithin1 left (Bool.andLeft within)
  | Infix _ _ _ _, never => (Bool.falseNotTrue never).impossible
  | other, _ => byComputing

--| No list in a slice 1 expression starts with an `auto` call: `readsBackLine`'s `typeFree` and `valueFree` from the
--| tree.
theorem autoFreeWithin1 ∀ (expr: Expr) (within: expr.within1 = True): expr.autoFree1 = True := match expr, within with
  | Atom _ _, _ => byComputing
  | Paren _ inner _, within => autoFreeWithin1 inner within
  | Tuple _ items _ _, within => autoFreeAllWithin1 items within
  | ListOf _ [] _ _, _ => byComputing
  | ListOf _ [one, ..others] _ _, within =>
    rewrite autoCallWithin1 one (Bool.andLeft within),
        autoFreeWithin1 one (Bool.andLeft within),
        autoFreeAllWithin1 others (Bool.andRight within)
  | App head arguments, within =>
    rewrite autoFreeWithin1 head (Bool.andLeft within), autoFreeAllWithin1 arguments (Bool.andRight within)
  | Prefix _ operand, within => autoFreeWithin1 operand (Bool.andLeft within)
  | Infix InfixBinary left _ right, within =>
    rewrite autoFreeWithin1 left (Bool.andLeft within), autoFreeWithin1 right (Bool.andLeft (Bool.andRight within))
  | Infix InfixArrow left _ right, within =>
    rewrite autoFreeWithin1 left (Bool.andLeft within), autoFreeWithin1 right (Bool.andLeft (Bool.andRight within))
  | other, never => (Bool.falseNotTrue never).impossible

theorem autoFreeAllWithin1 ∀ (exprs: List Expr) (within: allWithin1 exprs = True): autoFreeAll exprs = True :=
  match exprs, within with
    | [], _ => byComputing
    | [expr, ..rest], within =>
      rewrite autoFreeWithin1 expr (Bool.andLeft within), autoFreeAllWithin1 rest (Bool.andRight within)

--| The bracket items after the first (or first two), as `CommaReads`' steps: a comma, then an item's reading.
def SpeltSteps: List Expr → List (Item, List Item, Expr) → Prop
  | [], steps => steps = []
  | [expr, ..rest], steps =>
    ∃ (comma: Item) (read: List Item) (later: List (Item, List Item, Expr)) => steps = [(comma, read, expr), ..later]
      ∧ comma.kind = Comma
      ∧ Spelt expr read
      ∧ SpeltSteps rest later

--| How deep `self` calls nest when the parser reads the expression: one more for each bracket.
def Expr.nest1: Expr → Nat
  | Paren _ inner _ => inner.nest1 + 1
  | Tuple _ items _ _ => nestAll items + 1
  | ListOf _ items _ _ => nestAll items + 1
  | App head arguments => head.nest1 + nestAll arguments + 1
  | Prefix _ operand => operand.nest1 + 1
  | Infix _ left _ right => left.nest1 + right.nest1 + 1
  | _ => 0

def nestAll: List Expr → Nat
  | [] => 0
  | [expr, ..rest] => expr.nest1 + nestAll rest

theorem wordStart ∀ (kind: Tok) (word: kind.wordWithin1 = True): startKind kind = True := cases

theorem startLead ∀ (kind: Tok) (starts: startKind kind = True): leadKind kind = True := cases

theorem signLead ∀ (kind: Tok) (signed: signKind kind = True): leadKind kind = True := cases

--| An atom or a bracket is no prefix.
theorem atomicUnsigned ∀ (expr: Expr) (atomic: expr.atomic1 = True): expr.signed1 = False := match expr, atomic with
  | Atom _ _, _ => byComputing
  | Paren _ _ _, _ => byComputing
  | Tuple _ _ _ _, _ => byComputing
  | ListOf _ _ _ _, _ => byComputing
  | other, never => (Bool.falseNotTrue never).impossible

--| A spelt expression starts with a sign or an atom's first kind.
theorem speltStarts ∀ (expr: Expr) (read: List Item)
    (spelt: Spelt expr read):
    ∃ (item: Item) (more: List Item) => read = [item, ..more] ∧ leadKind item.kind = True :=
  match expr, spelt with
    | Atom kind word, (item, isRead, isKind, _, word) =>
      (item, [], isRead, rewrite isKind then startLead kind (wordStart kind word))
    | Paren _ _ _, (first, inside, last, isRead, isOpen, _) => (first, inside ++ [last], isRead, rewrite isOpen)
    | Tuple _ [_, _, .._] _ _, (first, read1, separator, read2, steps, last, isRead, _, isOpen, _) =>
      (first, read1 ++ ([separator, ..read2] ++ (commaReads steps ++ [last])), isRead, rewrite isOpen)
    | ListOf _ [] _ _, (first, last, isRead, _, isOpen, _) => (first, [last], isRead, rewrite isOpen)
    | ListOf _ [_, .._] _ _, (first, read1, steps, last, isRead, _, isOpen, _) =>
      (first, read1 ++ (commaReads steps ++ [last]), isRead, rewrite isOpen)
    | App head [_, .._], (headRead, argRead, steps, isRead, _, _, headSpelt, _) =>
      let (first, more, isHead, starts) := speltStarts head headRead headSpelt
      (first, more ++ (argRead ++ Parse.loopReads [] steps), (rewrite isRead, isHead), starts)
    | Prefix _ _, (sign, more, isRead, signed, _) => (sign, more, isRead, signLead sign.kind signed)
    | Infix InfixArrow left _ _, (leftRead, arrow, rightRead, isRead, _, _, _, leftSpelt, _) =>
      let (first, more, isLeft, starts) := speltStarts left leftRead leftSpelt
      (first, more ++ [arrow, ..rightRead], (rewrite isRead, isLeft), starts)
    | _, never => Void.impossible never

--| A spelt expression other than a prefix starts with an atom's first kind.
theorem speltPlainStarts ∀ (expr: Expr) (read: List Item)
    (spelt: Spelt expr read)
    (unsigned: expr.signed1 = False):
    ∃ (item: Item) (more: List Item) => read = [item, ..more] ∧ startKind item.kind = True :=
  match expr, spelt, unsigned with
    | Atom kind word, (item, isRead, isKind, _, word), _ => (item, [], isRead, rewrite isKind then wordStart kind word)
    | Paren _ _ _, (first, inside, last, isRead, isOpen, _), _ => (first, inside ++ [last], isRead, rewrite isOpen)
    | Tuple _ [_, _, .._] _ _, (first, read1, separator, read2, steps, last, isRead, _, isOpen, _), _ =>
      (first, read1 ++ ([separator, ..read2] ++ (commaReads steps ++ [last])), isRead, rewrite isOpen)
    | ListOf _ [] _ _, (first, last, isRead, _, isOpen, _), _ => (first, [last], isRead, rewrite isOpen)
    | ListOf _ [_, .._] _ _, (first, read1, steps, last, isRead, _, isOpen, _), _ =>
      (first, read1 ++ (commaReads steps ++ [last]), isRead, rewrite isOpen)
    | App head [_, .._], (headRead, argRead, steps, isRead, headAtomic, _, headSpelt, _), _ =>
      let (first, more, isHead, starts) := speltPlainStarts head headRead headSpelt (atomicUnsigned head headAtomic)
      (first, more ++ (argRead ++ Parse.loopReads [] steps), (rewrite isRead, isHead), starts)
    | Prefix _ _, _, never => (Bool.falseNotTrue never.flipped).impossible
    | Infix InfixArrow left _ _, (leftRead, arrow, rightRead, isRead, _, _, _, leftSpelt, _), unsigned =>
      let (first, more, isLeft, starts) := speltPlainStarts left leftRead leftSpelt unsigned
      (first, more ++ [arrow, ..rightRead], (rewrite isRead, isLeft), starts)
    | _, never, _ => Void.impossible never

--| The kinds inside an expression of this part: `lineKind` without `:=`.
def exprKind: Tok → Bool
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | Minus => True
  | Bang => True
  | Arrow => True
  | LParen => True
  | RParen => True
  | LBracket => True
  | RBracket => True
  | Comma => True
  | _ => False

def exprAll: List Item → Bool
  | [] => True
  | [item, ..rest] => exprKind item.kind && exprAll rest

theorem exprAppend ∀ (first rest: List Item): exprAll (first ++ rest) = (exprAll first && exprAll rest) :=
  match first with
    | [] => byComputing
    | [item, ..more] =>
      rewrite exprAppend more rest then
        match exprKind item.kind with
          | True => byComputing
          | False => byComputing

theorem wordExpr ∀ (kind: Tok) (word: kind.wordWithin1 = True): exprKind kind = True := cases

theorem signExpr ∀ (kind: Tok) (signed: signKind kind = True): exprKind kind = True := cases

theorem speltExpr ∀ (expr: Expr) (read: List Item) (spelt: Spelt expr read): exprAll read = True :=
  match expr, spelt with
    | Atom kind word, (item, isRead, isKind, _, word) => rewrite isRead, isKind, wordExpr kind word
    | Paren _ inner _, (first, inside, last, isRead, isOpen, _, isClose, _, innerSpelt) =>
      rewrite isRead, isOpen, exprAppend inside [last], speltExpr inner inside innerSpelt, isClose
    | Tuple _ [one, two, ..others] _ _, (first, read1, separator, read2, steps, last, isRead, _, isOpen, _, isComma,
        isClose, _, oneSpelt, twoSpelt, stepsSpelt) =>
      rewrite isRead,
          isOpen,
          exprAppend read1 ([separator, ..read2] ++ (commaReads steps ++ [last])),
          speltExpr one read1 oneSpelt,
          isComma,
          exprAppend read2 (commaReads steps ++ [last]),
          speltExpr two read2 twoSpelt,
          exprAppend (commaReads steps) [last],
          stepsExpr others steps stepsSpelt,
          isClose
    | ListOf _ [] _ _, (first, last, isRead, _, isOpen, _, isClose, _) => rewrite isRead, isOpen, isClose
    | ListOf _ [one, ..others] _ _, (first, read1, steps, last, isRead, _, isOpen, _, isClose, _, oneSpelt,
        stepsSpelt) =>
      rewrite isRead,
          isOpen,
          exprAppend read1 (commaReads steps ++ [last]),
          speltExpr one read1 oneSpelt,
          exprAppend (commaReads steps) [last],
          stepsExpr others steps stepsSpelt,
          isClose
    | App head [argument, ..more], (headRead, argRead, steps, isRead, _, _, headSpelt, argSpelt, argsSpelt) =>
      rewrite isRead,
          exprAppend headRead (argRead ++ Parse.loopReads [] steps),
          speltExpr head headRead headSpelt,
          exprAppend argRead (Parse.loopReads [] steps),
          speltExpr argument argRead argSpelt,
          argsExpr more steps argsSpelt
    | Prefix _ operand, (sign, more, isRead, signed, _, _, _, operandSpelt) =>
      rewrite isRead, signExpr sign.kind signed, speltExpr operand more operandSpelt
    | Infix InfixArrow left _ right, (leftRead, arrow, rightRead, isRead, isArrow, _, _, leftSpelt, rightSpelt) =>
      rewrite isRead,
          exprAppend leftRead [arrow, ..rightRead],
          speltExpr left leftRead leftSpelt,
          isArrow,
          speltExpr right rightRead rightSpelt
    | _, never => Void.impossible never

theorem argsExpr ∀ (exprs: List Expr) (steps: List (List Item, Expr))
    (spelt: SpeltArgs exprs steps):
    exprAll (Parse.loopReads [] steps) = True :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty
    | [argument, ..more], (read, later, isSteps, _, argSpelt, moreSpelt) =>
      rewrite isSteps,
          exprAppend read (Parse.loopReads [] later),
          speltExpr argument read argSpelt,
          argsExpr more later moreSpelt

theorem stepsExpr ∀ (exprs: List Expr) (steps: List (Item, List Item, Expr))
    (spelt: SpeltSteps exprs steps):
    exprAll (commaReads steps) = True :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty
    | [expr, ..rest], (comma, read, later, isSteps, isComma, exprSpelt, restSpelt) =>
      rewrite isSteps,
          isComma,
          exprAppend read (commaReads later),
          speltExpr expr read exprSpelt,
          stepsExpr rest later restSpelt

theorem exprNotColonEq ∀ (kind: Tok) (expr: exprKind kind = True): (kind == ColonEq) = False := cases

theorem startOutside ∀ (first second: Tok)
    (starts: startKind first = True)
    (expr: exprKind second = True):
    parenOutside (Some first) (Some second) = False :=
  match first, starts with
    | Lower, _ => rewrite exprNotColonEq second expr
    | Upper, _ => byComputing
    | Num, _ => byComputing
    | Float, _ => byComputing
    | LParen, _ => byComputing
    | LBracket, _ => byComputing
    | other, never => (Bool.falseNotTrue never).impossible

theorem startBracketPlain ∀ (first second: Tok)
    (starts: leadKind first = True)
    (expr: exprKind second = True):
    ((isSome Lower (Some first) || isSome KwDecreasing (Some first)) && isSome ColonEq (Some second)) = False :=
  match first, starts with
    | Lower, _ => rewrite exprNotColonEq second expr
    | Upper, _ => byComputing
    | Num, _ => byComputing
    | Float, _ => byComputing
    | LParen, _ => byComputing
    | LBracket, _ => byComputing
    | Minus, _ => byComputing
    | Bang, _ => byComputing
    | other, never => (Bool.falseNotTrue never).impossible

theorem leadNotDot ∀ (kind: Tok) (starts: leadKind kind = True): (kind == Dot) = False := cases

theorem signNotParen ∀ (kind: Tok) (signed: signKind kind = True): (kind == LParen) = False := cases

theorem signNotBracket ∀ (kind: Tok) (signed: signKind kind = True): (kind == LBracket) = False := cases

theorem signNotLower ∀ (kind: Tok) (signed: signKind kind = True): (kind == Lower) = False := cases

theorem signNotUpper ∀ (kind: Tok) (signed: signKind kind = True): (kind == Upper) = False := cases

--| After `(`, a sign then an expression's first kind is no `()`, named argument or section: `-` is no section
--| operator unless `)` follows, and `!` is no operator.
theorem signOutside ∀ (sign third: Tok)
    (signed: signKind sign = True)
    (lead: leadKind third = True):
    parenOutside (Some sign) (Some third) = False :=
  let (notClose, _, _) := startNotClose third lead
  match sign, signed with
    | Minus, _ => rewrite notClose
    | Bang, _ => byComputing
    | other, never => (Bool.falseNotTrue never).impossible

--| After `(`, a spelt expression, and an expression kind after it: no `()`, named argument or section.
--|
--| Proof idea: a prefix's sign is followed by its operand's first item (`signOutside`); any other expression starts
--| with an atom's kind, followed by an expression kind (`peekTwo`, `startOutside`).
theorem speltOutside ∀ (modes: Modes)
    (quiet: Quiet modes)
    (first: Item) (expr: Expr) (read after: List Item)
    (spelt: Spelt expr read)
    (open1: modes.stops first = False)
    (inRead: inLineAll read = True)
    (afterOpen: openHead modes after = True)
    (afterHead: exprHead after = True):
    parenOutside (peekIn modes 1 [first, ..read ++ after]) (peekIn modes 2 [first, ..read ++ after]) = False :=
  let kinds := speltExpr expr read spelt
  match signed: expr.signed1 with
    | False =>
      let (second, more, isRead, starts) := speltPlainStarts expr read spelt signed
      let kinds2: exprAll [second, ..more] = True := rewrite <- isRead then kinds
      let in2: inLineAll [second, ..more] = True := rewrite <- isRead then inRead
      let open2 := quietStops modes second quiet (notTrueFalse _ (Bool.andLeft in2))
      let (kind, peek2, kindExpr) :=
        peekTwo modes quiet first second more after open1 open2
          (Bool.andRight in2)
          afterOpen
          (Bool.andRight kinds2)
          afterHead
      rewrite isRead, quietPeekSecond modes first second (more ++ after) open1 open2, peek2 then
        startOutside second.kind kind starts kindExpr
    | True =>
      match expr, spelt, signed with
        | Prefix _ operand, (sign, more, isRead, isSign, _, _, _, operandSpelt), _ =>
          let in2: inLineAll [sign, ..more] = True := rewrite <- isRead then inRead
          let open2 := quietStops modes sign quiet (notTrueFalse _ (Bool.andLeft in2))
          let (third, others, isMore, thirdLead) := speltStarts operand more operandSpelt
          let in3: inLineAll [third, ..others] = True := rewrite <- isMore then Bool.andRight in2
          let open3 := quietStops modes third quiet (notTrueFalse _ (Bool.andLeft in3))
          rewrite isRead, isMore, open1, open2, open3 then signOutside sign.kind third.kind isSign thirdLead
        | Infix InfixArrow left _ _, (leftRead, arrow, rightRead, isRead, isArrow, _, _, leftSpelt, _), _ =>
          let ins: inLineAll (leftRead ++ [arrow, ..rightRead]) = True := rewrite <- isRead then inRead
          let (inLeft, inArrowRight) := inLineSplit leftRead [arrow, ..rightRead] ins
          let openArrow := quietStops modes arrow quiet (notTrueFalse _ (Bool.andLeft inArrowRight))
          rewrite isRead, List.appendAssoc leftRead [arrow, ..rightRead] after then
            speltOutside modes quiet first left leftRead
              ([arrow, ..rightRead] ++ after)
              leftSpelt
              open1
              inLeft
              (openHeadOf modes arrow (rightRead ++ after) openArrow)
              (rewrite isArrow)
        | Infix _ _ _ _, never, _ => Void.impossible never
        | other, _, never => (Bool.falseNotTrue never).impossible

def exprHead: List Item → Bool
  | [] => False
  | [item, .._] => exprKind item.kind

theorem peekTwo ∀ (modes: Modes)
    (quiet: Quiet modes)
    (first second: Item) (more tail: List Item)
    (open1: modes.stops first = False)
    (open2: modes.stops second = False)
    (inMore: inLineAll more = True)
    (tailOpen: openHead modes tail = True)
    (kinds: exprAll more = True)
    (head: exprHead tail = True):
    ∃ (kind: Tok) => peekIn modes 2 [first, second, ..more ++ tail] = Some kind ∧ exprKind kind = True :=
  match more, kinds, inMore with
    | [], _, _ =>
      match tail, head, tailOpen with
        | [], never, _ => (Bool.falseNotTrue never).impossible
        | [next, ..later], head, tailOpen =>
          (next.kind, (rewrite open1, open2, openHeadStops modes next later tailOpen), head)
    | [third, .._], kinds, inMore => (
      third.kind,
      (rewrite open1, open2, quietStops modes third quiet (notTrueFalse _ (Bool.andLeft inMore))),
      Bool.andLeft kinds
    )

--| The first item is no section operator.
def headPlain: List Item → Bool
  | [] => True
  | [item, .._] => !item.kind.isSectionOperator

theorem lineSection ∀ (kind: Tok) (line: lineKind kind = True): kind.isSectionOperator = False := cases

--| No section operator comes straight before a closer: all `rightOperator` needs of a group's items.
def beforeClosePlain: List Item → Bool
  | [first, second, ..rest] =>
    (!second.kind.isCloser || !first.kind.isSectionOperator) && beforeClosePlain [second, ..rest]
  | _ => True

--| The newest item collected is no section operator if the next item is a closer.
def pairPlain: List Item → List Item → Bool
  | [last, .._], [next, .._] => !next.kind.isCloser || !last.kind.isSectionOperator
  | _, _ => True

theorem orTrueRight ∀ (a: Bool): (a || True) = True := match a with
  | True => byComputing
  | False => byComputing

--| One step of `groupInside` keeps the invariant: the item taken and the next are a plain pair.
theorem beforeStep ∀ (item: Item) (found rest: List Item)
    (before: beforeClosePlain [item, ..rest] = True):
    pairPlain [item, ..found] rest = True ∧ beforeClosePlain rest = True :=
  match rest, before with
    | [], _ => (byComputing, byComputing)
    | [second, .._], before => (Bool.andLeft before, Bool.andRight before)

--| What was collected before a closer ends with no section operator.
theorem closedPlain ∀ (found: List Item) (item: Item) (rest: List Item)
    (plain: pairPlain found [item, ..rest] = True)
    (closer: item.kind.isCloser = True):
    headPlain found = True :=
  match found, plain with
    | [], _ => byComputing
    | [last, .._], plain => rewrite closer at plain then plain

--| `groupInside` gives what it has collected when the group closes, newest first reversed. Its last item came
--| straight before the closing closer, so it is no section operator.
--|
--| Proof idea: by induction on the items, as `groupInside` steps; `pairPlain` says the newest item collected and the
--| next are no section operator before a closer, which `beforeClosePlain` keeps (`beforeStep`); when the group
--| closes, the newest item collected is the head of `found` (`closedPlain`).
theorem groupLine ∀ (open: List Tok) (found items inside: List Item)
    (plain: pairPlain found items = True)
    (before: beforeClosePlain items = True)
    (groups: groupInside open found items = Some inside):
    headPlain inside.reverse = True :=
  match items, plain, before, groups with
    | [], _, _, never => (Option.noneNotSome inside never).impossible
    | [item, ..rest], plain, before, groups =>
      let (fresh, later) := beforeStep item found rest before
      match item.kind.isOpener, groups with
        | True, groups => groupLine [item.kind, ..open] [item, ..found] rest inside fresh later groups
        | False, groups =>
          match closer: item.kind.isCloser, groups with
            | False, groups => groupLine open [item, ..found] rest inside fresh later groups
            | True, groups =>
              match open, groups with
                | [], groups => groupLine [] [item, ..found] rest inside fresh later groups
                | [innermost, ..outer], groups =>
                  match pairs innermost item.kind, groups with
                    | False, groups => groupLine [innermost, ..outer] [item, ..found] rest inside fresh later groups
                    | True, groups =>
                      match outer, groups with
                        | [], groups =>
                          rewrite <- Option.someInjective groups, List.reverseReverse found then
                            closedPlain found item rest plain closer
                        | [next, ..more], groups =>
                          groupLine [next, ..more] [item, ..found] rest inside fresh later groups

--| Items of this part have no section operator at all.
theorem lineBefore ∀ (items: List Item) (line: lineAll items = True): beforeClosePlain items = True := match items with
  | [] => byComputing
  | [_] => byComputing
  | [first, second, ..rest] =>
    rewrite lineSection first.kind (Bool.andLeft line),
        lineBefore [second, ..rest] (Bool.andRight line),
        orTrueRight (!second.kind.isCloser)

--| No `(k +)` section: no section operator comes straight before the closer of the group.
theorem rightPlain ∀ (first: Item) (rest: List Item)
    (before: beforeClosePlain rest = True):
    rightOperator [first, ..rest] = None :=
  match groups: groupInside [LParen] [] rest with
    | None => byComputing
    | Some inside =>
      let plain := groupLine [LParen] [] rest inside byComputing before groups
      match backwards: inside.reverse with
        | [] => byComputing
        | [last, ..more] =>
          let lastPlain: headPlain [last, ..more] = True := rewrite <- backwards then plain
          rewrite notTrueFalse last.kind.isSectionOperator lastPlain

--| No `(k +)` section: no item of this part is a section operator.
theorem rightLine ∀ (first: Item) (rest: List Item) (line: lineAll rest = True): rightOperator [first, ..rest] = None :=
  rightPlain first rest (lineBefore rest line)

theorem startFacts ∀ (kind: Tok)
    (starts: startKind kind = True):
    (kind == Dot) = False ∧ (kind == KwMatch) = False ∧ (kind == Minus || kind == Bang) = False :=
  cases

--| A unary reading that nothing continues reads inline: every rung above it with no links.
--|
--| Proof idea: `inlineWord`'s ladder, for any unary reading: each chain with no links, no comparison, logic or end.
theorem inlineOfUnary ∀ (sub: Goal → List Item → List Item → Expr → Prop) (modes: Modes) (item: Item)
    (more rest: List Item) (value: Expr)
    (open: modes.stops item = False)
    (notDot: (item.kind == Dot) = False)
    (inline: InlinePlain modes item [item, ..more ++ rest])
    (ends: OperandEnds modes rest)
    (unaryReads: UnaryReads sub modes [item, ..more] rest value):
    InlineAt sub modes item more rest value :=
  let read := [item, ..more]
  let noSection: isSome Dot (peekIn modes 0 (read ++ rest)) = False :=
    rewrite peekFirst modes item (more ++ rest) open then notDot
  let noLinks: read = read ++ Parse.loopReads [] (linkSteps []) := (List.appendNil read).flipped
  let mulReads: MulReads sub modes read rest value := (read, value, [], noLinks, byComputing, unaryReads, ends.noMul)
  let addReads: AddReads sub modes read rest value := (read, value, [], noLinks, byComputing, mulReads, ends.noAdd)
  let appendReads: AppendReads sub modes read rest value :=
    (read, value, [], noLinks, byComputing, addReads, ends.noAppend)
  let whole: read = read ++ [] ++ [] := (List.appendNil read).flipped
  let operatorReads: OperatorReads sub modes read rest value := (
    read,
    [],
    [],
    value,
    value,
    whole,
    rewrite List.appendNil read then noSection,
    Inl ((ends.noRange, ends.noPipe, appendReads), ends.noCmp),
    Inl (byComputing, byComputing, ends.noAndOr),
    ends.noIff,
    Inl (byComputing, byComputing, ends.noEnd)
  )
  (open, inline, operatorReads)

def inLineAll: List Item → Bool
  | [] => True
  | [item, ..rest] => !item.leaf.token.lineStart && inLineAll rest

theorem lineAppend ∀ (first rest: List Item): lineAll (first ++ rest) = (lineAll first && lineAll rest) :=
  match first with
    | [] => byComputing
    | [item, ..more] =>
      rewrite lineAppend more rest then
        match lineKind item.kind with
          | True => byComputing
          | False => byComputing

theorem inLineAppend ∀ (first rest: List Item): inLineAll (first ++ rest) = (inLineAll first && inLineAll rest) :=
  match first with
    | [] => byComputing
    | [item, ..more] =>
      rewrite inLineAppend more rest then
        match item.leaf.token.lineStart with
          | True => byComputing
          | False => byComputing

theorem andBoth ∀ (a b: Bool) (both: (a && b) = True): a = True ∧ b = True := (Bool.andLeft both, Bool.andRight both)

theorem linePlainKind ∀ (kind: Tok) (line: lineKind kind = True): plainKind kind = True := cases

theorem linePlain ∀ (items: List Item) (line: lineAll items = True): plainAll items = True := match items with
  | [] => byComputing
  | [item, ..rest] => rewrite linePlainKind item.kind (Bool.andLeft line), linePlain rest (Bool.andRight line)

theorem noBarLine ∀ (modes: Modes) (item: Item) (later: List Item)
    (line: lineAll later = True):
    matchesBarOn modes [item, ..later] = False :=
  match later with
    | [] => noBarOne modes item
    | [next, ..rest] => noBarPlain modes item next rest (linePlainKind next.kind (Bool.andLeft line))

theorem endsOperandOf ∀ (modes: Modes) (rest: List Item) (ends: endsHere rest = True): OperandEnds modes rest :=
  match rest with
    | [] => operandEndsNil modes
    | [next, ..later] => operandEndsAt modes next later (endKind next.kind ends)

theorem endsNotBrace ∀ (kind: Tok) (ends: endsOperand kind = True): (kind == LBrace) = False := cases

theorem endsAtom ∀ (modes: Modes) (head: Bool) (kind: Tok) (rest: List Item)
    (restOpen: openHead modes rest = True)
    (ends: endsHere rest = True):
    AtomEnds modes head kind rest :=
  let operand := endsOperandOf modes rest ends
  let plain: (isSome Upper (Some kind) && head && isSome LBrace (peekIn modes 0 rest)) = False :=
    match rest, restOpen with
      | [], _ => andFalseRight (isSome Upper (Some kind)) head _ byComputing
      | [next, ..later], restOpen =>
        andFalseRight
          (isSome Upper (Some kind))
          head _
          (rewrite peekFirst modes next later (openHeadStops modes next later restOpen) then
            endsNotBrace next.kind ends)
  { plain, noCall = operand.noCall, noDot = operand.noDot }

--| What follows a unary reading ends it: no record's fields, `()` call or field access after an atom, and no argument
--| after a call.
type UnaryEnds (modes: Modes) (rest: List Item): Prop = {
  atom: ∀ (head: Bool) (kind: Tok) => AtomEnds modes head kind rest,
  noArgument: startsAtomOn modes rest = False
}

--| What ends every expression ends a unary reading.
theorem unaryEndsOf ∀ (modes: Modes) (rest: List Item)
    (restOpen: openHead modes rest = True)
    (ends: endsHere rest = True):
    UnaryEnds modes rest :=
  {
    atom = head kind => endsAtom modes head kind rest restOpen ends,
    noArgument = (endsOperandOf modes rest ends).noArgument
  }

theorem endsSteps ∀ (exprs: List Expr) (steps: List (Item, List Item, Expr)) (last: Item) (rest: List Item)
    (spelt: SpeltSteps exprs steps)
    (isEnd: endsOperand last.kind = True):
    endsHere (commaReads steps ++ [last, ..rest]) = True :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty then isEnd
    | [_, .._], (comma, _, _, isSteps, isComma, _, _) => rewrite isSteps, isComma

theorem andRightFalse ∀ (a b: Bool) (no: b = False): (a && b) = False :=
  rewrite no then
    match a with
      | True => byComputing
      | False => byComputing

theorem endsNotUpper ∀ (kind: Tok) (ends: endsOperand kind = True): (kind == Upper) = False := cases

theorem autoSecond ∀ (item second: Item) (later: List Item)
    (no: (second.kind == Lower) = False):
    namelessAutoAt [item, second, ..later] = False :=
  match later with
    | [] => byComputing
    | [_, .._] => rewrite no

theorem autoAfterWord ∀ (item second: Item) (later: List Item)
    (ends: endsHere later = True):
    namelessAutoAt [item, second, ..later] = False :=
  match later with
    | [] => byComputing
    | [third, .._] => andFalseRight _ _ _ (endsNotUpper third.kind ends)

theorem firstKind ∀ (item first: Item) (more inside: List Item)
    (isRead: [item, ..more] = [first, ..inside]):
    item.kind = first.kind :=
  rewrite List.consInjectiveHead item first more inside isRead

--| No `[auto Upper` starts a list on one line with no calls: a word inside is followed by a comma or `]`.
--| No `[auto Upper` starts a list in this part, which has no calls: a word inside is followed by a comma or `]`.
--|
--| Proof idea: only a list starts with `[`; its first item's first token is a bracket, or a word followed by a comma
--| or the `]`.
theorem noAutoLine ∀ (expr: Expr) (item: Item) (more rest: List Item)
    (spelt: Spelt expr [item, ..more])
    (free: expr.autoFree1 = True):
    (item.kind == LBracket && namelessAutoAt [item, ..more ++ rest]) = False :=
  match expr, spelt, free with
    | Atom kind word, (first, isRead, isKind, _, word), _ =>
      rewrite firstKind item first more [] isRead, isKind, wordNotBracket kind word
    | Paren _ _ _, (first, inside, _, isRead, isOpen, _), _ => rewrite firstKind item first more _ isRead, isOpen
    | Tuple _ [_, _, .._] _ _, (first, _, _, _, _, _, isRead, _, isOpen, _), _ =>
      rewrite firstKind item first more _ isRead, isOpen
    | ListOf _ [] _ _, (first, last, isRead, _, _, _, isClose, _), _ =>
      let isMore: more = [last] := Eq.cong (.drop 1) isRead
      rewrite isMore then andRightFalse _ _ (autoSecond item last rest (rewrite isClose))
    | ListOf _ [one, ..others] _ _, (first, read1, steps, last, isRead, _, _, _, isClose, _, oneSpelt,
        stepsSpelt), free =>
      let isMore: more = read1 ++ (commaReads steps ++ [last]) := Eq.cong (.drop 1) isRead
      let tail: (commaReads steps ++ [last]) ++ rest = commaReads steps ++ [last, ..rest] :=
        List.appendAssoc (commaReads steps) [last] rest
      let after := endsSteps others steps last rest stepsSpelt (rewrite isClose)
      rewrite isMore, List.appendAssoc read1 (commaReads steps ++ [last]) rest then
        andRightFalse _ _
          (noAutoFirst one item read1
            ((commaReads steps ++ [last]) ++ rest)
            oneSpelt
            (notTrueFalse _ (Bool.andLeft free))
            (rewrite tail then endsHeadNotUpper _ after))
    | App head [argument, ..arguments], (headRead, argRead, steps, isRead, _, _, headSpelt, _), free =>
      let (first, inside, isHead, _) := speltStarts head headRead headSpelt
      let joined: [item, ..more] = [first, ..inside ++ (argRead ++ Parse.loopReads [] steps)] := calc [item, ..more]
        _ = headRead ++ (argRead ++ Parse.loopReads [] steps) := isRead
        _ = [first, ..inside ++ (argRead ++ Parse.loopReads [] steps)] := rewrite isHead
      let isItem: item = first := List.consInjectiveHead item first more _ joined
      let isMore: more = inside ++ (argRead ++ Parse.loopReads [] steps) := Eq.cong (.drop 1) joined
      let headAt: Spelt head [first, ..inside] := rewrite <- isHead then headSpelt
      rewrite isItem, isMore, List.appendAssoc inside (argRead ++ Parse.loopReads [] steps) rest then
        noAutoLine head first inside ((argRead ++ Parse.loopReads [] steps) ++ rest) headAt (Bool.andLeft free)
    | Prefix _ _, (sign, _, isRead, signed, _), _ =>
      rewrite firstKind item sign more _ isRead, signNotBracket sign.kind signed
    | Infix InfixArrow left _ _, (leftRead, arrow, rightRead, isRead, _, _, _, leftSpelt, _), free =>
      let (first, inside, isLeft, _) := speltStarts left leftRead leftSpelt
      let joined: [item, ..more] = [first, ..inside ++ [arrow, ..rightRead]] := calc [item, ..more]
        _ = leftRead ++ [arrow, ..rightRead] := isRead
        _ = [first, ..inside ++ [arrow, ..rightRead]] := rewrite isLeft
      let isItem: item = first := List.consInjectiveHead item first more _ joined
      let isMore: more = inside ++ [arrow, ..rightRead] := Eq.cong (.drop 1) joined
      let leftAt: Spelt left [first, ..inside] := rewrite <- isLeft then leftSpelt
      rewrite isItem, isMore, List.appendAssoc inside [arrow, ..rightRead] rest then
        noAutoLine left first inside ([arrow, ..rightRead] ++ rest) leftAt (Bool.andLeft free)
    | _, never, _ => Void.impossible never

--| The first item is no type's name.
def headNotUpper: List Item → Bool
  | [] => True
  | [next, .._] => !(next.kind == Upper)

theorem endsHeadNotUpper ∀ (items: List Item) (ends: endsHere items = True): headNotUpper items = True :=
  match items with
    | [] => byComputing
    | [next, .._] => rewrite endsNotUpper next.kind ends

--| A spelt expression that is no `auto` call, followed by no type's name, doesn't make the list it starts an implicit
--| binder.
--|
--| Proof idea: by the expression's first items: a word followed by no type's name; a bracket or sign, no name; a call
--| by `noAutoCall`; an arrow by its left side, followed by `->`.
theorem noAutoFirst ∀ (expr: Expr) (item: Item) (read later: List Item)
    (spelt: Spelt expr read)
    (notAuto: expr.autoCall1 = False)
    (upper: headNotUpper later = True):
    namelessAutoAt [item, ..read ++ later] = False :=
  match expr, spelt, notAuto with
    | Atom _ _, (second, isRead, _), _ =>
      rewrite isRead then
        match later, upper with
          | [], _ => byComputing
          | [third, .._], upper => andFalseRight _ _ _ (notTrueFalse _ upper)
    | Paren _ _ _, (second, _, _, isRead, isOpen, _), _ => rewrite isRead then autoSecond item second _ (rewrite isOpen)
    | Tuple _ [_, _, .._] _ _, (second, _, _, _, _, _, isRead, _, isOpen, _), _ =>
      rewrite isRead then autoSecond item second _ (rewrite isOpen)
    | ListOf _ [] _ _, (second, _, isRead, _, isOpen, _), _ =>
      rewrite isRead then autoSecond item second _ (rewrite isOpen)
    | ListOf _ [_, .._] _ _, (second, _, _, _, isRead, _, isOpen, _), _ =>
      rewrite isRead then autoSecond item second _ (rewrite isOpen)
    | App head arguments, callSpelt, notAuto => noAutoCall head arguments item read later callSpelt notAuto
    | Prefix _ _, (second, _, isRead, signed, _), _ =>
      rewrite isRead then autoSecond item second _ (signNotLower second.kind signed)
    | Infix InfixArrow left _ _, (leftRead, arrow, rightRead, isRead, isArrow, _, _, leftSpelt, _), notAuto =>
      rewrite isRead, List.appendAssoc leftRead [arrow, ..rightRead] later then
        noAutoFirst left item leftRead ([arrow, ..rightRead] ++ later) leftSpelt notAuto (rewrite isArrow)
    | _, never, _ => Void.impossible never

--| A call that is no `auto` call on a type's name doesn't make the list it starts an implicit binder.
--|
--| Proof idea: the call's head is its second item, and its first argument's first item the third: a word head and a
--| word argument are `autoCall1`'s own test; a bracket in either place is no `Lower` or `Upper`.
theorem noAutoCall ∀ (head: Expr) (arguments: List Expr) (item: Item) (read later: List Item)
    (spelt: Spelt (App head arguments) read)
    (notAuto: (App head arguments).autoCall1 = False):
    namelessAutoAt [item, ..read ++ later] = False :=
  match arguments, spelt with
    | [argument, ..more], (headRead, argRead, steps, isRead, headAtomic, argAtomic, headSpelt, argSpelt, _) =>
      let tail := argRead ++ Parse.loopReads [] steps
      match head, headSpelt, headAtomic with
        | Atom headKind word, (second, isHead, isKind, isWord, _), _ =>
          let textIs: second.text = word.text := Eq.cong (found => found.text) isWord
          match argument, argSpelt, argAtomic with
            | Atom argumentKind _, (third, isArgument, isThird, _), _ =>
              rewrite isRead, isHead, isArgument, isKind, isThird, textIs then notAuto
            | Paren _ _ _, (third, _, _, isArgument, isOpen, _), _ =>
              rewrite isRead, isHead, isArgument then andFalseRight _ _ _ (rewrite isOpen)
            | Tuple _ [_, _, .._] _ _, (third, _, _, _, _, _, isArgument, _, isOpen, _), _ =>
              rewrite isRead, isHead, isArgument then andFalseRight _ _ _ (rewrite isOpen)
            | ListOf _ [] _ _, (third, _, isArgument, _, isOpen, _), _ =>
              rewrite isRead, isHead, isArgument then andFalseRight _ _ _ (rewrite isOpen)
            | ListOf _ [_, .._] _ _, (third, _, _, _, isArgument, _, isOpen, _), _ =>
              rewrite isRead, isHead, isArgument then andFalseRight _ _ _ (rewrite isOpen)
            | App _ _, _, never => (Bool.falseNotTrue never).impossible
            | Infix _ _ _ _, _, never => (Bool.falseNotTrue never).impossible
            | Prefix _ _, (third, _, isArgument, isSign, _), _ =>
              rewrite isRead, isHead, isArgument then andFalseRight _ _ _ (signNotUpper third.kind isSign)
            | _, never, _ => Void.impossible never
        | Paren _ _ _, (second, inside, last, isHead, isOpen, _), _ =>
          rewrite isRead, isHead then autoSecond item second (((inside ++ [last]) ++ tail) ++ later) (rewrite isOpen)
        | Tuple _ [_, _, .._] _ _, (second, read1, separator, read2, commas, last, isHead, _, isOpen, _), _ =>
          rewrite isRead, isHead then
            autoSecond item second
              (((read1 ++ ([separator, ..read2] ++ (commaReads commas ++ [last]))) ++ tail) ++ later)
              (rewrite isOpen)
        | ListOf _ [] _ _, (second, last, isHead, _, isOpen, _), _ =>
          rewrite isRead, isHead then autoSecond item second (([last] ++ tail) ++ later) (rewrite isOpen)
        | ListOf _ [_, .._] _ _, (second, read1, commas, last, isHead, _, isOpen, _), _ =>
          rewrite isRead, isHead then
            autoSecond item second (((read1 ++ (commaReads commas ++ [last])) ++ tail) ++ later) (rewrite isOpen)
        | App _ _, _, never => (Bool.falseNotTrue never).impossible
        | Prefix _ _, _, never => (Bool.falseNotTrue never).impossible
        | Infix _ _ _ _, _, never => (Bool.falseNotTrue never).impossible
        | _, never, _ => Void.impossible never
    | [], never => Void.impossible never

theorem commaDoneSteps ∀ (exprs: List Expr) (steps: List (Item, List Item, Expr)) (current: Expr) (found: List Expr)
    (spelt: SpeltSteps exprs steps):
    commaDone current found steps = found.reverse ++ [current, ..exprs] :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty then List.reverseCons current found
    | [expr, ..rest], (_, _, later, isSteps, _, _, restSpelt) =>
      rewrite isSteps, commaDoneSteps rest later expr [current, ..found] restSpelt, List.reverseCons current found then
        List.appendAssoc found.reverse [current] [expr, ..rest]

theorem exprHeadSteps ∀ (exprs: List Expr) (steps: List (Item, List Item, Expr)) (last: Item) (rest: List Item)
    (spelt: SpeltSteps exprs steps)
    (lastExpr: exprKind last.kind = True):
    exprHead ((commaReads steps ++ [last]) ++ rest) = True :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty then lastExpr
    | [_, .._], (comma, _, _, isSteps, isComma, _, _) => rewrite isSteps, isComma

theorem startNotClose ∀ (kind: Tok)
    (starts: leadKind kind = True):
    (kind == RParen) = False ∧ (kind == RBracket) = False ∧ (kind == DotDot) = False :=
  cases

theorem lineJoin ∀ (first rest: List Item)
    (lineFirst: lineAll first = True)
    (lineRest: lineAll rest = True):
    lineAll (first ++ rest) = True :=
  rewrite lineAppend first rest, lineFirst, lineRest

theorem lineSplit ∀ (first rest: List Item)
    (line: lineAll (first ++ rest) = True):
    lineAll first = True ∧ lineAll rest = True :=
  andBoth _ _ (rewrite <- lineAppend first rest then line)

theorem inLineSplit ∀ (first rest: List Item)
    (line: inLineAll (first ++ rest) = True):
    inLineAll first = True ∧ inLineAll rest = True :=
  andBoth _ _ (rewrite <- inLineAppend first rest then line)

--| Whether no item after the first starts a line.
def laterInLine: List Item → Bool
  | [] => True
  | [_, ..rest] => inLineAll rest

--| A bracket's elements after a comma end where the next comma or the closer comes, neither starting a line.
theorem openSteps ∀ (modes: Modes)
    (quiet: Quiet modes)
    (steps: List (Item, List Item, Expr)) (last: Item) (rest: List Item)
    (inCommas: inLineAll (commaReads steps) = True)
    (inLast: last.leaf.token.lineStart = False):
    openHead modes ((commaReads steps ++ [last]) ++ rest) = True :=
  match steps, inCommas with
    | [], _ => openHeadOf modes last rest (quietStops modes last quiet inLast)
    | [(comma, read, value), ..later], inCommas =>
      rewrite quietStops modes comma quiet (notTrueFalse _ (Bool.andLeft inCommas))

theorem openStepsRest ∀ (modes: Modes)
    (quiet: Quiet modes)
    (steps: List (Item, List Item, Expr)) (last: Item) (rest: List Item)
    (inCommas: inLineAll (commaReads steps) = True)
    (inLast: last.leaf.token.lineStart = False):
    openHead modes (commaReads steps ++ [last, ..rest]) = True :=
  rewrite <- List.appendAssoc (commaReads steps) [last] rest then openSteps modes quiet steps last rest inCommas inLast

-- Calls.

theorem argsValues ∀ (exprs: List Expr) (steps: List (List Item, Expr))
    (spelt: SpeltArgs exprs steps):
    Parse.stepValues steps = exprs :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty
    | [argument, ..more], (_, later, isSteps, _, _, moreSpelt) => rewrite isSteps, argsValues more later moreSpelt

theorem lineNotBrace ∀ (kind: Tok) (line: lineKind kind = True): (kind == LBrace) = False := cases

--| No item of this part is a `{`, so no look-ahead finds one.
theorem peekNoBrace ∀ (modes: Modes) (ahead: Nat) (items: List Item)
    (line: lineAll items = True):
    isSome LBrace (peekIn modes ahead items) = False :=
  match ahead, items, line with
    | _, [], _ => byComputing
    | Zero, [item, .._], line =>
      match modes.stops item with
        | True => byComputing
        | False => lineNotBrace item.kind (Bool.andLeft line)
    | Succ more, [item, ..later], line =>
      match modes.stops item with
        | True => byComputing
        | False => peekNoBrace modes more later (Bool.andRight line)

theorem startOpens ∀ (kind: Tok) (starts: startKind kind = True): opensArgument kind = True := cases

theorem wordNotParen ∀ (kind: Tok) (word: kind.wordWithin1 = True): (kind == LParen) = False := cases

theorem unitNotParen ∀ (first: Item) (items: List Item)
    (notParen: (first.kind == LParen) = False):
    unitCall [first, ..items] = False :=
  match items with
    | [] => byComputing
    | [_, .._] => rewrite notParen

--| A spelt expression starts no `()` call: its first item is no `(`, or the second is no `)`.
--|
--| Proof idea: by the expression: a word or a list starts with no `(`; a parenthesis or tuple has an expression
--| inside, which starts with no `)`; a call starts as its head.
theorem speltNoUnit ∀ (expr: Expr) (first: Item) (more later: List Item)
    (spelt: Spelt expr [first, ..more]):
    unitCall [first, ..more ++ later] = False :=
  match expr, spelt with
    | Atom kind word, (item, isRead, isKind, _, word) =>
      let notParen: (first.kind == LParen) = False :=
        rewrite firstKind first item more [] isRead, isKind then wordNotParen kind word
      unitNotParen first (more ++ later) notParen
    | Paren _ inner _, (open, inside, last, isRead, _, _, _, _, innerSpelt) =>
      let (second, others, isInside, starts) := speltStarts inner inside innerSpelt
      let (notClose, _, _) := startNotClose second.kind starts
      let isMore: more = inside ++ [last] := Eq.cong (.drop 1) isRead
      rewrite isMore, isInside, notClose then andFalseMiddle (first.kind == LParen) (first.glued && second.glued)
    | Tuple _ [one, _, .._] _ _, (open, read1, separator, read2, commas, last, isRead, _, _, _, _, _, _, oneSpelt, _) =>
      let (second, others, isRead1, starts) := speltStarts one read1 oneSpelt
      let (notClose, _, _) := startNotClose second.kind starts
      let isMore: more = read1 ++ ([separator, ..read2] ++ (commaReads commas ++ [last])) := Eq.cong (.drop 1) isRead
      rewrite isMore, isRead1, notClose then andFalseMiddle (first.kind == LParen) (first.glued && second.glued)
    | ListOf _ [] _ _, (open, last, isRead, _, isOpen, _) =>
      let isMore: more = [last] := Eq.cong (.drop 1) isRead
      rewrite isMore, firstKind first open more [last] isRead, isOpen
    | ListOf _ [_, .._] _ _, (open, read1, steps, last, isRead, _, isOpen, _) =>
      let notParen: (first.kind == LParen) = False := rewrite firstKind first open more _ isRead, isOpen
      unitNotParen first (more ++ later) notParen
    | App head [_, .._], (headRead, argRead, steps, isRead, _, _, headSpelt, _) =>
      let (start, inside, isHead, _) := speltStarts head headRead headSpelt
      let joined: [first, ..more] = [start, ..inside ++ (argRead ++ Parse.loopReads [] steps)] := calc [first, ..more]
        _ = headRead ++ (argRead ++ Parse.loopReads [] steps) := isRead
        _ = [start, ..inside ++ (argRead ++ Parse.loopReads [] steps)] := rewrite isHead
      let isFirst: first = start := List.consInjectiveHead first start more _ joined
      let isMore: more = inside ++ (argRead ++ Parse.loopReads [] steps) := Eq.cong (.drop 1) joined
      let headAt: Spelt head [start, ..inside] := rewrite <- isHead then headSpelt
      rewrite isFirst, isMore, List.appendAssoc inside (argRead ++ Parse.loopReads [] steps) later then
        speltNoUnit head start inside ((argRead ++ Parse.loopReads [] steps) ++ later) headAt
    | Prefix _ _, (sign, inside, isRead, signed, _) =>
      let notParen: (first.kind == LParen) = False :=
        rewrite firstKind first sign more inside isRead then signNotParen sign.kind signed
      unitNotParen first (more ++ later) notParen
    | Infix InfixArrow left _ _, (leftRead, arrow, rightRead, isRead, _, _, _, leftSpelt, _) =>
      let (start, inside, isLeft, _) := speltStarts left leftRead leftSpelt
      let joined: [first, ..more] = [start, ..inside ++ [arrow, ..rightRead]] := calc [first, ..more]
        _ = leftRead ++ [arrow, ..rightRead] := isRead
        _ = [start, ..inside ++ [arrow, ..rightRead]] := rewrite isLeft
      let isFirst: first = start := List.consInjectiveHead first start more _ joined
      let isMore: more = inside ++ [arrow, ..rightRead] := Eq.cong (.drop 1) joined
      let leftAt: Spelt left [start, ..inside] := rewrite <- isLeft then leftSpelt
      rewrite isFirst, isMore, List.appendAssoc inside [arrow, ..rightRead] later then
        speltNoUnit left start inside ([arrow, ..rightRead] ++ later) leftAt
    | _, never => Void.impossible never

--| Before a spelt expression whose first item the modes don't stop, an atom ends: no record's fields, no `()` call,
--| no field access.
theorem endsBeforeSpelt ∀ (modes: Modes) (head: Bool) (kind: Tok) (expr: Expr) (first: Item) (more later: List Item)
    (spelt: Spelt expr [first, ..more])
    (open: modes.stops first = False)
    (line: lineAll ([first, ..more] ++ later) = True):
    AtomEnds modes head kind ([first, ..more] ++ later) :=
  let (start, inside, isRead, starts) := speltStarts expr [first, ..more] spelt
  let notDot := leadNotDot first.kind (rewrite firstKind first start more inside isRead then starts)
  {
    plain = andFalseRight (isSome Upper (Some kind)) head _ (peekNoBrace modes 0 _ line),
    noCall = speltNoUnit expr first more later spelt,
    noDot = rewrite notDot
  }

theorem startOpensAtom ∀ (kind: Tok) (starts: startKind kind = True): kind.opensAtom = True := cases

theorem signCases ∀ (kind: Tok) (signed: signKind kind = True): kind = Minus ∨ kind = Bang := match kind, signed with
  | Minus, _ => Inl byComputing
  | Bang, _ => Inr byComputing
  | other, never => (Bool.falseNotTrue never).impossible

--| An argument of this part that is no prefix is an atom or a bracket.
theorem signArgAtomic ∀ (expr: Expr)
    (fits: expr.signArg1 = True)
    (unsigned: expr.signed1 = False):
    expr.atomic1 = True :=
  match expr, fits, unsigned with
    | Prefix _ _, _, never => (Bool.falseNotTrue never.flipped).impossible
    | Atom _ _, fits, _ => fits
    | Paren _ _ _, fits, _ => fits
    | Tuple _ _ _ _, fits, _ => fits
    | ListOf _ _ _ _, fits, _ => fits
    | other, never, _ => (Bool.falseNotTrue never).impossible

--| A sign spaced as an argument's, in its line and before an atom, negates an argument.
theorem argumentPrefixOf ∀ (sign next: Item) (later: List Item)
    (signed: signKind sign.kind = True)
    (glue: argumentGlue [sign, next, ..later] = True)
    (inLine: sign.leaf.token.lineStart = False)
    (opens: next.kind.opensAtom = True):
    argumentPrefix [sign, next, ..later] = True :=
  let spaced: (sign.afterOperand && (!sign.glued && next.glued)) = True := rewrite signed at glue then glue
  let (afterOperand, glues) := andBoth _ _ spaced
  let (unglued, nextGlued) := andBoth _ _ glues
  rewrite signOr sign.kind signed, afterOperand, notTrueFalse _ unglued, inLine, nextGlued, opens

--| A sign before an argument starts an atom.
theorem signStartsAtom ∀ (modes: Modes) (kind: Tok) (items: List Item)
    (signed: signKind kind = True)
    (prefix: argumentPrefix items = True):
    startsAtomKind modes kind items = True :=
  match kind, signed with
    | Minus, _ => rewrite prefix
    | Bang, _ => rewrite prefix
    | other, never => (Bool.falseNotTrue never).impossible

--| A spelt argument of this part, in its line, starts an atom.
theorem argStarts ∀ (modes: Modes) (argument: Expr) (first: Item) (more later: List Item)
    (spelt: Spelt argument [first, ..more])
    (fits: argumentFits argument [first, ..more] = True)
    (open: modes.stops first = False)
    (inLine: inLineAll [first, ..more] = True):
    startsAtomOn modes [first, ..more ++ later] = True :=
  match signed: argument.signed1 with
    | False =>
      let (start, inside, isRead, starts) := speltPlainStarts argument [first, ..more] spelt signed
      rewrite peekFirst modes first (more ++ later) open,
          firstKind first start more inside isRead,
          startOpens start.kind starts
    | True =>
      match argument, spelt, fits, signed with
        | Prefix _ operand, (sign, inner, isRead, isSign, _, _, _, operandSpelt), fits, _ =>
          let isSign1: first = sign := List.consInjectiveHead first sign more inner isRead
          let isInner: more = inner := Eq.cong (.drop 1) isRead
          let (next, others, isOperand, nextStarts) :=
            speltPlainStarts operand inner operandSpelt (atomicUnsigned operand (Bool.andLeft fits))
          let glueInner: argumentGlue [sign, ..inner] = True :=
            Eq.trans (Eq.cong (taken => argumentGlue taken) isRead).flipped (Bool.andRight fits)
          let glueNext: argumentGlue [sign, next, ..others] = True :=
            Eq.trans (Eq.cong (taken => argumentGlue [sign, ..taken]) isOperand).flipped glueInner
          let glue: argumentGlue [sign, next, ..others ++ later] = True := glueNext
          let inSign: sign.leaf.token.lineStart = False := rewrite <- isSign1 then notTrueFalse _ (Bool.andLeft inLine)
          rewrite isSign1,
              isInner,
              isOperand,
              peekFirst modes sign ([next, ..others] ++ later) (rewrite <- isSign1 then open) then
            signStartsAtom modes sign.kind
              [sign, next, ..others ++ later]
              isSign
              (argumentPrefixOf sign next (others ++ later) isSign glue inSign (startOpensAtom next.kind nextStarts))
        | Infix _ _ _ _, _, fits, _ => (Bool.falseNotTrue fits).impossible
        | other, _, _, never => (Bool.falseNotTrue never).impossible

--| A sign on an atom, spelt on one line, at the argument level: the sign glued to the atom, read as a negative numeral
--| (`NumberBase`) where it is `-` on a numeral, and as a sign on an argument (`SignBase`) otherwise.
--|
--| Proof idea: the spacing `argumentGlue` gives is `argumentPrefix`'s; `Spelt` says whether `negativeNumeral` holds,
--| and the operand is an atom or a bracket, read by `atomLine` one level down.
theorem signArgLine ∀ (modes: Modes)
    (quiet: Quiet modes)
    (operator: Word) (operand: Expr) (read later: List Item) (depth: Nat)
    (deep: (Prefix operator operand).nest1 <= depth)
    (spelt: Spelt (Prefix operator operand) read)
    (atomic: operand.atomic1 = True)
    (glue: argumentGlue read = True)
    (free: operand.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineLater: lineAll later = True)
    (inLine: inLineAll read = True)
    (after: ∀ (kind: Tok) => AtomEnds modes False kind later):
    AtomReads (TreeN depth) modes False read later (Prefix operator operand) :=
  let (sign, more, isRead, isSign, isWord, numeral, _, operandSpelt) := spelt
  let inItems: inLineAll [sign, ..more] = True := rewrite <- isRead then inLine
  let inSign: sign.leaf.token.lineStart = False := notTrueFalse _ (Bool.andLeft inItems)
  let openSign := quietStops modes sign quiet inSign
  let inMore: inLineAll more = True := Bool.andRight inItems
  let (next, others, isMore, nextStarts) := speltPlainStarts operand more operandSpelt (atomicUnsigned operand atomic)
  let inNext: inLineAll [next, ..others] = True := rewrite <- isMore then inMore
  let openNext := quietStops modes next quiet (notTrueFalse _ (Bool.andLeft inNext))
  let lineItems: lineAll [sign, ..more] = True := rewrite <- isRead then lineRead
  let lineMore: lineAll more = True := Bool.andRight lineItems
  let glueMore: argumentGlue [sign, ..more] = True :=
    Eq.trans (Eq.cong (taken => argumentGlue taken) isRead).flipped glue
  let glueNext: argumentGlue [sign, next, ..others] = True :=
    Eq.trans (Eq.cong (taken => argumentGlue [sign, ..taken]) isMore).flipped glueMore
  let glueAll: argumentGlue [sign, next, ..others ++ later] = True := glueNext
  let prefix := argumentPrefixOf sign next (others ++ later) isSign glueAll inSign (startOpensAtom next.kind nextStarts)
  let atMore: argumentPrefix [sign, ..more ++ later] = True := rewrite isMore then prefix
  let numeralAfter: negativeNumeral [sign, ..more ++ later] = negativeNumeral [sign, ..more] := rewrite isMore
  let openMore: openHead modes more = True := rewrite isMore then openHeadOf modes next others openNext
  let laterMore: laterInLine more = True := rewrite isMore then Bool.andRight inNext
  match depth, deep with
    | Zero, deep => Void.impossible (arithmetic [deep])
    | Succ below, deep =>
      let base: BaseReads (TreeN (Succ below)) modes sign more later (Prefix operator operand) :=
        match glued: (sign.kind == Minus && operand.numeral1) with
          | False =>
            let signs: (sign.kind = Minus
              ∧ negativeNumeral [sign, ..more ++ later] = False
              ∧ argumentMinus [sign, ..more ++ later] = True)
              ∨ (sign.kind = Bang ∧ argumentBang [sign, ..more ++ later] = True) :=
              match signCases sign.kind isSign with
                | Inl isMinus =>
                  Inl (isMinus, (rewrite numeralAfter then Eq.trans numeral glued), (rewrite isMinus, atMore))
                | Inr isBang => Inr (isBang, (rewrite isBang, atMore))
            Inr
              (Inr
                (Inr
                  (Inr
                    (Inr
                      (Inr (
                        operand,
                        (rewrite isWord),
                        signs,
                        atomLine modes quiet False operand more later below
                          (arithmetic [deep])
                          operandSpelt
                          atomic
                          free
                          lineMore
                          lineLater
                          openMore
                          laterMore
                          after
                      ))))))
          | True =>
            match operand, operandSpelt, numeral, glued with
              | Atom kind word, (number, isNumber, isKind, isNumberWord, _), numeral, glued =>
                let isMinus: sign.kind = Minus := minusOf sign.kind (Bool.andLeft glued)
                let atNumber: negativeNumeral [sign, number] = True := rewrite <- isNumber then Eq.trans numeral glued
                let negNumber: negativeNumeral [sign, number, ..later] = True := atNumber
                Inr
                  (Inr
                    (Inr
                      (Inr (Inr (Inl (number, isNumber, (rewrite isWord, isKind, isNumberWord), isMinus, negNumber))))))
              | other, _, _, never => (Bool.falseNotTrue (Bool.andRight never)).impossible
      (sign, more, isRead, openSign, after sign.kind, base)

--| An argument spelt on one line: what `arguments` reads for each argument.
theorem argumentLine ∀ (modes: Modes)
    (quiet: Quiet modes)
    (argument: Expr) (read later: List Item) (below: Nat)
    (deep: argument.nest1 <= below)
    (spelt: Spelt argument read)
    (fits: argumentFits argument read = True)
    (free: argument.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineLater: lineAll later = True)
    (inLine: inLineAll read = True)
    (after: ∀ (kind: Tok) => AtomEnds modes False kind later):
    ArgumentReads (TreeN (Succ below)) modes read later argument :=
  let (first, more, isRead, starts) := speltStarts argument read spelt
  let notDot := leadNotDot first.kind starts
  let inItems: inLineAll [first, ..more] = True := rewrite <- isRead then inLine
  let open: modes.stops first = False := quietStops modes first quiet (notTrueFalse _ (Bool.andLeft inItems))
  let openRead: openHead modes read = True := rewrite isRead then openHeadOf modes first more open
  let laterRead: laterInLine read = True := rewrite isRead then Bool.andRight inItems
  let atom: AtomReads (TreeN below) modes False read later argument := match signed: argument.signed1 with
    | False =>
      atomLine modes quiet False argument read later below deep spelt
        (signArgAtomic argument (Bool.andLeft fits) signed)
        free
        lineRead
        lineLater
        openRead
        laterRead
        after
    | True =>
      match argument, spelt, fits, free, deep, signed with
        | Prefix operator operand, spelt, fits, free, deep, _ =>
          signArgLine modes quiet operator operand read later below deep spelt
            (Bool.andLeft fits)
            (Bool.andRight fits)
            free
            lineRead
            lineLater
            inLine
            after
        | Infix _ _ _ _, _, fits, _, _, _ => (Bool.falseNotTrue fits).impossible
        | other, _, _, _, _, never => (Bool.falseNotTrue never).impossible
  (
    (rewrite isRead, notDot),
    andRightFalse _ _ (peekNoBrace modes 1 (read ++ later) (lineJoin read later lineRead lineLater)),
    atom
  )

--| What follows an argument: the next argument, or what follows the call.
theorem argEnds ∀ (modes: Modes)
    (quiet: Quiet modes)
    (head: Bool) (kind: Tok) (exprs: List Expr) (steps: List (List Item, Expr)) (rest: List Item)
    (spelt: SpeltArgs exprs steps)
    (line: lineAll (Parse.loopReads [] steps ++ rest) = True)
    (inSteps: inLineAll (Parse.loopReads [] steps) = True)
    (ends: UnaryEnds modes rest):
    AtomEnds modes head kind (Parse.loopReads [] steps ++ rest) :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty then ends.atom head kind
    | [argument, ..more], (read, later, isSteps, _, argSpelt, _) =>
      let (first, inside, isRead, _) := speltStarts argument read argSpelt
      let reads: Parse.loopReads [] steps = [first, ..inside ++ Parse.loopReads [] later] := rewrite isSteps, isRead
      let inFirst: inLineAll [first, ..inside ++ Parse.loopReads [] later] = True := rewrite <- reads then inSteps
      let joined: [first, ..inside] ++ (Parse.loopReads [] later ++ rest) = Parse.loopReads [] steps ++ rest :=
        rewrite reads then Eq.cong (Cons first) (List.appendAssoc inside (Parse.loopReads [] later) rest).flipped
      let lineFirst: lineAll ([first, ..inside] ++ (Parse.loopReads [] later ++ rest)) = True :=
        Eq.trans (Eq.cong lineAll joined) line
      rewrite <- joined then
        endsBeforeSpelt modes head kind argument first inside
          (Parse.loopReads [] later ++ rest)
          (rewrite <- isRead then argSpelt)
          (quietStops modes first quiet (notTrueFalse _ (Bool.andLeft inFirst)))
          lineFirst

--| The arguments after the first, spelt on one line, are `arguments`' rounds.
theorem argsLine ∀ (modes: Modes)
    (quiet: Quiet modes)
    (exprs: List Expr) (steps: List (List Item, Expr)) (rest: List Item) (below: Nat)
    (deep: nestAll exprs <= below)
    (spelt: SpeltArgs exprs steps)
    (free: autoFreeAll exprs = True)
    (lineSteps: lineAll (Parse.loopReads [] steps) = True)
    (lineRest: lineAll rest = True)
    (inSteps: inLineAll (Parse.loopReads [] steps) = True)
    (ends: UnaryEnds modes rest):
    ArgsReads (TreeN (Succ below)) modes steps rest :=
  match exprs, spelt, free with
    | [], isEmpty, _ => rewrite isEmpty then ends.noArgument
    | [argument, ..more], (read, later, isSteps, fits, argSpelt, moreSpelt), free =>
      let lineHere: lineAll (read ++ Parse.loopReads [] later) = True :=
        Eq.trans (Eq.cong (taken => lineAll (Parse.loopReads [] taken)) isSteps).flipped lineSteps
      let inHere: inLineAll (read ++ Parse.loopReads [] later) = True :=
        Eq.trans (Eq.cong (taken => inLineAll (Parse.loopReads [] taken)) isSteps).flipped inSteps
      let (lineRead, lineLater) := lineSplit read (Parse.loopReads [] later) lineHere
      let (inRead, inLater) := inLineSplit read (Parse.loopReads [] later) inHere
      let (first, inside, isRead, _) := speltStarts argument read argSpelt
      let inItems: inLineAll [first, ..inside] = True := rewrite <- isRead then inRead
      let open: modes.stops first = False := quietStops modes first quiet (notTrueFalse _ (Bool.andLeft inItems))
      let lineAfter: lineAll (Parse.loopReads [] later ++ rest) = True := lineJoin _ rest lineLater lineRest
      rewrite isSteps then
        (
          isEmpty => Bool.falseNotTrue (Eq.cong List.isEmpty (Eq.trans isRead.flipped isEmpty)),
          (rewrite isRead then
            argStarts modes argument first inside
              (Parse.loopReads [] later ++ rest)
              (rewrite <- isRead then argSpelt)
              (rewrite <- isRead then fits)
              open
              inItems),
          argumentLine modes quiet argument read
            (Parse.loopReads [] later ++ rest)
            below
            (arithmetic [deep])
            argSpelt
            fits
            (Bool.andLeft free)
            lineRead
            lineAfter
            inRead
            (kind => argEnds modes quiet False kind more later rest moreSpelt lineAfter inLater ends),
          argsLine modes quiet more later rest below
            (arithmetic [deep])
            moreSpelt
            (Bool.andRight free)
            lineLater
            lineRest
            inLater
            ends
        )

--| A call spelt on one line, nothing after it continuing it, is what `app` reads: the head atom, then each argument.
--|
--| Proof idea: `AppReads`' call reading: the head by `atomLine`, ended by the first argument (`endsBeforeSpelt`);
--| the first argument by `argumentLine`, the others by `argsLine`, each at the depth below the call's.
theorem appLine ∀ (modes: Modes)
    (quiet: Quiet modes)
    (head argument: Expr) (more: List Expr) (read rest: List Item) (depth: Nat)
    (deep: (App head [argument, ..more]).nest1 <= depth)
    (spelt: Spelt (App head [argument, ..more]) read)
    (free: (App head [argument, ..more]).autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (openFirst: openHead modes read = True)
    (inLater: laterInLine read = True)
    (ends: UnaryEnds modes rest):
    AppReads (TreeN depth) modes read rest (App head [argument, ..more]) :=
  let (headRead, argRead, steps, isRead, headAtomic, argFits, headSpelt, argSpelt, argsSpelt) := spelt
  let tail := argRead ++ Parse.loopReads [] steps
  let (first, inside, isHead, starts) := speltStarts head headRead headSpelt
  let joined: read = [first, ..inside ++ tail] := calc read
    _ = headRead ++ tail := isRead
    _ = [first, ..inside ++ tail] := rewrite isHead
  let lines: lineAll (headRead ++ tail) = True := rewrite <- isRead then lineRead
  let (lineHead, lineTail) := lineSplit headRead tail lines
  let (lineArg, lineSteps) := lineSplit argRead (Parse.loopReads [] steps) lineTail
  let laterIn: laterInLine [first, ..inside ++ tail] = True := rewrite <- joined then inLater
  let (inInside, inTail) := inLineSplit inside tail laterIn
  let (inArg, inSteps) := inLineSplit argRead (Parse.loopReads [] steps) inTail
  let openRead: openHead modes [first, ..inside ++ tail] = True := rewrite <- joined then openFirst
  let open1 := openHeadStops modes first (inside ++ tail) openRead
  let notDot := leadNotDot first.kind starts
  let (argFirst, argMore, isArg, _) := speltStarts argument argRead argSpelt
  let argItems: inLineAll [argFirst, ..argMore] = True := rewrite <- isArg then inArg
  let argOpen := quietStops modes argFirst quiet (notTrueFalse _ (Bool.andLeft argItems))
  let lineAfterArg: lineAll (Parse.loopReads [] steps ++ rest) = True := lineJoin _ rest lineSteps lineRest
  let lineAfterHead: lineAll (tail ++ rest) = True := lineJoin tail rest lineTail lineRest
  let argAt: Spelt argument [argFirst, ..argMore] := rewrite <- isArg then argSpelt
  let argJoin: [argFirst, ..argMore] ++ (Parse.loopReads [] steps ++ rest)
    = (argRead ++ Parse.loopReads [] steps) ++ rest :=
    rewrite isArg then (List.appendAssoc [argFirst, ..argMore] (Parse.loopReads [] steps) rest).flipped
  match depth, deep with
    | Zero, deep => Void.impossible (arithmetic [deep])
    | Succ below, deep => Inr (
      headRead,
      argRead,
      steps,
      head,
      argument,
      isRead,
      (rewrite argsValues more steps argsSpelt),
      (rewrite joined, peekFirst modes first ((inside ++ tail) ++ rest) open1, notDot),
      atomLine modes quiet True head headRead
        (tail ++ rest)
        (Succ below)
        (arithmetic [deep])
        headSpelt
        headAtomic
        (Bool.andLeft free)
        lineHead
        lineAfterHead
        (rewrite isHead then openHeadOf modes first inside open1)
        (rewrite isHead then inInside)
        (kind =>
          rewrite <- argJoin then
            endsBeforeSpelt modes True kind argument argFirst argMore
              (Parse.loopReads [] steps ++ rest)
              argAt
              argOpen
              (Eq.trans (Eq.cong lineAll argJoin) lineAfterHead)),
      (rewrite <- argJoin then
        argStarts modes argument argFirst argMore
          (Parse.loopReads [] steps ++ rest)
          argAt
          (rewrite <- isArg then argFits)
          argOpen
          argItems),
      argumentLine modes quiet argument argRead
        (Parse.loopReads [] steps ++ rest)
        below
        (arithmetic [deep])
        argSpelt
        argFits
        (Bool.andLeft (Bool.andRight free))
        lineArg
        lineAfterArg
        inArg
        (kind => argEnds modes quiet False kind more steps rest argsSpelt lineAfterArg inSteps ends),
      argsLine modes quiet more steps rest below
        (arithmetic [deep])
        argsSpelt
        (Bool.andRight (Bool.andRight free))
        lineSteps
        lineRest
        inSteps
        ends
    )

--| A spelt expression, nothing after it continuing it, is what `app` reads: a call by `appLine`, an atom or bracket
--| alone by `atomLine`.
theorem appAny ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read rest: List Item) (depth: Nat)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (openFirst: openHead modes read = True)
    (inLater: laterInLine read = True)
    (ends: UnaryEnds modes rest)
    (unsigned: expr.signed1 = False)
    (plain: expr.unary1 = True):
    AppReads (TreeN depth) modes read rest expr :=
  let alone: expr.atomic1 = True → AppReads (TreeN depth) modes read rest expr := atomic =>
    let (item, more, isRead, starts) := speltStarts expr read spelt
    let openItems: openHead modes [item, ..more] = True := rewrite <- isRead then openFirst
    let open1 := openHeadStops modes item more openItems
    let notDot := leadNotDot item.kind starts
    Inl (
      (rewrite isRead, peekFirst modes item (more ++ rest) open1, notDot),
      atomLine modes quiet True expr read rest depth deep spelt atomic free lineRead lineRest openFirst inLater (kind =>
        ends.atom True kind),
      ends.noArgument
    )
  match expr, spelt with
    | App head [argument, ..more], spelt =>
      appLine modes quiet head argument more read rest depth deep spelt free lineRead lineRest openFirst inLater ends
    | Atom _ _, _ => alone byComputing
    | Paren _ _ _, _ => alone byComputing
    | Tuple _ _ _ _, _ => alone byComputing
    | ListOf _ _ _ _, _ => alone byComputing
    | Prefix _ _, _ => (Bool.falseNotTrue unsigned.flipped).impossible
    | Infix _ _ _ _, _ => (Bool.falseNotTrue plain).impossible
    | _, never => Void.impossible never

theorem signOr ∀ (kind: Tok) (signed: signKind kind = True): (kind == Minus || kind == Bang) = True := cases

theorem minusOf ∀ (kind: Tok) (minus: (kind == Minus) = True): kind = Minus := cases

--| A spelt expression, nothing after it continuing it, is what `unary` reads: a sign and its operand, a `-` glued to
--| a numeral as one atom, or anything else as `app` reads it.
--|
--| Proof idea: by induction on the prefixes. A sign whose operand is no numeral after `-` is `UnaryReads`' sign
--| reading, the operand read by `unaryLine` one level down; a `-` glued to a numeral is the negative numeral's atom
--| (`NumberBase`), which `Spelt` says the parser sees exactly there; anything else is `appAny`, after no sign.
theorem unaryLine ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read rest: List Item) (depth: Nat)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (openFirst: openHead modes read = True)
    (inLater: laterInLine read = True)
    (ends: UnaryEnds modes rest)
    (unary: expr.unary1 = True):
    UnaryReads (TreeN depth) modes read rest expr :=
  match signed: expr.signed1 with
    | False =>
      let (item, more, isRead, starts) := speltPlainStarts expr read spelt signed
      let openItems: openHead modes [item, ..more] = True := rewrite <- isRead then openFirst
      let lineItems: lineAll [item, ..more] = True := rewrite <- isRead then lineRead
      let (_, notMatch, unsigned) := startFacts item.kind starts
      Inr (
        item,
        more,
        isRead,
        openHeadStops modes item more openItems,
        notMatch,
        noBarLine modes item (more ++ rest) (lineJoin more rest (Bool.andRight lineItems) lineRest),
        Inl unsigned,
        appAny modes quiet expr read rest depth deep spelt free lineRead lineRest openFirst inLater ends signed unary
      )
    | True =>
      match expr, spelt, signed, depth, deep with
        | Prefix _ _, _, _, Zero, deep => Void.impossible (arithmetic [deep])
        | Prefix operator operand, (sign, more, isRead, isSign, isWord, numeral, operandUnary, operandSpelt), _, Succ
              below, deep =>
          let openItems: openHead modes [sign, ..more] = True := rewrite <- isRead then openFirst
          let openSign := openHeadStops modes sign more openItems
          let lineItems: lineAll [sign, ..more] = True := rewrite <- isRead then lineRead
          let lineMore: lineAll more = True := Bool.andRight lineItems
          let laterItems: laterInLine [sign, ..more] = True := rewrite <- isRead then inLater
          let inMore: inLineAll more = True := laterItems
          let (first, others, isMore, _) := speltStarts operand more operandSpelt
          let inFirst: inLineAll [first, ..others] = True := rewrite <- isMore then inMore
          let openMore: openHead modes more = True :=
            rewrite isMore then
              openHeadOf modes first others (quietStops modes first quiet (notTrueFalse _ (Bool.andLeft inFirst)))
          let laterMore: laterInLine more = True := rewrite isMore then Bool.andRight inFirst
          let noBar := noBarLine modes sign (more ++ rest) (lineJoin more rest lineMore lineRest)
          let numeralAfter: negativeNumeral [sign, ..more ++ rest] = negativeNumeral [sign, ..more] := rewrite isMore
          match glued: (sign.kind == Minus && operand.numeral1) with
            | False => Inl (
              sign,
              more,
              operand,
              isRead,
              (rewrite isWord),
              openSign,
              signOr sign.kind isSign,
              noBar,
              (rewrite numeralAfter, numeral then andRightFalse _ _ glued),
              unaryLine modes quiet operand more rest below
                (arithmetic [deep])
                operandSpelt
                free
                lineMore
                lineRest
                openMore
                laterMore
                ends
                operandUnary
            )
            | True =>
              match operand, operandSpelt, numeral, glued with
                | Atom kind word, (number, isNumber, isKind, isNumberWord, _), numeral, glued =>
                  let isMinus: sign.kind = Minus := minusOf sign.kind (Bool.andLeft glued)
                  let atMore: negativeNumeral [sign, ..more] = True := Eq.trans numeral glued
                  let atNumber: negativeNumeral [sign, number] = True := rewrite <- isNumber then atMore
                  let negNumber: negativeNumeral [sign, number, ..rest] = True := atNumber
                  let atomReads: AtomReads
                    (TreeN (Succ below))
                    modes
                    True
                    [sign, ..more]
                    rest
                    (Prefix operator (Atom kind word)) :=
                    (
                      sign,
                      more,
                      byComputing,
                      openSign,
                      ends.atom True sign.kind,
                      Inr
                        (Inr
                          (Inr
                            (Inr
                              (Inr
                                (Inl (number, isNumber, (rewrite isWord, isKind, isNumberWord), isMinus, negNumber))))))
                    )
                  rewrite isRead then
                    Inr (
                      sign,
                      more,
                      byComputing,
                      openSign,
                      (rewrite isMinus),
                      noBar,
                      Inr (Bool.andLeft glued, (rewrite isNumber then negNumber)),
                      Inl ((rewrite peekFirst modes sign (more ++ rest) openSign, isMinus), atomReads, ends.noArgument)
                    )
                | other, _, _, never => (Bool.falseNotTrue (Bool.andRight never)).impossible
        | Infix _ _ _ _, _, _, _, _ => (Bool.falseNotTrue unary).impossible
        | other, _, never, _, _ => (Bool.falseNotTrue never).impossible

--| A spelt expression whose first item doesn't stop the modes, and whose other items don't start a line, is what
--| `exprInline` reads in quiet modes, at any depth its nesting fits in: its atom reading (`atomLine`) lifted by
--| `inlineOfAtom`, the look-aheads from the kinds and what follows.
theorem inlineUnary ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (item: Item) (more rest: List Item) (depth: Nat)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr [item, ..more])
    (free: expr.autoFree1 = True)
    (lineRead: lineAll [item, ..more] = True)
    (lineRest: lineAll rest = True)
    (open: modes.stops item = False)
    (inLater: inLineAll more = True)
    (restOpen: openHead modes rest = True)
    (ends: endsHere rest = True)
    (unary: expr.unary1 = True):
    InlineAt (TreeN depth) modes item more rest expr :=
  let unary :=
    unaryLine modes quiet expr
      [item, ..more]
      rest
      depth
      deep
      spelt
      free
      lineRead
      lineRest
      (openHeadOf modes item more open)
      inLater
      (unaryEndsOf modes rest restOpen ends)
      unary
  let (first, inside, isRead, starts) := speltStarts expr [item, ..more] spelt
  let itemStarts: leadKind item.kind = True := rewrite firstKind item first more inside isRead then starts
  inlineOfUnary
    (TreeN depth)
    modes
    item
    more
    rest
    expr
    open
    (leadNotDot item.kind itemStarts)
    (inlinePlainOf modes item
      (more ++ rest)
      (linePlain [item, ..more ++ rest] (lineJoin [item, ..more] rest lineRead lineRest))
      (noAutoLine expr item more rest spelt free))
    (endsOperandOf modes rest ends)
    unary

--| Before `->`, a unary reading ends.
theorem arrowUnaryEnds ∀ (modes: Modes) (arrow: Item) (later: List Item)
    (isArrow: arrow.kind = Arrow)
    (open: modes.stops arrow = False):
    UnaryEnds modes [arrow, ..later] :=
  let peek: peekIn modes 0 [arrow, ..later] = Some Arrow := rewrite peekFirst modes arrow later open, isArrow
  {
    atom = head kind =>
      {
        plain = andFalseRight _ head _ (rewrite peek),
        noCall = (match later with
          | [] => byComputing
          | [_, .._] => rewrite isArrow),
        noDot = (rewrite isArrow)
      },
    noArgument = (match later with
      | [] => rewrite peek
      | [_, .._] => rewrite peek, isArrow)
  }

--| No `{` first: `allowBraceOn` leaves the modes.
theorem allowNoBrace ∀ (modes: Modes) (item: Item) (rest: List Item)
    (notBrace: (item.kind == LBrace) = False):
    allowBraceOn modes [item, ..rest] = modes :=
  match limit: modes.limit with
    | None => byComputing
    | Some column => rewrite notBrace

--| An arrow spelt on one line, its left side no infix, nothing after it continuing it, is what `exprInline` reads:
--| the left side as a comparison with no links or logic, then `->` and the right side read in full.
--|
--| Proof idea: `OperatorReads` with the left side by `unaryLine` (ended by `->`, `arrowUnaryEnds`) lifted through
--| each chain with no links, no comparison and no logic; `EndReads`' arrow, its result by `fullLine` one level down,
--| `allowBraceOn` leaving the modes since no `{` starts it.
theorem arrowLine ∀ (modes: Modes)
    (quiet: Quiet modes)
    (left right: Expr) (operator: Word) (item: Item) (more rest: List Item) (depth: Nat)
    (deep: (Infix InfixArrow left operator right).nest1 <= depth)
    (spelt: Spelt (Infix InfixArrow left operator right) [item, ..more])
    (free: (Infix InfixArrow left operator right).autoFree1 = True)
    (lineRead: lineAll [item, ..more] = True)
    (lineRest: lineAll rest = True)
    (open: modes.stops item = False)
    (inLater: inLineAll more = True)
    (restOpen: openHead modes rest = True)
    (ends: endsHere rest = True):
    InlineAt (TreeN depth) modes item more rest (Infix InfixArrow left operator right) :=
  let (leftRead, arrow, rightRead, isRead, isArrow, isWord, leftUnary, leftSpelt, rightSpelt) := spelt
  let (first, inside, isLeft, starts) := speltStarts left leftRead leftSpelt
  let joined: [item, ..more] = [first, ..inside ++ [arrow, ..rightRead]] := calc [item, ..more]
    _ = leftRead ++ [arrow, ..rightRead] := isRead
    _ = [first, ..inside ++ [arrow, ..rightRead]] := rewrite isLeft
  let isItem: item = first := List.consInjectiveHead item first more _ joined
  let isMore: more = inside ++ [arrow, ..rightRead] := Eq.cong (.drop 1) joined
  let itemLead: leadKind item.kind = True := rewrite isItem then starts
  let lineAll1: lineAll (leftRead ++ [arrow, ..rightRead]) = True := rewrite <- isRead then lineRead
  let (lineLeft, lineArrowRight) := lineSplit leftRead [arrow, ..rightRead] lineAll1
  let lineRight: lineAll rightRead = True := Bool.andRight lineArrowRight
  let inMore: inLineAll (inside ++ [arrow, ..rightRead]) = True := rewrite <- isMore then inLater
  let (inInside, inArrowRight) := inLineSplit inside [arrow, ..rightRead] inMore
  let openArrow := quietStops modes arrow quiet (notTrueFalse _ (Bool.andLeft inArrowRight))
  let inRight: inLineAll rightRead = True := Bool.andRight inArrowRight
  let openLeft: openHead modes leftRead = True :=
    rewrite isLeft then openHeadOf modes first inside (rewrite <- isItem then open)
  let laterLeft: laterInLine leftRead = True := rewrite isLeft then inInside
  let after := rightRead ++ rest
  let lineAfterLeft: lineAll [arrow, ..after] = True := lineJoin [arrow, ..rightRead] rest lineArrowRight lineRest
  let peekArrow: peekIn modes 0 [arrow, ..after] = Some Arrow := rewrite peekFirst modes arrow after openArrow, isArrow
  let (rightFirst, rightMore, isRight, rightStarts) := speltStarts right rightRead rightSpelt
  let inRightItems: inLineAll [rightFirst, ..rightMore] = True := rewrite <- isRight then inRight
  let openRight := quietStops modes rightFirst quiet (notTrueFalse _ (Bool.andLeft inRightItems))
  let allowed: allowBraceOn modes (rightRead ++ rest) = modes :=
    rewrite isRight then allowNoBrace modes rightFirst (rightMore ++ rest) (startNotBrace rightFirst.kind rightStarts)
  let noRow: rowOn
    (isSome LBrace (peekIn (allowBraceOn modes (rightRead ++ rest)) 0 (rightRead ++ rest)))
    (rightRead ++ rest)
    = False :=
    rewrite allowed,
        isRight,
        peekFirst modes rightFirst (rightMore ++ rest) openRight,
        startNotBrace rightFirst.kind rightStarts
  match depth, deep with
    | Zero, deep => Void.impossible (arithmetic [deep])
    | Succ below, deep =>
      let sub := TreeN (Succ below)
      let unaryReads: UnaryReads sub modes leftRead [arrow, ..after] left :=
        unaryLine modes quiet left leftRead
          [arrow, ..after]
          (Succ below)
          (arithmetic [deep])
          leftSpelt
          (Bool.andLeft free)
          lineLeft
          lineAfterLeft
          openLeft
          laterLeft
          (arrowUnaryEnds modes arrow after isArrow openArrow)
          leftUnary
      let noLinks: leftRead = leftRead ++ Parse.loopReads [] (linkSteps []) := (List.appendNil leftRead).flipped
      let mulReads: MulReads sub modes leftRead [arrow, ..after] left :=
        (leftRead, left, [], noLinks, byComputing, unaryReads, takesEnds modes _ arrow after (rewrite isArrow))
      let addReads: AddReads sub modes leftRead [arrow, ..after] left :=
        (leftRead, left, [], noLinks, byComputing, mulReads, takesEnds modes _ arrow after (rewrite isArrow))
      let appendReads: AppendReads sub modes leftRead [arrow, ..after] left :=
        (leftRead, left, [], noLinks, byComputing, addReads, takesEnds modes _ arrow after (rewrite isArrow))
      let rightTree: sub { modes = allowBraceOn modes (rightRead ++ rest), level = LevelFull } rightRead rest right :=
        rewrite allowed then
          fullLine modes quiet right rightRead rest below
            (arithmetic [deep])
            rightSpelt
            (Bool.andRight free)
            lineRight
            lineRest
            inRight
            restOpen
            ends
      let operatorReads: OperatorReads sub modes [item, ..more] rest (Infix InfixArrow left operator right) := (
        leftRead,
        [],
        [arrow, ..rightRead],
        left,
        left,
        isRead,
        (rewrite <- isRead, peekFirst modes item (more ++ rest) open then leadNotDot item.kind itemLead),
        Inl (((rewrite peekArrow), (rewrite isArrow), appendReads), (rewrite peekArrow)),
        Inl (byComputing, byComputing, (rewrite peekArrow)),
        (rewrite peekArrow),
        Inr (arrow, rightRead, right, byComputing, (rewrite isWord), openArrow, isArrow, (noRow, rightTree))
      )
      (
        open,
        inlinePlainOf modes item
          (more ++ rest)
          (linePlain [item, ..more ++ rest] (lineJoin [item, ..more] rest lineRead lineRest))
          (noAutoLine (Infix InfixArrow left operator right) item more rest spelt free),
        operatorReads
      )

--| A spelt expression whose first item doesn't stop the modes, and whose other items don't start a line, is what
--| `exprInline` reads in quiet modes: an arrow by `arrowLine`, anything else by `inlineUnary`.
theorem inlineLine ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (item: Item) (more rest: List Item) (depth: Nat)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr [item, ..more])
    (free: expr.autoFree1 = True)
    (lineRead: lineAll [item, ..more] = True)
    (lineRest: lineAll rest = True)
    (open: modes.stops item = False)
    (inLater: inLineAll more = True)
    (restOpen: openHead modes rest = True)
    (ends: endsHere rest = True):
    InlineAt (TreeN depth) modes item more rest expr :=
  match unary: expr.unary1 with
    | True =>
      inlineUnary modes quiet expr item more rest depth deep spelt free lineRead lineRest open inLater restOpen ends
          unary
    | False =>
      match expr, spelt, unary with
        | Infix InfixArrow left operator right, spelt, _ =>
          arrowLine modes quiet left right operator item more rest depth deep spelt free lineRead lineRest open inLater
              restOpen ends
        | Infix _ _ _ _, never, _ => Void.impossible never
        | other, _, never => (Bool.falseNotTrue never.flipped).impossible

--| A spelt expression on its line's middle is what `expr` reads in quiet modes: `inlineLine`, no block starting.
theorem fullLine ∀ (modes: Modes)
    (quiet: Quiet modes)
    (expr: Expr) (read rest: List Item) (depth: Nat)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (inLine: inLineAll read = True)
    (restOpen: openHead modes rest = True)
    (ends: endsHere rest = True):
    FullReads (TreeN depth) modes read rest expr :=
  let (item, more, isRead, _) := speltStarts expr read spelt
  let sameSpelt: Spelt expr [item, ..more] := rewrite <- isRead then spelt
  let lineItems: lineAll [item, ..more] = True := rewrite <- isRead then lineRead
  let inItems: inLineAll [item, ..more] = True := rewrite <- isRead then inLine
  let inFirst: item.leaf.token.lineStart = False := notTrueFalse _ (Bool.andLeft inItems)
  rewrite isRead then
    fullOfInline
      (TreeN depth)
      modes
      item
      more
      rest
      expr
      inFirst
      (inlineLine modes quiet expr item more rest depth deep sameSpelt free lineItems lineRest
        (quietStops modes item quiet inFirst)
        (Bool.andRight inItems)
        restOpen
        ends)

theorem startNotOther ∀ (kind: Tok) (starts: leadKind kind = True): startsOtherStatement kind = False := cases

--| A spelt expression that ends what is read, its items after the first not starting a line, is what `expr` reads in
--| quiet modes with no line limit, whatever line its first item starts: where no block starts, inline; where one
--| does, as a block's one line, whose modes allow the first item's index.
theorem fullAnyLine ∀ (modes: Modes)
    (quiet: Quiet modes)
    (noLimit: modes.limit = None)
    (expr: Expr) (item: Item) (more: List Item) (depth: Nat)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr [item, ..more])
    (free: expr.autoFree1 = True)
    (lineRead: lineAll [item, ..more] = True)
    (inLater: inLineAll more = True):
    FullReads (TreeN depth) modes [item, ..more] [] expr :=
  let (first, inside, isRead, starts) := speltStarts expr [item, ..more] spelt
  let itemStarts: leadKind item.kind = True := rewrite firstKind item first more inside isRead then starts
  let column := item.leaf.token.column
  let right: rightOfLimit column modes.limit = True := rewrite noLimit
  fullOfStarts
    (TreeN depth)
    modes
    item
    more
    []
    expr
    (startsBlock modes item)
    byComputing
    (inline =>
      inlineLine modes quiet expr item more [] depth deep spelt free lineRead byComputing
        (rewrite quiet.noGuard, quiet.noCalc, quiet.noRule, noLimit)
        inLater
        byComputing
        byComputing)
    (blockStarts =>
      (
        right,
        byComputing,
        startNotOther item.kind itemStarts,
        kind =>
          let lined := lineModes (blockModes modes column True) column True (Some item.index) kind
          let lineQuiet: Quiet lined := { noGuard = quiet.noGuard, noCalc = quiet.noCalc, noRule = quiet.noRule }
          inlineLine lined lineQuiet expr item more [] depth deep spelt free lineRead byComputing
            (rewrite quiet.noGuard, quiet.noCalc, quiet.noRule, DecEq.neSelf (Some item.index))
            inLater
            byComputing
            byComputing
      ))

--| A spelt expression is what `atom` reads, at any depth its nesting fits in.
--|
--| Proof idea: by induction on the expression, with `fullLine` for the brackets' items one level down
--| (`tupleSteps` and `listSteps` for the items after the first). A word is `WordBase`; a bracket is its base with
--| the look-aheads from the first two items inside (`startOutside`, `startBracketPlain`, `peekTwo`) and the kinds
--| (`rightLine`), each item followed by a comma or the closer.
theorem atomLine ∀ (modes: Modes)
    (quiet: Quiet modes)
    (head: Bool) (expr: Expr) (read rest: List Item) (depth: Nat)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (atomic: expr.atomic1 = True)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (openFirst: openHead modes read = True)
    (inLater: laterInLine read = True)
    (after: ∀ (kind: Tok) => AtomEnds modes head kind rest):
    AtomReads (TreeN depth) modes head read rest expr :=
  let inner := modes.inBrackets
  let innerQuiet := quietBrackets modes quiet
  match expr, spelt with
    | Atom kind word, (item, isRead, isKind, isWord, word) =>
      let openItem: openHead modes [item] = True := rewrite <- isRead then openFirst
      rewrite isRead then
        (
          item,
          [],
          byComputing,
          openHeadStops modes item [] openItem,
          after item.kind,
          Inl (byComputing, (rewrite isKind, isWord), rewrite isKind then (wordPlain kind word).left)
        )
    | Paren open body close, (first, inside, last, isRead, isOpen, isOpenWord, isClose, isCloseWord, bodySpelt) =>
      match depth, deep with
        | Zero, deep => Void.impossible (arithmetic [deep])
        | Succ below, deep =>
          let lineItems: lineAll [first, ..inside ++ [last]] = True := rewrite <- isRead then lineRead
          let openItems: openHead modes [first, ..inside ++ [last]] = True := rewrite <- isRead then openFirst
          let inTail: laterInLine [first, ..inside ++ [last]] = True := rewrite <- isRead then inLater
          let open1 := openHeadStops modes first (inside ++ [last]) openItems
          let (lineInside, lineLast) := lineSplit inside [last] (Bool.andRight lineItems)
          let (inInside, inLastOnly) := inLineSplit inside [last] inTail
          let inLast: last.leaf.token.lineStart = False := notTrueFalse _ (Bool.andLeft inLastOnly)
          let bodyTree: TreeN (Succ below) { modes = inner, level = LevelFull } inside [last, ..rest] body :=
            fullLine inner innerQuiet body inside
              [last, ..rest]
              below
              (arithmetic [deep])
              bodySpelt
              free
              lineInside
              (lineJoin [last] rest lineLast lineRest)
              inInside
              (openHeadOf inner last rest (quietStops inner last innerQuiet inLast))
              (rewrite isClose)
          let assoc: (inside ++ [last]) ++ rest = inside ++ [last, ..rest] := List.appendAssoc inside [last] rest
          let plain: ParenPlain modes [first, ..(inside ++ [last]) ++ rest] := {
            notOutside = rewrite assoc then
              speltOutside modes quiet first body inside
                [last, ..rest]
                bodySpelt
                open1
                inInside
                (openHeadOf modes last rest (quietStops modes last quiet inLast))
                (rewrite isClose),
            noRight = rightLine first
              ((inside ++ [last]) ++ rest)
              (lineJoin (inside ++ [last]) rest (Bool.andRight lineItems) lineRest)
          }
          rewrite isRead then
            (
              first,
              inside ++ [last],
              byComputing,
              open1,
              after first.kind,
              Inr
                (Inl (
                  inside,
                  last,
                  body,
                  byComputing,
                  (rewrite isOpenWord, isCloseWord),
                  isOpen,
                  plain,
                  bodyTree,
                  quietStops inner last innerQuiet inLast,
                  isClose
                ))
            )
    | Tuple open [one, two, ..others] comma close, (first, read1, separator, read2, steps, last, isRead, isBare, isOpen,
        isOpenWord, isComma, isClose, isCloseWord, oneSpelt, twoSpelt, stepsSpelt) =>
      match depth, deep with
        | Zero, deep => Void.impossible (arithmetic [deep])
        | Succ below, deep =>
          let elements := [separator, ..read2] ++ (commaReads steps ++ [last])
          let lineItems: lineAll [first, ..read1 ++ elements] = True := rewrite <- isRead then lineRead
          let openItems: openHead modes [first, ..read1 ++ elements] = True := rewrite <- isRead then openFirst
          let inTail: laterInLine [first, ..read1 ++ elements] = True := rewrite <- isRead then inLater
          let open1 := openHeadStops modes first (read1 ++ elements) openItems
          let (line1, lineElements) := lineSplit read1 elements (Bool.andRight lineItems)
          let (line2, lineSteps) := lineSplit read2 (commaReads steps ++ [last]) (Bool.andRight lineElements)
          let (lineCommas, lineLast) := lineSplit (commaReads steps) [last] lineSteps
          let (in1, inElements) := inLineSplit read1 elements inTail
          let inSeparator: separator.leaf.token.lineStart = False := notTrueFalse _ (Bool.andLeft inElements)
          let (in2, inSteps) := inLineSplit read2 (commaReads steps ++ [last]) (Bool.andRight inElements)
          let (inCommas, inLastOnly) := inLineSplit (commaReads steps) [last] inSteps
          let inLast: last.leaf.token.lineStart = False := notTrueFalse _ (Bool.andLeft inLastOnly)
          let elementsOpen: ∀ (lined: Modes) => Quiet lined → openHead lined (elements ++ rest) = True :=
            lined linedQuiet => rewrite quietStops lined separator linedQuiet inSeparator
          let goal: Goal := { modes = inner, level = LevelFull }
          let oneTree: TreeN (Succ below) goal read1 (elements ++ rest) one :=
            fullLine inner innerQuiet one read1
              (elements ++ rest)
              below
              (arithmetic [deep])
              oneSpelt
              (Bool.andLeft free)
              line1
              (lineJoin elements rest lineElements lineRest)
              in1
              (elementsOpen inner innerQuiet)
              (rewrite isComma)
          let twoTree: TreeN (Succ below) goal read2 ((commaReads steps ++ [last]) ++ rest) two :=
            fullLine inner innerQuiet two read2
              ((commaReads steps ++ [last]) ++ rest)
              below
              (arithmetic [deep])
              twoSpelt
              (Bool.andLeft (Bool.andRight free))
              line2
              (lineJoin (commaReads steps ++ [last]) rest lineSteps lineRest)
              in2
              (openSteps inner innerQuiet steps last rest inCommas inLast)
              (rewrite List.appendAssoc (commaReads steps) [last] rest then
                endsSteps others steps last rest stepsSpelt (rewrite isClose))
          let rounds: CommaReads inner (tupleEnds inner) (TreeN (Succ below) goal) 2 steps [last, ..rest] :=
            tupleSteps inner innerQuiet others steps 2 last rest below
              (arithmetic [deep])
              stepsSpelt
              (Bool.andRight (Bool.andRight free))
              lineCommas
              (lineJoin [last] rest lineLast lineRest)
              inCommas
              inLast
              isClose
          let assoc: (read1 ++ elements) ++ rest = read1 ++ (elements ++ rest) := List.appendAssoc read1 elements rest
          let plain: ParenPlain modes [first, ..(read1 ++ elements) ++ rest] := {
            notOutside = rewrite assoc then
              speltOutside modes quiet first one read1
                (elements ++ rest)
                oneSpelt
                open1
                in1
                (elementsOpen modes quiet)
                (rewrite isComma),
            noRight = rightLine first
              ((read1 ++ elements) ++ rest)
              (lineJoin (read1 ++ elements) rest (Bool.andRight lineItems) lineRest)
          }
          rewrite isRead then
            (
              first,
              read1 ++ elements,
              byComputing,
              open1,
              after first.kind,
              Inr
                (Inr
                  (Inl (
                    read1,
                    separator,
                    read2,
                    steps,
                    last,
                    one,
                    two,
                    byComputing,
                    (rewrite isBare, isOpenWord, isCloseWord, commaDoneSteps others steps two [one] stepsSpelt),
                    isOpen,
                    plain,
                    oneTree,
                    quietStops inner separator innerQuiet inSeparator,
                    isComma,
                    twoTree,
                    rounds,
                    quietStops inner last innerQuiet inLast,
                    isClose
                  )))
            )
    | ListOf open [] comma close, (first, last, isRead, isBare, isOpen, isOpenWord, isClose, isCloseWord) =>
      let openItems: openHead modes [first, last] = True := rewrite <- isRead then openFirst
      let inTail: laterInLine [first, last] = True := rewrite <- isRead then inLater
      let open1 := openHeadStops modes first [last] openItems
      let inLast: last.leaf.token.lineStart = False := notTrueFalse _ (Bool.andLeft inTail)
      rewrite isRead then
        (
          first,
          [last],
          byComputing,
          open1,
          after first.kind,
          Inr
            (Inr
              (Inr
                (Inl (
                  last,
                  byComputing,
                  (rewrite isBare, isOpenWord, isCloseWord),
                  isOpen,
                  (rewrite quietPeekSecond modes first last rest open1 (quietStops modes last quiet inLast), isClose),
                  quietStops inner last innerQuiet inLast,
                  isClose
                ))))
        )
    | ListOf open [one, ..others] comma close, (first, read1, steps, last, isRead, isBare, isOpen, isOpenWord, isClose,
        isCloseWord, oneSpelt, stepsSpelt) =>
      match depth, deep with
        | Zero, deep => Void.impossible (arithmetic [deep])
        | Succ below, deep =>
          let elements := commaReads steps ++ [last]
          let lineItems: lineAll [first, ..read1 ++ elements] = True := rewrite <- isRead then lineRead
          let openItems: openHead modes [first, ..read1 ++ elements] = True := rewrite <- isRead then openFirst
          let inTail: laterInLine [first, ..read1 ++ elements] = True := rewrite <- isRead then inLater
          let open1 := openHeadStops modes first (read1 ++ elements) openItems
          let (line1, lineElements) := lineSplit read1 elements (Bool.andRight lineItems)
          let (lineCommas, lineLast) := lineSplit (commaReads steps) [last] lineElements
          let (in1, inElements) := inLineSplit read1 elements inTail
          let (inCommas, inLastOnly) := inLineSplit (commaReads steps) [last] inElements
          let inLast: last.leaf.token.lineStart = False := notTrueFalse _ (Bool.andLeft inLastOnly)
          let goal: Goal := { modes = inner, level = LevelFull }
          let (second, more, isRead1, starts) := speltStarts one read1 oneSpelt
          let (_, notBracket, notSpread) := startNotClose second.kind starts
          let oneTree: TreeN (Succ below) goal read1 (elements ++ rest) one :=
            fullLine inner innerQuiet one read1
              (elements ++ rest)
              below
              (arithmetic [deep])
              oneSpelt
              (Bool.andLeft (Bool.andRight free))
              line1
              (lineJoin elements rest lineElements lineRest)
              in1
              (openSteps inner innerQuiet steps last rest inCommas inLast)
              (rewrite List.appendAssoc (commaReads steps) [last] rest then
                endsSteps others steps last rest stepsSpelt (rewrite isClose))
          let rounds: CommaReads inner (count => inner.at RBracket) (ListElement (TreeN (Succ below)) inner) 1 steps [
            last,
            ..rest
          ] :=
            listSteps inner innerQuiet others steps 1 last rest below
              (arithmetic [deep])
              stepsSpelt
              (Bool.andRight (Bool.andRight free))
              lineCommas
              (lineJoin [last] rest lineLast lineRest)
              inCommas
              inLast
              isClose
          let kinds: exprAll [second, ..more] = True := rewrite <- isRead1 then speltExpr one read1 oneSpelt
          let inOne: inLineAll [second, ..more] = True := rewrite <- isRead1 then in1
          let inSecond: second.leaf.token.lineStart = False := notTrueFalse _ (Bool.andLeft inOne)
          let open2 := quietStops modes second quiet inSecond
          let (kind, peek2, kindExpr) :=
            peekTwo modes quiet first second more
              (elements ++ rest)
              open1
              open2
              (Bool.andRight inOne)
              (openSteps modes quiet steps last rest inCommas inLast)
              (Bool.andRight kinds)
              (exprHeadSteps others steps last rest stepsSpelt (rewrite isClose))
          let assoc: (read1 ++ elements) ++ rest = read1 ++ (elements ++ rest) := List.appendAssoc read1 elements rest
          let firstPeek: peekIn inner 0 ((read1 ++ elements) ++ rest) = Some second.kind :=
            rewrite assoc, isRead1 then
              peekFirst inner second (more ++ (elements ++ rest)) (quietStops inner second innerQuiet inSecond)
          let elementPeek: peekIn inner 0 (read1 ++ (elements ++ rest)) = Some second.kind :=
            rewrite isRead1 then
              peekFirst inner second (more ++ (elements ++ rest)) (quietStops inner second innerQuiet inSecond)
          rewrite isRead then
            (
              first,
              read1 ++ elements,
              byComputing,
              open1,
              after first.kind,
              Inr
                (Inr
                  (Inr
                    (Inr
                      (Inl (
                        read1,
                        steps,
                        last,
                        one,
                        byComputing,
                        (rewrite isBare, isOpenWord, isCloseWord, commaDoneSteps others steps one [] stepsSpelt),
                        isOpen,
                        (rewrite assoc,
                            isRead1,
                            quietPeekSecond modes first second (more ++ (elements ++ rest)) open1 open2,
                            peek2 then
                          startBracketPlain second.kind kind starts kindExpr),
                        (rewrite firstPeek then notBracket),
                        ((rewrite elementPeek then notSpread), oneTree),
                        rounds,
                        quietStops inner last innerQuiet inLast,
                        isClose
                      )))))
            )
    | App _ _, _ => (Bool.falseNotTrue atomic).impossible
    | Prefix _ _, _ => (Bool.falseNotTrue atomic).impossible
    | Infix _ _ _ _, _ => (Bool.falseNotTrue atomic).impossible
    | _, never => Void.impossible never

--| A tuple's items after the second, spelt, are its `CommaReads`, each read by `fullLine`.
theorem tupleSteps ∀ (modes: Modes)
    (quiet: Quiet modes)
    (exprs: List Expr) (steps: List (Item, List Item, Expr)) (count: Nat) (last: Item) (rest: List Item) (depth: Nat)
    (deep: nestAll exprs <= depth)
    (spelt: SpeltSteps exprs steps)
    (free: autoFreeAll exprs = True)
    (lineSteps: lineAll (commaReads steps) = True)
    (lineRest: lineAll [last, ..rest] = True)
    (inSteps: inLineAll (commaReads steps) = True)
    (inLast: last.leaf.token.lineStart = False)
    (isClose: last.kind = RParen):
    CommaReads modes (tupleEnds modes) (TreeN (Succ depth) { modes, level = LevelFull }) count steps [last, ..rest] :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty, peekFirst modes last rest (quietStops modes last quiet inLast), isClose
    | [expr, ..more], (comma, read, later, isSteps, isComma, exprSpelt, moreSpelt) =>
      let lineAll1: lineAll [comma, ..read ++ commaReads later] = True :=
        Eq.trans (Eq.cong (taken => lineAll (commaReads taken)) isSteps).flipped lineSteps
      let inAll1: inLineAll [comma, ..read ++ commaReads later] = True :=
        Eq.trans (Eq.cong (taken => inLineAll (commaReads taken)) isSteps).flipped inSteps
      let (lineRead, lineLater) := lineSplit read (commaReads later) (Bool.andRight lineAll1)
      let (inRead, inLater) := inLineSplit read (commaReads later) (Bool.andRight inAll1)
      let (first, inside, isRead, starts) := speltStarts expr read exprSpelt
      let inComma: comma.leaf.token.lineStart = False := notTrueFalse _ (Bool.andLeft inAll1)
      let inFirst: inLineAll [first, ..inside] = True := rewrite <- isRead then inRead
      let openFirst := quietStops modes first quiet (notTrueFalse _ (Bool.andLeft inFirst))
      let (notClose, _, _) := startNotClose first.kind starts
      rewrite isSteps then
        (
          quietStops modes comma quiet inComma,
          isComma,
          runsTupleEndsGo modes count
            (read ++ commaReads later ++ [last, ..rest])
            (rewrite isRead, peekFirst modes first (inside ++ commaReads later ++ [last, ..rest]) openFirst then
              notClose),
          fullLine modes quiet expr read
            (commaReads later ++ [last, ..rest])
            depth
            (arithmetic [deep])
            exprSpelt
            (Bool.andLeft free)
            lineRead
            (lineJoin (commaReads later) [last, ..rest] lineLater lineRest)
            inRead
            (openStepsRest modes quiet later last rest inLater inLast)
            (endsSteps more later last rest moreSpelt (rewrite isClose)),
          tupleSteps modes quiet more later
            (count + 1)
            last
            rest
            depth
            (arithmetic [deep])
            moreSpelt
            (Bool.andRight free)
            lineLater
            lineRest
            inLater
            inLast
            isClose
        )

--| A list's items after the first, spelt, are its `CommaReads`, each read by `fullLine` after no `..`.
theorem listSteps ∀ (modes: Modes)
    (quiet: Quiet modes)
    (exprs: List Expr) (steps: List (Item, List Item, Expr)) (count: Nat) (last: Item) (rest: List Item) (depth: Nat)
    (deep: nestAll exprs <= depth)
    (spelt: SpeltSteps exprs steps)
    (free: autoFreeAll exprs = True)
    (lineSteps: lineAll (commaReads steps) = True)
    (lineRest: lineAll [last, ..rest] = True)
    (inSteps: inLineAll (commaReads steps) = True)
    (inLast: last.leaf.token.lineStart = False)
    (isClose: last.kind = RBracket):
    CommaReads modes (count => modes.at RBracket) (ListElement (TreeN (Succ depth)) modes) count steps [last, ..rest] :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty, peekFirst modes last rest (quietStops modes last quiet inLast), isClose
    | [expr, ..more], (comma, read, later, isSteps, isComma, exprSpelt, moreSpelt) =>
      let lineAll1: lineAll [comma, ..read ++ commaReads later] = True :=
        Eq.trans (Eq.cong (taken => lineAll (commaReads taken)) isSteps).flipped lineSteps
      let inAll1: inLineAll [comma, ..read ++ commaReads later] = True :=
        Eq.trans (Eq.cong (taken => inLineAll (commaReads taken)) isSteps).flipped inSteps
      let (lineRead, lineLater) := lineSplit read (commaReads later) (Bool.andRight lineAll1)
      let (inRead, inLater) := inLineSplit read (commaReads later) (Bool.andRight inAll1)
      let (first, inside, isRead, starts) := speltStarts expr read exprSpelt
      let inComma: comma.leaf.token.lineStart = False := notTrueFalse _ (Bool.andLeft inAll1)
      let inFirst: inLineAll [first, ..inside] = True := rewrite <- isRead then inRead
      let openFirst := quietStops modes first quiet (notTrueFalse _ (Bool.andLeft inFirst))
      let (_, notBracket, notSpread) := startNotClose first.kind starts
      let firstPeek: peekIn modes 0 (read ++ commaReads later ++ [last, ..rest]) = Some first.kind :=
        rewrite isRead then peekFirst modes first (inside ++ commaReads later ++ [last, ..rest]) openFirst
      rewrite isSteps then
        (
          quietStops modes comma quiet inComma,
          isComma,
          (rewrite <- (rewrite firstPeek then notBracket: isSome RBracket
                (peekIn modes 0 (read ++ commaReads later ++ [last, ..rest]))
                = False) then
            runsAtOn modes RBracket (read ++ commaReads later ++ [last, ..rest])),
          (
            (rewrite firstPeek then notSpread),
            fullLine modes quiet expr read
              (commaReads later ++ [last, ..rest])
              depth
              (arithmetic [deep])
              exprSpelt
              (Bool.andLeft free)
              lineRead
              (lineJoin (commaReads later) [last, ..rest] lineLater lineRest)
              inRead
              (openStepsRest modes quiet later last rest inLater inLast)
              (endsSteps more later last rest moreSpelt (rewrite isClose))
          ),
          listSteps modes quiet more later
            (count + 1)
            last
            rest
            depth
            (arithmetic [deep])
            moreSpelt
            (Bool.andRight free)
            lineLater
            lineRest
            inLater
            inLast
            isClose
        )

theorem startNotBrace ∀ (kind: Tok) (starts: leadKind kind = True): (kind == LBrace) = False := cases

--| The read-back of a declaration on its `def`'s line, or with its value on the next (tickets 17d and 17e):
--| `def name: A := b`, with `A` and `b` words, parentheses, tuples, lists and calls spelt by the items between `:` and `:=`
--| and after `:=`, none starting a line but `b`'s first, parses as `parseGroups` runs it to that definition, the words
--| being the items'. Neither may hold a list starting `auto Name` (`typeFree`, `valueFree`): the parser reads that as
--| an implicit binder.
--|
--| Proof idea: `declarationTree`, with the type as a `fullLine` tree and the value as a `fullAnyLine` tree at their
--| nesting depth, the modes of the start and the body being quiet with no line limit.
theorem readsBackLine ∀ (seen: Seen) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr)
    (isDef: keyword.kind = KwDef)
    (isLower: name.kind = Lower)
    (isColon: colon.kind = Colon)
    (isColonEq: colonEq.kind = ColonEq)
    (typeSpelt: Spelt result typeRead)
    (valueSpelt: Spelt value valueRead)
    (typeLine: lineAll typeRead = True)
    (valueLine: lineAll valueRead = True)
    (typeInLine: inLineAll typeRead = True)
    (valueLater: laterInLine valueRead = True)
    (typeFree: result.autoFree1 = True)
    (valueFree: value.autoFree1 = True):
    Parse.run [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]] (() =>
      let decl := declaration seen
      decl)
      = Ok (Definition [] (plainHeader keyword name colon result) (Assigned colonEq.leaf.word.comments value)) :=
  let startQuiet: Quiet Modes.start := { noGuard = byComputing, noCalc = byComputing, noRule = byComputing }
  let body := { Modes.start | recover = True }
  let bodyQuiet: Quiet body := { noGuard = byComputing, noCalc = byComputing, noRule = byComputing }
  let after := [colonEq, ..valueRead]
  let lineAfter: lineAll after = True := rewrite isColonEq, valueLine
  let (first, more, isType, starts) := speltStarts result typeRead typeSpelt
  let allowed: allowBraceOn Modes.start (typeRead ++ after) = Modes.start := rewrite isType
  let noRow: rowOn
    (isSome LBrace (peekIn (allowBraceOn Modes.start (typeRead ++ after)) 0 (typeRead ++ after)))
    (typeRead ++ after)
    = False :=
    rewrite allowed, isType, peekFirst Modes.start first (more ++ after) byComputing, startNotBrace first.kind starts
  let typeTree: Tree { modes = allowBraceOn Modes.start (typeRead ++ after), level = LevelFull } typeRead after
      result :=
    rewrite allowed then
      (
        Succ result.nest1,
        fullLine Modes.start startQuiet result typeRead after result.nest1
          (arithmetic [])
          typeSpelt
          typeFree
          typeLine
          lineAfter
          typeInLine
          byComputing
          (rewrite isColonEq)
      )
  let (valueFirst, valueMore, isValue, _) := speltStarts value valueRead valueSpelt
  let firstSpelt: Spelt value [valueFirst, ..valueMore] := rewrite <- isValue then valueSpelt
  let firstLine: lineAll [valueFirst, ..valueMore] = True := rewrite <- isValue then valueLine
  let firstLater: laterInLine [valueFirst, ..valueMore] = True := rewrite <- isValue then valueLater
  let valueTree: Tree { modes = body, level = LevelFull } valueRead [] value :=
    rewrite isValue then
      (
        Succ value.nest1,
        fullAnyLine body bodyQuiet byComputing value valueFirst valueMore value.nest1
          (arithmetic [])
          firstSpelt
          valueFree
          firstLine
          firstLater
      )
  declarationTree seen keyword name colon colonEq typeRead valueRead result value {
    isDef,
    isLower,
    isColon,
    isColonEq,
    typeReads = (noRow, typeTree),
    valueTree
  }

--| `readsBackLine` for slice 1 trees: `within1` refuses the name `auto`, so no list reads as an implicit binder.
theorem readsBackLineWithin ∀ (seen: Seen) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr)
    (isDef: keyword.kind = KwDef)
    (isLower: name.kind = Lower)
    (isColon: colon.kind = Colon)
    (isColonEq: colonEq.kind = ColonEq)
    (typeSpelt: Spelt result typeRead)
    (valueSpelt: Spelt value valueRead)
    (typeLine: lineAll typeRead = True)
    (valueLine: lineAll valueRead = True)
    (typeInLine: inLineAll typeRead = True)
    (valueLater: laterInLine valueRead = True)
    (typeWithin: result.within1 = True)
    (valueWithin: value.within1 = True):
    Parse.run [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]] (() =>
      let decl := declaration seen
      decl)
      = Ok (Definition [] (plainHeader keyword name colon result) (Assigned colonEq.leaf.word.comments value)) :=
  readsBackLine seen keyword name colon colonEq typeRead valueRead result value isDef isLower isColon isColonEq
      typeSpelt valueSpelt typeLine valueLine typeInLine valueLater
      (autoFreeWithin1 result typeWithin)
      (autoFreeWithin1 value valueWithin)

--| `(a, [b])`, as `wordItem`s from index 5: the value of `readsBackLineExample`.
def exampleItems: List Item := [
  wordItem LParen "(" 5,
  wordItem Lower "a" 6,
  wordItem Comma "," 7,
  wordItem LBracket "[" 8,
  wordItem Lower "b" 9,
  wordItem RBracket "]" 10,
  wordItem RParen ")" 11
]

def exampleValue: Expr :=
  Tuple
    (wordItem LParen "(" 5).leaf.word
    [
      Atom Lower (wordItem Lower "a" 6).leaf.word,
      ListOf
        (wordItem LBracket "[" 8).leaf.word
        [Atom Lower (wordItem Lower "b" 9).leaf.word]
        False
        (wordItem RBracket "]" 10).leaf.word
    ]
    False
    (wordItem RParen ")" 11).leaf.word

--| `def d: A := (a, [b])` on one line: `readsBackLine`'s hypotheses can hold.
theorem readsBackLineExample: Parse.run
      [
        wordItem KwDef "def" 0,
        wordItem Lower "d" 1,
        wordItem Colon ":" 2,
        ..[wordItem Upper "A" 3] ++ [wordItem ColonEq ":=" 4, ..exampleItems]
      ]
      (() =>
        let decl := declaration Seen.start
        decl)
      = Ok
        (Definition []
          (plainHeader
            (wordItem KwDef "def" 0)
            (wordItem Lower "d" 1)
            (wordItem Colon ":" 2)
            (Atom Upper (wordItem Upper "A" 3).leaf.word))
          (Assigned (wordItem ColonEq ":=" 4).leaf.word.comments exampleValue)) :=
  readsBackLine Seen.start
    (wordItem KwDef "def" 0)
    (wordItem Lower "d" 1)
    (wordItem Colon ":" 2)
    (wordItem ColonEq ":=" 4)
    [wordItem Upper "A" 3]
    exampleItems
    (Atom Upper (wordItem Upper "A" 3).leaf.word)
    exampleValue
    byComputing
    byComputing
    byComputing
    byComputing
    (wordItem Upper "A" 3, byComputing, byComputing, byComputing, byComputing)
    (
      wordItem LParen "(" 5,
      [wordItem Lower "a" 6],
      wordItem Comma "," 7,
      [wordItem LBracket "[" 8, wordItem Lower "b" 9, wordItem RBracket "]" 10],
      [],
      wordItem RParen ")" 11,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      (wordItem Lower "a" 6, byComputing, byComputing, byComputing, byComputing),
      (
        wordItem LBracket "[" 8,
        [wordItem Lower "b" 9],
        [],
        wordItem RBracket "]" 10,
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        (wordItem Lower "b" 9, byComputing, byComputing, byComputing, byComputing),
        byComputing
      ),
      byComputing
    )
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing

--| An item for the witnesses below that starts the second line, at column 2.
def lineStartItem (kind: Tok) (text: Text) (index: Nat): Item := {
  leaf = { token = { kind, text, column = 2, lineStart = True }, trivia = Trivia.empty },
  glued = False,
  afterOperand = False,
  afterDot = False,
  index,
  depth = 0,
  lineIndent = 2
}

--| `exampleItems` on a line of their own: `def d: A :=⏎  (a, [b])`.
def ownLineItems: List Item := [
  lineStartItem LParen "(" 5,
  wordItem Lower "a" 6,
  wordItem Comma "," 7,
  wordItem LBracket "[" 8,
  wordItem Lower "b" 9,
  wordItem RBracket "]" 10,
  wordItem RParen ")" 11
]

def ownLineValue: Expr :=
  Tuple
    (lineStartItem LParen "(" 5).leaf.word
    [
      Atom Lower (wordItem Lower "a" 6).leaf.word,
      ListOf
        (wordItem LBracket "[" 8).leaf.word
        [Atom Lower (wordItem Lower "b" 9).leaf.word]
        False
        (wordItem RBracket "]" 10).leaf.word
    ]
    False
    (wordItem RParen ")" 11).leaf.word

--| The value of `def d: A :=⏎  (a, [b])` starts a block.
theorem ownLineStartsBlock: startsBlock { Modes.start | recover = True } (lineStartItem LParen "(" 5) = True :=
  byComputing

--| `def d: A :=⏎  (a, [b])`, the value starting a line of its own: `readsBackLine`'s hypotheses can hold where the
--| value is read as a block (`ownLineStartsBlock`).
theorem readsBackOwnLineExample: Parse.run
      [
        wordItem KwDef "def" 0,
        wordItem Lower "d" 1,
        wordItem Colon ":" 2,
        ..[wordItem Upper "A" 3] ++ [wordItem ColonEq ":=" 4, ..ownLineItems]
      ]
      (() =>
        let decl := declaration Seen.start
        decl)
      = Ok
        (Definition []
          (plainHeader
            (wordItem KwDef "def" 0)
            (wordItem Lower "d" 1)
            (wordItem Colon ":" 2)
            (Atom Upper (wordItem Upper "A" 3).leaf.word))
          (Assigned (wordItem ColonEq ":=" 4).leaf.word.comments ownLineValue)) :=
  readsBackLine Seen.start
    (wordItem KwDef "def" 0)
    (wordItem Lower "d" 1)
    (wordItem Colon ":" 2)
    (wordItem ColonEq ":=" 4)
    [wordItem Upper "A" 3]
    ownLineItems
    (Atom Upper (wordItem Upper "A" 3).leaf.word)
    ownLineValue
    byComputing
    byComputing
    byComputing
    byComputing
    (wordItem Upper "A" 3, byComputing, byComputing, byComputing, byComputing)
    (
      lineStartItem LParen "(" 5,
      [wordItem Lower "a" 6],
      wordItem Comma "," 7,
      [wordItem LBracket "[" 8, wordItem Lower "b" 9, wordItem RBracket "]" 10],
      [],
      wordItem RParen ")" 11,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      (wordItem Lower "a" 6, byComputing, byComputing, byComputing, byComputing),
      (
        wordItem LBracket "[" 8,
        [wordItem Lower "b" 9],
        [],
        wordItem RBracket "]" 10,
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        (wordItem Lower "b" 9, byComputing, byComputing, byComputing, byComputing),
        byComputing
      ),
      byComputing
    )
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing

--| `f x [y]` on a line of its own, from index 5: the value of `readsBackCallExample`.
def callItems: List Item := [
  lineStartItem Lower "f" 5,
  wordItem Lower "x" 6,
  wordItem LBracket "[" 7,
  wordItem Lower "y" 8,
  wordItem RBracket "]" 9
]

def callValue: Expr := App (Atom Lower (lineStartItem Lower "f" 5).leaf.word) [
  Atom Lower (wordItem Lower "x" 6).leaf.word,
  ListOf
    (wordItem LBracket "[" 7).leaf.word
    [Atom Lower (wordItem Lower "y" 8).leaf.word]
    False
    (wordItem RBracket "]" 9).leaf.word
]

--| `def d: A :=⏎  f x [y]`, a call starting its own line: `readsBackLine`'s hypotheses can hold for a call.
theorem readsBackCallExample: Parse.run
      [
        wordItem KwDef "def" 0,
        wordItem Lower "d" 1,
        wordItem Colon ":" 2,
        ..[wordItem Upper "A" 3] ++ [wordItem ColonEq ":=" 4, ..callItems]
      ]
      (() =>
        let decl := declaration Seen.start
        decl)
      = Ok
        (Definition []
          (plainHeader
            (wordItem KwDef "def" 0)
            (wordItem Lower "d" 1)
            (wordItem Colon ":" 2)
            (Atom Upper (wordItem Upper "A" 3).leaf.word))
          (Assigned (wordItem ColonEq ":=" 4).leaf.word.comments callValue)) :=
  readsBackLine Seen.start
    (wordItem KwDef "def" 0)
    (wordItem Lower "d" 1)
    (wordItem Colon ":" 2)
    (wordItem ColonEq ":=" 4)
    [wordItem Upper "A" 3]
    callItems
    (Atom Upper (wordItem Upper "A" 3).leaf.word)
    callValue
    byComputing
    byComputing
    byComputing
    byComputing
    (wordItem Upper "A" 3, byComputing, byComputing, byComputing, byComputing)
    (
      [lineStartItem Lower "f" 5],
      [wordItem Lower "x" 6],
      [
        (
          [wordItem LBracket "[" 7, wordItem Lower "y" 8, wordItem RBracket "]" 9],
          ListOf
            (wordItem LBracket "[" 7).leaf.word
            [Atom Lower (wordItem Lower "y" 8).leaf.word]
            False
            (wordItem RBracket "]" 9).leaf.word
        )
      ],
      byComputing,
      byComputing,
      byComputing,
      (lineStartItem Lower "f" 5, byComputing, byComputing, byComputing, byComputing),
      (wordItem Lower "x" 6, byComputing, byComputing, byComputing, byComputing),
      (
        [wordItem LBracket "[" 7, wordItem Lower "y" 8, wordItem RBracket "]" 9],
        [],
        byComputing,
        byComputing,
        (
          wordItem LBracket "[" 7,
          [wordItem Lower "y" 8],
          [],
          wordItem RBracket "]" 9,
          byComputing,
          byComputing,
          byComputing,
          byComputing,
          byComputing,
          byComputing,
          (wordItem Lower "y" 8, byComputing, byComputing, byComputing, byComputing),
          byComputing
        ),
        byComputing
      )
    )
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing

--| `1` glued to the `-` before it.
def gluedOne: Item := { wordItem Num "1" 8 | glued = True }

def signItems: List Item :=
  [wordItem Bang "!" 5, wordItem LParen "(" 6, wordItem Minus "-" 7, gluedOne, wordItem RParen ")" 9]

def signValue: Expr :=
  Prefix
    (wordItem Bang "!" 5).leaf.word
    (Paren
      (wordItem LParen "(" 6).leaf.word
      (Prefix (wordItem Minus "-" 7).leaf.word (Atom Num gluedOne.leaf.word))
      (wordItem RParen ")" 9).leaf.word)

--| `def d: A := !(-1)`: a sign before a bracket, and `-` glued to a numeral, which reads as one atom.
theorem readsBackSignExample: Parse.run
      [
        wordItem KwDef "def" 0,
        wordItem Lower "d" 1,
        wordItem Colon ":" 2,
        ..[wordItem Upper "A" 3] ++ [wordItem ColonEq ":=" 4, ..signItems]
      ]
      (() =>
        let decl := declaration Seen.start
        decl)
      = Ok
        (Definition []
          (plainHeader
            (wordItem KwDef "def" 0)
            (wordItem Lower "d" 1)
            (wordItem Colon ":" 2)
            (Atom Upper (wordItem Upper "A" 3).leaf.word))
          (Assigned (wordItem ColonEq ":=" 4).leaf.word.comments signValue)) :=
  readsBackLine Seen.start
    (wordItem KwDef "def" 0)
    (wordItem Lower "d" 1)
    (wordItem Colon ":" 2)
    (wordItem ColonEq ":=" 4)
    [wordItem Upper "A" 3]
    signItems
    (Atom Upper (wordItem Upper "A" 3).leaf.word)
    signValue
    byComputing
    byComputing
    byComputing
    byComputing
    (wordItem Upper "A" 3, byComputing, byComputing, byComputing, byComputing)
    (
      wordItem Bang "!" 5,
      [wordItem LParen "(" 6, wordItem Minus "-" 7, gluedOne, wordItem RParen ")" 9],
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      (
        wordItem LParen "(" 6,
        [wordItem Minus "-" 7, gluedOne],
        wordItem RParen ")" 9,
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        (
          wordItem Minus "-" 7,
          [gluedOne],
          byComputing,
          byComputing,
          byComputing,
          byComputing,
          byComputing,
          (gluedOne, byComputing, byComputing, byComputing, byComputing)
        )
      )
    )
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing

--| An item for the witnesses with its spacing: glued to the token before, which ends an operand or not.
def spacedItem (kind: Tok) (text: Text) (index: Nat) (glued afterOperand: Bool): Item :=
  { wordItem kind text index | glued, afterOperand }

def signArgItems: List Item := [
  spacedItem Minus "-" 6 False True,
  spacedItem Lower "x" 7 True False,
  spacedItem Bang "!" 8 False True,
  spacedItem Lower "y" 9 True False,
  spacedItem Minus "-" 10 False True,
  spacedItem Num "1" 11 True False
]

def signArgValue: Expr := App (Atom Lower (wordItem Lower "f" 5).leaf.word) [
  Prefix (spacedItem Minus "-" 6 False True).leaf.word (Atom Lower (spacedItem Lower "x" 7 True False).leaf.word),
  Prefix (spacedItem Bang "!" 8 False True).leaf.word (Atom Lower (spacedItem Lower "y" 9 True False).leaf.word),
  Prefix (spacedItem Minus "-" 10 False True).leaf.word (Atom Num (spacedItem Num "1" 11 True False).leaf.word)
]

--| `def d: A := f -x !y -1`: signs as arguments, the last a negative numeral.
theorem readsBackSignArgExample: Parse.run
      [
        wordItem KwDef "def" 0,
        wordItem Lower "d" 1,
        wordItem Colon ":" 2,
        ..[wordItem Upper "A" 3] ++ [wordItem ColonEq ":=" 4, wordItem Lower "f" 5, ..signArgItems]
      ]
      (() =>
        let decl := declaration Seen.start
        decl)
      = Ok
        (Definition []
          (plainHeader
            (wordItem KwDef "def" 0)
            (wordItem Lower "d" 1)
            (wordItem Colon ":" 2)
            (Atom Upper (wordItem Upper "A" 3).leaf.word))
          (Assigned (wordItem ColonEq ":=" 4).leaf.word.comments signArgValue)) :=
  readsBackLine Seen.start
    (wordItem KwDef "def" 0)
    (wordItem Lower "d" 1)
    (wordItem Colon ":" 2)
    (wordItem ColonEq ":=" 4)
    [wordItem Upper "A" 3]
    [wordItem Lower "f" 5, ..signArgItems]
    (Atom Upper (wordItem Upper "A" 3).leaf.word)
    signArgValue
    byComputing
    byComputing
    byComputing
    byComputing
    (wordItem Upper "A" 3, byComputing, byComputing, byComputing, byComputing)
    (
      [wordItem Lower "f" 5],
      [spacedItem Minus "-" 6 False True, spacedItem Lower "x" 7 True False],
      [
        (
          [spacedItem Bang "!" 8 False True, spacedItem Lower "y" 9 True False],
          Prefix (spacedItem Bang "!" 8 False True).leaf.word (Atom Lower (spacedItem Lower "y" 9 True False).leaf.word)
        ),
        (
          [spacedItem Minus "-" 10 False True, spacedItem Num "1" 11 True False],
          Prefix (spacedItem Minus "-" 10 False True).leaf.word (Atom Num (spacedItem Num "1" 11 True False).leaf.word)
        )
      ],
      byComputing,
      byComputing,
      byComputing,
      (wordItem Lower "f" 5, byComputing, byComputing, byComputing, byComputing),
      (
        spacedItem Minus "-" 6 False True,
        [spacedItem Lower "x" 7 True False],
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        (spacedItem Lower "x" 7 True False, byComputing, byComputing, byComputing, byComputing)
      ),
      (
        [spacedItem Bang "!" 8 False True, spacedItem Lower "y" 9 True False],
        [
          (
            [spacedItem Minus "-" 10 False True, spacedItem Num "1" 11 True False],
            Prefix
              (spacedItem Minus "-" 10 False True).leaf.word
              (Atom Num (spacedItem Num "1" 11 True False).leaf.word)
          )
        ],
        byComputing,
        byComputing,
        (
          spacedItem Bang "!" 8 False True,
          [spacedItem Lower "y" 9 True False],
          byComputing,
          byComputing,
          byComputing,
          byComputing,
          byComputing,
          (spacedItem Lower "y" 9 True False, byComputing, byComputing, byComputing, byComputing)
        ),
        (
          [spacedItem Minus "-" 10 False True, spacedItem Num "1" 11 True False],
          [],
          byComputing,
          byComputing,
          (
            spacedItem Minus "-" 10 False True,
            [spacedItem Num "1" 11 True False],
            byComputing,
            byComputing,
            byComputing,
            byComputing,
            byComputing,
            (spacedItem Num "1" 11 True False, byComputing, byComputing, byComputing, byComputing)
          ),
          byComputing
        )
      )
    )
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing

--| `-x` after an operand: `signStartsAtom`'s hypotheses can hold.
theorem signStartsAtomExample: startsAtomKind Modes.start Minus [
      spacedItem Minus "-" 6 False True,
      spacedItem Lower "x" 7 True False
    ]
      = True :=
  signStartsAtom Modes.start Minus
    [spacedItem Minus "-" 6 False True, spacedItem Lower "x" 7 True False]
    byComputing
    byComputing

def arrowType: Expr :=
  Infix InfixArrow
    (Atom Upper (wordItem Upper "A" 3).leaf.word)
    (wordItem Arrow "->" 4).leaf.word
    (Infix InfixArrow
      (Atom Upper (wordItem Upper "B" 5).leaf.word)
      (wordItem Arrow "->" 6).leaf.word
      (Atom Upper (wordItem Upper "C" 7).leaf.word))

--| `def d: A -> B -> C := x`: arrows nest to the right, each result read in full.
theorem readsBackArrowExample: Parse.run
      [
        wordItem KwDef "def" 0,
        wordItem Lower "d" 1,
        wordItem Colon ":" 2,
        ..[
          wordItem Upper "A" 3,
          wordItem Arrow "->" 4,
          wordItem Upper "B" 5,
          wordItem Arrow "->" 6,
          wordItem Upper "C" 7
        ]
          ++ [wordItem ColonEq ":=" 8, wordItem Lower "x" 9]
      ]
      (() =>
        let decl := declaration Seen.start
        decl)
      = Ok
        (Definition []
          (plainHeader (wordItem KwDef "def" 0) (wordItem Lower "d" 1) (wordItem Colon ":" 2) arrowType)
          (Assigned (wordItem ColonEq ":=" 8).leaf.word.comments (Atom Lower (wordItem Lower "x" 9).leaf.word))) :=
  readsBackLine Seen.start
    (wordItem KwDef "def" 0)
    (wordItem Lower "d" 1)
    (wordItem Colon ":" 2)
    (wordItem ColonEq ":=" 8)
    [wordItem Upper "A" 3, wordItem Arrow "->" 4, wordItem Upper "B" 5, wordItem Arrow "->" 6, wordItem Upper "C" 7]
    [wordItem Lower "x" 9]
    arrowType
    (Atom Lower (wordItem Lower "x" 9).leaf.word)
    byComputing
    byComputing
    byComputing
    byComputing
    (
      [wordItem Upper "A" 3],
      wordItem Arrow "->" 4,
      [wordItem Upper "B" 5, wordItem Arrow "->" 6, wordItem Upper "C" 7],
      byComputing,
      byComputing,
      byComputing,
      byComputing,
      (wordItem Upper "A" 3, byComputing, byComputing, byComputing, byComputing),
      (
        [wordItem Upper "B" 5],
        wordItem Arrow "->" 6,
        [wordItem Upper "C" 7],
        byComputing,
        byComputing,
        byComputing,
        byComputing,
        (wordItem Upper "B" 5, byComputing, byComputing, byComputing, byComputing),
        (wordItem Upper "C" 7, byComputing, byComputing, byComputing, byComputing)
      )
    )
    (wordItem Lower "x" 9, byComputing, byComputing, byComputing, byComputing)
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing
    byComputing

--| A group closed at once: `groupLine`'s hypotheses can hold.
theorem groupLineExample: headPlain [wordItem Lower "a" 1].reverse = True :=
  groupLine
    [LParen]
    []
    [wordItem Lower "a" 1, wordItem RParen ")" 2]
    [wordItem Lower "a" 1]
    byComputing
    byComputing
    byComputing

theorem firstKindExample: (wordItem Lower "a" 0).kind = (wordItem Lower "a" 0).kind :=
  firstKind (wordItem Lower "a" 0) (wordItem Lower "a" 0) [] [] byComputing
