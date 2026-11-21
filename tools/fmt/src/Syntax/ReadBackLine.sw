--| Slice 1's read-back vocabulary (tickets 17d to 17g): how a declaration's items spell its type and value, and what
--| the items' kinds and the parser's modes tell about a reading. The read-back itself, over any number of lines, is
--| `Syntax.ReadBackHungTop.readsBackHung`, built on these.
--|
--| The items are related to the tree by `Spelt` (each node's tokens in order, each item carrying the node's word, a
--| comma between bracket items and none after the last); the look-aheads are discharged by `Syntax.ReadBackEnds`
--| from the item kinds (`lineAll`: words, brackets, commas and `:=`) and from what follows each node. In `Quiet` modes
--| only a line start stops a reading. No list that starts a full expression may start with `auto` on a type's name
--| (`Syntax.AutoPlaced.Expr.autoPlaced`), which reads there as an implicit binder. `-` glued to a numeral reads as
--| one atom, as `Spelt` says the parser sees it, and a sign may start a call's argument, glued to its atom and spaced
--| from what precedes it (`argumentGlue`). Binary operators
--| read as the parser's chains: each operator ends the operand before it (`opEnds`) and is spaced from the one after
--| (`operandApart`, so `a - x` is no call `a -x`); `&&` and `||` read as `groupLogic` regroups them, the chain
--| flattened into its first comparison and links (`orFlat`, `conjFlat`).

namespace Syntax.ReadBackLine
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Void, byDecision)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackRuns (plainHeader)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackEnds (..)
import Syntax.AutoPlaced (..)

--| Modes in which nothing but a line start stops a reading: no guard, `calc` or `rewrite` rule, as in a declaration's
--| type and body, inside their brackets, and in a block's line.
type Quiet (modes: Modes): Prop = {
  noGuard: modes.guard = False,
  noCalc: modes.inCalc = False,
  noRule: modes.rewriteRule = None
}

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
  Bool.notTrue _ open

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
  | Lower |
      Upper |
      Num |
      Float |
      Minus |
      Star |
      Slash |
      Percent |
      Plus |
      PlusPlus |
      Equals |
      EqEq |
      NotEq |
      Lt |
      Le |
      Gt |
      Ge |
      AndAnd |
      OrOr |
      Bang |
      Arrow |
      ColonEq |
      LParen |
      RParen |
      LBracket |
      RBracket |
      Comma => True
  | _ => False

def lineAll: List Item → Bool
  | [] => True
  | [item, ..rest] => lineKind item.kind && lineAll rest

--| The kinds an expression of this part starts with.
def startKind: Tok → Bool
  | Lower | Upper | Num | Float | LParen | LBracket => True
  | _ => False

--| The signs a prefix of this part is written with.
def signKind: Tok → Bool
  | Minus | Bang => True
  | _ => False

--| The kinds any expression of this part starts with: an atom's or a sign.
def leadKind: Tok → Bool
  | Lower | Upper | Num | Float | LParen | LBracket | Minus | Bang => True
  | _ => False

--| The binary operators of this part.
def binaryTok: Tok → Bool
  | Star | Slash | Percent | Plus | Minus | PlusPlus | Equals | EqEq | NotEq | Lt | Le | Gt | Ge | AndAnd | OrOr => True
  | _ => False

--| The operator token an infix of this kind is spelt with: `->` for an arrow, a binary operator of this part.
def infixTok (kind: InfixKind) (tok: Tok): Bool := match kind with
  | InfixArrow => tok == Arrow
  | InfixBinary => binaryTok tok
  | _ => False

--| `infixLevel` by the operator's token: how tightly it binds in the parser's ladder.
def tokLevel: Tok → Nat
  | Arrow => 1
  | OrOr => 4
  | AndAnd => 5
  | Equals | EqEq | NotEq | Lt | Le | Gt | Ge => 6
  | PlusPlus => 12
  | Plus | Minus => 14
  | Star | Slash | Percent => 16
  | _ => 0

--| An infix's right operand doesn't touch its operator: so `a - x` isn't read as the call `a -x`.
def operandApart: List Item → Bool
  | [first, .._] => !first.glued
  | [] => True

--| An expression that starts with a sign: a prefix, or a call or an infix whose head or left side does.
def Expr.signed: Expr → Bool
  | Prefix _ _ => True
  | App head _ | Infix _ head _ _ => head.signed
  | _ => False

--| No infix operator at the top: what `unary` reads whole.
def Expr.unary: Expr → Bool
  | Infix _ _ _ _ => False
  | _ => True

--| `read` spells `expr`: the node's tokens in order, each an item of the token's kind carrying the node's word, a
--| comma between each two bracket items and none after the last (`comma = False`); a tuple has two items or more. A
--| prefix is its sign and its operand, no infix, the two read as a negative numeral (the parser's `negativeNumeral`)
--| only when the operand is a numeral: a `-` before a numeral but apart from it, as across a comment in
--| `(- -- c⏎  1)`, reads as a sign on its operand. An infix (an arrow, or a
--| binary operator of `binaryTok`, `&&` and `||` among them) is its left side, its operator and its right side: the operator's text binds as its
--| token does (`tokLevel`), the operands sit at the levels `shaped` asks (`leftNeeds`, `rightNeeds`), and the right
--| operand doesn't touch the operator (`operandApart`).
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
      ∧ headFits head headRead = True
      ∧ argumentFits argument argRead = True
      ∧ Spelt head headRead
      ∧ Spelt argument argRead
      ∧ SpeltArgs more steps
  | Prefix operator operand, read =>
    ∃ (sign: Item) (more: List Item) => read = [sign, ..more]
      ∧ signKind sign.kind = True
      ∧ sign.leaf.word = operator
      ∧ (negativeNumeral [sign, ..more] = True → operand.numeral1 = True)
      ∧ operand.unary = True
      ∧ Spelt operand more
  | Infix kind left operator right, read =>
    ∃ (leftRead: List Item) (op: Item) (rightRead: List Item) => read = leftRead ++ [op, ..rightRead]
      ∧ infixTok kind op.kind = True
      ∧ op.leaf.word = operator
      ∧ infixLevel kind operator.text = tokLevel op.kind
      ∧ leftNeeds kind operator.text <= left.level
      ∧ rightNeeds kind operator.text <= right.level
      ∧ operandApart rightRead = True
      ∧ Spelt left leftRead
      ∧ Spelt right rightRead
  | _, _ => Void

def Expr.prefix: Expr → Bool
  | Prefix _ _ => True
  | _ => False

--| A call's head: an atom or a bracket, or a sign read as a negative numeral (`-1 n`), the one sign `unaryNext` hands
--| to `app`.
def headFits (head: Expr) (read: List Item): Bool := head.primary || (head.prefix && negativeNumeral read)

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
def Expr.signArg: Expr → Bool
  | Prefix _ operand | operand => operand.primary

--| A sign starting an argument is glued to what follows it and not to what precedes it, which ends an operand: the
--| spacing `argumentPrefix` asks of `f -x`.
def argumentGlue: List Item → Bool
  | [first, next, .._] => !signKind first.kind || (first.afterOperand && (!first.glued && next.glued))
  | _ => True

--| An argument of this part, its sign (if any) spaced as an argument's.
def argumentFits (argument: Expr) (read: List Item): Bool := argument.signArg && argumentGlue read

--| The bracket items after the first (or first two), as `CommaReads`' steps: a comma, then an item's reading.
def SpeltSteps: List Expr → List (Item, List Item, Expr) → Prop
  | [], steps => steps = []
  | [expr, ..rest], steps =>
    ∃ (comma: Item) (read: List Item) (later: List (Item, List Item, Expr)) => steps = [(comma, read, expr), ..later]
      ∧ comma.kind = Comma
      ∧ Spelt expr read
      ∧ SpeltSteps rest later

--| How deep `self` calls nest when the parser reads the expression: one more for each bracket.
def Expr.nest: Expr → Nat
  | Paren _ inner _ => inner.nest + 1
  | Tuple _ items _ _ | ListOf _ items _ _ => nestAll items + 1
  | App head arguments => head.nest + nestAll arguments + 1
  | Prefix _ operand => operand.nest + 1
  | Infix _ left _ right => left.nest + right.nest + 1
  | _ => 0

def nestAll: List Expr → Nat
  | [] => 0
  | [expr, ..rest] => expr.nest + nestAll rest

theorem wordStart ∀ (kind: Tok) (word: kind.wordWithin1 = True): startKind kind = True := cases

theorem startLead ∀ (kind: Tok) (starts: startKind kind = True): leadKind kind = True := cases

theorem signLead ∀ (kind: Tok) (signed: signKind kind = True): leadKind kind = True := cases

--| An atom or a bracket is no prefix.
theorem atomicUnsigned ∀ (expr: Expr) (atomic: expr.primary = True): expr.signed = False := match expr, atomic with
  | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _, _ => byComputing
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
    | Infix _ left _ _, (leftRead, arrow, rightRead, isRead, _, _, _, _, _, _, leftSpelt, _) =>
      let (first, more, isLeft, starts) := speltStarts left leftRead leftSpelt
      (first, more ++ [arrow, ..rightRead], (rewrite isRead, isLeft), starts)
    | _, never => Void.impossible never

--| A spelt expression other than a prefix starts with an atom's first kind.
theorem speltPlainStarts ∀ (expr: Expr) (read: List Item)
    (spelt: Spelt expr read)
    (unsigned: expr.signed = False):
    ∃ (item: Item) (more: List Item) => read = [item, ..more] ∧ startKind item.kind = True :=
  match expr, spelt, unsigned with
    | Atom kind word, (item, isRead, isKind, _, word), _ => (item, [], isRead, rewrite isKind then wordStart kind word)
    | Paren _ _ _, (first, inside, last, isRead, isOpen, _), _ => (first, inside ++ [last], isRead, rewrite isOpen)
    | Tuple _ [_, _, .._] _ _, (first, read1, separator, read2, steps, last, isRead, _, isOpen, _), _ =>
      (first, read1 ++ ([separator, ..read2] ++ (commaReads steps ++ [last])), isRead, rewrite isOpen)
    | ListOf _ [] _ _, (first, last, isRead, _, isOpen, _), _ => (first, [last], isRead, rewrite isOpen)
    | ListOf _ [_, .._] _ _, (first, read1, steps, last, isRead, _, isOpen, _), _ =>
      (first, read1 ++ (commaReads steps ++ [last]), isRead, rewrite isOpen)
    | App head [_, .._], (headRead, argRead, steps, isRead, _, _, headSpelt, _), unsigned =>
      let (first, more, isHead, starts) := speltPlainStarts head headRead headSpelt unsigned
      (first, more ++ (argRead ++ Parse.loopReads [] steps), (rewrite isRead, isHead), starts)
    | Prefix _ _, _, never => (Bool.falseNotTrue never.flipped).impossible
    | Infix _ left _ _, (leftRead, arrow, rightRead, isRead, _, _, _, _, _, _, leftSpelt, _), unsigned =>
      let (first, more, isLeft, starts) := speltPlainStarts left leftRead leftSpelt unsigned
      (first, more ++ [arrow, ..rightRead], (rewrite isRead, isLeft), starts)
    | _, never, _ => Void.impossible never

--| The kinds inside an expression of this part: `lineKind` without `:=`.
def exprKind: Tok → Bool
  | Lower |
      Upper |
      Num |
      Float |
      Minus |
      Star |
      Slash |
      Percent |
      Plus |
      PlusPlus |
      Equals |
      EqEq |
      NotEq |
      Lt |
      Le |
      Gt |
      Ge |
      AndAnd |
      OrOr |
      Bang |
      Arrow |
      LParen |
      RParen |
      LBracket |
      RBracket |
      Comma => True
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
          | True | False => byComputing

theorem exprLineKind ∀ (kind: Tok) (expr: exprKind kind = True): lineKind kind = True := cases

--| An expression's items are of the kinds read on a line.
theorem exprLine ∀ (items: List Item) (expr: exprAll items = True): lineAll items = True := match items with
  | [] => byComputing
  | [item, ..more] => rewrite exprLineKind item.kind (Bool.andLeft expr), exprLine more (Bool.andRight expr)

--| An infix's operator is a kind of this part.
theorem infixExpr ∀ (kind: InfixKind) (tok: Tok) (isOp: infixTok kind tok = True): exprKind tok = True :=
  match kind, isOp with
    | InfixArrow, isOp => rewrite DecEq.sound isOp
    | InfixBinary, isOp => binaryExpr tok isOp
    | _, never => (Bool.falseNotTrue never).impossible

theorem binaryExpr ∀ (tok: Tok) (isOp: binaryTok tok = True): exprKind tok = True := cases

theorem infixNotUpper ∀ (kind: InfixKind) (tok: Tok) (isOp: infixTok kind tok = True): (tok == Upper) = False :=
  match kind, isOp with
    | InfixArrow, isOp => rewrite DecEq.sound isOp
    | InfixBinary, isOp => binaryNotUpper tok isOp
    | _, never => (Bool.falseNotTrue never).impossible

theorem binaryNotUpper ∀ (tok: Tok) (isOp: binaryTok tok = True): (tok == Upper) = False := cases

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
    | Infix kind left _ right, (leftRead, arrow, rightRead, isRead, isOp, _, _, _, _, _, leftSpelt, rightSpelt) =>
      rewrite isRead,
          exprAppend leftRead [arrow, ..rightRead],
          speltExpr left leftRead leftSpelt,
          infixExpr kind arrow.kind isOp,
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
    | Upper | Num | Float | LParen | LBracket, _ => byComputing
    | other, never => (Bool.falseNotTrue never).impossible

theorem startBracketPlain ∀ (first second: Tok)
    (starts: leadKind first = True)
    (expr: exprKind second = True):
    ((isSome Lower (Some first) || isSome KwDecreasing (Some first)) && isSome ColonEq (Some second)) = False :=
  match first, starts with
    | Lower, _ => rewrite exprNotColonEq second expr
    | Upper | Num | Float | LParen | LBracket | Minus | Bang, _ => byComputing
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

def exprHead: List Item → Bool
  | [] => False
  | [item, .._] => exprKind item.kind

--| The first item is no section operator.
def headPlain: List Item → Bool
  | [] => True
  | [item, .._] => !item.kind.isSectionOperator

theorem ontoAppend ∀ (first rest found: List Item):
    List.reverseOnto (first ++ rest) found = List.reverseOnto rest (List.reverseOnto first found) :=
  match first with
    | [] => byComputing
    | [item, ..more] => ontoAppend more rest [item, ..found]

--| An item that opens and closes no bracket is collected as it is.
theorem groupPlain ∀ (open: Tok) (outer: List Tok) (found: List Item) (item: Item) (rest: List Item)
    (notOpen: item.kind.isOpener = False)
    (notClose: item.kind.isCloser = False):
    groupInside [open, ..outer] found [item, ..rest] = groupInside [open, ..outer] [item, ..found] rest :=
  rewrite notOpen, notClose

theorem wordFlat ∀ (kind: Tok) (word: kind.wordWithin1 = True): kind.isOpener = False ∧ kind.isCloser = False := cases

theorem signFlat ∀ (kind: Tok) (signed: signKind kind = True): kind.isOpener = False ∧ kind.isCloser = False := cases

theorem binaryFlat ∀ (tok: Tok) (isOp: binaryTok tok = True): tok.isOpener = False ∧ tok.isCloser = False := cases

theorem infixFlat ∀ (kind: InfixKind) (tok: Tok)
    (isOp: infixTok kind tok = True):
    tok.isOpener = False ∧ tok.isCloser = False :=
  match kind, isOp with
    | InfixArrow, isOp => rewrite DecEq.sound isOp then (byComputing, byComputing)
    | InfixBinary, isOp => binaryFlat tok isOp
    | _, never => (Bool.falseNotTrue never).impossible

theorem wordNotSection ∀ (kind: Tok) (word: kind.wordWithin1 = True): kind.isSectionOperator = False := cases

--| Inside an open group, a spelt expression's items are collected as they are: every bracket it opens, it closes.
--|
--| Proof idea: by induction on the expression; an opener pushes its kind, the inside is walked by induction, and its
--| closer pairs it and pops back to the group outside, which is still open; words, signs, commas and operators open
--| and close nothing.
theorem groupInsideReverse ∀ (expr: Expr) (read: List Item)
    (spelt: Spelt expr read)
    (open: Tok) (outer: List Tok) (found rest: List Item):
    groupInside [open, ..outer] found (read ++ rest) = groupInside [open, ..outer] (List.reverseOnto read found) rest :=
  match expr, spelt with
    | Atom kind word, (item, isRead, isKind, _, word) =>
      let (notOpen, notClose) := wordFlat kind word
      rewrite isRead then
        groupPlain open outer found item rest (rewrite isKind then notOpen) (rewrite isKind then notClose)
    | Paren _ inner _, (first, inside, last, isRead, isOpen, _, isClose, _, innerSpelt) =>
      rewrite isRead,
          isOpen,
          List.appendAssoc inside [last] rest,
          groupInsideReverse inner inside innerSpelt LParen [open, ..outer] [first, ..found] [last, ..rest],
          isClose,
          ontoAppend inside [last] [first, ..found]
    | Tuple _ [one, two, ..others] _ _, (first, read1, separator, read2, steps, last, isRead, _, isOpen, _, isComma,
        isClose, _, oneSpelt, twoSpelt, stepsSpelt) =>
      let body := read1 ++ ([separator, ..read2] ++ commaReads steps)
      let shape: (read1 ++ ([separator, ..read2] ++ (commaReads steps ++ [last]))) ++ rest = body ++ [last, ..rest] :=
        rewrite repeatedly [List.appendAssoc] then byComputing
      rewrite isRead,
          isOpen,
          shape,
          tupleWalk one two others read1 separator read2 steps oneSpelt isComma twoSpelt stepsSpelt LParen
            [open, ..outer]
            [first, ..found]
            [last, ..rest],
          isClose,
          ontoAppend read1 ([separator, ..read2] ++ (commaReads steps ++ [last])) [first, ..found],
          ontoAppend read1 ([separator, ..read2] ++ commaReads steps) [first, ..found],
          <- List.appendAssoc read2 (commaReads steps) [last],
          ontoAppend (read2 ++ commaReads steps) [last] [separator, ..List.reverseOnto read1 [first, ..found]]
    | ListOf _ [] _ _, (first, last, isRead, _, isOpen, _, isClose, _) => rewrite isRead, isOpen, isClose
    | ListOf _ [one, ..others] _ _, (first, read1, steps, last, isRead, _, isOpen, _, isClose, _, oneSpelt,
        stepsSpelt) =>
      rewrite isRead,
          isOpen,
          List.appendAssoc read1 (commaReads steps ++ [last]) rest,
          groupInsideReverse one read1 oneSpelt LBracket
            [open, ..outer]
            [first, ..found]
            ((commaReads steps ++ [last]) ++ rest),
          List.appendAssoc (commaReads steps) [last] rest,
          stepsWalk others steps stepsSpelt LBracket [open, ..outer] (List.reverseOnto read1 [first, ..found]) [
            last,
            ..rest
          ],
          isClose,
          ontoAppend read1 (commaReads steps ++ [last]) [first, ..found],
          ontoAppend (commaReads steps) [last] (List.reverseOnto read1 [first, ..found])
    | App head [argument, ..more], (headRead, argRead, steps, isRead, _, _, headSpelt, argSpelt, argsSpelt) =>
      rewrite isRead,
          List.appendAssoc headRead (argRead ++ Parse.loopReads [] steps) rest,
          groupInsideReverse head headRead headSpelt open outer found ((argRead ++ Parse.loopReads [] steps) ++ rest),
          List.appendAssoc argRead (Parse.loopReads [] steps) rest,
          groupInsideReverse argument argRead argSpelt open outer
            (List.reverseOnto headRead found)
            (Parse.loopReads [] steps ++ rest),
          argsWalk more steps argsSpelt open outer (List.reverseOnto argRead (List.reverseOnto headRead found)) rest,
          ontoAppend headRead (argRead ++ Parse.loopReads [] steps) found,
          ontoAppend argRead (Parse.loopReads [] steps) (List.reverseOnto headRead found)
    | Prefix _ operand, (sign, more, isRead, signed, _, _, _, operandSpelt) =>
      let (notOpen, notClose) := signFlat sign.kind signed
      rewrite isRead,
          groupPlain open outer found sign (more ++ rest) notOpen notClose,
          groupInsideReverse operand more operandSpelt open outer [sign, ..found] rest
    | Infix kind left _ right, (leftRead, op, rightRead, isRead, isOp, _, _, _, _, _, leftSpelt, rightSpelt) =>
      let (notOpen, notClose) := infixFlat kind op.kind isOp
      rewrite isRead,
          List.appendAssoc leftRead [op, ..rightRead] rest,
          groupInsideReverse left leftRead leftSpelt open outer found ([op, ..rightRead] ++ rest),
          groupPlain open outer (List.reverseOnto leftRead found) op (rightRead ++ rest) notOpen notClose,
          groupInsideReverse right rightRead rightSpelt open outer [op, ..List.reverseOnto leftRead found] rest,
          ontoAppend leftRead [op, ..rightRead] found
    | _, never => Void.impossible never

--| A tuple's items before its closer, walked as `groupInsideReverse` walks each.
theorem tupleWalk ∀ (one two: Expr) (others: List Expr) (read1: List Item) (separator: Item)
    (read2: List Item) (steps: List (Item, List Item, Expr))
    (oneSpelt: Spelt one read1)
    (isComma: separator.kind = Comma)
    (twoSpelt: Spelt two read2)
    (stepsSpelt: SpeltSteps others steps)
    (open: Tok) (outer: List Tok) (found rest: List Item):
    groupInside [open, ..outer] found ((read1 ++ ([separator, ..read2] ++ commaReads steps)) ++ rest)
      = groupInside
        [open, ..outer]
        (List.reverseOnto (read1 ++ ([separator, ..read2] ++ commaReads steps)) found)
        rest :=
  rewrite List.appendAssoc read1 ([separator, ..read2] ++ commaReads steps) rest,
      groupInsideReverse one read1 oneSpelt open outer found (([separator, ..read2] ++ commaReads steps) ++ rest),
      groupPlain open outer
        (List.reverseOnto read1 found)
        separator
        ((read2 ++ commaReads steps) ++ rest)
        (rewrite isComma)
        (rewrite isComma),
      List.appendAssoc read2 (commaReads steps) rest,
      groupInsideReverse two read2 twoSpelt open outer
        [separator, ..List.reverseOnto read1 found]
        (commaReads steps ++ rest),
      stepsWalk others steps stepsSpelt open outer
        (List.reverseOnto read2 [separator, ..List.reverseOnto read1 found])
        rest,
      ontoAppend read1 ([separator, ..read2] ++ commaReads steps) found,
      ontoAppend read2 (commaReads steps) [separator, ..List.reverseOnto read1 found]

theorem stepsWalk ∀ (exprs: List Expr) (steps: List (Item, List Item, Expr))
    (spelt: SpeltSteps exprs steps)
    (open: Tok) (outer: List Tok) (found rest: List Item):
    groupInside [open, ..outer] found (commaReads steps ++ rest)
      = groupInside [open, ..outer] (List.reverseOnto (commaReads steps) found) rest :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty
    | [expr, ..more], (comma, read, later, isSteps, isComma, exprSpelt, laterSpelt) =>
      rewrite isSteps,
          List.appendAssoc [comma, ..read] (commaReads later) rest,
          groupPlain open outer found comma (read ++ (commaReads later ++ rest)) (rewrite isComma) (rewrite isComma),
          groupInsideReverse expr read exprSpelt open outer [comma, ..found] (commaReads later ++ rest),
          stepsWalk more later laterSpelt open outer (List.reverseOnto read [comma, ..found]) rest,
          ontoAppend [comma, ..read] (commaReads later) found

theorem argsWalk ∀ (exprs: List Expr) (steps: List (List Item, Expr))
    (spelt: SpeltArgs exprs steps)
    (open: Tok) (outer: List Tok) (found rest: List Item):
    groupInside [open, ..outer] found (Parse.loopReads [] steps ++ rest)
      = groupInside [open, ..outer] (List.reverseOnto (Parse.loopReads [] steps) found) rest :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty
    | [argument, ..more], (read, later, isSteps, _, argSpelt, laterSpelt) =>
      rewrite isSteps,
          List.appendAssoc read (Parse.loopReads [] later) rest,
          groupInsideReverse argument read argSpelt open outer found (Parse.loopReads [] later ++ rest),
          argsWalk more later laterSpelt open outer (List.reverseOnto read found) rest,
          ontoAppend read (Parse.loopReads [] later) found

--| What ends with `ending`'s items keeps their last, whatever came before.
theorem lastOf ∀ (first ending found: List Item)
    (plain: ∀ (before: List Item) => headPlain (List.reverseOnto ending before) = True):
    headPlain (List.reverseOnto (first ++ ending) found) = True :=
  rewrite ontoAppend first ending found then plain (List.reverseOnto first found)

--| A spelt expression ends with no section operator: a word, a closer, or an operand's last.
theorem speltLast ∀ (expr: Expr) (read: List Item)
    (spelt: Spelt expr read) (found: List Item):
    headPlain (List.reverseOnto read found) = True :=
  match expr, spelt with
    | Atom kind word, (item, isRead, isKind, _, word) => rewrite isRead, isKind, wordNotSection kind word
    | Paren _ _ _, (first, inside, last, isRead, _, _, isClose, _) =>
      rewrite isRead then lastOf inside [last] [first, ..found] (before => rewrite isClose)
    | Tuple _ [_, _, .._] _ _, (first, read1, separator, read2, steps, last, isRead, _, _, _, _, isClose, _) =>
      rewrite isRead then
        lastOf read1 ([separator, ..read2] ++ (commaReads steps ++ [last])) [first, ..found] (before =>
          lastOf [separator, ..read2] (commaReads steps ++ [last]) before (later =>
            lastOf (commaReads steps) [last] later (end => rewrite isClose)))
    | ListOf _ [] _ _, (first, last, isRead, _, _, _, isClose, _) => rewrite isRead, isClose
    | ListOf _ [_, .._] _ _, (first, read1, steps, last, isRead, _, _, _, isClose, _) =>
      rewrite isRead then
        lastOf read1 (commaReads steps ++ [last]) [first, ..found] (before =>
          lastOf (commaReads steps) [last] before (end => rewrite isClose))
    | App head [argument, ..more], (headRead, argRead, steps, isRead, _, _, _, argSpelt, argsSpelt) =>
      rewrite isRead then
        lastOf headRead (argRead ++ Parse.loopReads [] steps) found (before =>
          rewrite ontoAppend argRead (Parse.loopReads [] steps) before then
            argsLast more steps argsSpelt
              (List.reverseOnto argRead before)
              (speltLast argument argRead argSpelt before))
    | Prefix _ operand, (sign, more, isRead, _, _, _, _, operandSpelt) =>
      rewrite isRead then speltLast operand more operandSpelt [sign, ..found]
    | Infix _ _ _ right, (leftRead, op, rightRead, isRead, _, _, _, _, _, _, _, rightSpelt) =>
      rewrite isRead then
        lastOf leftRead [op, ..rightRead] found (before => speltLast right rightRead rightSpelt [op, ..before])
    | _, never => Void.impossible never

theorem argsLast ∀ (exprs: List Expr) (steps: List (List Item, Expr))
    (spelt: SpeltArgs exprs steps) (found: List Item)
    (plain: headPlain found = True):
    headPlain (List.reverseOnto (Parse.loopReads [] steps) found) = True :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty then plain
    | [argument, ..more], (read, later, isSteps, _, argSpelt, laterSpelt) =>
      rewrite isSteps, ontoAppend read (Parse.loopReads [] later) found then
        argsLast more later laterSpelt (List.reverseOnto read found) (speltLast argument read argSpelt found)

theorem headPlainCommaReads ∀ (exprs: List Expr) (steps: List (Item, List Item, Expr))
    (spelt: SpeltSteps exprs steps) (found: List Item)
    (plain: headPlain found = True):
    headPlain (List.reverseOnto (commaReads steps) found) = True :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty then plain
    | [expr, ..more], (comma, read, later, isSteps, _, exprSpelt, laterSpelt) =>
      rewrite isSteps, ontoAppend [comma, ..read] (commaReads later) found then
        headPlainCommaReads more later laterSpelt
          (List.reverseOnto read [comma, ..found])
          (speltLast expr read exprSpelt [comma, ..found])

--| No `(k +)` section: the group a `(` opens closes at `last`, after a body whose last item is no section operator.
theorem rightClosed ∀ (first: Item) (body: List Item) (last: Item) (rest: List Item)
    (walk: groupInside [LParen] [] (body ++ [last, ..rest])
      = groupInside [LParen] (List.reverseOnto body []) [last, ..rest])
    (plain: headPlain (List.reverseOnto body []) = True)
    (isClose: last.kind = RParen):
    rightOperator [first, ..body ++ [last, ..rest]] = None :=
  let closes: groupInside [LParen] [] (body ++ [last, ..rest]) = Some (List.reverseOnto body []).reverse :=
    rewrite walk, isClose
  rewrite closes, List.reverseReverse (List.reverseOnto body []) then
    match backwards: List.reverseOnto body [] with
      | [] => byComputing
      | [lastItem, ..more] =>
        let lastPlain: headPlain [lastItem, ..more] = True := rewrite <- backwards then plain
        rewrite Bool.notTrue lastItem.kind.isSectionOperator lastPlain

theorem startFacts ∀ (kind: Tok)
    (starts: startKind kind = True):
    (kind == Dot) = False ∧ (kind == KwMatch) = False ∧ (kind == Minus || kind == Bang) = False :=
  cases

theorem lineAppend ∀ (first rest: List Item): lineAll (first ++ rest) = (lineAll first && lineAll rest) :=
  match first with
    | [] => byComputing
    | [item, ..more] =>
      rewrite lineAppend more rest then
        match lineKind item.kind with
          | True | False => byComputing

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
    (ends: endsHere rest = True):
    AtomEnds modes head kind rest :=
  let operand := endsOperandOf modes rest ends
  let plain: (isSome Upper (Some kind) && head && isSome LBrace (peekIn modes 0 rest)) = False := match rest with
    | [] => Bool.andAndFalse (isSome Upper (Some kind)) head _ byComputing
    | [next, ..later] =>
      Bool.andAndFalse
        (isSome Upper (Some kind))
        head _
        (match modes.stops next with
          | True => byComputing
          | False => endsNotBrace next.kind ends)
  { plain, noCall = operand.noCall, noDot = operand.noDot }

--| What follows a unary reading ends it: no record's fields, `()` call or field access after an atom, and no argument
--| after a call.
type UnaryEnds (modes: Modes) (rest: List Item): Prop = {
  atom: ∀ (head: Bool) (kind: Tok) => AtomEnds modes head kind rest,
  noArgument: startsAtomOn modes rest = False
}

--| What ends every expression ends a unary reading.
theorem unaryEndsOf ∀ (modes: Modes) (rest: List Item) (ends: endsHere rest = True): UnaryEnds modes rest :=
  { atom = head kind => endsAtom modes head kind rest ends, noArgument = (endsOperandOf modes rest ends).noArgument }

theorem endsSteps ∀ (exprs: List Expr) (steps: List (Item, List Item, Expr)) (last: Item) (rest: List Item)
    (spelt: SpeltSteps exprs steps)
    (isEnd: endsOperand last.kind = True):
    endsHere (commaReads steps ++ [last, ..rest]) = True :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty then isEnd
    | [_, .._], (comma, _, _, isSteps, isComma, _, _) => rewrite isSteps, isComma

theorem endsNotUpper ∀ (kind: Tok) (ends: endsOperand kind = True): (kind == Upper) = False := cases

theorem autoSecond ∀ (item second: Item) (later: List Item)
    (no: (second.kind == Lower) = False):
    namelessAutoAt [item, second, ..later] = False :=
  match later with
    | [] => byComputing
    | [_, .._] => rewrite no

theorem firstKind ∀ (item first: Item) (more inside: List Item)
    (isRead: [item, ..more] = [first, ..inside]):
    item.kind = first.kind :=
  rewrite List.consInjectiveHead isRead

--| No `[auto Upper` starts a list on one line with no calls: a word inside is followed by a comma or `]`.
--| No `[auto Upper` starts a list in this part, which has no calls: a word inside is followed by a comma or `]`.
--|
--| Proof idea: only a list starts with `[`; its first item's first token is a bracket, or a word followed by a comma
--| or the `]`.
theorem noAutoLine ∀ (expr: Expr) (item: Item) (more rest: List Item)
    (spelt: Spelt expr [item, ..more])
    (free: expr.autoPlaced True = True):
    (item.kind == LBracket && namelessAutoAt [item, ..more ++ rest]) = False :=
  match expr, spelt, free with
    | Atom kind word, (first, isRead, isKind, _, word), _ =>
      rewrite firstKind item first more [] isRead, isKind, wordNotBracket kind word
    | Paren _ _ _, (first, inside, _, isRead, isOpen, _), _ => rewrite firstKind item first more _ isRead, isOpen
    | Tuple _ [_, _, .._] _ _, (first, _, _, _, _, _, isRead, _, isOpen, _), _ =>
      rewrite firstKind item first more _ isRead, isOpen
    | ListOf _ [] _ _, (first, last, isRead, _, _, _, isClose, _), _ =>
      let isMore: more = [last] := Eq.cong (.drop 1) isRead
      rewrite isMore then Bool.andFalseRight _ _ (autoSecond item last rest (rewrite isClose))
    | ListOf _ [one, ..others] _ _, (first, read1, steps, last, isRead, _, _, _, isClose, _, oneSpelt,
        stepsSpelt), free =>
      let isMore: more = read1 ++ (commaReads steps ++ [last]) := Eq.cong (.drop 1) isRead
      let tail: (commaReads steps ++ [last]) ++ rest = commaReads steps ++ [last, ..rest] :=
        List.appendAssoc (commaReads steps) [last] rest
      let after := endsSteps others steps last rest stepsSpelt (rewrite isClose)
      rewrite isMore, List.appendAssoc read1 (commaReads steps ++ [last]) rest then
        Bool.andFalseRight _ _
          (noAutoFirst one item read1
            ((commaReads steps ++ [last]) ++ rest)
            oneSpelt
            (autoLeadFull one (Bool.andLeft free))
            (rewrite tail then endsHeadNotUpper _ after))
    | App head [argument, ..arguments], (headRead, argRead, steps, isRead, _, _, headSpelt, _), free =>
      let (first, inside, isHead, _) := speltStarts head headRead headSpelt
      let joined: [item, ..more] = [first, ..inside ++ (argRead ++ Parse.loopReads [] steps)] := calc [item, ..more]
        _ = headRead ++ (argRead ++ Parse.loopReads [] steps) := isRead
        _ = [first, ..inside ++ (argRead ++ Parse.loopReads [] steps)] := rewrite isHead
      let isItem: item = first := List.consInjectiveHead joined
      let isMore: more = inside ++ (argRead ++ Parse.loopReads [] steps) := Eq.cong (.drop 1) joined
      let headAt: Spelt head [first, ..inside] := rewrite <- isHead then headSpelt
      rewrite isItem, isMore, List.appendAssoc inside (argRead ++ Parse.loopReads [] steps) rest then
        noAutoLine head first inside ((argRead ++ Parse.loopReads [] steps) ++ rest) headAt (Bool.andLeft free)
    | Prefix _ _, (sign, _, isRead, signed, _), _ =>
      rewrite firstKind item sign more _ isRead, signNotBracket sign.kind signed
    | Infix _ left _ _, (leftRead, arrow, rightRead, isRead, _, _, _, _, _, _, leftSpelt, _), free =>
      let (first, inside, isLeft, _) := speltStarts left leftRead leftSpelt
      let joined: [item, ..more] = [first, ..inside ++ [arrow, ..rightRead]] := calc [item, ..more]
        _ = leftRead ++ [arrow, ..rightRead] := isRead
        _ = [first, ..inside ++ [arrow, ..rightRead]] := rewrite isLeft
      let isItem: item = first := List.consInjectiveHead joined
      let isMore: more = inside ++ [arrow, ..rightRead] := Eq.cong (.drop 1) joined
      let leftAt: Spelt left [first, ..inside] := rewrite <- isLeft then leftSpelt
      rewrite isItem, isMore, List.appendAssoc inside [arrow, ..rightRead] rest then
        noAutoLine left first inside ([arrow, ..rightRead] ++ rest) leftAt (Bool.andLeft free)
    | _, never, _ => Void.impossible never

--| A kind an expression of this part starts with is no `byWalking`.
theorem leadNotWalk ∀ (kind: Tok) (lead: leadKind kind = True): (kind == KwByWalking) = False := cases

--| No walk starts an expression of this part: its first token is a name, a numeral, a bracket or a sign, and a walk
--| starts with the keyword `byWalking`.
theorem noWalkLine ∀ (modes: Modes) (expr: Expr) (item: Item) (more rest: List Item)
    (spelt: Spelt expr [item, ..more]):
    walkOn modes [item, ..more ++ rest] = False :=
  let (first, inside, isRead, starts) := speltStarts expr [item, ..more] spelt
  let lead: leadKind item.kind = True := rewrite firstKind item first more inside isRead then starts
  match stops: modes.stops item with
    | True => byComputing
    | False => leadNotWalk item.kind lead

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
    (notAuto: expr.autoCall = False)
    (upper: headNotUpper later = True):
    namelessAutoAt [item, ..read ++ later] = False :=
  match expr, spelt, notAuto with
    | Atom _ _, (second, isRead, _), _ =>
      rewrite isRead then
        match later, upper with
          | [], _ => byComputing
          | [third, .._], upper => Bool.andAndFalse _ _ _ (Bool.notTrue _ upper)
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
    | Infix kind left _ _, (leftRead, arrow, rightRead, isRead, isOp, _, _, _, _, _, leftSpelt, _), notAuto =>
      rewrite isRead, List.appendAssoc leftRead [arrow, ..rightRead] later then
        noAutoFirst left item leftRead
          ([arrow, ..rightRead] ++ later)
          leftSpelt
          notAuto
          (rewrite infixNotUpper kind arrow.kind isOp)
    | _, never, _ => Void.impossible never

--| A call that is no `auto` call on a type's name doesn't make the list it starts an implicit binder.
--|
--| Proof idea: the call's head is its second item, and its first argument's first item the third: a word head and a
--| word argument are `autoCall`'s own test; a bracket in either place is no `Lower` or `Upper`.
theorem noAutoCall ∀ (head: Expr) (arguments: List Expr) (item: Item) (read later: List Item)
    (spelt: Spelt (App head arguments) read)
    (notAuto: (App head arguments).autoCall = False):
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
              rewrite isRead, isHead, isArgument then Bool.andAndFalse _ _ _ (rewrite isOpen)
            | Tuple _ [_, _, .._] _ _, (third, _, _, _, _, _, isArgument, _, isOpen, _), _ =>
              rewrite isRead, isHead, isArgument then Bool.andAndFalse _ _ _ (rewrite isOpen)
            | ListOf _ [] _ _, (third, _, isArgument, _, isOpen, _), _ =>
              rewrite isRead, isHead, isArgument then Bool.andAndFalse _ _ _ (rewrite isOpen)
            | ListOf _ [_, .._] _ _, (third, _, _, _, isArgument, _, isOpen, _), _ =>
              rewrite isRead, isHead, isArgument then Bool.andAndFalse _ _ _ (rewrite isOpen)
            | App _ _ | Infix _ _ _ _, _, never => (Bool.falseNotTrue never).impossible
            | Prefix _ _, (third, _, isArgument, isSign, _), _ =>
              rewrite isRead, isHead, isArgument then Bool.andAndFalse _ _ _ (signNotUpper third.kind isSign)
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
        | Prefix _ _, (second, _, isHead, signed, _), _ =>
          rewrite isRead, isHead then autoSecond item second _ (signNotLower second.kind signed)
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
  Bool.andElim _ _ (rewrite <- lineAppend first rest then line)

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
      rewrite isMore, isInside, notClose then Bool.andFalseMiddle (first.kind == LParen) (first.glued && second.glued)
    | Tuple _ [one, _, .._] _ _, (open, read1, separator, read2, commas, last, isRead, _, _, _, _, _, _, oneSpelt, _) =>
      let (second, others, isRead1, starts) := speltStarts one read1 oneSpelt
      let (notClose, _, _) := startNotClose second.kind starts
      let isMore: more = read1 ++ ([separator, ..read2] ++ (commaReads commas ++ [last])) := Eq.cong (.drop 1) isRead
      rewrite isMore, isRead1, notClose then Bool.andFalseMiddle (first.kind == LParen) (first.glued && second.glued)
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
      let isFirst: first = start := List.consInjectiveHead joined
      let isMore: more = inside ++ (argRead ++ Parse.loopReads [] steps) := Eq.cong (.drop 1) joined
      let headAt: Spelt head [start, ..inside] := rewrite <- isHead then headSpelt
      rewrite isFirst, isMore, List.appendAssoc inside (argRead ++ Parse.loopReads [] steps) later then
        speltNoUnit head start inside ((argRead ++ Parse.loopReads [] steps) ++ later) headAt
    | Prefix _ _, (sign, inside, isRead, signed, _) =>
      let notParen: (first.kind == LParen) = False :=
        rewrite firstKind first sign more inside isRead then signNotParen sign.kind signed
      unitNotParen first (more ++ later) notParen
    | Infix _ left _ _, (leftRead, arrow, rightRead, isRead, _, _, _, _, _, _, leftSpelt, _) =>
      let (start, inside, isLeft, _) := speltStarts left leftRead leftSpelt
      let joined: [first, ..more] = [start, ..inside ++ [arrow, ..rightRead]] := calc [first, ..more]
        _ = leftRead ++ [arrow, ..rightRead] := isRead
        _ = [start, ..inside ++ [arrow, ..rightRead]] := rewrite isLeft
      let isFirst: first = start := List.consInjectiveHead joined
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
    plain = Bool.andAndFalse (isSome Upper (Some kind)) head _ (peekNoBrace modes 0 _ line),
    noCall = speltNoUnit expr first more later spelt,
    noDot = rewrite notDot
  }

theorem startOpensAtom ∀ (kind: Tok) (starts: startKind kind = True): kind.opensAtom = True := cases

theorem signCases ∀ (kind: Tok) (signed: signKind kind = True): kind = Minus ∨ kind = Bang := match kind, signed with
  | Minus, _ => Inl byComputing
  | Bang, _ => Inr byComputing
  | other, never => (Bool.falseNotTrue never).impossible

--| An argument of this part that is no prefix is an atom or a bracket.
theorem signArgAtomic ∀ (expr: Expr) (fits: expr.signArg = True) (unsigned: expr.signed = False): expr.primary = True :=
  match expr, fits, unsigned with
    | Prefix _ _, _, never => (Bool.falseNotTrue never.flipped).impossible
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _, fits, _ => fits
    | other, never, _ => (Bool.falseNotTrue never).impossible

--| A sign before an argument starts an atom.
theorem signStartsAtom ∀ (modes: Modes) (kind: Tok) (items: List Item)
    (signed: signKind kind = True)
    (prefix: argumentPrefix items = True):
    startsAtomKind modes kind items = True :=
  match kind, signed with
    | Minus | Bang, _ => rewrite prefix
    | other, never => (Bool.falseNotTrue never).impossible

theorem signOr ∀ (kind: Tok) (signed: signKind kind = True): (kind == Minus || kind == Bang) = True := cases

theorem minusOf ∀ (kind: Tok) (minus: (kind == Minus) = True): kind = Minus := cases

--| A negative numeral starts with `-`.
theorem negativeMinus ∀ (sign: Item) (more: List Item)
    (numeral: negativeNumeral [sign, ..more] = True):
    sign.kind = Minus :=
  match more, numeral with
    | [_, .._], numeral => minusOf sign.kind (Bool.andLeft numeral)
    | [], never => (Bool.falseNotTrue never).impossible

--| The `-1` of `def d: A := f -x [-1]` (`lexedLineIs`) is a negative numeral: `negativeMinus` isn't vacuous.
theorem negativeMinusExample: (lexedAt 9).kind = Minus := negativeMinus (lexedAt 9) [lexedAt 10] byComputing

-- Operators: what ends an operand, and the chains.

--| The rung of the ladder an operator of this part is read at: `&&` and `||` share the logic links.
def tokRung: Tok → Nat
  | Arrow => 1
  | OrOr | AndAnd => 5
  | Equals | EqEq | NotEq | Lt | Le | Gt | Ge => 6
  | PlusPlus => 12
  | Plus | Minus => 14
  | Star | Slash | Percent => 16
  | _ => 0

--| What follows an operand read at `level` of the ladder ends it there: what ends a unary reading, and no operator
--| of a rung from `level` up. An operator of a looser rung gives it (`opEnds`), as does what ends every expression
--| (`endsAtOf`).
type EndsAt (modes: Modes) (level: Nat) (rest: List Item): Prop = {
  unary: UnaryEnds modes rest,
  noMul: level <= 16 → takesAhead modes (kind => kind == Star || kind == Slash || kind == Percent) rest = False,
  noAdd: level <= 14 → takesAhead modes (kind => kind == Plus || kind == Minus) rest = False,
  noAppend: level <= 12 → takesAhead modes (kind => kind == PlusPlus) rest = False,
  noRange: rangeAhead modes rest = False,
  noPipe: atPipeOn modes rest = False,
  noCmp: level <= 6 → cmpAhead modes rest = False,
  noAndOr: level <= 5 → andOrOn modes rest = False,
  noIff: isSome IffArrow (peekIn modes 0 rest) = False,
  noEnd: level <= 1 → opEndsAhead modes (sequenceOn modes rest) rest = False
}

--| What ends every expression ends an operand at every level.
theorem endsAtOf ∀ (modes: Modes) (level: Nat) (rest: List Item)
    (ends: endsHere rest = True):
    EndsAt modes level rest :=
  let operand := endsOperandOf modes rest ends
  {
    unary = unaryEndsOf modes rest ends,
    noMul = _ => operand.noMul,
    noAdd = _ => operand.noAdd,
    noAppend = _ => operand.noAppend,
    noRange = operand.noRange,
    noPipe = operand.noPipe,
    noCmp = _ => operand.noCmp,
    noAndOr = _ => operand.noAndOr,
    noIff = operand.noIff,
    noEnd = _ => operand.noEnd
  }

--| What ends an operand at a level ends it at any tighter one.
theorem endsAtUp ∀ (modes: Modes) (low high: Nat) (rest: List Item)
    (up: low <= high)
    (ends: EndsAt modes low rest):
    EndsAt modes high rest :=
  {
    unary = ends.unary,
    noMul = below => ends.noMul (arithmetic [below, up]),
    noAdd = below => ends.noAdd (arithmetic [below, up]),
    noAppend = below => ends.noAppend (arithmetic [below, up]),
    noRange = ends.noRange,
    noPipe = ends.noPipe,
    noCmp = below => ends.noCmp (arithmetic [below, up]),
    noAndOr = below => ends.noAndOr (arithmetic [below, up]),
    noIff = ends.noIff,
    noEnd = below => ends.noEnd (arithmetic [below, up])
  }

--| An operator of this part, as `infixTok` admits them.
def opTok (tok: Tok): Bool := tok == Arrow || binaryTok tok

theorem infixOp ∀ (kind: InfixKind) (tok: Tok) (isOp: infixTok kind tok = True): opTok tok = True :=
  match kind, isOp with
    | InfixArrow, isOp => rewrite DecEq.sound isOp
    | InfixBinary, isOp => rewrite isOp then Bool.orTrue (tok == Arrow)
    | _, never => (Bool.falseNotTrue never).impossible

--| An operator is no bracket, field, argument, `cases`, range, pipe or `<->`, and its rung is at least 1.
type OpKind (tok: Tok): Prop = {
  notOpen: (tok == LParen) = False,
  notBrace: (tok == LBrace) = False,
  notDot: (tok == Dot) = False,
  notArgument: opensArgument tok = False,
  notCases: (tok == KwCases) = False,
  notRange: (tok == DotDot || tok == DotDotLt || tok == DotDotEq) = False,
  notPipe: (tok == PipeGt) = False,
  notIff: (tok == IffArrow) = False,
  ranked: 1 <= tokRung tok
}

theorem opKind ∀ (tok: Tok) (isOp: opTok tok = True): OpKind tok := match tok, isOp with
  | Arrow, _ =>
    opKindOfPlainKind Arrow byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing byComputing
  | Star, _ =>
    opKindOfPlainKind Star byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing byComputing
  | Slash, _ =>
    opKindOfPlainKind Slash byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing byComputing
  | Percent, _ =>
    opKindOfPlainKind Percent byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing byComputing
  | Plus, _ =>
    opKindOfPlainKind Plus byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing byComputing
  | Minus, _ =>
    opKindOfPlainKind Minus byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing byComputing
  | PlusPlus, _ =>
    opKindOfPlainKind PlusPlus byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing byComputing
  | Equals, _ =>
    opKindOfPlainKind Equals byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing byComputing
  | EqEq, _ =>
    opKindOfPlainKind EqEq byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing byComputing
  | NotEq, _ =>
    opKindOfPlainKind NotEq byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing byComputing
  | Lt, _ =>
    opKindOfPlainKind Lt byComputing byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing
  | Le, _ =>
    opKindOfPlainKind Le byComputing byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing
  | Gt, _ =>
    opKindOfPlainKind Gt byComputing byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing
  | Ge, _ =>
    opKindOfPlainKind Ge byComputing byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing
  | AndAnd, _ =>
    opKindOfPlainKind AndAnd byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing byComputing
  | OrOr, _ =>
    opKindOfPlainKind OrOr byComputing byComputing byComputing byComputing byComputing byComputing byComputing
        byComputing byComputing
  | _, never => (Bool.falseNotTrue never).impossible

theorem opKindOfPlainKind ∀ (tok: Tok)
    (notOpen: (tok == LParen) = False)
    (notBrace: (tok == LBrace) = False)
    (notDot: (tok == Dot) = False)
    (notArgument: opensArgument tok = False)
    (notCases: (tok == KwCases) = False)
    (notRange: (tok == DotDot || tok == DotDotLt || tok == DotDotEq) = False)
    (notPipe: (tok == PipeGt) = False)
    (notIff: (tok == IffArrow) = False)
    (ranked: 1 <= tokRung tok):
    OpKind tok :=
  { notOpen, notBrace, notDot, notArgument, notCases, notRange, notPipe, notIff, ranked }

theorem rungMul ∀ (tok: Tok) (level: Nat)
    (isOp: opTok tok = True)
    (above: tokRung tok < level)
    (low: level <= 16):
    (tok == Star || tok == Slash || tok == Percent) = False :=
  cases

theorem rungAdd ∀ (tok: Tok) (level: Nat)
    (isOp: opTok tok = True)
    (above: tokRung tok < level)
    (low: level <= 14):
    (tok == Plus || tok == Minus) = False :=
  cases

theorem rungAppend ∀ (tok: Tok) (level: Nat)
    (isOp: opTok tok = True)
    (above: tokRung tok < level)
    (low: level <= 12):
    (tok == PlusPlus) = False :=
  cases

theorem rungCmp ∀ (tok: Tok) (level: Nat)
    (isOp: opTok tok = True)
    (above: tokRung tok < level)
    (low: level <= 6):
    (tok == KwIn || tok == NotIn || tok.isComparison) = False :=
  cases

theorem rungAndOr ∀ (tok: Tok) (level: Nat)
    (isOp: opTok tok = True)
    (above: tokRung tok < level)
    (low: level <= 5):
    (tok == AndAnd || tok == OrOr) = False :=
  cases

--| A sign is an argument's only where the item after it touches it: an operator spaced from its operand is none.
theorem prefixApart ∀ (op: Item) (after: List Item)
    (apart: operandApart after = True):
    argumentPrefix [op, ..after] = False :=
  match after, apart with
    | [], _ => byComputing
    | [next, .._], apart =>
      rewrite Bool.notTrue _ apart then
        match op.kind == Minus || op.kind == Bang with
          | False => byComputing
          | True =>
            match op.afterOperand with
              | False => byComputing
              | True =>
                match op.leaf.token.lineStart || !op.glued with
                  | False | True => byComputing

--| An operator, its operand spaced from it, ends an operand at every level tighter than its rung.
--|
--| Proof idea: the modes don't stop at the operator, so each look-ahead sees its kind: no bracket, field or argument
--| (`OpKind`, `prefixApart`), and an operator of each rung from `level` up only if its rung were that tight.
theorem opEnds ∀ (modes: Modes) (level: Nat) (op: Item) (after: List Item) (kind: InfixKind)
    (open: modes.stops op = False)
    (isOp: infixTok kind op.kind = True)
    (apart: operandApart after = True)
    (above: tokRung op.kind < level):
    EndsAt modes level [op, ..after] :=
  let opIs := infixOp kind op.kind isOp
  let facts := opKind op.kind opIs
  let peek: peekIn modes 0 [op, ..after] = Some op.kind := peekFirst modes op after open
  {
    unary = {
      atom = head atomKind =>
        {
          plain = Bool.andAndFalse _ head _ (rewrite peek then facts.notBrace),
          noCall = unitNotParen op after facts.notOpen,
          noDot = rewrite facts.notDot
        },
      noArgument = rewrite peek, facts.notArgument, facts.notDot, facts.notCases, prefixApart op after apart
    },
    noMul = low => rewrite peek then rungMul op.kind level opIs above low,
    noAdd = low => rewrite peek then rungAdd op.kind level opIs above low,
    noAppend = low => rewrite peek then rungAppend op.kind level opIs above low,
    noRange = rewrite peek then facts.notRange,
    noPipe = (rewrite facts.notPipe),
    noCmp = low => rewrite peek then rungCmp op.kind level opIs above low,
    noAndOr = low => rewrite peek then rungAndOr op.kind level opIs above low,
    noIff = rewrite peek then facts.notIff,
    noEnd = low => Void.impossible (arithmetic [low, above, facts.ranked])
  }

theorem binaryAtMost ∀ (tok: Tok) (isOp: binaryTok tok = True): tokLevel tok <= 16 := cases

theorem infixAtMost ∀ (kind: InfixKind) (tok: Tok) (isOp: infixTok kind tok = True): tokLevel tok <= 16 :=
  match kind, isOp with
    | InfixArrow, isOp => rewrite DecEq.sound isOp then arithmetic []
    | InfixBinary, isOp => binaryAtMost tok isOp
    | _, never => (Bool.falseNotTrue never).impossible

--| An expression of this part binding tighter than every infix is no infix.
theorem highUnary ∀ (expr: Expr) (read: List Item)
    (spelt: Spelt expr read)
    (high: 17 <= expr.level):
    expr.unary = True :=
  match expr, spelt, high with
    | Infix kind _ operator _, (_, op, _, _, isOp, _, level, _), high =>
      Void.impossible (arithmetic [high, level, infixAtMost kind op.kind isOp])
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ | Prefix _ _, _, _ => byComputing
    | _, never, _ => Void.impossible never

--| A spelt expression that is no infix binds at the unary level or tighter.
theorem unaryLevel ∀ (expr: Expr) (read: List Item)
    (spelt: Spelt expr read)
    (unary: expr.unary = True):
    18 <= expr.level :=
  match expr, spelt, unary with
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ | App _ _ | Prefix _ _, _, _ => arithmetic []
    | Infix _ _ _ _, _, never => (Bool.falseNotTrue never).impossible
    | _, never, _ => Void.impossible never

theorem mulOf ∀ (tok: Tok)
    (isOp: binaryTok tok = True)
    (high: 16 <= tokLevel tok):
    (tok == Star || tok == Slash || tok == Percent) = True :=
  cases

theorem addOf ∀ (tok: Tok)
    (isOp: binaryTok tok = True)
    (is14: tokLevel tok = 14):
    (tok == Plus || tok == Minus) = True :=
  cases

--| A binary operator of this part binding at the additive level or tighter is additive or multiplicative.
theorem binaryLow ∀ (tok: Tok)
    (isOp: binaryTok tok = True)
    (high: 14 <= tokLevel tok):
    tokLevel tok = 14 ∨ tokLevel tok = 16 :=
  cases

--| A binary operator of this part binding at the append level or tighter is `++` or tighter still.
theorem binaryAppend ∀ (tok: Tok)
    (isOp: binaryTok tok = True)
    (high: 12 <= tokLevel tok):
    tokLevel tok = 12 ∨ 14 <= tokLevel tok :=
  cases

--| A binary operator of this part binding at the comparison level or tighter is a comparison or binds at the append
--| level or tighter.
theorem binaryCmp ∀ (tok: Tok)
    (isOp: binaryTok tok = True)
    (high: 6 <= tokLevel tok):
    tokLevel tok = 6 ∨ 12 <= tokLevel tok :=
  cases

--| A binary operator of this part is `||`, `&&`, or binds at the comparison level or tighter.
theorem binaryLogic ∀ (tok: Tok)
    (isOp: binaryTok tok = True):
    tokLevel tok = 4 ∨ tokLevel tok = 5 ∨ 6 <= tokLevel tok :=
  cases

theorem appendOf ∀ (tok: Tok) (isOp: binaryTok tok = True) (is12: tokLevel tok = 12): (tok == PlusPlus) = True := cases

theorem cmpOf ∀ (tok: Tok)
    (isOp: binaryTok tok = True)
    (is6: tokLevel tok = 6):
    tok.isComparison = True ∧ (tok == KwIn || tok == NotIn) = False :=
  cases

theorem leadNotIf ∀ (kind: Tok) (starts: leadKind kind = True): (kind == KwIf) = False := cases

--| `++` nests to the right.
theorem appendNeeds ∀ (text: Text)
    (is12: infixLevel InfixBinary text = 12):
    leftNeeds InfixBinary text = 14 ∧ rightNeeds InfixBinary text = 12 :=
  cases

--| `++`: `appendNeeds`'s hypothesis can hold.
theorem appendNeedsExample: leftNeeds InfixBinary "++" = 14 ∧ rightNeeds InfixBinary "++" = 12 :=
  appendNeeds "++" byComputing

--| A comparison doesn't chain: both operands above it.
theorem cmpNeeds ∀ (text: Text)
    (is6: infixLevel InfixBinary text = 6):
    leftNeeds InfixBinary text = 8 ∧ rightNeeds InfixBinary text = 8 :=
  cases

--| `*`, `/` and `%` nest to the left, their right operand one rung up.
theorem mulNeeds ∀ (text: Text)
    (is16: infixLevel InfixBinary text = 16):
    leftNeeds InfixBinary text = 16 ∧ rightNeeds InfixBinary text = 18 :=
  cases

--| `*`: `mulNeeds`'s hypothesis can hold.
theorem mulNeedsExample: leftNeeds InfixBinary "*" = 16 ∧ rightNeeds InfixBinary "*" = 18 := mulNeeds "*" byComputing

--| `+` and `-` nest to the left, their right operand one rung up.
theorem addNeeds ∀ (text: Text)
    (is14: infixLevel InfixBinary text = 14):
    leftNeeds InfixBinary text = 14 ∧ rightNeeds InfixBinary text = 16 :=
  cases

--| `+`: `addNeeds`'s hypothesis can hold.
theorem addNeedsExample: leftNeeds InfixBinary "+" = 14 ∧ rightNeeds InfixBinary "+" = 16 := addNeeds "+" byComputing

theorem rungMulOf ∀ (tok: Tok) (isMul: (tok == Star || tok == Slash || tok == Percent) = True): tokRung tok = 16 :=
  cases

theorem rungAddOf ∀ (tok: Tok) (isAdd: (tok == Plus || tok == Minus) = True): tokRung tok = 14 := cases

--| A spelt read's spacing from what precedes it is its first item's, whatever follows.
theorem speltApart ∀ (expr: Expr) (read rest: List Item)
    (spelt: Spelt expr read):
    operandApart (read ++ rest) = operandApart read :=
  let (first, more, isRead, _) := speltStarts expr read spelt
  rewrite isRead

--| What `rightNested` chains are made of: a first operand, an operator, and a chain read after it.
theorem rightCons ∀ (modes: Modes) (takes: Tok → Bool) (operand: List Item → List Item → Expr → Prop)
    (headRead: List Item) (op: Item) (rightRead rest: List Item) (head right: Expr) (all: List Item) (value: Expr)
    (whole: all = headRead ++ [op, ..rightRead])
    (isValue: value = Infix InfixBinary head op.leaf.word right)
    (headReads: operand headRead ([op, ..rightRead] ++ rest) head)
    (open: modes.stops op = False)
    (took: takes op.kind = True)
    (rightReads: ChainReads modes takes rightNested operand operand rightRead rest right):
    ChainReads modes takes rightNested operand operand all rest value :=
  let (read1, first, links, isRight, isRightValue, firstReads, linked) := rightReads
  (
    headRead,
    head,
    [(op, read1, first), ..links],
    (rewrite whole, isRight),
    (rewrite isValue, isRightValue),
    (rewrite isRight at headReads then headReads),
    (open, took, firstReads, linked)
  )

theorem rungAppendOf ∀ (tok: Tok) (isAppend: (tok == PlusPlus) = True): tokRung tok = 12 := cases

--| A spelt expression binding above the comparisons binds at the `++` level or tighter.
theorem aboveCmp ∀ (expr: Expr) (read: List Item) (spelt: Spelt expr read) (fits: 7 <= expr.level): 12 <= expr.level :=
  match expr, spelt, fits with
    | Infix InfixBinary _ operator _, (_, op, _, _, isOp, _, level, _), fits =>
      match binaryCmp op.kind isOp (arithmetic [fits, level]) with
        | Inl is6 => Void.impossible (arithmetic [fits, level, is6])
        | Inr high => arithmetic [level, high]
    | Infix InfixArrow _ _ _, _, fits => Void.impossible (arithmetic [fits])
    | Infix _ _ _ _, (_, _, _, _, never, _), _ => (Bool.falseNotTrue never).impossible
    | other, spelt, _ => arithmetic [unaryLevel other read spelt byComputing]

theorem rungCmpOf ∀ (tok: Tok) (isCmp: tok.isComparison = True): tokRung tok = 6 := cases

theorem binaryAboveArrow ∀ (tok: Tok) (isOp: binaryTok tok = True): 4 <= tokLevel tok := cases

--| A spelt expression that is no arrow binds at the `||` level or tighter: no looser operator is spelt yet.
theorem plainLevel ∀ (expr: Expr) (read: List Item) (spelt: Spelt expr read) (fits: 2 <= expr.level): 4 <= expr.level :=
  match expr, spelt, fits with
    | Infix InfixBinary _ operator _, (_, op, _, _, isOp, _, level, _), _ =>
      arithmetic [level, binaryAboveArrow op.kind isOp]
    | Infix InfixArrow _ _ _, _, fits => Void.impossible (arithmetic [fits])
    | Infix _ _ _ _, (_, _, _, _, never, _), _ => (Bool.falseNotTrue never).impossible
    | other, spelt, _ => arithmetic [unaryLevel other read spelt byComputing]

--| Whether a word is `&&`: what `conjunctionOf` joins on.
def isAnd (word: Word): Bool := word.text == "&&" || word.text == "∧"

--| Whether the first link, if any, is a `&&`: where `conjunctionOf` goes on.
def andLed: List (Word, Expr) → Bool
  | [(word, _), .._] => isAnd word
  | [] => False

theorem conjunctionAnd ∀ (first next: Expr) (word: Word) (rest: List (Word, Expr))
    (and: isAnd word = True):
    conjunctionOf first [(word, next), ..rest] = conjunctionJoin first word (conjunctionOf next rest) :=
  rewrite and

theorem conjunctionStop ∀ (first: Expr) (links: List (Word, Expr))
    (stop: andLed links = False):
    conjunctionOf first links = (first, links) :=
  match links, stop with
    | [], _ => byComputing
    | [(word, next), ..rest], stop => rewrite stop

theorem groupConj ∀ (fuel: Nat) (first expr: Expr) (links: List (Word, Expr))
    (conj: conjunctionOf first links = (expr, [])):
    groupLogic fuel first links = expr :=
  rewrite conj then match fuel with | Zero | Succ _ => byComputing

theorem groupOr ∀ (fuel: Nat) (first left next: Expr) (word: Word) (links rest: List (Word, Expr))
    (conj: conjunctionOf first links = (left, [(word, next), ..rest])):
    groupLogic (Succ fuel) first links = Infix InfixBinary left word (groupLogic fuel next rest) :=
  rewrite conj

--| `&&` nests to the right over comparisons.
theorem andNeeds ∀ (text: Text)
    (is5: infixLevel InfixBinary text = 5):
    leftNeeds InfixBinary text = 6 ∧ rightNeeds InfixBinary text = 5 ∧ (text == "&&" || text == "∧") = True :=
  cases

--| `&&`: `andNeeds`'s hypothesis can hold.
theorem andNeedsExample: leftNeeds InfixBinary "&&" = 6
      ∧ rightNeeds InfixBinary "&&" = 5
      ∧ ("&&" == "&&" || "&&" == "∧") = True :=
  andNeeds "&&" byComputing

--| `||` nests to the right over conjunctions.
theorem orNeeds ∀ (text: Text)
    (is4: infixLevel InfixBinary text = 4):
    leftNeeds InfixBinary text = 5 ∧ rightNeeds InfixBinary text = 4 ∧ (text == "&&" || text == "∧") = False :=
  cases

--| `||`: `orNeeds`'s hypothesis can hold.
theorem orNeedsExample: leftNeeds InfixBinary "||" = 5
      ∧ rightNeeds InfixBinary "||" = 4
      ∧ ("||" == "&&" || "||" == "∧") = False :=
  orNeeds "||" byComputing

theorem logicTok ∀ (tok: Tok)
    (isOp: binaryTok tok = True)
    (low: tokLevel tok <= 5):
    (tok == AndAnd || tok == OrOr) = True :=
  cases

theorem linkValuesLength ∀ (links: List (Item, List Item, Expr)):
    (Parse.stepValues (linkSteps links)).length = links.length :=
  match links with
    | [] => byComputing
    | [(_, _, _), ..later] => rewrite linkValuesLength later

--| A comparison operand of a logic chain: spelt, binding at the comparison level or tighter, within `depth`.
type OperandSpelt (depth: Nat) (expr: Expr) (read: List Item): Prop = {
  spelt: Spelt expr read,
  fits: 6 <= expr.level,
  free: expr.autoPlaced False = True,
  deep: expr.nest <= depth
}

--| The links of a logic chain spelt: each operator `&&` or `||`, its operand a comparison spelt by its read and spaced
--| from the operator.
def LinksSpelt (depth: Nat): List (Item, List Item, Expr) → Prop
  | [] => True = True
  | [(operator, read, value), ..links] =>
    (operator.kind == AndAnd || operator.kind == OrOr) = True
      ∧ operandApart read = True
      ∧ OperandSpelt depth value read
      ∧ LinksSpelt depth links

--| A conjunction's read followed by the links `tail`, flattened: its first comparison and the links from there,
--| `tail` last, which `conjunctionOf` takes back to the conjunction and `tail`.
def ConjFlat (depth: Nat) (expr: Expr) (read: List Item) (tail: List (Item, List Item, Expr)): Prop :=
  ∃ (first: Expr) (firstRead: List Item) (links: List (Item, List Item, Expr)) => read
    ++ Parse.loopReads [] (linkSteps tail)
    = firstRead ++ Parse.loopReads [] (linkSteps links)
    ∧ OperandSpelt depth first firstRead
    ∧ LinksSpelt depth links
    ∧ tail.length <= links.length
    ∧ conjunctionOf first (Parse.stepValues (linkSteps links)) = (expr, Parse.stepValues (linkSteps tail))

theorem conjLeaf ∀ (depth: Nat) (expr: Expr) (read: List Item) (tail: List (Item, List Item, Expr))
    (spelt: Spelt expr read)
    (high: 6 <= expr.level)
    (free: expr.autoPlaced False = True)
    (deep: expr.nest <= depth)
    (tailSpelt: LinksSpelt depth tail)
    (stop: andLed (Parse.stepValues (linkSteps tail)) = False):
    ConjFlat depth expr read tail :=
  (
    expr,
    read,
    tail,
    byComputing,
    { spelt, fits = high, free, deep },
    tailSpelt,
    arithmetic [],
    conjunctionStop expr (Parse.stepValues (linkSteps tail)) stop
  )

--| A spelt conjunction (`&&` nesting to the right over comparisons) followed by `tail`, which starts with no `&&`,
--| flattens: `conjunctionOf` takes exactly its `&&`s.
--|
--| Proof idea: by induction on the right spine. A comparison is its own first operand (`conjLeaf`); `left && right`
--| puts `&& first` of `right`'s flattening after `left`, and `conjunctionOf` joins `left` to what it gives for `right`.
theorem conjFlat ∀ (depth: Nat) (expr: Expr) (read: List Item) (tail: List (Item, List Item, Expr))
    (spelt: Spelt expr read)
    (fits: 5 <= expr.level)
    (free: expr.autoPlaced False = True)
    (deep: expr.nest <= depth)
    (tailSpelt: LinksSpelt depth tail)
    (stop: andLed (Parse.stepValues (linkSteps tail)) = False):
    ConjFlat depth expr read tail :=
  match expr, spelt, fits with
    | Infix InfixBinary left operator right, sp, fits =>
      let (leftRead, op, rightRead, isRead, isOp, isWord, level, leftFits, rightFits, apart, leftSpelt, rightSpelt) :=
        sp
      match binaryLogic op.kind isOp with
        | Inl is4 => Void.impossible (arithmetic [fits, level, is4])
        | Inr (Inl is5) =>
          let at5: infixLevel InfixBinary operator.text = 5 := arithmetic [level, is5]
          let (leftNeed, rightNeed, andText) := andNeeds operator.text at5
          let (first, firstRead, links, isRight, rightOperand, linksSpelt, longer, conj) :=
            conjFlat depth right rightRead tail rightSpelt
              (arithmetic [rightFits, rightNeed])
              (Bool.andRight free)
              (arithmetic [deep])
              tailSpelt
              stop
          let and: isAnd op.leaf.word = True := rewrite isWord then andText
          let firstApart: operandApart firstRead = True := calc operandApart firstRead
            _ = operandApart (firstRead ++ Parse.loopReads [] (linkSteps links)) :=
              (speltApart first firstRead (Parse.loopReads [] (linkSteps links)) rightOperand.spelt).flipped
            _ = operandApart (rightRead ++ Parse.loopReads [] (linkSteps tail)) := rewrite isRight
            _ = operandApart rightRead := speltApart right rightRead (Parse.loopReads [] (linkSteps tail)) rightSpelt
            _ = True := apart
          (
            left,
            leftRead,
            [(op, firstRead, first), ..links],
            (calc read ++ Parse.loopReads [] (linkSteps tail)
              _ = (leftRead ++ [op, ..rightRead]) ++ Parse.loopReads [] (linkSteps tail) := rewrite isRead
              _ = leftRead ++ [op, ..rightRead ++ Parse.loopReads [] (linkSteps tail)] :=
                List.appendAssoc leftRead [op, ..rightRead] (Parse.loopReads [] (linkSteps tail))
              _ = leftRead ++ [op, ..firstRead ++ Parse.loopReads [] (linkSteps links)] := rewrite isRight),
            {
              spelt = leftSpelt,
              fits = arithmetic [leftFits, leftNeed],
              free = Bool.andLeft free,
              deep = arithmetic [deep]
            },
            (logicTok op.kind isOp (arithmetic [is5]), firstApart, rightOperand, linksSpelt),
            arithmetic [longer],
            (calc conjunctionOf left [(op.leaf.word, first), ..Parse.stepValues (linkSteps links)]
              _ = conjunctionJoin left op.leaf.word (conjunctionOf first (Parse.stepValues (linkSteps links))) :=
                conjunctionAnd left first op.leaf.word (Parse.stepValues (linkSteps links)) and
              _ = (Infix InfixBinary left operator right, Parse.stepValues (linkSteps tail)) := rewrite conj, isWord)
          )
        | Inr (Inr high) =>
          conjLeaf depth
            (Infix InfixBinary left operator right)
            read
            tail
            sp
            (arithmetic [level, high])
            free
            deep
            tailSpelt
            stop
    | Infix InfixArrow _ _ _, _, fits => Void.impossible (arithmetic [fits])
    | Infix _ _ _ _, (_, _, _, _, never, _), _ => (Bool.falseNotTrue never).impossible
    | other, spelt, _ =>
      conjLeaf depth other read tail spelt
        (arithmetic [unaryLevel other read spelt byComputing])
        free
        deep
        tailSpelt
        stop

--| A logic chain's read, flattened: its first comparison and its links, which `groupLogic` with fuel enough regroups
--| into the chain.
def LogicSplit (depth: Nat) (expr: Expr) (read: List Item): Prop :=
  ∃ (first: Expr) (firstRead: List Item) (links: List (Item, List Item, Expr)) => read
    = firstRead ++ Parse.loopReads [] (linkSteps links)
    ∧ OperandSpelt depth first firstRead
    ∧ LinksSpelt depth links
    ∧ (∀ (fuel: Nat) => links.length < fuel → groupLogic fuel first (Parse.stepValues (linkSteps links)) = expr)

theorem orOfConj ∀ (depth: Nat) (expr: Expr) (read: List Item)
    (spelt: Spelt expr read)
    (fits: 5 <= expr.level)
    (free: expr.autoPlaced False = True)
    (deep: expr.nest <= depth):
    LogicSplit depth expr read :=
  let (first, firstRead, links, isRead, operand, linksSpelt, _, conj) :=
    conjFlat depth expr read [] spelt fits free deep byComputing byComputing
  (
    first,
    firstRead,
    links,
    Eq.trans (List.appendNil read).flipped isRead,
    operand,
    linksSpelt,
    fuel _ => groupConj fuel first expr (Parse.stepValues (linkSteps links)) conj
  )

--| A spelt logic chain (`||` nesting to the right over conjunctions) flattens into its first comparison and links,
--| which `groupLogic` regroups as it was.
--|
--| Proof idea: by induction on the `||` spine. A conjunction is `conjFlat`'s with no links after; `left || right`
--| flattens `right`, then `left` with `|| first` of that before its links, so `conjunctionOf` stops at the `||` and
--| `groupLogic` puts `left` before it and regroups the rest, on one fuel less.
theorem orFlat ∀ (depth: Nat) (expr: Expr) (read: List Item)
    (spelt: Spelt expr read)
    (fits: 4 <= expr.level)
    (free: expr.autoPlaced False = True)
    (deep: expr.nest <= depth):
    LogicSplit depth expr read :=
  match expr, spelt, fits with
    | Infix InfixBinary left operator right, sp, fits =>
      let (leftRead, op, rightRead, isRead, isOp, isWord, level, leftFits, rightFits, apart, leftSpelt, rightSpelt) :=
        sp
      match binaryLogic op.kind isOp with
        | Inl is4 =>
          let at4: infixLevel InfixBinary operator.text = 4 := arithmetic [level, is4]
          let (leftNeed, rightNeed, orText) := orNeeds operator.text at4
          let (rightFirst, rightFirstRead, rightLinks, isRight, rightOperand, rightLinksSpelt, rightGroup) :=
            orFlat depth right rightRead rightSpelt
              (arithmetic [rightFits, rightNeed])
              (Bool.andRight free)
              (arithmetic [deep])
          let tail := [(op, rightFirstRead, rightFirst), ..rightLinks]
          let firstApart: operandApart rightFirstRead = True := calc operandApart rightFirstRead
            _ = operandApart (rightFirstRead ++ Parse.loopReads [] (linkSteps rightLinks)) :=
              Eq.flipped
                (speltApart rightFirst rightFirstRead (Parse.loopReads [] (linkSteps rightLinks)) rightOperand.spelt)
            _ = operandApart rightRead := rewrite isRight
            _ = True := apart
          let tailSpelt: LinksSpelt depth tail :=
            (logicTok op.kind isOp (arithmetic [is4]), firstApart, rightOperand, rightLinksSpelt)
          let stop: andLed (Parse.stepValues (linkSteps tail)) = False := rewrite isWord then orText
          let (first, firstRead, links, isLeft, operand, linksSpelt, longer, conj) :=
            conjFlat depth left leftRead tail leftSpelt
              (arithmetic [leftFits, leftNeed])
              (Bool.andLeft free)
              (arithmetic [deep])
              tailSpelt
              stop
          (
            first,
            firstRead,
            links,
            (calc read
              _ = leftRead ++ [op, ..rightRead] := isRead
              _ = leftRead ++ [op, ..rightFirstRead ++ Parse.loopReads [] (linkSteps rightLinks)] := rewrite isRight
              _ = leftRead ++ Parse.loopReads [] (linkSteps tail) := byComputing
              _ = firstRead ++ Parse.loopReads [] (linkSteps links) := isLeft),
            operand,
            linksSpelt,
            fuel small =>
              match fuel, small with
                | Zero, small => Void.impossible (arithmetic [small])
                | Succ more, small =>
                  rewrite groupOr more first left rightFirst op.leaf.word
                        (Parse.stepValues (linkSteps links))
                        (Parse.stepValues (linkSteps rightLinks))
                        conj,
                      rightGroup more (arithmetic [small, longer]),
                      isWord
          )
        | Inr (Inl is5) =>
          orOfConj depth (Infix InfixBinary left operator right) read sp (arithmetic [level, is5]) free deep
        | Inr (Inr high) =>
          orOfConj depth (Infix InfixBinary left operator right) read sp (arithmetic [level, high]) free deep
    | Infix InfixArrow _ _ _, _, fits => Void.impossible (arithmetic [fits])
    | Infix _ _ _ _, (_, _, _, _, never, _), _ => (Bool.falseNotTrue never).impossible
    | other, spelt, _ =>
      orOfConj depth other read spelt (arithmetic [unaryLevel other read spelt byComputing]) free deep

theorem leadNotExists ∀ (kind: Tok) (starts: leadKind kind = True): (kind == KwExists) = False := cases

theorem leadNotForall ∀ (kind: Tok) (starts: leadKind kind = True): (kind == KwForall) = False := cases

theorem andOrBinary ∀ (tok: Tok) (andOr: (tok == AndAnd || tok == OrOr) = True): binaryTok tok = True := cases

theorem andOrRung ∀ (tok: Tok) (andOr: (tok == AndAnd || tok == OrOr) = True): tokRung tok = 5 := cases

--| No `{` first: `allowBraceOn` leaves the modes.
theorem allowNoBrace ∀ (modes: Modes) (item: Item) (rest: List Item)
    (notBrace: (item.kind == LBrace) = False):
    allowBraceOn modes [item, ..rest] = modes :=
  match limit: modes.limit with
    | None => byComputing
    | Some column => rewrite notBrace

theorem startNotOther ∀ (kind: Tok) (starts: leadKind kind = True): startsOtherStatement kind = False := cases

theorem startNotBrace ∀ (kind: Tok) (starts: leadKind kind = True): (kind == LBrace) = False := cases

--| An item for the witnesses with its spacing: glued to the token before, which ends an operand or not.
def spacedItem (kind: Tok) (text: Text) (index: Nat) (glued afterOperand: Bool): Item :=
  { wordItem kind text index | glued, afterOperand }

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

theorem firstKindExample: (wordItem Lower "a" 0).kind = (wordItem Lower "a" 0).kind :=
  firstKind (wordItem Lower "a" 0) (wordItem Lower "a" 0) [] [] byComputing

-- A witness from the lexer's own items (SW-4074): depth, glue and `afterOperand` as `items` gives them.

--| The items the lexer gives a source, none if it doesn't lex.
def lexedItems (source: Text): List Item := match lex source with
  | Ok lexed => items lexed.leaves
  | Err _ => []

--| An item as the lexer gives it on a first line with no comments, at column `column`.
def lexedItem (kind: Tok) (text: Text) (column: Nat) (glued afterOperand: Bool) (index depth: Nat): Item := {
  leaf = { token = { kind, text, column, lineStart = index == 0 }, trivia = Trivia.empty },
  glued,
  afterOperand,
  afterDot = False,
  index,
  depth,
  lineIndent = 0
}

--| `lexedLine`'s items, written out: `lexedLineIs` says the lexer gives these.
def lexedAt (index: Nat): Item := match index with
  | 0 => lexedItem KwDef "def" 0 False False 0 0
  | 1 => lexedItem Lower "d" 4 False False 1 0
  | 2 => lexedItem Colon ":" 5 True True 2 0
  | 3 => lexedItem Upper "A" 7 False False 3 0
  | 4 => lexedItem ColonEq ":=" 9 False True 4 0
  | 5 => lexedItem Lower "f" 12 False False 5 0
  | 6 => lexedItem Minus "-" 14 False True 6 0
  | 7 => lexedItem Lower "x" 15 True False 7 0
  | 8 => lexedItem LBracket "[" 17 False True 8 0
  | 9 => lexedItem Minus "-" 18 True False 9 1
  | 10 => lexedItem Num "1" 19 True False 10 1
  | _ => lexedItem RBracket "]" 20 True True 11 1

-- A `-` before a numeral, apart from it across a comment (SW-4077): a sign on its operand, not a negative numeral.

--| `def d: A := (- -- c⏎  1)`: the comment ends the line, so the `1` isn't glued to the `-`.
def commentLine: List Item := lexedItems "def d: A := (- -- c\n  1)\n"

--| The lexer's item at `index` of `commentLine`.
def commentAt (index: Nat): Item := match commentLine.drop index with
  | [item, .._] => item
  | [] => lexedAt 0

--| `(- -- c⏎  1)`.
def commentValue: Expr :=
  Paren
    (commentAt 5).leaf.word
    (Prefix (commentAt 6).leaf.word (Atom Num (commentAt 7).leaf.word))
    (commentAt 8).leaf.word

--| `Spelt` holds of the lexer's items for `(- -- c⏎  1)`: a `-` read as no negative numeral asks nothing of its
--| operand.
theorem commentSpeltExample: Spelt commentValue [commentAt 5, commentAt 6, commentAt 7, commentAt 8] := (
  commentAt 5,
  [commentAt 6, commentAt 7],
  commentAt 8,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  (
    commentAt 6,
    [commentAt 7],
    byComputing,
    byComputing,
    byComputing,
    (never => (Bool.falseNotTrue never).impossible),
    byComputing,
    (commentAt 7, byComputing, byComputing, byComputing, byComputing)
  )
)

--| The parser reads `def d: A := (- -- c⏎  1)` back as `commentValue`.
theorem readsBackCommentExample: Parse.run commentLine (() =>
      let decl := declaration Seen.start
      decl)
      = Ok
        (Definition []
          (plainHeader (commentAt 0) (commentAt 1) (commentAt 2) (Atom Upper (commentAt 3).leaf.word))
          (Assigned (commentAt 4).leaf.word.comments commentValue)) :=
  byComputing
