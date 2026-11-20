--| The parser's expressions and patterns (stage 2a), on `Parse` over the
--| settled leaves, following `crates/syntax`'s parser function for function
--| so that the tree and the first line of every error are the same.
--|
--| It never backs up. Where the Rust parser looks ahead by index (is this a
--| lambda? an operator section?), a pure function looks at the items left;
--| an error is `Parse.fatal` with the Rust message, so no choice can turn
--| it into another one.
--|
--| Recursion goes only through `self`, the expression parser at a `Goal`
--| (a level of the precedence ladder and the modes), and patterns' own
--| `pself`, so `Parse.recursiveWith`'s fuel bounds it and every other
--| function is a plain call or a loop with fuel from the items left.
--|
--| Declarations, parameter groups and types with abilities are
--| `DeclParser.sw`'s (stage 2b); blocks, `let`, local definitions and the
--| proof steps (`calc`, `rewrite`, `cases`, `match induct`) and `handle`
--| are `Statements.sw`'s (stage 2c).

namespace Syntax
import Std (Bool, Empty, List, Nat, Option, Parse, Result, Text)

--| A leaf as the parser reads it, with what the Rust parser learns from
--| spans: whether no space separates it from the token before on its line
--| (`glued`), and whether that token ends an operand (`afterOperand`), which
--| together decide what a `-`, `!` or `.` is; and for layout, its index,
--| how many brackets are open before it, and the column of its line's
--| first token; and whether a `.` comes right before it (`(p).at` is a
--| field, never a `rewrite`'s `at`).
type Item = {
  leaf: Leaf,
  glued: Bool,
  afterOperand: Bool,
  afterDot: Bool,
  index: Nat,
  depth: Nat,
  lineIndent: Nat
}

def Item.kind (item: Item): Tok := item.leaf.token.kind

def Item.text (item: Item): Text := item.leaf.token.text

def items (leaves: List Leaf): List Item := itemsAfter None 0 0 0 leaves

--| The column just past a token: a `"""` text spans lines, so its end is the
--| length of its last line, which starts at column 0.
def endColumn (token: Token): Nat := match token.text.split '\n' |> .reverse with
  | [last, _, .._] => last.utf8Length
  | _ => token.column + token.text.utf8Length

def itemsAfter (before: Option Token) (index depth lineIndent: Nat): List Leaf → List Item
  | [] => []
  | [leaf, ..rest] =>
    let token := leaf.token
    let glued := match before with
      | Some previous => !token.lineStart && endColumn previous == token.column
      | None => False
    let afterOperand := before.map (previous => previous.kind.closesOperand) |> .getOrElse False
    let afterDot := before.map (previous => previous.kind == Dot) |> .getOrElse False
    let indent := if token.lineStart then token.column else lineIndent
    let after :=
      if token.kind.isOpener then depth + 1
      else if token.kind.isCloser then depth - 1
      else depth
    [
      { leaf, glued, afterOperand, afterDot, index, depth, lineIndent = indent },
      ..itemsAfter (Some token) (index + 1) after indent rest
    ]

--| Whether a token ends an operand (`crates/syntax`'s `closes_operand`).
def Tok.closesOperand: Tok → Bool
  | Lower |
      Upper |
      Num |
      Float |
      Str |
      StrEnd |
      CharLit |
      RParen |
      RBracket |
      RBrace |
      Underscore |
      Question |
      TypeU |
      PropU |
      KwArithmetic |
      KwAlgebra |
      KwCases => True
  | _ => False

--| A binary operator, which can stand alone as a function, `(&&)`.
def Tok.isOperator: Tok → Bool
  | Plus |
      Minus |
      Star |
      Slash |
      Percent |
      PlusPlus |
      Equals |
      NotEq |
      EqEq |
      Lt |
      Le |
      Gt |
      Ge |
      AndAnd |
      OrOr |
      KwIn |
      NotIn |
      IffArrow => True
  | _ => False

--| An operator a section can take: any but `-`, so `(- 1)` is a number.
def Tok.isSectionOperator (tok: Tok): Bool := tok.isOperator && tok != Minus

def Tok.isComparison: Tok → Bool
  | Equals | NotEq | EqEq | Lt | Le | Gt | Ge => True
  | _ => False

--| How the Rust parser writes a comparison in a message: its ASCII form.
def Tok.written: Tok → Text
  | Le => "<="
  | Gt => ">"
  | Ge => ">="
  | Equals => "="
  | EqEq => "=="
  | NotEq => "!="
  | _ => "<"

--| A token as an error message names it (`describe` and `spelled`).
def Item.spelled (item: Item): Text := match item.kind with
  | StrStart | StrMid | StrEnd => "a text literal"
  | InterpOpen => "`\${`"
  | InterpClose => "`}` closing a `\${…}`"
  | At => "`@[`"
  | _ => "`${item.text}`"

-- Modes and goals.

--| What the Rust parser keeps in `Modes` that stages 2a and 2b need:
--| whether a guard's condition is being read, outside brackets opened since
--| (so a `=>` ends it); where a method section that starts an expression
--| starts (an offset), which its own parser marks; the block's column
--| (`limit`) and the statement's first token (`allow`); and whether this is
--| a top-level definition's body, where the Rust parser recovers from an
--| error (`recover`), which changes one message: a missing expression where
--| a line at the block's column starts.
--|
--| Stage 2c adds what ends a construct whatever its column: inside a
--| `calc`, a line starting with `_` (`inCalc`); inside a `rewrite` rule or
--| target, a `then`, an `in` or (in a rule) an `at` outside the brackets
--| opened since the rule's first item (`rewriteRule`, that item's index
--| and bracket depth, and `rewriteAt`); and inside a `let`'s value, the
--| bracket depth of its `let` (`letValue`), so a `;` at that depth ends the
--| value instead of starting a sequence.
type Modes = {
  guard: Bool,
  sectionHead: Option Nat,
  limit: Option Nat,
  allow: Option Nat,
  recover: Bool,
  inCalc: Bool,
  rewriteRule: Option (Nat, Nat),
  rewriteAt: Bool,
  letValue: Option Nat,
  lines: List BlockLine
}

--| A block being read, innermost first in `Modes.lines`: its column,
--| whether it may have more lines, and what its current line is. When a
--| recovering body runs out (R1), the Rust parser carries on, and a block
--| that then ends on a `let` or a local definition reports that, at the
--| line's first token, which is before the gap and so the first error.
type BlockLine = { column: Nat, many: Bool, kind: LineKind }

--| `DefHeaderLine` is a local definition's result type or `decreasing`:
--| a gap there leaves it no body, which `local_def` reports at its keyword
--| whether or not the block goes on.
type LineKind = | ExprLine | LetLine | DefLine | DefHeaderLine

def Modes.start: Modes := {
  guard = False,
  sectionHead = None,
  limit = None,
  allow = None,
  recover = False,
  inCalc = False,
  rewriteRule = None,
  rewriteAt = False,
  letValue = None,
  lines = []
}

--| The modes inside a bracket: a `=>` there is no guard's.
def Modes.inBrackets (modes: Modes): Modes := { modes | guard = False }

--| Whether `item` is the guard's `=>`, which ends it whatever else is
--| being read.
def Modes.endsGuard (modes: Modes) (item: Item): Bool := modes.guard && item.kind == FatArrow

--| Whether `item` ends what is being read (`is_stop`): the guard's `=>`,
--| or a line starting at or left of the block's column (`limit`), unless
--| it closes or continues a bracket, starts with an operator that can only
--| continue the line above, or is the statement's own first token
--| (`allow`).
def Modes.stops (modes: Modes) (item: Item): Bool := modes.endsConstruct item || modes.stopsByLine item

--| Whether `item` belongs to an enclosing construct, whatever its column
--| (`ends_construct`): the next `calc` step, the end of a `rewrite` rule,
--| the guard's `=>`.
def Modes.endsConstruct (modes: Modes) (item: Item): Bool :=
  modes.startsCalcStep item || modes.endsRule item || modes.endsGuard item

def Modes.startsCalcStep (modes: Modes) (item: Item): Bool :=
  modes.inCalc && item.kind == Underscore && item.leaf.token.lineStart

def Modes.endsRule (modes: Modes) (item: Item): Bool := match modes.rewriteRule with
  | Some (start, depth) =>
    let word := match item.kind with
      | KwThen => True
      | KwIn => True
      | Lower => item.text == "at" && modes.rewriteAt && item.index > start
      | _ => False
    word && !item.afterDot && item.depth <= depth
  | None => False

def Modes.stopsByLine (modes: Modes) (item: Item): Bool := match modes.limit with
  | Some limit =>
    modes.allow != Some item.index
      && item.leaf.token.lineStart
      && item.leaf.token.column <= limit
      && !((item.kind == Comma || item.kind.isCloser) && item.depth > 0)
      && !(item.leaf.token.column == limit && item.kind.isInfixOnly)
  | None => False

--| An infix operator no expression starts with (`is_infix_only`).
def Tok.isInfixOnly: Tok → Bool
  | AndAnd |
      OrOr |
      IffArrow |
      Arrow |
      Equals |
      EqEq |
      NotEq |
      Lt |
      Le |
      Gt |
      Ge |
      Plus |
      PlusPlus |
      Star |
      Slash |
      Percent |
      NotIn => True
  | _ => False

--| The rungs of the precedence ladder that are parsed from more than one
--| place, each with the Rust function it stands for.
type Level =
  --| `expr`
  | LevelFull
  --| `expr_inline`
  | LevelInline
  --| `cmp_expr`, then `logic_chain`: a section's operand after `<->`.
  | LevelLogic
  --| `cmp_expr`
  | LevelComparison
  --| `append_expr`
  | LevelAppend
  --| `add_expr`
  | LevelAdditive
  --| `mul_expr`
  | LevelMultiplicative
  --| `unary`
  | LevelUnary
  --| `atom(false)`: an argument.
  | LevelArgument
  --| `app`: a row's ability, a data type's index, a constructor's result.
  | LevelApp
  --| `then_body`: after a `rewrite`'s or `cases`'s `then`.
  | LevelThenBody

type Goal = { modes: Modes, level: Level }

type PatternLevel =
  --| `pattern`
  | PatternPlain
  --| `tuple_component`
  | PatternTupleComponent
  --| `list_component`
  | PatternListComponent
  --| `alt_pattern_one`
  | PatternAltOne
  --| A record pattern's field value: a constructor's arguments run to the
  --| next `,` or `}`.
  | PatternFieldValue

type PatternGoal = { modes: Modes, level: PatternLevel }

-- Reading.

def fatal (message: Text): {Parse Item} a := Empty.absurd (Parse.fatal message)

def left(): {Parse Item} List Item := Parse.mark().rest

def offset(): {Parse Item} Nat := Parse.mark().offset

--| The next token's kind, unless it ends what is being read.
def Modes.peek (modes: Modes): {Parse Item} Option Tok := peekIn modes 0 left()

--| The kind of the token `ahead` places on, if nothing up to it ends what
--| is being read.
def Modes.peekAt (modes: Modes) (ahead: Nat): {Parse Item} Option Tok := peekIn modes ahead left()

def peekIn (modes: Modes) (ahead: Nat) (items: List Item): Option Tok := match ahead, items with
  | _, [] => None
  | Zero, [item, .._] => if modes.stops item then None else Some item.kind
  | Succ more, [item, ..later] => if modes.stops item then None else peekIn modes more later

def Modes.at (modes: Modes) (wanted: Tok): {Parse Item} Bool := isSome wanted modes.peek

def isSome (wanted: Tok): Option Tok → Bool
  | Some found => found == wanted
  | None => False

--| The next item, read.
def bump(): {Parse Item} Word := match Parse.next (item => True) with
  | Some item => item.leaf.word
  | None => fatal "the parser read past the end of its input"

def Modes.eat (modes: Modes) (wanted: Tok): {Parse Item} Option Word := if modes.at wanted then Some bump() else None

def Modes.expect (modes: Modes) (wanted: Tok) (what: Text): {Parse Item} Word := modes.expectOn wanted what modes.peek

--| `expect`, given what `modes.peek` saw.
def Modes.expectOn (modes: Modes) (wanted: Tok) (what: Text) (seen: Option Tok): {Parse Item} Word :=
  if isSome wanted seen then bump() else modes.fail what

--| "expected `what`, but …": the Rust parser's `unexpected`.
def Modes.unexpected (modes: Modes) (what: Text): {Parse Item} Text := modes.unexpectedAt what left()

--| The message, given the items left.
def Modes.unexpectedAt (modes: Modes) (what: Text) (items: List Item): Text := match items with
  | [] => "expected ${what}, but reached the end of the declaration"
  | [item, .._] =>
    if item.kind == At && !modes.stops item then "attributes can't be written here"
    else if modes.startsCalcStep item then "expected ${what}, but the next `calc` step starts here"
    else if modes.endsGuard item then "expected ${what}, but the guard's `=>` starts here"
    else if modes.stopsByLine item && !modes.endsConstruct item then
      let limit := modes.limit.getOrElse 0
      "expected ${what}, but the line starting with ${item.spelled} (in column ${item.leaf.token.column + 1}) is at or left of the enclosing block's column (${limit + 1}), so it starts a new statement"
    else "expected ${what}, but found ${item.spelled}"

def Modes.fail (modes: Modes) (what: Text): {Parse Item} a := fatal (modes.unexpected what)

--| `unexpected`, naming a keyword as one (`unexpected_name`).
def Modes.failName (modes: Modes) (what: Text): {Parse Item} a := modes.failNameOn what left()

def Modes.failNameOn (modes: Modes) (what: Text) (items: List Item): {Parse Item} a := match items with
  | [item, .._] =>
    if keywordHere modes item then fatal "expected ${what}, but found the keyword `${item.text}`" else modes.fail what
  | [] => modes.fail what

def keywordHere (modes: Modes) (item: Item): Bool := !modes.stops item && Tok.keyword item.text |> .isSome

--| An unqualified lowercase name (the Rust parser's `lower`).
def Modes.lower (modes: Modes) (what: Text): {Parse Item} Word := modes.lowerOn what left()

def Modes.lowerOn (modes: Modes) (what: Text) (items: List Item): {Parse Item} Word := match items with
  | [item, .._] if item.kind == Lower && !modes.stops item =>
    if isQualified item then fatal "`${item.text}` is a qualified name, which can't be used here" else bump()
  | _ => modes.failName what

-- Looking ahead, as the Rust parser does by index.

--| The items after the bracket group `items` starts with, if its opener
--| has a partner. Brackets pair by kind, and a closer that doesn't match
--| the innermost open bracket is passed over, as the Rust parser's
--| `match_brackets` pairs them: `open` is the brackets open, innermost
--| first.
def skipGroup (open: List Tok): List Item → Option (List Item)
  | [] => None
  | [item, ..rest] =>
    if item.kind.isOpener then skipGroup [item.kind, ..open] rest
    else if item.kind.isCloser then
      match open with
        | [innermost, ..outer] if pairs innermost item.kind =>
          match outer with
            | [] => Some rest
            | _ => skipGroup outer rest
        | _ => skipGroup open rest
    else skipGroup open rest

def pairs (opener closer: Tok): Bool := match opener, closer with
  | LParen, RParen => True
  | LBracket, RBracket => True
  | LBrace, RBrace => True
  | _, _ => False

--| The items inside a bracket group, from after its opener, if it closes
--| (paired as `skipGroup` pairs them).
def groupInside (open: List Tok) (found: List Item): List Item → Option (List Item)
  | [] => None
  | [item, ..rest] =>
    if item.kind.isOpener then groupInside [item.kind, ..open] [item, ..found] rest
    else if item.kind.isCloser then
      match open with
        | [innermost, ..outer] if pairs innermost item.kind =>
          match outer with
            | [] => Some found.reverse
            | _ => groupInside outer [item, ..found] rest
        | _ => groupInside open [item, ..found] rest
    else groupInside open [item, ..found] rest

def isQualified (item: Item): Bool := item.text.contains "."

--| `lambda_ahead`: names, `_` and bracket groups, then a `=>`.
--| `fuel` bounds the items looked at: one more than are left.
def lambdaAhead (modes: Modes) (fuel: Nat) (items: List Item): Bool := lambdaAheadFrom fuel modes 0 items

def lambdaAheadFrom (fuel: Nat) (modes: Modes) (count: Nat) (items: List Item): Bool := match fuel, items with
  | Zero, _ => False
  | _, [] => False
  | Succ more, [item, ..rest] =>
    if modes.stops item then False
    else
      match item.kind with
        | Lower => if isQualified item then False else lambdaAheadFrom more modes (count + 1) rest
        | Underscore => lambdaAheadFrom more modes (count + 1) rest
        | LParen => afterGroup more modes count items
        | LBrace => afterGroup more modes count items
        | LBracket => if implicitGroupAt items || namelessAutoAt items then afterGroup more modes count items else False
        | FatArrow => count > 0
        | _ => False

def afterGroup (more: Nat) (modes: Modes) (count: Nat) (items: List Item): Bool := match skipGroup [] items with
  | Some after => lambdaAheadFrom more modes (count + 1) after
  | None => False

--| A lambda written with a result type, `(x: A): B => body`
--| (`lambda_result_type_ahead`): parameters ending in a bracketed one,
--| then `:`, then a `=>` before the bracket around it closes.
def lambdaResultType (modes: Modes) (fuel: Nat) (bracketedLast: Bool) (items: List Item): Bool := match fuel, items with
  | Zero, _ => False
  | _, [] => False
  | Succ more, [item, ..rest] =>
    let colon := bracketedLast && item.kind == Colon && resultArrowAhead modes more rest
    if modes.stops item then colon
    else
      match item.kind with
        | Lower => if isQualified item then colon else lambdaResultType modes more False rest
        | Underscore => lambdaResultType modes more False rest
        | LParen => afterBracket modes more items
        | LBracket => afterBracket modes more items
        | _ => colon

def afterBracket (modes: Modes) (more: Nat) (items: List Item): Bool := match skipGroup [] items with
  | Some after => lambdaResultType modes more True after
  | None => False

def resultArrowAhead (modes: Modes) (fuel: Nat) (items: List Item): Bool := match fuel, items with
  | Zero, _ => False
  | _, [] => False
  | Succ more, [item, ..rest] =>
    if modes.stops item then False
    else
      match item.kind with
        | FatArrow => True
        | ColonEq => False
        | RParen => False
        | RBracket => False
        | RBrace => False
        | kind =>
          if kind.isOpener then
            match skipGroup [] items with
              | Some after => resultArrowAhead modes more after
              | None => False
          else resultArrowAhead modes more rest

--| `[a b: …]` or `[a]`: names after the `[`, then `:` or `]`.
def implicitGroupAt: List Item → Bool
  | [_, ..rest] => namesThen rest 0 (kind => kind == Colon || kind == RBracket)
  | [] => False

--| Whether at least one unqualified-or-not lowercase name comes first, then
--| a token that `then` accepts.
def namesThen (items: List Item) (count: Nat) (accepts: Tok → Bool): Bool := match items with
  | [item, ..rest] if item.kind == Lower => namesThen rest (count + 1) accepts
  | [item, .._] => count > 0 && accepts item.kind
  | [] => False

--| `[auto Ord a]`.
def namelessAutoAt: List Item → Bool
  | [_, auto, upper, .._] => auto.kind == Lower && auto.text == "auto" && upper.kind == Upper
  | _ => False

--| `(x y: A)`: names, then `:`.
def annotatedParamAhead (items: List Item): Bool := match items with
  | [_, ..rest] => namesThen rest 0 (kind => kind == Colon)
  | [] => False

--| `((a, b): A)`: a `:` at the bracket's own depth, after something, with
--| no comma before it.
def annotatedPatternAhead (fuel: Nat) (items: List Item): Bool := match items with
  | [_, ..rest] => annotatedFrom fuel True rest
  | [] => False

def annotatedFrom (fuel: Nat) (first: Bool) (items: List Item): Bool := match fuel, items with
  | Zero, _ => False
  | _, [] => False
  | Succ more, [item, ..rest] =>
    match item.kind with
      | Colon => !first
      | Comma => False
      | kind =>
        if kind.isOpener then
          match skipGroup [] [item, ..rest] with
            | Some after => annotatedFrom more False after
            | None => False
        else if kind.isCloser then False
        else annotatedFrom more False rest

--| `[x: A]`, `[auto P]`, `[@[…] x: A]` starting a function type.
def implicitBinderAhead (fuel: Nat) (items: List Item): Bool := match items with
  | [open, ..rest] if open.kind == LBracket =>
    namelessAutoAt items || namesThen (pastAttributes fuel rest) 0 (kind => kind == Colon)
  | _ => False

def pastAttributes (fuel: Nat) (items: List Item): List Item := match fuel, items with
  | Succ more, [at, ..rest] if at.kind == At =>
    match skipGroup [] rest with
      | Some after => pastAttributes more after
      | None => items
  | _, _ => items

--| `(x: A) -> B`: names and `:` in brackets, an arrow after them.
def piBinderAhead (items: List Item): Bool := match items with
  | [open, ..rest] if open.kind == LParen && namesThen rest 0 (kind => kind == Colon) =>
    match skipGroup [] items with
      | Some [arrow, .._] => arrow.kind == Arrow
      | _ => False
  | _ => False

--| `.name` with no space after the `.` and one before it: a method section.
def sectionAt: List Item → Bool
  | [dot, name, .._] => dot.kind == Dot && name.kind == Lower && name.glued && !dot.glued
  | _ => False

--| A `-` or `!` that negates an argument: `f -x`, `g !b`.
def argumentPrefix: List Item → Bool
  | [sign, next, .._] =>
    (sign.kind == Minus || sign.kind == Bang)
      && sign.afterOperand
      && (sign.leaf.token.lineStart || !sign.glued)
      && next.glued
      && next.kind.opensAtom
  | _ => False

def argumentMinus (items: List Item): Bool := match items with
  | [sign, .._] => sign.kind == Minus && argumentPrefix items
  | [] => False

def argumentBang (items: List Item): Bool := match items with
  | [sign, .._] => sign.kind == Bang && argumentPrefix items
  | [] => False

--| `-1` written as one atom.
def negativeNumeral: List Item → Bool
  | [minus, number, .._] =>
    minus.kind == Minus
      && (number.kind == Num || number.kind == Float)
      && number.glued
      && !(minus.afterOperand && minus.glued)
  | _ => False

--| `f()`: a `(` against what came before, and its `)` against it.
def unitCall: List Item → Bool
  | [open, close, .._] => open.kind == LParen && close.kind == RParen && open.glued && close.glued
  | _ => False

--| The number of items inside a `(k +)` section's brackets, if its last is
--| a section's operator.
def rightOperator (items: List Item): Option Nat := match items with
  | [_, ..rest] =>
    match groupInside [LParen] [] rest with
      | Some inside =>
        match inside.reverse with
          | [last, .._] => if last.kind.isSectionOperator then Some inside.length else None
          | [] => None
      | None => None
  | [] => None

-- Expressions.

--| The fuel is `Parse.recursiveWith`'s, the items left and one more, and
--| never runs out: every rule reads an item before it calls `self`. The
--| ladder's levels below the goal's are plain calls (`cmpExpr` to `unary`
--| to `atom`), not calls of `self`, and `self` is called only after a
--| bracket, an operator, a keyword, a `=>` or an application's head. So a
--| call `d` deep has at least `d - 1` items read before it, and the fuel
--| at each call is at least the items left there and one more.
def expression (modes: Modes): {Parse Item} Expr := Parse.recursiveWith expressionRule { modes, level = LevelFull }

def expressionRule (self: Goal → {Parse Item} Expr) (goal: Goal): {Parse Item} Expr :=
  let modes := goal.modes
  match goal.level with
    | LevelFull => expr self modes
    | LevelInline => exprInline self modes
    | LevelLogic => logicLevel self modes
    | LevelComparison => cmpExpr self modes
    | LevelAppend => appendExpr self modes
    | LevelAdditive => addExpr self modes
    | LevelMultiplicative => mulExpr self modes
    | LevelUnary => unary self modes
    | LevelArgument => atom self modes False
    | LevelApp => app self modes
    | LevelThenBody => thenBody self modes

def full (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := self { modes, level = LevelFull }

--| `expr`: a line after the first starting here would be a block.
def expr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := exprOn self modes left()

--| Whether `expr` takes `item` as the start of a block: it starts a line after the declaration's first item, the
--| modes don't allow it (as a block's own line), and it doesn't end the construct around. It tests the item's index
--| (Rust's `self.pos`), which in a declaration group is the parser's offset, so that it depends on the items alone
--| and a reading of them holds from any parser state.
def startsBlock (modes: Modes) (item: Item): Bool :=
  item.leaf.token.lineStart && item.index > 0 && modes.allow != Some item.index && !modes.endsConstruct item

def exprOn (self: Goal → {Parse Item} Expr) (modes: Modes): List Item → {Parse Item} Expr
  | [item, .._] => if startsBlock modes item then exprBlock self modes item else exprInline self modes
  | _ => exprInline self modes

def exprBlock (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item): {Parse Item} Expr :=
  let column := item.leaf.token.column
  match modes.limit with
    | None => block self modes column True
    | Some limit =>
      if column > limit then block self modes column True
      else exprRuns self modes item limit (runsOutAt modes item limit left())

--| The line starts at the block's column, after a line that ran out (R1).
def runsOutAt (modes: Modes) (item: Item) (limit: Nat) (items: List Item): Bool :=
  item.leaf.token.column == limit && modes.recover && startsStatement item.kind && !lineHasSemicolon limit True items

def exprRuns (self: Goal → {Parse Item} Expr) (modes: Modes) (item: Item) (limit: Nat) (runs: Bool):
    {Parse Item} Expr :=
  if runs then modes.gap ranOutLine
  else if item.leaf.token.column == limit then block self modes item.leaf.token.column False
  else exprInline self modes

--| The modes for an expression that a keyword or token must follow (an
--| `if`'s condition, a scrutinee): after a gap there, that token is missing,
--| an error after the gap, so no block's ending can come before it.
def Modes.sealed (modes: Modes): Modes := { modes | lines = [] }

def localNeedsBody: Text := "a local definition needs a body: `:=` and an expression, or arms starting with `|`"

def ranOutLine: Text := "expected an expression, but the line ends here"

--| R1: what was wanted ran out where a line or the declaration ends. The
--| Rust parser reports `message` there and reads on; the first error is
--| still this one, unless the blocks around end on a `let` or a local
--| definition (`blockEnd`).
def Modes.gap (modes: Modes) (message: Text): {Parse Item} a := modes.gapOn message left()

def Modes.gapOn (modes: Modes) (message: Text) (items: List Item): {Parse Item} a :=
  match blockEnd modes.lines items.head with
    | Some ending => fatal ending
    | None => fatal message

--| The error of the innermost block that ends at `next` on a `let` or a
--| local definition, once the blocks that end on an expression are left.
def blockEnd (lines: List BlockLine) (next: Option Item): Option Text := match lines with
  | [] => None
  | [{ column, many, kind }, ..outer] =>
    let continues := match next with
      | Some item => item.leaf.token.lineStart && item.leaf.token.column == column && !endsBlocks item.kind
      | None => False
    if kind == DefHeaderLine then Some localNeedsBody
    else if many && continues then None
    else
      match kind with
        | LetLine => Some "a block must end with an expression, not `let`"
        | DefLine => Some "a block must end with an expression, not a local `def` or `theorem`"
        | _ => blockEnd outer next

--| A line at the block's column that starts with one of these after a
--| line that ran out is the next statement (R1), not the rest of the line
--| above.
def startsStatement: Tok → Bool
  | KwLet | KwDef | KwTheorem => True
  | _ => False

--| Whether the line `items` starts has a `;` before the next line at or
--| left of `limit` (`line_has_semicolon`).
def lineHasSemicolon (limit: Nat) (first: Bool): List Item → Bool
  | [] => False
  | [item, ..rest] =>
    if !first && item.leaf.token.lineStart && item.leaf.token.column <= limit then False
    else item.kind == Semi || lineHasSemicolon limit False rest

--| Lines at `column`, each a statement, the last its value (`block`); with
--| `many` false, one line continuing the line above. A block of one line
--| is that line's expression; of more, a `Block`.
def block (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool): {Parse Item} Expr :=
  let inner := if many then { modes | limit = Some column, letValue = None } else { modes | limit = Some column }
  blockResult (blockLines (Parse.mark().left + 1) self inner column many [])

def blockResult (statements: List Statement): {Parse Item} Expr := match statements with
  | [ExprStatement value] => value
  | [ExprStatement value, last, ..earlier] =>
    match [last, ..earlier].reverse with
      | [first, ..rest] => Block first rest value
      | [] => value
  | [LetStatement _, .._] => fatal "a block must end with an expression, not `let`"
  | [LocalDef _ _ _, .._] => fatal "a block must end with an expression, not a local `def` or `theorem`"
  | [] => fatal "the parser read no line of a block"

--| The lines of a block, newest first. Each reads at least one item, or
--| the loop stops, so the fuel (the items left and one more) is enough.
def blockLines (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat)
    (many: Bool) (found: List Statement):
    {Parse Item} List Statement :=
  match fuel with
    | Zero => found
    | Succ more => blockLine more self modes column many found offset() left()

def blockLine (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (before: Nat) (items: List Item):
    {Parse Item} List Statement :=
  blockPeek more self modes column many found before { modes | allow = nextIndex items }

--| The index of the next item, which a block's line allows to start a line (Rust's `self.pos`).
def nextIndex: List Item → Option Nat
  | [item, .._] => Some item.index
  | [] => None

def blockPeek (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (before: Nat) (statementModes: Modes):
    {Parse Item} List Statement :=
  blockKind more self modes column many found before statementModes statementModes.peek

def lineKindOf: Option Tok → LineKind
  | Some KwLet => LetLine
  | Some KwDef | Some KwTheorem | Some At => DefLine
  | _ => ExprLine

def blockKind (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (before: Nat) (statementModes: Modes) (seen: Option Tok):
    {Parse Item} List Statement :=
  blockDone more self modes column many found before
    (statement self { statementModes | lines = [{ column, many, kind = lineKindOf seen }, ..modes.lines] })

def blockDone (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (found: List Statement) (before: Nat) (line: Statement):
    {Parse Item} List Statement :=
  blockItems more self modes column many [line, ..found] before left()

def blockItems (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (done: List Statement) (before: Nat):
    List Item → {Parse Item} List Statement
  | [next, .._] => blockOffset more self modes column many done before next offset()
  | [] => done

def blockOffset (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (many: Bool)
    (done: List Statement) (before: Nat) (next: Item) (now: Nat):
    {Parse Item} List Statement :=
  if now != before
    && many
    && next.leaf.token.lineStart
    && next.leaf.token.column == column
    && !endsBlocks next.kind then
    blockLines more self modes column many done
  else done

def endsBlocks: Tok → Bool
  | Pipe | KwWhere | ColonEq | KwDecreasing | KwUnfolding => True
  | _ => False

--| The column of the first token on the line of the next token.
def headIndent(): {Parse Item} Nat := headIndentOn left()

def headIndentOn (items: List Item): Nat := items.head.map (item => item.lineIndent) |> .getOrElse 0

def exprInline (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := exprInlineOn self modes modes.peek

def exprInlineOn (self: Goal → {Parse Item} Expr) (modes: Modes): Option Tok → {Parse Item} Expr
  | Some kind => if startsKeywordExpr kind then exprKeyword self modes kind else exprOther self modes
  | None => exprOther self modes

--| The keywords that start an expression read by the layout and proof constructs (stage 2c).
def startsKeywordExpr: Tok → Bool
  | KwHandle | KwLet | KwCalc | KwRewrite | KwCases | KwMatch => True
  | _ => False

def exprKeyword (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok): {Parse Item} Expr :=
  if kind == KwHandle then handleExpr self modes
  else if kind == KwLet then letExpr self modes
  else if kind == KwCalc then calcExpr self modes
  else if kind == KwRewrite then rewriteExpr self modes
  else if kind == KwCases then casesExpr self modes
  else matchPiped self modes

def letExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let binding := letStatement self modes.sealed
  letBody self modes binding

def matchPiped (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let indent := headIndent()
  let keyword := bump()
  let matched := matchExpr self modes keyword
  matchedPiped self modes indent matched (atPipe modes)

def matchedPiped (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (matched: Expr) (piped: Bool):
    {Parse Item} Expr :=
  if piped then pipeChain self modes indent matched else matched

def exprOther (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := exprWalk self modes (walkHere modes)

--| The keyword `byWalking` starts a walk (`expr_inline`).
def walkHere (modes: Modes): {Parse Item} Bool := walkOn modes left()

def walkOn (modes: Modes) (items: List Item): Bool := isSome KwByWalking (peekIn modes 0 items)

def exprWalk (self: Goal → {Parse Item} Expr) (modes: Modes) (walk: Bool): {Parse Item} Expr :=
  if walk then walkExpr self modes else exprLambda self modes (lambdaHere modes)

def lambdaHere (modes: Modes): {Parse Item} Bool := lambdaAhead modes (Parse.mark().left + 1) left()

def lambdaResultHere (modes: Modes): {Parse Item} Bool := lambdaResultType modes (Parse.mark().left + 1) False left()

def exprLambda (self: Goal → {Parse Item} Expr) (modes: Modes) (lambdas: Bool): {Parse Item} Expr :=
  if lambdas then lambda self modes None else exprResult self modes (lambdaResultHere modes)

def exprResult (self: Goal → {Parse Item} Expr) (modes: Modes) (refused: Bool): {Parse Item} Expr :=
  if refused then fatal "a lambda doesn't take a result type" else exprBinder self modes modes.peek

def exprBinder (self: Goal → {Parse Item} Expr) (modes: Modes): Option Tok → {Parse Item} Expr
  | Some kind =>
    if kind == KwExists || kind == KwForall then quantifier self modes
    else if kind == KwIf then ifKeyword self modes
    else exprPlain self modes
  | None => exprPlain self modes

def ifKeyword (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let indent := headIndent()
  let keyword := bump()
  ifExpr self modes indent keyword

def exprPlain (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  exprImplicit self modes (implicitHere modes)

def implicitHere (modes: Modes): {Parse Item} Bool := implicitOn (Parse.mark().left + 1) left() modes.peek

def implicitOn (fuel: Nat) (items: List Item) (seen: Option Tok): Bool :=
  implicitBinderAhead fuel items && isSome LBracket seen

def exprImplicit (self: Goal → {Parse Item} Expr) (modes: Modes) (implicit: Bool): {Parse Item} Expr :=
  if implicit then piExpr self modes True else exprPi self modes (piHere modes)

def piHere (modes: Modes): {Parse Item} Bool := piOn left() modes.peek

def piOn (items: List Item) (seen: Option Tok): Bool := piBinderAhead items && isSome LParen seen

def exprPi (self: Goal → {Parse Item} Expr) (modes: Modes) (pi: Bool): {Parse Item} Expr :=
  if pi then piExpr self modes False else operatorExpr self modes

def andOrAhead (modes: Modes): {Parse Item} Bool := andOrOn modes left()

def andOrOn (modes: Modes) (items: List Item): Bool :=
  isSome AndAnd (peekIn modes 0 items) || isSome OrOr (peekIn modes 0 items)

--| The rest of `expr_inline`: comparisons, `&&` and `||`, `<->`, a method
--| section around them, then `->` or `;`.
def operatorExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := opStart self modes offset()

def opStart (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Nat): {Parse Item} Expr :=
  opSection self modes start (modes.at Dot)

def opSection (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Nat) (section: Bool): {Parse Item} Expr :=
  opCompared self modes section (cmpExpr self (if section then { modes | sectionHead = Some start } else modes))

def opCompared (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (compared: Expr): {Parse Item} Expr :=
  opLogic self modes section (logicAfter self modes compared)

def logicOf (self: Goal → {Parse Item} Expr) (modes: Modes) (compared: Expr) (ahead: Bool): {Parse Item} Expr :=
  if ahead then logicChain self modes compared else compared

def logicLevel (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  logicAfter self modes (cmpExpr self modes)

def logicAfter (self: Goal → {Parse Item} Expr) (modes: Modes) (compared: Expr): {Parse Item} Expr :=
  logicOf self modes compared (andOrAhead modes)

def opLogic (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (logic: Expr): {Parse Item} Expr :=
  opIffed self modes section (iffOf self modes logic (modes.at IffArrow))

def iffOf (self: Goal → {Parse Item} Expr) (modes: Modes) (logic: Expr) (ahead: Bool): {Parse Item} Expr :=
  if ahead then iff self modes logic else logic

def opIffed (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (iffed: Expr): {Parse Item} Expr :=
  opSequence self modes (sectioned section iffed) (sequenceAhead modes)

def opSequence (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr) (sequence: Bool): {Parse Item} Expr :=
  opEnd self modes value sequence modes.peek

def opEnd (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr) (sequence: Bool): Option Tok → {Parse Item} Expr
  | Some kind =>
    if kind == Arrow then
      let arrow := bump()
      arrowEnd self modes value arrow
    else if kind == Semi && sequence then semiExpr self modes value
    else value
  | None => value

def arrowEnd (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr) (arrow: Word): {Parse Item} Expr :=
  Infix InfixArrow value arrow (resultType self modes)

def semiExpr (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr): {Parse Item} Expr :=
  let semicolon := bump()
  semiAfter self modes value semicolon modes.peek

def semiAfter (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr) (semicolon: Word):
    Option Tok → {Parse Item} Expr
  | None | Some RParen | Some RBracket | Some RBrace | Some Comma => fatal semicolonAtEnd
  | _ => Infix InfixSeq value semicolon (full self modes)

def semicolonAtEnd: Text := "`;` needs an expression after it: `(a; b)` runs `a`, then gives `b`'s value"

--| `a && b || c`: `&&` within each disjunct and `||` between them, both
--| grouped to the right.
def logicChain (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Expr): {Parse Item} Expr :=
  let links := logicLinks self modes
  groupLogic (links.length + 1) first links

def logicLinks (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} List (Word, Expr) :=
  Parse.loop (() => logicOn self modes modes.peek)

def logicOn (self: Goal → {Parse Item} Expr) (modes: Modes): Option Tok → {Parse Item} Option (Word, Expr)
  | Some kind => if kind == AndAnd || kind == OrOr then logicLink self modes else None
  | None => None

def logicLink (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Option (Word, Expr) :=
  let operator := bump()
  logicOperand self modes operator (quantifierAhead modes)

def logicOperand (self: Goal → {Parse Item} Expr) (modes: Modes) (operator: Word) (quantified: Bool):
    {Parse Item} Option (Word, Expr) :=
  if quantified then
    let operand := quantifier self modes
    Some (operator, operand)
  else
    let operand := cmpExpr self modes
    Some (operator, operand)

def groupLogic (fuel: Nat) (first: Expr) (links: List (Word, Expr)): Expr := groupAfter fuel (conjunctionOf first links)

def groupAfter (fuel: Nat) (conjoined: (Expr, List (Word, Expr))): Expr := match conjoined with
  | (conjunction, after) => groupFrom fuel conjunction after

def groupFrom (fuel: Nat) (conjunction: Expr) (after: List (Word, Expr)): Expr := match fuel, after with
  | Succ more, [(or, next), ..rest] => Infix InfixBinary conjunction or (groupLogic more next rest)
  | _, _ => conjunction

--| The `&&`s from `first` up to the next `||`, grouped to the right, and
--| the links from that `||` on.
def conjunctionOf (first: Expr): List (Word, Expr) → (Expr, List (Word, Expr))
  | [(and, next), ..rest] =>
    if and.text == "&&" || and.text == "∧" then conjunctionJoin first and (conjunctionOf next rest)
    else (first, [(and, next), ..rest])
  | links => (first, links)

def conjunctionJoin (first: Expr) (and: Word) (conjoined: (Expr, List (Word, Expr))): (Expr, List (Word, Expr)) :=
  match conjoined with | (right, after) => (Infix InfixBinary first and right, after)

--| `a <-> b`, which doesn't chain.
def iff (self: Goal → {Parse Item} Expr) (modes: Modes) (left: Expr): {Parse Item} Expr :=
  let operator := bump()
  iffAfter self modes left operator (quantifierAhead modes)

def iffAfter (self: Goal → {Parse Item} Expr) (modes: Modes) (left: Expr) (operator: Word) (quantified: Bool):
    {Parse Item} Expr :=
  let right := iffRight self modes quantified
  iffEnd left operator right (modes.at IffArrow)

def iffRight (self: Goal → {Parse Item} Expr) (modes: Modes) (quantified: Bool): {Parse Item} Expr :=
  if quantified then quantifier self modes
  else
    let compared := cmpExpr self modes
    logicAfter self modes compared

def iffEnd (left: Expr) (operator: Word) (right: Expr) (chained: Bool): {Parse Item} Expr :=
  if chained then fatal "`<->` doesn't chain" else Infix InfixIff left operator right

def quantifierAhead (modes: Modes): {Parse Item} Bool := modes.at KwExists || modes.at KwForall

def quantifier (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := quantifierOn self modes left()

def quantifierOn (self: Goal → {Parse Item} Expr) (modes: Modes) (items: List Item): {Parse Item} Expr :=
  match items with
    | [item, .._] => if item.kind == KwForall then forallExpr self modes else existsExpr self modes
    | _ => existsExpr self modes

def existsExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let keyword := bump()
  let here := Parse.mark()
  let items := left()
  existsLambda self modes keyword (lambdaAhead modes (here.left + 1) items)

def existsLambda (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word) (ahead: Bool): {Parse Item} Expr :=
  if ahead then lambda self modes (Some keyword) else modes.fail "a parameter and `=>` after `exists`"

--| `∀ (x: A) [b: B] n => P`: names and typed groups, but no patterns.
def forallExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let keyword := bump()
  let params := forallParams self modes
  if params.isEmpty then modes.fail "a parameter after `${keyword.text}`"
  else forallArrow self modes keyword params (modes.at FatArrow)

def forallArrow (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word) (params: List Param) (atArrow: Bool):
    {Parse Item} Expr :=
  if atArrow then
    let arrow := bump()
    Binding BindsForall (Some keyword) params arrow (full self modes)
  else modes.fail "`=>` after the parameters of `${keyword.text}`"

def forallParams (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} List Param :=
  Parse.loop (() => forallStep self modes left())

def forallStep (self: Goal → {Parse Item} Expr) (modes: Modes) (items: List Item): {Parse Item} Option Param :=
  match items with
    | [item, .._] => if modes.stops item then None else forallParam self modes items item
    | _ => None

def forallParam (self: Goal → {Parse Item} Expr) (modes: Modes) (items: List Item) (item: Item):
    {Parse Item} Option Param :=
  match item.kind with
    | Lower =>
      if isQualified item then None
      else
        let name := bump()
        Some (NameParam name)
    | Underscore =>
      let name := bump()
      Some (NameParam name)
    | LParen => if annotatedParamAhead items then forallGroup self modes else None
    | LBracket => if implicitGroupAt items || namelessAutoAt items then forallGroup self modes else None
    | _ => None

def forallGroup (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Option Param :=
  let group := headerGroup self modes GroupLambda (Some forallDefault)
  Some (Grouped group)

--| A lambda's parameters, `=>` and body; with a keyword, an `∃`'s.
def lambda (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Option Word): {Parse Item} Expr :=
  let params := lambdaParams self modes
  if params.isEmpty then modes.fail "a parameter name"
  else
    let arrow := modes.expect FatArrow "`=>`"
    Binding (if keyword.isSome then BindsExists else BindsLambda) keyword params arrow (full self modes)

def lambdaParams (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} List Param :=
  Parse.loop (() => lambdaStep self modes left())

def lambdaStep (self: Goal → {Parse Item} Expr) (modes: Modes) (items: List Item): {Parse Item} Option Param :=
  match items with
    | [item, .._] => if modes.stops item then None else lambdaParam self modes items item.kind
    | _ => None

def lambdaParam (self: Goal → {Parse Item} Expr) (modes: Modes) (items: List Item) (kind: Tok):
    {Parse Item} Option Param :=
  match kind with
    | Lower =>
      let name := modes.lower "a name"
      Some (NameParam name)
    | Underscore =>
      let name := bump()
      Some (NameParam name)
    | LParen => lambdaParen self modes items
    | LBracket => if implicitGroupAt items || namelessAutoAt items then lambdaGroup self modes else None
    | LBrace =>
      let pattern := patternOf modes
      Some (PatternParam pattern)
    | _ => None

def lambdaGroup (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Option Param :=
  let group := headerGroup self modes GroupLambda (Some defaultPlaces)
  Some (Grouped group)

def lambdaParen (self: Goal → {Parse Item} Expr) (modes: Modes) (items: List Item): {Parse Item} Option Param :=
  if annotatedParamAhead items then lambdaGroup self modes
  else
    let here := Parse.mark()
    lambdaPattern self modes (annotatedPatternAhead (here.left + 1) items)

def lambdaPattern (self: Goal → {Parse Item} Expr) (modes: Modes) (typed: Bool): {Parse Item} Option Param :=
  if typed then
    let open := bump()
    let inner := modes.inBrackets
    let pattern := patternOf inner
    let colon := inner.expect Colon "`:`"
    let annotation := binderType self inner
    let close := inner.expect RParen "`)`"
    Some (TypedPattern open pattern colon annotation close)
  else
    let pattern := patternOf modes
    Some (PatternParam pattern)

def ifExpr (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (keyword: Word): {Parse Item} Expr :=
  let binder := namedBinder modes
  let condition := full self modes.sealed
  let thenKeyword := modes.expectKeyword KwThen "`then`" indent
  let whenTrue := full self modes.sealed
  let elseKeyword := modes.expectKeyword KwElse "`else`" indent
  If keyword binder condition thenKeyword whenTrue elseKeyword (full self modes)

--| `h:` before a condition or scrutinee.
def namedBinder (modes: Modes): {Parse Item} Option (Word, Word) :=
  namedBinderOn modes (modes.at Lower) (modes.peekAt 1)

def namedBinderOn (modes: Modes) (lower: Bool) (second: Option Tok): {Parse Item} Option (Word, Word) :=
  if lower && isSome Colon second then
    let name := modes.lower "a name"
    let colon := bump()
    Some (name, colon)
  else None

--| `then` or `else`, which may also start a line left of the block's
--| column, if not left of the `if`'s line (`expect_keyword`).
def Modes.expectKeyword (modes: Modes) (wanted: Tok) (what: Text) (indent: Nat): {Parse Item} Word :=
  modes.expectKeywordOn wanted what indent modes.peek left()

def Modes.expectKeywordOn (modes: Modes) (wanted: Tok) (what: Text) (indent: Nat) (seen: Option Tok) (items: List Item):
    {Parse Item} Word :=
  match seen, items with
    | None, [item, .._] if item.kind == wanted && item.leaf.token.lineStart && item.leaf.token.column >= indent =>
      bump()
    | _, _ => modes.expect wanted what

--| A `|>` next: on this line, or starting one (`at_pipe`).
def atPipe (modes: Modes): {Parse Item} Bool := atPipeOn modes left()

def atPipeOn (modes: Modes): List Item → Bool
  | [item, .._] => item.kind == PipeGt && (!modes.stops item || item.leaf.token.lineStart)
  | [] => False

--| `x |> f |> g`, after `x`: grouped to the left.
--| `indent` is the column of the line the piped value starts on: a line
--| starting with `|>` continues the chain if it isn't left of it.
def pipeChain (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (value: Expr): {Parse Item} Expr :=
  pipesFrom (Parse.mark().left + 1) self modes indent value

def pipesFrom (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (value: Expr):
    {Parse Item} Expr :=
  pipesStep fuel self modes indent value (pipeAheadOn modes indent left())

def pipeAheadOn (modes: Modes) (indent: Nat): List Item → Bool
  | [item, .._] =>
    item.kind == PipeGt && (!modes.stops item || (item.leaf.token.lineStart && item.leaf.token.column >= indent))
  | [] => False

def pipesStep (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (value: Expr) (ahead: Bool):
    {Parse Item} Expr :=
  match fuel with
    | Succ more if ahead =>
      let operator := bump()
      pipesAfter more self modes indent value operator (lambdaHere modes)
    | _ => value

def pipesAfter (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (value: Expr)
    (operator: Word) (lambdas: Bool):
    {Parse Item} Expr :=
  let function := pipeFunction self modes lambdas
  pipesFrom more self modes indent (Infix InfixPipe value operator function)

def pipeFunction (self: Goal → {Parse Item} Expr) (modes: Modes) (lambdas: Bool): {Parse Item} Expr :=
  if lambdas then lambda self modes None else pipeOperand self modes

def pipeOperand (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  pipeSection self modes offset() (modes.at Dot)

def pipeSection (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Nat) (section: Bool): {Parse Item} Expr :=
  let inner := if section then { modes | sectionHead = Some start } else modes
  let operand := appendExpr self inner
  if section then Section operand else operand

--| `cmp_expr`: one comparison, a chain of them, or a membership test,
--| each operand a range and its pipeline.
def cmpExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  cmpFirst self modes (left().head.map Item.kind)

def cmpFirst (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Option Tok): {Parse Item} Expr :=
  cmpPiped self modes first (pipedRange self modes)

def cmpPiped (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Option Tok) (lhs: Expr): {Parse Item} Expr :=
  cmpOn self modes first lhs modes.peek

def cmpOn (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Option Tok) (lhs: Expr):
    Option Tok → {Parse Item} Expr
  | Some kind => cmpKind self modes first lhs kind
  | None => lhs

def cmpKind (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Option Tok) (lhs: Expr) (kind: Tok):
    {Parse Item} Expr :=
  if kind == KwIn || kind == NotIn then membership self modes first lhs
  else if kind.isComparison then cmpCompare self modes lhs kind
  else lhs

def cmpCompare (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (kind: Tok): {Parse Item} Expr :=
  let operator := bump()
  cmpAfter self modes lhs kind operator (modes.at KwIf)

def cmpAfter (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (kind: Tok)
    (operator: Word) (conditional: Bool):
    {Parse Item} Expr :=
  if conditional then cmpIf self modes lhs operator else cmpSecond self modes lhs kind operator (pipedRange self modes)

def cmpIf (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (operator: Word): {Parse Item} Expr :=
  let indent := headIndent()
  let keyword := bump()
  Infix InfixBinary lhs operator (ifExpr self modes indent keyword)

def cmpSecond (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (kind: Tok) (operator: Word) (second: Expr):
    {Parse Item} Expr :=
  cmpChain self modes lhs kind operator second modes.peek

def cmpChain (self: Goal → {Parse Item} Expr) (modes: Modes) (lhs: Expr) (kind: Tok) (operator: Word) (second: Expr):
    Option Tok → {Parse Item} Expr
  | Some next =>
    if next.isComparison || next == KwIn || next == NotIn then comparisonChain self modes lhs kind operator second
    else Infix InfixBinary lhs operator second
  | None => Infix InfixBinary lhs operator second

def pipedRange (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := pipedAt self modes headIndent()

def pipedAt (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat): {Parse Item} Expr :=
  pipedAfter self modes indent (rangeExpr self modes)

def pipedAfter (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (range: Expr): {Parse Item} Expr :=
  pipedEnd self modes indent range (atPipe modes)

def pipedEnd (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (range: Expr) (pipe: Bool):
    {Parse Item} Expr :=
  if pipe then pipeChain self modes indent range else range

def membership (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Option Tok) (element: Expr): {Parse Item} Expr :=
  if isSome Bang first then fatal "`!` here applies to the element, not to the membership test"
  else
    let operator := bump()
    Infix InfixMembership element operator (pipedRange self modes)

--| `a <= b < c …`, after `a <= b`.
def comparisonChain (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Expr) (kind: Tok)
    (operator: Word) (second: Expr):
    {Parse Item} Expr :=
  if kind == Equals || kind == EqEq || kind == NotEq then fatal (chainRefused kind)
  else chainAfter self modes first operator second (isDescending kind)

def chainAfter (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Expr) (operator: Word)
    (second: Expr) (descending: Bool):
    {Parse Item} Expr :=
  let links := chainLinks self modes descending
  Chain first [(operator, second), ..links]

--| `>` and `>=` start a chain that goes down.
def isDescending (kind: Tok): Bool := kind == Gt || kind == Ge

def chainRefused (kind: Tok): Text := "`${kind.written}` can't be part of a chain of comparisons"

def chainLinks (self: Goal → {Parse Item} Expr) (modes: Modes) (descending: Bool): {Parse Item} List (Word, Expr) :=
  Parse.loop (() => chainOn self modes descending modes.peek)

def chainOn (self: Goal → {Parse Item} Expr) (modes: Modes) (descending: Bool):
    Option Tok → {Parse Item} Option (Word, Expr)
  | Some kind => chainLink self modes descending kind
  | None => None

def chainLink (self: Goal → {Parse Item} Expr) (modes: Modes) (descending: Bool) (kind: Tok):
    {Parse Item} Option (Word, Expr) :=
  let flip := isDescending kind
  if kind == Equals || kind == EqEq then fatal (chainRefused kind)
  else if kind == NotEq then fatal "`!=` can't be part of a chain of comparisons"
  else if kind == KwIn || kind == NotIn then fatal "`in` can't be part of a chain of comparisons"
  else if !(kind == Lt || kind == Le || flip) then None
  else if flip != descending then
    fatal "a chain of comparisons goes one way: `<` and `<=` can't be mixed with `>` and `>=`"
  else
    let operator := bump()
    let operand := pipedRange self modes
    Some (operator, operand)

def rangeExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  rangeFrom self modes (appendExpr self modes)

def rangeFrom (self: Goal → {Parse Item} Expr) (modes: Modes) (low: Expr): {Parse Item} Expr :=
  rangeOn self modes low modes.peek

def rangeOn (self: Goal → {Parse Item} Expr) (modes: Modes) (low: Expr): Option Tok → {Parse Item} Expr
  | Some kind =>
    if kind == DotDot then fatal "a range is `a ..< b` (up to, not including, `b`) or `a ..= b` (through `b`)"
    else if kind == DotDotLt || kind == DotDotEq then rangeHigh self modes low
    else low
  | None => low

def rangeHigh (self: Goal → {Parse Item} Expr) (modes: Modes) (low: Expr): {Parse Item} Expr :=
  let operator := bump()
  rangeEnd modes low operator (appendExpr self modes)

def rangeEnd (modes: Modes) (low: Expr) (operator: Word) (high: Expr): {Parse Item} Expr :=
  rangeChained low operator high (modes.at DotDotLt || modes.at DotDotEq)

def rangeChained (low: Expr) (operator: Word) (high: Expr) (chained: Bool): {Parse Item} Expr :=
  if chained then fatal "ranges don't chain" else Infix InfixRange low operator high

--| `a ++ b ++ c`, grouped to the right.
def appendExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let first := addExpr self modes
  rightNested first (operatorLinks modes (kind => kind == PlusPlus) (() => addExpr self modes))

def rightNested (first: Expr): List (Word, Expr) → Expr
  | [] => first
  | [(operator, next), ..rest] => Infix InfixBinary first operator (rightNested next rest)

--| The operators `takes` accepts that come next, each with its operand.
def operatorLinks (modes: Modes) (takes: Tok → Bool) (operand: () → {Parse Item} Expr):
    {Parse Item} List (Word, Expr) :=
  Parse.loop (() =>
    match modes.peek with
      | Some kind if takes kind =>
        let operator := bump()
        let value := operand()
        Some (operator, value)
      | _ => None)

def leftNested (first: Expr): List (Word, Expr) → Expr
  | [] => first
  | [(operator, next), ..rest] => leftNested (Infix InfixBinary first operator next) rest

def addExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let first := mulExpr self modes
  leftNested first (operatorLinks modes (kind => kind == Plus || kind == Minus) (() => mulExpr self modes))

def mulExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let first := unary self modes
  leftNested first
    (operatorLinks modes (kind => kind == Star || kind == Slash || kind == Percent) (() => unary self modes))

def unary (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := unaryOn self modes modes.peek

def unaryOn (self: Goal → {Parse Item} Expr) (modes: Modes): Option Tok → {Parse Item} Expr
  | Some kind => unarySome self modes kind
  | None => app self modes

def unarySome (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok): {Parse Item} Expr :=
  if kind == KwMatch then
    let keyword := bump()
    matchExpr self modes keyword
  else unaryBar self modes kind (matchesBarAhead modes)

def unaryBar (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok) (bar: Bool): {Parse Item} Expr :=
  if bar then
    let keyword := bump()
    clauseLambda self modes keyword None ClauseMatches
  else unaryNext self modes kind left()

def unaryNext (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok) (items: List Item): {Parse Item} Expr :=
  if kind == Minus && negativeNumeral items then app self modes
  else if kind == Minus || kind == Bang then
    let operator := bump()
    Prefix operator (self { modes, level = LevelUnary })
  else app self modes

--| `f a b`: one `App` however many arguments.
def app (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := appAt self modes offset()

def appAt (self: Goal → {Parse Item} Expr) (modes: Modes) (start: Nat): {Parse Item} Expr :=
  appHead self modes (modes.at Dot && modes.sectionHead != Some start)

def appHead (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool): {Parse Item} Expr :=
  appCalls self modes section (atom self modes True)

def appCalls (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (head: Expr): {Parse Item} Expr :=
  appEnd self modes section head (startsAtom modes)

def appEnd (self: Goal → {Parse Item} Expr) (modes: Modes) (section: Bool) (head: Expr) (applies: Bool):
    {Parse Item} Expr :=
  if applies then sectioned section (appliedTo self modes head) else sectioned section head

def sectioned (section: Bool) (applied: Expr): Expr := if section then Section applied else applied

--| The head's arguments, after a first that `startsAtom` has promised: the first is read outright, so the list is
--| not empty by construction.
def appliedTo (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Expr): {Parse Item} Expr :=
  let first := argument self modes
  let more := arguments self modes
  App head [first, ..more]

def arguments (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} List Expr :=
  Parse.loop (() => argumentStep self modes (startsAtom modes))

def argumentStep (self: Goal → {Parse Item} Expr) (modes: Modes) (starts: Bool): {Parse Item} Option Expr :=
  if starts then Some (argument self modes) else None

def argument (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := argumentAt self modes left()

def argumentAt (self: Goal → {Parse Item} Expr) (modes: Modes) (items: List Item): {Parse Item} Expr :=
  if sectionLineAt modes items then fatal "a line can't start with a method section"
  else argumentBrace self modes (modes.at Upper && isSome LBrace (modes.peekAt 1))

def sectionLineAt (modes: Modes): List Item → Bool
  | [item, .._] => item.kind == Dot && item.leaf.token.lineStart && !modes.stops item
  | [] => False

def argumentBrace (self: Goal → {Parse Item} Expr) (modes: Modes) (brace: Bool): {Parse Item} Expr :=
  if brace then braceArgument self modes else self { modes, level = LevelArgument }

def startsAtom (modes: Modes): {Parse Item} Bool := startsAtomOn modes left()

def startsAtomOn (modes: Modes) (items: List Item): Bool := match peekIn modes 0 items with
  | Some kind => startsAtomKind modes kind items
  | None => False

def startsAtomKind (modes: Modes) (kind: Tok) (items: List Item): Bool :=
  opensArgument kind
    || (kind == Dot && sectionAt items)
    || (kind == KwCases && bareCasesOn modes items)
    || argumentPrefix items

def opensArgument: Tok → Bool
  | Lower |
      Upper |
      Num |
      Float |
      CharLit |
      Str |
      StrStart |
      KwInclude |
      KwArithmetic |
      KwAlgebra |
      TypeU |
      PropU |
      LParen |
      LBracket |
      LBrace |
      Underscore |
      Question => True
  | _ => False

def bareCases (modes: Modes): {Parse Item} Bool := bareCasesOn modes left()

def bareCasesOn (modes: Modes) (items: List Item): Bool := match peekIn modes 1 items with
  | Some KwThen | Some KwIn => False
  | _ => True

--| An atom, then `()` calls and field accesses.
def atom (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool): {Parse Item} Expr :=
  let first := modes.peek
  let base := atomBase self modes
  atomAfter self modes head first base

--| `base`, which started with a token of kind `first`, and what follows it: a record's fields, calls and field
--| accesses.
def atomAfter (self: Goal → {Parse Item} Expr) (modes: Modes) (head: Bool) (first: Option Tok) (base: Expr):
    {Parse Item} Expr :=
  let section := isSome Dot first
  let upper := isSome Upper first
  let paren := isSome LParen first
  let callable := isSome Lower first || upper || section
  let (based, callable) := atomRecord self modes head upper base callable
  let result := suffixes (Parse.mark().left + 1) modes based callable paren
  if section && !head then Section result else result

def atomRecord (self: Goal → {Parse Item} Expr) (modes: Modes) (head upper: Bool) (base: Expr) (callable: Bool):
    {Parse Item} (Expr, Bool) :=
  if upper && head && modes.at LBrace then
    let fields := recordExpr self modes
    (CtorFields base fields, False)
  else (base, callable)

def suffixes (fuel: Nat) (modes: Modes) (target: Expr) (callable paren: Bool): {Parse Item} Expr := match fuel with
  | Zero => target
  | Succ more => suffixesAfterCall more modes (suffixCalled target callable paren) paren

--| `f()`, if the next two items are a glued `()` and `target` can be called.
def suffixCalled (target: Expr) (callable paren: Bool): {Parse Item} Expr := suffixCalledOn target callable paren left()

def suffixCalledOn (target: Expr) (callable paren: Bool) (items: List Item): {Parse Item} Expr :=
  if unitCall items && (callable || paren && callableParen target) then
    let open := bump()
    let close := bump()
    App target [Unit open close]
  else target

--| A field access after `called`, and what follows it.
def suffixesAfterCall (more: Nat) (modes: Modes) (called: Expr) (paren: Bool): {Parse Item} Expr :=
  suffixesOn more modes called paren left()

def suffixesOn (more: Nat) (modes: Modes) (called: Expr) (paren: Bool) (items: List Item): {Parse Item} Expr :=
  match items with
    | [dot, field, .._] if dot.kind == Dot && !modes.stops dot && !sectionAt items =>
      if !((field.kind == Lower || field.kind == Upper) && !isQualified field && !modes.stops field) then
        fatal "expected a field name after `.`"
      else if !dot.glued || !field.glued then fatal "field access is written without spaces around the `.`"
      else
        let dotLeaf := bump()
        let name := bump()
        suffixes more modes (FieldAccess (Some called) dotLeaf name) True paren
    | [dot] if dot.kind == Dot && !modes.stops dot => fatal "expected a field name after `.`"
    | _ => called

--| Whether `(e)()` calls `e`: a name or a field access, in brackets.
def callableParen: Expr → Bool
  | Paren _ inner _ => callableInside inner
  | _ => False

def callableInside: Expr → Bool
  | Atom kind _ => kind == Lower || kind == Upper
  | FieldAccess _ _ _ => True
  | Paren _ inner _ => callableInside inner
  | _ => False

def atomBase (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := atomBaseOn self modes modes.peek

def atomBaseOn (self: Goal → {Parse Item} Expr) (modes: Modes): Option Tok → {Parse Item} Expr
  | Some kind => atomOf self modes kind
  | None => atomMissing self modes

--| The kinds `atomBase` reads in slice 1: a `-` or `!`, a bracket, a name or numeral; the others are `atomRest`.
def atomOf (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok): {Parse Item} Expr :=
  if kind == Minus then negativeAtom self modes
  else if kind == Bang then prefixBang self modes
  else if kind == LParen then parenAtom self modes
  else if kind == LBracket then bracketAtom self modes
  else if isWord kind then wordAtom kind
  else atomRest self modes kind

def wordAtom (kind: Tok): {Parse Item} Expr :=
  let word := bump()
  Atom kind word

def atomRest (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok): {Parse Item} Expr :=
  if kind == StrStart then interpolated self modes
  else if kind == KwInclude then includeAtom modes
  else if kind == KwArithmetic then facts self modes KwArithmetic FactsOmega
  else if kind == KwAlgebra then facts self modes KwAlgebra FactsRing
  else if kind == KwCases then casesAtom modes
  else if kind == TypeU then universeAtom modes
  else if kind == LBrace then recordExpr self modes
  else if kind == Dot then sectionStart modes
  else atomMissing self modes

def includeAtom (modes: Modes): {Parse Item} Expr :=
  let keyword := bump()
  includeAfter modes keyword (modes.at Str)

def includeAfter (modes: Modes) (keyword: Word) (path: Bool): {Parse Item} Expr :=
  if path then
    let word := bump()
    Include keyword word
  else modes.fail "a path in quotes, as in `include \"inputs/day04.txt\"`"

def casesAtom (modes: Modes): {Parse Item} Expr := casesAfter modes (bareCases modes)

def casesAfter (modes: Modes) (bare: Bool): {Parse Item} Expr :=
  if bare then
    let keyword := bump()
    Atom KwCases keyword
  else modes.fail "an expression"

def universeAtom (modes: Modes): {Parse Item} Expr :=
  let keyword := bump()
  universeAfter modes keyword left()

def universeAfter (modes: Modes) (keyword: Word) (items: List Item): {Parse Item} Expr := match items with
  | [level, .._] if level.kind == Num && !modes.stops level =>
    if (level.text.toNat |> .getOrElse 0) > 65535 then fatal "universe level is too large"
    else
      let number := bump()
      Universe keyword number
  | _ => Atom TypeU keyword

--| What `atomBase` reads at a token that starts no atom: an error.
def atomMissing (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := atomMissingAt modes modes.peek

def atomMissingAt (modes: Modes) (seen: Option Tok): {Parse Item} Expr :=
  if modes.recover && seen.isNone then atomGap modes (ranOutAtLine modes) else atomNamed modes (modes.peekAt 1)

def atomGap (modes: Modes) (ran: Bool): {Parse Item} Expr :=
  if ran then modes.gap ranOutLine
  else
    let message := modes.unexpected "an expression"
    modes.gap message

def atomNamed (modes: Modes) (second: Option Tok): {Parse Item} Expr :=
  if isSome FatArrow second then modes.failName "an expression" else modes.fail "an expression"

def bracketAtom (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  bracketSecond self modes (modes.peekAt 1)

def bracketSecond (self: Goal → {Parse Item} Expr) (modes: Modes) (second: Option Tok): {Parse Item} Expr :=
  bracketAt self modes second (modes.peekAt 2)

def bracketAt (self: Goal → {Parse Item} Expr) (modes: Modes) (second third: Option Tok): {Parse Item} Expr :=
  if (isSome Lower second || isSome KwDecreasing second) && isSome ColonEq third then
    namedArgument self modes RBracket "`]`"
  else listExpr self modes

def isWord: Tok → Bool
  | Lower | Upper | Num | Float | Str | CharLit | Underscore | Question | PropU => True
  | _ => False

def negativeAtom (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := negativeAtomOn self modes left()

def negativeAtomOn (self: Goal → {Parse Item} Expr) (modes: Modes) (items: List Item): {Parse Item} Expr :=
  if negativeNumeral items then negativeNumber() else prefixAtom self modes (argumentMinus items)

def negativeNumber(): {Parse Item} Expr :=
  let minus := bump()
  numberAfter minus left()

def numberAfter (minus: Word) (items: List Item): {Parse Item} Expr :=
  let number := bump()
  Prefix minus (Atom (numberKind items) number)

def numberKind (items: List Item): Tok := items.head.map Item.kind |> .getOrElse Num

def prefixBang (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := prefixBangOn self modes left()

def prefixBangOn (self: Goal → {Parse Item} Expr) (modes: Modes) (items: List Item): {Parse Item} Expr :=
  prefixAtom self modes (argumentBang items)

--| A `-` or `!` negating an argument, if `negates`.
def prefixAtom (self: Goal → {Parse Item} Expr) (modes: Modes) (negates: Bool): {Parse Item} Expr :=
  if negates then
    let operator := bump()
    Prefix operator (self { modes, level = LevelArgument })
  else modes.failName "an expression"

--| `arithmetic` or `algebra`, and its facts if a list follows.
def facts (self: Goal → {Parse Item} Expr) (modes: Modes) (token: Tok) (kind: FactsKind): {Parse Item} Expr :=
  let keyword := bump()
  factsAfter self modes token kind keyword (modes.at LBracket)

def factsAfter (self: Goal → {Parse Item} Expr) (modes: Modes) (token: Tok) (kind: FactsKind)
    (keyword: Word) (bracket: Bool):
    {Parse Item} Expr :=
  if bracket then
    let list := listExpr self modes
    factsEnd kind keyword list
  else Atom token keyword

def factsEnd (kind: FactsKind) (keyword: Word) (list: Expr): {Parse Item} Expr :=
  if hasSpread list then fatal "a list of facts can't have a `..` spread" else Facts kind keyword list

def hasSpread: Expr → Bool
  | ListOf _ items _ _ => items.any (matches
    | Spread _ _)
  | _ => False

--| `.name` with no receiver, starting a method section.
def sectionStart (modes: Modes): {Parse Item} Expr :=
  let dot := bump()
  sectionAfter modes dot left()

def sectionAfter (modes: Modes) (dot: Word) (items: List Item): {Parse Item} Expr := match items with
  | [name, .._] if name.kind == Lower && name.glued && !isQualified name && !modes.stops name =>
    FieldAccess None dot bump()
  | _ => fatal "expected a name right after `.`"

--| `(x := e)` or `[x := e]`.
def namedArgument (self: Goal → {Parse Item} Expr) (modes: Modes) (closer: Tok) (closeText: Text): {Parse Item} Expr :=
  let open := bump()
  let inner := modes.inBrackets
  namedHead self inner open closer closeText (inner.at KwDecreasing)

def namedHead (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (closer: Tok)
    (closeText: Text) (keyword: Bool):
    {Parse Item} Expr :=
  let name := if keyword then bump() else inner.lower "a name"
  namedColon self inner open name closer closeText

def namedColon (self: Goal → {Parse Item} Expr) (inner: Modes) (open name: Word) (closer: Tok) (closeText: Text):
    {Parse Item} Expr :=
  let colonEq := bump()
  let value := full self inner
  namedClose inner open name colonEq value closer closeText

def namedClose (inner: Modes) (open name colonEq: Word) (value: Expr) (closer: Tok) (closeText: Text):
    {Parse Item} Expr :=
  NamedArg open name colonEq value (inner.expect closer closeText)

--| What starts with `(`: `()`, a named argument, an operator section, a
--| bracketed expression, a tuple or an annotation.
def parenAtom (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  parenSecond self modes (modes.peekAt 1)

def parenSecond (self: Goal → {Parse Item} Expr) (modes: Modes) (second: Option Tok): {Parse Item} Expr :=
  parenOn self modes second (modes.peekAt 2)

def parenOn (self: Goal → {Parse Item} Expr) (modes: Modes) (second third: Option Tok): {Parse Item} Expr :=
  if parenOutside second third then parenOther self modes second third else parenRest self modes left()

--| The `(` is followed by `)`, a name and `:=`, or an operator a section can take.
def parenOutside (second third: Option Tok): Bool :=
  isSome RParen second
    || (isSome Lower second && isSome ColonEq third)
    || (match second with
      | Some next => next.isSectionOperator || (next.isOperator && isSome RParen third)
      | None => False)

def parenOther (self: Goal → {Parse Item} Expr) (modes: Modes) (second third: Option Tok): {Parse Item} Expr :=
  if isSome RParen second then
    let open := bump()
    let close := bump()
    Unit open close
  else if isSome Lower second && isSome ColonEq third then namedArgument self modes RParen "`)`"
  else operatorSection self modes

def parenRest (self: Goal → {Parse Item} Expr) (modes: Modes) (items: List Item): {Parse Item} Expr :=
  match rightOperator items with
    | Some inside => rightSection self modes inside
    | None => bracketed self modes

def bracketed (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let open := bump()
  bracketedTail self modes open

def bracketedTail (self: Goal → {Parse Item} Expr) (modes: Modes) (open: Word): {Parse Item} Expr :=
  let inner := modes.inBrackets
  bracketedFirst self inner open (full self inner)

def bracketedFirst (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr): {Parse Item} Expr :=
  bracketedAfter self inner open first inner.peek

def bracketedAfter (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr):
    Option Tok → {Parse Item} Expr
  | Some kind =>
    if kind == Comma then tupleRest self inner open first
    else if kind == Colon then annotated self inner open first
    else parenClose inner open first
  | None => parenClose inner open first

def parenClose (inner: Modes) (open: Word) (first: Expr): {Parse Item} Expr :=
  let close := inner.expect RParen "`)`"
  Paren open first close

def annotated (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr): {Parse Item} Expr :=
  let colon := bump()
  let annotation := full self inner
  annotatedEnd inner open first colon annotation (inner.at Comma)

def annotatedEnd (inner: Modes) (open: Word) (first: Expr) (colon: Word) (annotation: Expr) (comma: Bool):
    {Parse Item} Expr :=
  if comma then fatal tupleAnnotation
  else
    let close := inner.expect RParen "`)`"
    Annotation open first colon annotation close

--| A tuple: the comma after its first item is read here, so that the items come to at least two (`commaListFrom`
--| would read the same comma and the next item, as the first round of `commaList`).
def tupleRest (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr): {Parse Item} Expr :=
  tupleFuel self inner open first Parse.mark().left

def tupleFuel (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr) (fuel: Nat):
    {Parse Item} Expr :=
  let comma := bump()
  tupleSecond self inner open first fuel (full self inner)

def tupleSecond (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr) (fuel: Nat) (second: Expr):
    {Parse Item} Expr :=
  tupleEnd inner open (commaListFrom fuel inner (tupleEnds inner) (() => full self inner) 2 second [first])

def tupleEnds (inner: Modes) (count: Nat): {Parse Item} Bool := inner.at RParen && count >= 2

def tupleEnd (inner: Modes) (open: Word) (pair: (List Expr, Bool)): {Parse Item} Expr := match pair with
  | (items, trailingComma) => Tuple open items trailingComma (tupleClose inner)

def tupleClose (modes: Modes): {Parse Item} Word := tupleCloseAfter modes (modes.at Colon)

def tupleCloseAfter (modes: Modes) (annotated: Bool): {Parse Item} Word :=
  if annotated then fatal tupleAnnotation else modes.expect RParen "`)`"

def tupleAnnotation: Text := "an annotation can't be written inside a tuple without brackets"

--| `current` and the items after it, and whether a comma followed the
--| last: while a comma follows, it is read (and dropped: rule N left it no
--| comments), and unless `ends` (given the number of items so far) says
--| the list ends there, another item.
def commaList (fuel: Nat) (modes: Modes) (ends: Nat → {Parse Item} Bool) (next: () → {Parse Item} a)
    (current: a) (found: List a):
    {Parse Item} (List a, Bool) :=
  commaListFrom fuel modes ends next 1 current found

--| `count` is the number of items read, `current` included.
def commaListFrom (fuel: Nat) (modes: Modes) (ends: Nat → {Parse Item} Bool) (next: () → {Parse Item} a) (count: Nat)
    (current: a) (found: List a):
    {Parse Item} (List a, Bool) :=
  match fuel, modes.peek with
    | Succ more, Some kind =>
      if kind == Comma then
        let comma := bump()
        if ends count then ([current, ..found].reverse, True)
        else commaListFrom more modes ends next (count + 1) (next()) [current, ..found]
      else ([current, ..found].reverse, False)
    | _, _ => ([current, ..found].reverse, False)

--| `(+ 1)`, `(&&)`: the operator first.
def operatorSection (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let open := bump()
  operatorFirst self modes.inBrackets open left()

def operatorFirst (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (items: List Item): {Parse Item} Expr :=
  let operatorKind := items.head.map Item.kind |> .getOrElse Plus
  let operator := bump()
  operatorHead self inner open operatorKind operator (inner.at RParen)

def operatorHead (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (operatorKind: Tok)
    (operator: Word) (closed: Bool):
    {Parse Item} Expr :=
  if closed then operatorClose open operator None
  else
    let operand := sectionOperand self inner operatorKind
    operatorEnd inner open operator operand (inner.at RParen)

def operatorEnd (inner: Modes) (open operator: Word) (operand: Expr) (closed: Bool): {Parse Item} Expr :=
  if closed then operatorClose open operator (Some operand) else inner.fail "`)` after the operand of a section"

def operatorClose (open operator: Word) (operand: Option Expr): {Parse Item} Expr :=
  OperatorSection open None operator operand bump()

--| A left section's operand: what binds tighter than its operator.
def sectionOperand (self: Goal → {Parse Item} Expr) (modes: Modes) (operator: Tok): {Parse Item} Expr :=
  match operator with
    | Plus => self { modes, level = LevelMultiplicative }
    | Star | Slash | Percent => self { modes, level = LevelUnary }
    | AndAnd => self { modes, level = LevelComparison }
    | OrOr =>
      let first := self { modes, level = LevelComparison }
      rightNested first (operatorLinks modes (kind => kind == AndAnd) (() => self { modes, level = LevelComparison }))
    | IffArrow => self { modes, level = LevelLogic }
    | _ => self { modes, level = LevelAppend }

--| `(k +)`: the operand, which must end just before the operator, `inside`
--| items after the `(`.
def rightSection (self: Goal → {Parse Item} Expr) (modes: Modes) (inside: Nat): {Parse Item} Expr :=
  let open := bump()
  let start := offset()
  rightKind self modes.inBrackets open inside start left()

def rightKind (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (inside start: Nat) (items: List Item):
    {Parse Item} Expr :=
  let operatorKind := match items.drop (inside - 1) with
    | [item, .._] => item.kind
    | [] => Plus
  let operand := rightOperand self inner operatorKind
  rightEnd inner open inside start operand offset()

def rightOperand (self: Goal → {Parse Item} Expr) (inner: Modes) (operatorKind: Tok): {Parse Item} Expr :=
  match operatorKind with
    | Plus => self { modes = inner, level = LevelMultiplicative }
    | Star | Slash | Percent => self { modes = inner, level = LevelUnary }
    | PlusPlus => self { modes = inner, level = LevelAdditive }
    | AndAnd | OrOr | IffArrow => self { modes = inner, level = LevelComparison }
    | _ => self { modes = inner, level = LevelAppend }

def rightEnd (inner: Modes) (open: Word) (inside start: Nat) (operand: Expr) (here: Nat): {Parse Item} Expr :=
  if here != start + inside - 1 then inner.fail "`)` after the operator of a section"
  else
    let operator := bump()
    rightClose inner open operand operator

def rightClose (inner: Modes) (open: Word) (operand: Expr) (operator: Word): {Parse Item} Expr :=
  OperatorSection open (Some operand) operator None (inner.expect RParen "`)`")

def listExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let open := bump()
  listTail self modes open

def listTail (self: Goal → {Parse Item} Expr) (modes: Modes) (open: Word): {Parse Item} Expr :=
  listPeek self modes.inBrackets open

def listPeek (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word): {Parse Item} Expr :=
  listAfter self inner open inner.peek

def listAfter (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word): Option Tok → {Parse Item} Expr
  | Some kind =>
    if kind == RBracket then
      let close := bump()
      ListOf open [] False close
    else listItems self inner open
  | None => listItems self inner open

def listItems (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word): {Parse Item} Expr :=
  listItemsFrom self inner open (listItem self inner)

def listItemsFrom (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (first: Expr): {Parse Item} Expr :=
  listItemsEnd self inner open
    (commaList (Parse.mark().left + 1) inner (count => inner.at RBracket) (() => listItem self inner) first [])

def listItemsEnd (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (pair: (List Expr, Bool)):
    {Parse Item} Expr :=
  match pair with
    | (items, trailingComma) =>
      let close := inner.expect RBracket "`,` or `]`"
      ListOf open items trailingComma close

def listItem (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  listItemAfter self modes (modes.at DotDot)

def listItemAfter (self: Goal → {Parse Item} Expr) (modes: Modes) (spread: Bool): {Parse Item} Expr :=
  if spread then
    let dots := bump()
    listSpread self modes dots (modes.at Comma || modes.at RBracket)
  else full self modes

def listSpread (self: Goal → {Parse Item} Expr) (modes: Modes) (dots: Word) (empty: Bool): {Parse Item} Expr :=
  if empty then fatal "expected a list after `..`, as in `[x, ..xs]`" else Spread dots (full self modes)

def recordExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let open := modes.expect LBrace "`{`"
  let inner := modes.inBrackets
  recordBody self inner open (inner.at RBrace)

def recordBody (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (empty: Bool): {Parse Item} Expr :=
  if empty then Record open None [] False bump() else recordLiteral self inner open (inner.at Lower) (inner.peekAt 1)

def recordLiteral (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (lower: Bool) (second: Option Tok):
    {Parse Item} Expr :=
  let literal := lower && literalSecond second
  let base := recordBase self inner literal
  recordFields self inner open base

def literalSecond: Option Tok → Bool
  | Some Equals | Some Comma | Some RBrace => True
  | _ => False

def recordBase (self: Goal → {Parse Item} Expr) (inner: Modes) (literal: Bool): {Parse Item} Option (Expr, Word) :=
  if literal then None
  else
    let record := full self inner
    recordPipe inner record

def recordPipe (inner: Modes) (record: Expr): {Parse Item} Option (Expr, Word) :=
  let bar := inner.expect Pipe "`|` and the fields to update"
  Some (record, bar)

def recordFields (self: Goal → {Parse Item} Expr) (inner: Modes) (open: Word) (base: Option (Expr, Word)):
    {Parse Item} Expr :=
  let first := recordField self inner
  recordEnd inner open base
    (commaList (Parse.mark().left + 1) inner (count => inner.at RBrace) (() => recordField self inner) first [])

def recordEnd (inner: Modes) (open: Word) (base: Option (Expr, Word)) (pair: (List Expr, Bool)): {Parse Item} Expr :=
  match pair with | (fields, trailingComma) => Record open base fields trailingComma (inner.expect RBrace "`,` or `}`")

def recordField (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let name := modes.lower "a field name"
  recordFieldAfter self modes name (modes.at Equals)

def recordFieldAfter (self: Goal → {Parse Item} Expr) (modes: Modes) (name: Word) (equalsNext: Bool):
    {Parse Item} Expr :=
  if equalsNext then
    let equals := bump()
    RecordField name equals (full self modes)
  else Atom Lower name

--| `C { … }` as an argument.
def braceArgument (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let ctor := atomBase self modes
  CtorFields ctor (recordExpr self modes)

def interpolated (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let start := bump()
  let pieces := interpolations self modes
  Interpolated [TextPiece start, ..pieces]

def interpolations (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} List Piece :=
  let pieces := Parse.loop (() => interpolationStep self modes)
  interpolationLast modes pieces (modes.at StrEnd)

def interpolationStep (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Option Piece :=
  interpolationOn self modes modes.peek

def interpolationOn (self: Goal → {Parse Item} Expr) (modes: Modes) (seen: Option Tok): {Parse Item} Option Piece :=
  if isSome StrMid seen then
    let word := bump()
    Some (TextPiece word)
  else if isSome InterpOpen seen then interpolationOpen self modes
  else if isSome StrEnd seen then None
  else modes.fail "`\${` or the end of the text"

def interpolationOpen (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Option Piece :=
  let open := modes.expect InterpOpen "`\${`"
  let value := full self modes
  let close := modes.expect InterpClose "`}`"
  Some (Interpolation open value close)

def interpolationLast (modes: Modes) (pieces: List Piece) (ended: Bool): {Parse Item} List Piece :=
  let last := interpolationEnd modes ended
  pieces ++ [TextPiece last]

def interpolationEnd (modes: Modes) (ended: Bool): {Parse Item} Word :=
  if ended then bump() else modes.fail "`\${` or the end of the text"

-- `match` and clause lambdas.

type ClauseKind = | ClausePlain | ClauseSome | ClauseMatches

def wordAhead (modes: Modes) (word: Text): {Parse Item} Bool := wordOn modes word left()

def wordOn (modes: Modes) (word: Text): List Item → Bool
  | [item, .._] => item.kind == Lower && item.text == word && !modes.stops item
  | [] => False

def matchesBarAhead (modes: Modes): {Parse Item} Bool := matchesBarOn modes left()

def matchesBarOn (modes: Modes) (items: List Item): Bool :=
  wordOn modes "matches" items
    && isSome Pipe (peekIn modes 1 items)
    && !(isSome Lower (peekIn modes 2 items) && isSome Equals (peekIn modes 3 items))

--| `match induct` and `match reify`: the word, then not what a scrutinee
--| named `induct` would have after it.
def specialAhead (modes: Modes) (word: Text): {Parse Item} Bool := specialOf (wordAhead modes word) (modes.peekAt 1)

def specialOf (word: Bool) (second: Option Tok): Bool :=
  word
    && (match second with
      | Some KwWith | Some Comma | Some Colon | None => False
      | _ => True)

def matchExpr (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word): {Parse Item} Expr :=
  matchSpecial self modes keyword (specialAhead modes "induct")

def matchSpecial (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word) (induct: Bool): {Parse Item} Expr :=
  if induct then
    let word := fixedFrom()
    inductExpr self modes keyword.comments word
  else matchReify self modes keyword (specialAhead modes "reify")

def matchReify (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word) (reify: Bool): {Parse Item} Expr :=
  if reify then
    let word := fixedFrom()
    reifyExpr self modes keyword.comments word
  else matchPipe self modes keyword (modes.at Pipe)

def matchPipe (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word) (piped: Bool): {Parse Item} Expr :=
  if piped then clauseLambda self modes keyword None ClausePlain
  else matchSome self modes keyword (wordAhead modes "some") (modes.peekAt 1)

def matchSome (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word) (some: Bool) (second: Option Tok):
    {Parse Item} Expr :=
  if some && isSome Pipe second then
    let word := bump()
    clauseLambda self modes keyword (Some word) ClauseSome
  else
    let first := scrutinee self modes
    let (scrutinees, _) :=
      commaList (Parse.mark().left + 1) modes (count => False) (() => scrutinee self modes) first []
    let withKeyword := modes.expect KwWith "`with`"
    let arms := matchArms (Parse.mark().left + 1) self modes scrutinees.length None []
    if arms.isEmpty then modes.fail "`|` and an alternative" else Match keyword scrutinees withKeyword arms

def scrutinee (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Scrutinee :=
  let name := namedBinder modes
  let value := self { modes = modes.sealed, level = LevelInline }
  { name, value }

def plural (count: Nat) (noun: Text): Text := if count == 1 then "${count} ${noun}" else "${count} ${noun}s"

def matchArms (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (scrutinees: Nat)
    (column: Option Nat) (found: List Arm):
    {Parse Item} List Arm :=
  matchArmsLined fuel self modes scrutinees found (armColumn column)

def matchArmsLined (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (scrutinees: Nat)
    (found: List Arm) (columned: (Bool, Option Nat)):
    {Parse Item} List Arm :=
  match columned with | (lined, column) => matchArmsAhead fuel self modes scrutinees column found lined (modes.at Pipe)

def matchArmsAhead (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (scrutinees: Nat) (column: Option Nat)
    (found: List Arm) (lined atPipe: Bool):
    {Parse Item} List Arm :=
  match fuel with
    | Succ more => if atPipe && lined then matchArm more self modes scrutinees column found else found.reverse
    | Zero => found.reverse

def matchArm (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (scrutinees: Nat)
    (column: Option Nat) (found: List Arm):
    {Parse Item} List Arm :=
  let bar := bump()
  let patterns := armPatterns modes
  if patterns.length != scrutinees then
    fatal
      "this alternative has ${plural patterns.length "pattern"}, but the `match` has ${plural scrutinees "scrutinee"}"
  else
    let guard := guardOf self modes
    let body := armBody self modes (anyAbsurd patterns) "`=>`"
    matchArms more self modes scrutinees column [{ bar, patterns, guard, body }, ..found]

--| Whether an arm's `|` starting a line lines up with the first arm that
--| did, and the column they line up at.
def armColumn (column: Option Nat): {Parse Item} (Bool, Option Nat) := armColumnOn column left()

def armColumnOn (column: Option Nat) (items: List Item): (Bool, Option Nat) := match items with
  | [item, .._] =>
    if item.leaf.token.lineStart then
      match column with
        | None => (True, Some item.leaf.token.column)
        | Some first => (first == item.leaf.token.column, column)
    else (True, column)
  | _ => (True, column)

def armPatterns (modes: Modes): {Parse Item} List Pattern :=
  let first := altPattern modes
  let (patterns, _) := commaList (Parse.mark().left + 1) modes (count => False) (() => altPattern modes) first []
  patterns

--| `=> e`, or nothing after an absurd pattern with no `=>`.
def armBody (self: Goal → {Parse Item} Expr) (modes: Modes) (absurd: Bool) (what: Text):
    {Parse Item} Option (Word, Expr) :=
  armBodyOf self modes absurd what (modes.at FatArrow)

def armBodyOf (self: Goal → {Parse Item} Expr) (modes: Modes) (absurd: Bool) (what: Text) (atArrow: Bool):
    {Parse Item} Option (Word, Expr) :=
  if absurd && !atArrow then None
  else
    let arrow := modes.expect FatArrow what
    let value := full self modes
    Some (arrow, value)

def guardOf (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Option Guard :=
  guardAt self modes (modes.at KwIf)

def guardAt (self: Goal → {Parse Item} Expr) (modes: Modes) (atIf: Bool): {Parse Item} Option Guard :=
  if atIf then
    let keyword := bump()
    let binder := namedBinder modes
    let condition := full self { modes | guard = True, lines = [] }
    Some { keyword, binder, condition }
  else None

def clauseLambda (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word) (word: Option Word) (kind: ClauseKind):
    {Parse Item} Expr :=
  let arms := clauseArms (Parse.mark().left + 1) self modes kind None None []
  if arms.isEmpty then modes.fail "`|` and an alternative" else ClauseLambda keyword word arms

def clauseArms (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: ClauseKind)
    (count column: Option Nat) (found: List Arm):
    {Parse Item} List Arm :=
  clauseArmsLined fuel self modes kind count found (armColumn column)

def clauseArmsLined (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: ClauseKind) (count: Option Nat)
    (found: List Arm) (columned: (Bool, Option Nat)):
    {Parse Item} List Arm :=
  match columned with | (lined, column) => clauseArmsAhead fuel self modes kind count column found lined (modes.at Pipe)

def clauseArmsAhead (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: ClauseKind)
    (count column: Option Nat) (found: List Arm) (lined atPipe: Bool):
    {Parse Item} List Arm :=
  match fuel with
    | Succ more => if atPipe && lined then clauseArm more self modes kind count column found else found.reverse
    | Zero => found.reverse

def clauseArm (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: ClauseKind)
    (count column: Option Nat) (found: List Arm):
    {Parse Item} List Arm :=
  let bar := bump()
  let patterns := armPatterns modes
  match count with
    | Some first =>
      if first != patterns.length then
        fatal "this alternative has ${plural patterns.length "pattern"}, but the first has ${first}"
      else clauseArmBody more self modes kind column found bar patterns
    | None => clauseArmBody more self modes kind column found bar patterns

def clauseArmBody (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: ClauseKind) (column: Option Nat)
    (found: List Arm) (bar: Word) (patterns: List Pattern):
    {Parse Item} List Arm :=
  let guard := guardOf self modes
  let absurd := anyAbsurd patterns
  let body := clauseBody self modes kind absurd
  clauseArms more self modes kind (Some patterns.length) column [{ bar, patterns, guard, body }, ..found]

def clauseBody (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: ClauseKind) (absurd: Bool):
    {Parse Item} Option (Word, Expr) :=
  match kind with
    | ClauseMatches => clauseMatchesBody self modes (modes.at FatArrow)
    | ClausePlain => armBody self modes absurd "`=>`"
    | ClauseSome => armBody self modes False "`=>`"

def clauseMatchesBody (self: Goal → {Parse Item} Expr) (modes: Modes) (atArrow: Bool):
    {Parse Item} Option (Word, Expr) :=
  if atArrow then armBody self modes False "`=>`" else None

-- Patterns.

--| With `Parse.recursiveWith`'s fuel, as `expression`, and for the same
--| reason: every rule reads an item before it calls `pself`, so a level
--| hands over to the plain pattern by a plain call (`tupleComponent`).
def pattern (goal: PatternGoal): {Parse Item} Pattern := Parse.recursiveWith patternRule goal

def patternOf (modes: Modes): {Parse Item} Pattern := pattern { modes, level = PatternPlain }

def patternRule (pself: PatternGoal → {Parse Item} Pattern) (goal: PatternGoal): {Parse Item} Pattern :=
  let modes := goal.modes
  match goal.level with
    | PatternPlain => plainPattern pself modes
    | PatternTupleComponent => tupleComponent pself modes
    | PatternListComponent => listComponent pself modes
    | PatternAltOne => altPatternOne pself modes
    | PatternFieldValue => fieldValuePattern pself modes (ctorAhead modes)

def fieldValuePattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (isCtor: Bool): {Parse Item} Pattern :=
  if isCtor then
    let ctor := bump()
    ctorArgs pself modes ctor (kind => kind == Comma || kind == RBrace)
  else plainPattern pself modes

def Pattern.hasAbsurd: Pattern → Bool
  | PatternAbsurd _ _ => True
  | PatternCtor _ arguments | PatternTuple _ arguments _ _ | PatternList _ arguments _ _ _ => anyAbsurd arguments
  | PatternOr first rest => first.hasAbsurd || anyLinkAbsurd rest
  | PatternParen _ inner _ => inner.hasAbsurd
  | _ => False

def anyAbsurd: List Pattern → Bool
  | [] => False
  | [first, ..rest] => first.hasAbsurd || anyAbsurd rest

def anyLinkAbsurd: List (Word, Pattern) → Bool
  | [] => False
  | [(bar, item), ..rest] => item.hasAbsurd || anyLinkAbsurd rest

def ctorAhead (modes: Modes): {Parse Item} Bool := ctorAheadOf (modes.at Upper) (wordAhead modes "Quot.mk")

def ctorAheadOf (upper quot: Bool): Bool := upper || quot

def plainPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  plainPatternOn pself modes modes.peek

def plainPatternOn (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (seen: Option Tok):
    {Parse Item} Pattern :=
  match seen with
    | Some Upper => PatternWord Upper bump()
    | Some Lower => PatternWord Lower (quotOrLower modes (wordAhead modes "Quot.mk"))
    | Some Underscore => PatternWord Underscore bump()
    | Some Num => PatternWord Num bump()
    | Some CharLit => PatternWord CharLit bump()
    | Some Str => PatternWord Str bump()
    | Some StrStart => fatal "a text pattern can't interpolate"
    | Some LBrace => PatternRecord (fieldsPattern pself modes)
    | Some LBracket => bracketPattern pself modes (modes.peekAt 1)
    | Some LParen => parenPattern pself modes (modes.peekAt 1)
    | _ => modes.failName "a pattern or `=`"

def quotOrLower (modes: Modes) (quot: Bool): {Parse Item} Word := if quot then bump() else modes.lower "a pattern"

def bracketPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (second: Option Tok):
    {Parse Item} Pattern :=
  bracketPatternOn pself modes second (modes.peekAt 2)

def bracketPatternOn (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (second third: Option Tok):
    {Parse Item} Pattern :=
  match second, third with
    | Some Lower, Some ColonEq => namedPattern pself modes
    | _, _ => listPattern pself modes

def namedPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  let open := bump()
  let inner := modes.inBrackets
  let name := inner.lower "a field name"
  let colonEq := bump()
  let value := pself { modes = inner, level = PatternPlain }
  PatternNamed open name colonEq value (inner.expect RBracket "`]`")

def parenPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (second: Option Tok):
    {Parse Item} Pattern :=
  match second with
    | Some RParen =>
      let open := bump()
      PatternAbsurd open bump()
    | Some Minus => parenMinusPattern pself modes
    | _ => parenOpenPattern pself modes

def parenMinusPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  let open := bump()
  let inner := modes.inBrackets
  let first := tupleItem pself inner
  parenPatternEnd pself inner open first

def parenOpenPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  let open := bump()
  let inner := modes.inBrackets
  let component := parenComponent pself inner (ctorAhead inner)
  let appended := patternAppend pself inner component PatternTupleComponent
  let first := alternatives pself inner appended PatternTupleComponent
  parenPatternEnd pself inner open first

def parenComponent (pself: PatternGoal → {Parse Item} Pattern) (inner: Modes) (isCtor: Bool): {Parse Item} Pattern :=
  if isCtor then
    let name := bump()
    ctorArgs pself inner name (kind => kind == RParen || kind == Comma || kind == Pipe || kind == PlusPlus)
  else pself { modes = inner, level = PatternPlain }

--| After a bracketed pattern's first part: a tuple's other items, or `)`.
def parenPatternEnd (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (open: Word) (first: Pattern):
    {Parse Item} Pattern :=
  parenPatternOf pself modes open first (modes.at Comma)

def parenPatternOf (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (open: Word)
    (first: Pattern) (comma: Bool):
    {Parse Item} Pattern :=
  if comma then
    let here := Parse.mark()
    let pair :=
      commaList (here.left + 1) modes (count => modes.at RParen && count >= 2) (() => tupleItem pself modes) first []
    tuplePatternEnd modes open pair
  else PatternParen open first (modes.expect RParen "`)`")

def tuplePatternEnd (modes: Modes) (open: Word) (pair: (List Pattern, Bool)): {Parse Item} Pattern := match pair with
  | (items, trailingComma) => PatternTuple open items trailingComma (modes.expect RParen "`)`")

def listPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  let open := bump()
  let inner := modes.inBrackets
  let here := Parse.mark()
  listPatternEnd inner open (listPatternItems (here.left + 1) pself inner [])

def listPatternEnd (inner: Modes) (open: Word) (read: (List Pattern, Bool, Option (Word, Pattern))):
    {Parse Item} Pattern :=
  match read with
    | (items, trailingComma, tail) => listPatternClose inner open items trailingComma tail (inner.at Comma)

def listPatternClose (inner: Modes) (open: Word) (items: List Pattern) (trailingComma: Bool)
    (tail: Option (Word, Pattern)) (comma: Bool):
    {Parse Item} Pattern :=
  match tail, comma with
    | Some _, True => fatal "a `..` tail must be the last item of a list pattern"
    | Some _, False =>
      PatternList open items trailingComma tail (inner.expect RBracket "`]`: a `..` tail must be the last item")
    | None, _ => PatternList open items trailingComma tail (inner.expect RBracket "`,` or `]`")

def listPatternItems (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (found: List Pattern):
    {Parse Item} (List Pattern, Bool, Option (Word, Pattern)) :=
  match fuel with
    | Zero => (found.reverse, False, None)
    | Succ more => listPatternStep more pself modes found (modes.at RBracket)

def listPatternStep (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (found: List Pattern) (closed: Bool):
    {Parse Item} (List Pattern, Bool, Option (Word, Pattern)) :=
  if closed then (found.reverse, !found.isEmpty, None) else listPatternDots more pself modes found (modes.at DotDot)

def listPatternDots (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (found: List Pattern) (dots: Bool):
    {Parse Item} (List Pattern, Bool, Option (Word, Pattern)) :=
  if dots then
    let dotsWord := bump()
    let tail := pself { modes, level = PatternPlain }
    (found.reverse, False, Some (dotsWord, tail))
  else
    let item := listItemPattern pself modes
    listPatternNext more pself modes found item (modes.eat Comma)

def listPatternNext (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (found: List Pattern)
    (item: Pattern) (comma: Option Word):
    {Parse Item} (List Pattern, Bool, Option (Word, Pattern)) :=
  match comma with
    | Some _ => listPatternItems more pself modes [item, ..found]
    | None => ([item, ..found].reverse, False, None)

--| Called after a `[` or `,`, so the call of `pself` follows a read.
def listItemPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  let first := pself { modes, level = PatternListComponent }
  alternatives pself modes first PatternListComponent

--| Called after a `(` or `,`, so the call of `pself` follows a read.
def tupleItem (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  let first := pself { modes, level = PatternTupleComponent }
  alternatives pself modes first PatternTupleComponent

def listComponent (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  listComponentOf pself modes (ctorAhead modes)

def listComponentOf (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (isCtor: Bool): {Parse Item} Pattern :=
  if isCtor then
    let name := bump()
    let ctor :=
      ctorArgs pself modes name (kind => kind == Comma || kind == RBracket || kind == Pipe || kind == PlusPlus)
    patternAppend pself modes ctor PatternListComponent
  else tupleComponent pself modes

def tupleComponent (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  tupleComponentOf pself modes (ctorAhead modes)

def tupleComponentOf (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (isCtor: Bool): {Parse Item} Pattern :=
  if isCtor then
    let name := bump()
    let ctor := ctorArgs pself modes name (kind => kind == Comma || kind == RParen || kind == Pipe || kind == PlusPlus)
    patternAppend pself modes ctor PatternTupleComponent
  else tupleSigned pself modes (modes.at Minus)

def tupleSigned (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (minus: Bool): {Parse Item} Pattern :=
  if !minus then
    let plain := plainPattern pself modes
    patternAppend pself modes plain PatternTupleComponent
  else negativePattern modes

--| `-` and the number after it.
def negativePattern (modes: Modes): {Parse Item} Pattern :=
  let minus := bump()
  negativeDigits modes minus (modes.at Num)

def negativeDigits (modes: Modes) (minus: Word) (number: Bool): {Parse Item} Pattern :=
  if number then PatternNegative minus bump() else modes.fail "a number"

def altPattern (modes: Modes): {Parse Item} Pattern :=
  let first := pattern { modes, level = PatternAltOne }
  alternatives pattern modes first PatternAltOne

def altPatternOne (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  altPatternOneOf pself modes (ctorAhead modes)

def altPatternOneOf (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (isCtor: Bool): {Parse Item} Pattern :=
  if isCtor then
    let name := bump()
    let ctor := ctorArgs pself modes name endsAltArguments
    patternAppend pself modes ctor PatternAltOne
  else tupleComponent pself modes

def endsAltArguments: Tok → Bool
  | Comma | Arrow | FatArrow | Pipe | KwIf | PlusPlus | RParen | RBracket | RBrace => True
  | _ => False

--| A constructor's arguments, up to a token `stops` accepts (or the end).
def ctorArgs (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word) (stops: Tok → Bool):
    {Parse Item} Pattern :=
  ctorArgsOf pself modes name stops (modes.at LBrace)

def ctorArgsOf (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word)
    (stops: Tok → Bool) (braced: Bool):
    {Parse Item} Pattern :=
  if braced then
    let fields := fieldsPattern pself modes
    ctorFieldsEnd name fields stops modes.peek
  else
    let here := Parse.mark()
    ctorListEnd name (ctorArgList (here.left + 1) pself modes name stops [])

def ctorFieldsEnd (name: Word) (fields: FieldsPattern) (stops: Tok → Bool) (seen: Option Tok): {Parse Item} Pattern :=
  match seen with
    | Some kind =>
      if stops kind then PatternCtorFields name fields
      else fatal "braces after `${name.text}` in a pattern take no further arguments"
    | None => PatternCtorFields name fields

def ctorListEnd (name: Word) (arguments: List Pattern): {Parse Item} Pattern := match arguments with
  | [] => PatternWord (if name.text == "Quot.mk" then Lower else Upper) name
  | _ => PatternCtor name arguments

def ctorArgList (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word)
    (stops: Tok → Bool) (found: List Pattern):
    {Parse Item} List Pattern :=
  ctorArgListOn fuel pself modes name stops found modes.peek

def ctorArgListOn (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word)
    (stops: Tok → Bool) (found: List Pattern) (seen: Option Tok):
    {Parse Item} List Pattern :=
  match fuel, seen with
    | Succ more, Some kind =>
      if stops kind then found.reverse else ctorArgBrace more pself modes name stops found (kind == LBrace)
    | _, _ => found.reverse

def ctorArgBrace (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word) (stops: Tok → Bool)
    (found: List Pattern) (brace: Bool):
    {Parse Item} List Pattern :=
  if brace then
    let argument := ctorRecordArgument pself modes name found
    ctorArgList more pself modes name stops [argument, ..found]
  else ctorArgMinus more pself modes name stops found (argumentMinus left())

def ctorRecordArgument (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word) (found: List Pattern):
    {Parse Item} Pattern :=
  if lastIsUpper name found then
    fatal "a record pattern after a constructor in an argument of `${name.text}` is written in brackets: `({ … })`"
  else PatternRecord (fieldsPattern pself modes)

def ctorArgMinus (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word) (stops: Tok → Bool)
    (found: List Pattern) (minus: Bool):
    {Parse Item} List Pattern :=
  if minus then
    let argument := negativePattern modes
    ctorArgList more pself modes name stops [argument, ..found]
  else
    let argument := pself { modes, level = PatternPlain }
    ctorArgList more pself modes name stops [argument, ..found]

--| Whether the token before is an uppercase name (`found` is newest first).
def lastIsUpper (name: Word) (found: List Pattern): Bool := match found with
  | [] => name.text != "Quot.mk"
  | [PatternWord kind _, .._] => kind == Upper
  | _ => False

def fieldsPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} FieldsPattern :=
  let open := modes.expect LBrace "`{`"
  let inner := modes.inBrackets
  let here := Parse.mark()
  fieldsPatternEnd inner open (fieldPatterns (here.left + 1) pself inner [])

def fieldsPatternEnd (inner: Modes) (open: Word) (read: (List FieldPattern, Bool, Option Word)):
    {Parse Item} FieldsPattern :=
  match read with
    | (fields, trailingComma, rest) =>
      let close := inner.expect RBrace "`,` or `}`"
      { open, fields, trailingComma, rest, close }

def fieldPatterns (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (found: List FieldPattern):
    {Parse Item} (List FieldPattern, Bool, Option Word) :=
  match fuel with
    | Zero => (found.reverse, False, None)
    | Succ more => fieldPatternStep more pself modes found (modes.at DotDot)

def fieldPatternStep (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (found: List FieldPattern) (dots: Bool):
    {Parse Item} (List FieldPattern, Bool, Option Word) :=
  if dots then
    let rest := bump()
    (found.reverse, False, Some rest)
  else fieldPatternClose more pself modes found (modes.at RBrace)

def fieldPatternClose (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (found: List FieldPattern) (closed: Bool):
    {Parse Item} (List FieldPattern, Bool, Option Word) :=
  if closed then (found.reverse, !found.isEmpty, None)
  else
    let name := modes.lower "a field name, or `..`"
    let value := fieldPatternValue pself modes (modes.eat Equals)
    let field := { name, value }
    fieldPatternNext more pself modes found field (modes.eat Comma)

def fieldPatternValue (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (equals: Option Word):
    {Parse Item} Option (Word, Pattern) :=
  match equals with
    | Some word =>
      let value := pself { modes, level = PatternFieldValue }
      Some (word, value)
    | None => None

def fieldPatternNext (more: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (found: List FieldPattern)
    (field: FieldPattern) (comma: Option Word):
    {Parse Item} (List FieldPattern, Bool, Option Word) :=
  match comma with
    | Some _ => fieldPatterns more pself modes [field, ..found]
    | None => ([field, ..found].reverse, False, None)

--| `"--" ++ rest`: only a text literal may stand before the `++`.
def patternAppend (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (start: Pattern) (next: PatternLevel):
    {Parse Item} Pattern :=
  patternAppendOf pself modes start next (modes.at PlusPlus)

def patternAppendOf (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (start: Pattern)
    (next: PatternLevel) (plus: Bool):
    {Parse Item} Pattern :=
  if !plus then start
  else if isTextPattern start then
    let operator := bump()
    PatternAppend start operator (pself { modes, level = next })
  else fatal "a text pattern can only take a fixed start"

def isTextPattern: Pattern → Bool
  | PatternWord kind _ => kind == Str
  | _ => False

--| `p | q`, with the `|` on the same line.
def alternatives (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (first: Pattern) (next: PatternLevel):
    {Parse Item} Pattern :=
  let here := Parse.mark()
  alternativesEnd first (alternativeLinks (here.left + 1) pself modes next [])

def alternativesEnd (first: Pattern) (links: List (Word, Pattern)): Pattern := match links with
  | [] => first
  | _ => PatternOr first links

def alternativeLinks (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (next: PatternLevel) (found: List (Word, Pattern)):
    {Parse Item} List (Word, Pattern) :=
  alternativeLinksOn fuel pself modes next found left()

def alternativeLinksOn (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (next: PatternLevel)
    (found: List (Word, Pattern)) (items: List Item):
    {Parse Item} List (Word, Pattern) :=
  match fuel, items with
    | Succ more, [bar, .._] =>
      if linkHere modes bar then
        let barLeaf := bump()
        let alternative := pself { modes, level = next }
        alternativeLinks more pself modes next [(barLeaf, alternative), ..found]
      else found.reverse
    | _, _ => found.reverse

--| An alternative's `|` stays on its line and isn't one that ends the pattern.
def linkHere (modes: Modes) (bar: Item): Bool := bar.kind == Pipe && !bar.leaf.token.lineStart && !modes.stops bar

-- Running it.

--| A whole input read as one expression (`parse_expression_tree`): its
--| tree, or the first line of the Rust parser's message.
def parseExpression (leaves: List Leaf): Result Expr Text := match Parse.run (items leaves) wholeExpression with
  | Ok value =>
    match value.loweringError with
      | Some message => Err message
      | None => Ok value
  | Err failure => Err (failure.messages.head.getOrElse "the parser failed without a message")

def wholeExpression(): {Parse Item} Expr :=
  let value := expression Modes.start
  if left().isEmpty then value else Modes.start.fail "the end of the declaration"
