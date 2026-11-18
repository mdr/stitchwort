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
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | Str => True
  | StrEnd => True
  | CharLit => True
  | RParen => True
  | RBracket => True
  | RBrace => True
  | Underscore => True
  | Question => True
  | TypeU => True
  | PropU => True
  | KwArithmetic => True
  | KwAlgebra => True
  | KwCases => True
  | _ => False

--| A binary operator, which can stand alone as a function, `(&&)`.
def Tok.isOperator: Tok → Bool
  | Plus => True
  | Minus => True
  | Star => True
  | Slash => True
  | Percent => True
  | PlusPlus => True
  | Equals => True
  | NotEq => True
  | EqEq => True
  | Lt => True
  | Le => True
  | Gt => True
  | Ge => True
  | AndAnd => True
  | OrOr => True
  | KwIn => True
  | NotIn => True
  | IffArrow => True
  | _ => False

--| An operator a section can take: any but `-`, so `(- 1)` is a number.
def Tok.isSectionOperator (tok: Tok): Bool := tok.isOperator && tok != Minus

def Tok.isComparison: Tok → Bool
  | Equals => True
  | NotEq => True
  | EqEq => True
  | Lt => True
  | Le => True
  | Gt => True
  | Ge => True
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
  | StrStart => "a text literal"
  | StrMid => "a text literal"
  | StrEnd => "a text literal"
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
  | AndAnd => True
  | OrOr => True
  | IffArrow => True
  | Arrow => True
  | Equals => True
  | EqEq => True
  | NotEq => True
  | Lt => True
  | Le => True
  | Gt => True
  | Ge => True
  | Plus => True
  | PlusPlus => True
  | Star => True
  | Slash => True
  | Percent => True
  | NotIn => True
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
def Modes.failName (modes: Modes) (what: Text): {Parse Item} a := match left() with
  | [item, .._] if !modes.stops item && Tok.keyword item.text |> .isSome =>
    fatal "expected ${what}, but found the keyword `${item.text}`"
  | _ => modes.fail what

--| An unqualified lowercase name (the Rust parser's `lower`).
def Modes.lower (modes: Modes) (what: Text): {Parse Item} Word := match left() with
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
    | LevelLogic =>
      let compared := cmpExpr self modes
      if andOrAhead modes then logicChain self modes compared else compared
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
def expr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let later: Bool := offset() > 0
  match left() with
    | [item, .._] if item.leaf.token.lineStart
        && later
        && modes.allow != Some item.index
        && !modes.endsConstruct item =>
      let column := item.leaf.token.column
      match modes.limit with
        | None => block self modes column True
        | Some limit =>
          if column > limit then block self modes column True
          else if column == limit
            && modes.recover
            && startsStatement item.kind
            && !lineHasSemicolon limit True left() then
            modes.gap ranOutLine
          else if column == limit then block self modes column False
          else exprInline self modes
    | _ => exprInline self modes

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
def Modes.gap (modes: Modes) (message: Text): {Parse Item} a := match blockEnd modes.lines left().head with
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
  | KwLet => True
  | KwDef => True
  | KwTheorem => True
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
  match blockLines (Parse.mark().left + 1) self inner column many [] with
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
    | Succ more =>
      let before := offset()
      let statementModes := { modes | allow = Some before }
      let kind := lineKind statementModes
      let line := statement self { statementModes | lines = [{ column, many, kind }, ..modes.lines] }
      let done := [line, ..found]
      if blockAgain before column many then blockLines more self modes column many done else done

--| What a block's line is, by its first token.
def lineKind (modes: Modes): {Parse Item} LineKind := lineKindOf modes.peek

def lineKindOf: Option Tok → LineKind
  | Some KwLet => LetLine
  | Some KwDef => DefLine
  | Some KwTheorem => DefLine
  | Some At => DefLine
  | _ => ExprLine

--| Whether a block goes on after a line that started at offset `before`:
--| the line read something, and the next starts a line at the block's
--| column with what doesn't end blocks.
def blockAgain (before column: Nat) (many: Bool): {Parse Item} Bool :=
  let at := offset()
  match left() with
    | [next, .._] =>
      at != before && many && next.leaf.token.lineStart && next.leaf.token.column == column && !endsBlocks next.kind
    | [] => False

def endsBlocks: Tok → Bool
  | Pipe => True
  | KwWhere => True
  | ColonEq => True
  | KwDecreasing => True
  | KwUnfolding => True
  | _ => False

--| The column of the first token on the line of the next token.
def headIndent(): {Parse Item} Nat := left().head.map (item => item.lineIndent) |> .getOrElse 0

def exprInline (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := match modes.peek with
  | Some KwHandle => handleExpr self modes
  | Some KwLet =>
    let binding := letStatement self modes.sealed
    letBody self modes binding
  | Some KwCalc => calcExpr self modes
  | Some KwRewrite => rewriteExpr self modes
  | Some KwCases => casesExpr self modes
  | Some KwMatch =>
    let indent := headIndent()
    let keyword := bump()
    let matched := matchExpr self modes keyword
    if atPipe modes then pipeChain self modes indent matched else matched
  | _ =>
    if lambdaAhead modes (Parse.mark().left + 1) left() then lambda self modes None
    else if lambdaResultType modes (Parse.mark().left + 1) False left() then fatal "a lambda doesn't take a result type"
    else
      match modes.peek with
        | Some KwExists => quantifier self modes
        | Some KwForall => quantifier self modes
        | Some KwIf =>
          let indent := headIndent()
          let keyword := bump()
          ifExpr self modes indent keyword
        | _ =>
          if implicitBinderAhead (Parse.mark().left + 1) left() && isSome LBracket modes.peek then
            piExpr self modes True
          else if piBinderAhead left() && isSome LParen modes.peek then piExpr self modes False
          else operatorExpr self modes

def andOrAhead (modes: Modes): {Parse Item} Bool := modes.at AndAnd || modes.at OrOr

--| The rest of `expr_inline`: comparisons, `&&` and `||`, `<->`, a method
--| section around them, then `->` or `;`.
def operatorExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let start := offset()
  let section := modes.at Dot
  let inner := if section then { modes | sectionHead = Some start } else modes
  let compared := cmpExpr self inner
  let logic := if andOrAhead modes then logicChain self modes compared else compared
  let iffed := if modes.at IffArrow then iff self modes logic else logic
  let sectioned := if section then Section iffed else iffed
  let sequence := sequenceAhead modes
  match modes.peek with
    | Some Arrow =>
      let arrow := bump()
      Infix InfixArrow sectioned arrow (resultType self modes)
    | Some Semi if sequence =>
      let semicolon := bump()
      match modes.peek with
        | None => fatal semicolonAtEnd
        | Some RParen => fatal semicolonAtEnd
        | Some RBracket => fatal semicolonAtEnd
        | Some RBrace => fatal semicolonAtEnd
        | Some Comma => fatal semicolonAtEnd
        | _ => Infix InfixSeq sectioned semicolon (full self modes)
    | _ => sectioned

def semicolonAtEnd: Text := "`;` needs an expression after it: `(a; b)` runs `a`, then gives `b`'s value"

--| `a && b || c`: `&&` within each disjunct and `||` between them, both
--| grouped to the right.
def logicChain (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Expr): {Parse Item} Expr :=
  let links := logicLinks self modes
  groupLogic (links.length + 1) first links

def logicLinks (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} List (Word, Expr) := Parse.loop (() =>
  if andOrAhead modes then
    let operator := bump()
    let operand := if quantifierAhead modes then quantifier self modes else cmpExpr self modes
    Some (operator, operand)
  else None)

def groupLogic (fuel: Nat) (first: Expr) (links: List (Word, Expr)): Expr :=
  let (conjunction, after) := conjunctionOf first links
  match fuel, after with
    | Succ more, [(or, next), ..rest] => Infix InfixBinary conjunction or (groupLogic more next rest)
    | _, _ => conjunction

--| The `&&`s from `first` up to the next `||`, grouped to the right, and
--| the links from that `||` on.
def conjunctionOf (first: Expr): List (Word, Expr) → (Expr, List (Word, Expr))
  | [(and, next), ..rest] if and.text == "&&" || and.text == "∧" =>
    let (right, after) := conjunctionOf next rest
    (Infix InfixBinary first and right, after)
  | links => (first, links)

--| `a <-> b`, which doesn't chain.
def iff (self: Goal → {Parse Item} Expr) (modes: Modes) (left: Expr): {Parse Item} Expr :=
  let operator := bump()
  let right :=
    if quantifierAhead modes then quantifier self modes
    else
      let compared := cmpExpr self modes
      if andOrAhead modes then logicChain self modes compared else compared
  if modes.at IffArrow then fatal "`<->` doesn't chain" else Infix InfixIff left operator right

def quantifierAhead (modes: Modes): {Parse Item} Bool := modes.at KwExists || modes.at KwForall

def quantifier (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := match left() with
  | [item, .._] if item.kind == KwForall => forallExpr self modes
  | _ =>
    let keyword := bump()
    if lambdaAhead modes (Parse.mark().left + 1) left() then lambda self modes (Some keyword)
    else modes.fail "a parameter and `=>` after `exists`"

--| `∀ (x: A) [b: B] n => P`: names and typed groups, but no patterns.
def forallExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let keyword := bump()
  let params := forallParams self modes
  if params.isEmpty then modes.fail "a parameter after `${keyword.text}`"
  else if modes.at FatArrow then
    let arrow := bump()
    Binding BindsForall (Some keyword) params arrow (full self modes)
  else modes.fail "`=>` after the parameters of `${keyword.text}`"

def forallParams (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} List Param := Parse.loop (() =>
  let items := left()
  match items with
    | [item, .._] if !modes.stops item =>
      match item.kind with
        | Lower if !isQualified item => Some (NameParam bump())
        | Underscore => Some (NameParam bump())
        | LParen if annotatedParamAhead items =>
          Some (Grouped (headerGroup self modes GroupLambda (Some forallDefault)))
        | LBracket if implicitGroupAt items || namelessAutoAt items =>
          Some (Grouped (headerGroup self modes GroupLambda (Some forallDefault)))
        | _ => None
    | _ => None)

--| A lambda's parameters, `=>` and body; with a keyword, an `∃`'s.
def lambda (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Option Word): {Parse Item} Expr :=
  let params := lambdaParams self modes
  if params.isEmpty then modes.fail "a parameter name"
  else
    let arrow := modes.expect FatArrow "`=>`"
    Binding (if keyword.isSome then BindsExists else BindsLambda) keyword params arrow (full self modes)

def lambdaParams (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} List Param := Parse.loop (() =>
  let items := left()
  match items with
    | [item, .._] if !modes.stops item =>
      match item.kind with
        | Lower => Some (NameParam (modes.lower "a name"))
        | Underscore => Some (NameParam bump())
        | LParen =>
          if annotatedParamAhead items then Some (Grouped (headerGroup self modes GroupLambda (Some defaultPlaces)))
          else if annotatedPatternAhead (Parse.mark().left + 1) items then
            let open := bump()
            let inner := modes.inBrackets
            let pattern := patternOf inner
            let colon := inner.expect Colon "`:`"
            let annotation := binderType self inner
            let close := inner.expect RParen "`)`"
            Some (TypedPattern open pattern colon annotation close)
          else Some (PatternParam (patternOf modes))
        | LBracket if implicitGroupAt items || namelessAutoAt items =>
          Some (Grouped (headerGroup self modes GroupLambda (Some defaultPlaces)))
        | LBrace => Some (PatternParam (patternOf modes))
        | _ => None
    | _ => None)

def ifExpr (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (keyword: Word): {Parse Item} Expr :=
  let binder := namedBinder modes
  let condition := full self modes.sealed
  let thenKeyword := modes.expectKeyword KwThen "`then`" indent
  let whenTrue := full self modes.sealed
  let elseKeyword := modes.expectKeyword KwElse "`else`" indent
  If keyword binder condition thenKeyword whenTrue elseKeyword (full self modes)

--| `h:` before a condition or scrutinee.
def namedBinder (modes: Modes): {Parse Item} Option (Word, Word) :=
  if modes.at Lower && isSome Colon (modes.peekAt 1) then
    let name := modes.lower "a name"
    Some (name, bump())
  else None

--| `then` or `else`, which may also start a line left of the block's
--| column, if not left of the `if`'s line (`expect_keyword`).
def Modes.expectKeyword (modes: Modes) (wanted: Tok) (what: Text) (indent: Nat): {Parse Item} Word :=
  match modes.peek, left() with
    | None, [item, .._] if item.kind == wanted && item.leaf.token.lineStart && item.leaf.token.column >= indent =>
      bump()
    | _, _ => modes.expect wanted what

--| A `|>` next: on this line, or starting one (`at_pipe`).
def atPipe (modes: Modes): {Parse Item} Bool := match left() with
  | [item, .._] => item.kind == PipeGt && (!modes.stops item || item.leaf.token.lineStart)
  | [] => False

--| `x |> f |> g`, after `x`: grouped to the left.
--| `indent` is the column of the line the piped value starts on: a line
--| starting with `|>` continues the chain if it isn't left of it.
def pipeChain (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (value: Expr): {Parse Item} Expr :=
  pipesFrom (Parse.mark().left + 1) self modes indent value

def pipesFrom (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (value: Expr):
    {Parse Item} Expr :=
  let ahead := match left() with
    | [item, .._] =>
      item.kind == PipeGt && (!modes.stops item || (item.leaf.token.lineStart && item.leaf.token.column >= indent))
    | [] => False
  match fuel with
    | Succ more if ahead =>
      let operator := bump()
      let function :=
        if lambdaAhead modes (Parse.mark().left + 1) left() then lambda self modes None
        else
          let start := offset()
          let section := modes.at Dot
          let inner := if section then { modes | sectionHead = Some start } else modes
          let operand := appendExpr self inner
          if section then Section operand else operand
      pipesFrom more self modes indent (Infix InfixPipe value operator function)
    | _ => value

--| `cmp_expr`: one comparison, a chain of them, or a membership test,
--| each operand a range and its pipeline.
def cmpExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let first := left().head.map Item.kind
  let lhs := pipedRange self modes
  match modes.peek with
    | Some KwIn => membership self modes first lhs
    | Some NotIn => membership self modes first lhs
    | Some kind if kind.isComparison =>
      let operator := bump()
      if modes.at KwIf then
        let indent := headIndent()
        let keyword := bump()
        Infix InfixBinary lhs operator (ifExpr self modes indent keyword)
      else
        let second := pipedRange self modes
        match modes.peek with
          | Some next if next.isComparison || next == KwIn || next == NotIn =>
            comparisonChain self modes lhs kind operator second
          | _ => Infix InfixBinary lhs operator second
    | _ => lhs

def pipedRange (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let indent := headIndent()
  let range := rangeExpr self modes
  if atPipe modes then pipeChain self modes indent range else range

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
  else
    let descending := kind == Gt || kind == Ge
    Chain first [(operator, second), ..chainLinks self modes descending]

def chainRefused (kind: Tok): Text := "`${kind.written}` can't be part of a chain of comparisons"

def chainLinks (self: Goal → {Parse Item} Expr) (modes: Modes) (descending: Bool): {Parse Item} List (Word, Expr) :=
  Parse.loop (() =>
    match modes.peek with
      | Some kind =>
        let flip := kind == Gt || kind == Ge
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
      | None => None)

def rangeExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let low := appendExpr self modes
  match modes.peek with
    | Some DotDot => fatal "a range is `a ..< b` (up to, not including, `b`) or `a ..= b` (through `b`)"
    | Some kind if kind == DotDotLt || kind == DotDotEq =>
      let operator := bump()
      let high := appendExpr self modes
      if modes.at DotDotLt || modes.at DotDotEq then fatal "ranges don't chain" else Infix InfixRange low operator high
    | _ => low

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

def unary (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := match modes.peek with
  | Some KwMatch =>
    let keyword := bump()
    matchExpr self modes keyword
  | Some kind =>
    if matchesBarAhead modes then
      let keyword := bump()
      clauseLambda self modes keyword None ClauseMatches
    else if kind == Minus && negativeNumeral left() then app self modes
    else if kind == Minus || kind == Bang then
      let operator := bump()
      Prefix operator (self { modes, level = LevelUnary })
    else app self modes
  | None => app self modes

--| `f a b`: one `App` however many arguments.
def app (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let start := offset()
  let section := modes.at Dot && modes.sectionHead != Some start
  let head := atom self modes True
  let applied := if startsAtom modes then App head (arguments self modes) else head
  if section then Section applied else applied

def arguments (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} List Expr := Parse.loop (() =>
  if startsAtom modes then
    let sectionLine := match left() with
      | [item, .._] => item.kind == Dot && item.leaf.token.lineStart && !modes.stops item
      | [] => False
    if sectionLine then fatal "a line can't start with a method section"
    else if modes.at Upper && isSome LBrace (modes.peekAt 1) then Some (braceArgument self modes)
    else Some (self { modes, level = LevelArgument })
  else None)

def startsAtom (modes: Modes): {Parse Item} Bool := match modes.peek with
  | Some kind =>
    opensArgument kind
      || (kind == Dot && sectionAt left())
      || (kind == KwCases && bareCases modes)
      || argumentPrefix left()
  | None => False

def opensArgument: Tok → Bool
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | CharLit => True
  | Str => True
  | StrStart => True
  | KwInclude => True
  | KwArithmetic => True
  | KwAlgebra => True
  | TypeU => True
  | PropU => True
  | LParen => True
  | LBracket => True
  | LBrace => True
  | Underscore => True
  | Question => True
  | _ => False

def bareCases (modes: Modes): {Parse Item} Bool := match modes.peekAt 1 with
  | Some KwThen => False
  | Some KwIn => False
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

def atomBase (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := match modes.peek with
  | Some Minus => negativeAtom self modes
  | Some Bang => prefixAtom self modes (argumentBang left())
  | Some StrStart => interpolated self modes
  | Some KwInclude =>
    let keyword := bump()
    if modes.at Str then Include keyword bump() else modes.fail "a path in quotes, as in `include \"inputs/day04.txt\"`"
  | Some KwArithmetic => facts self modes KwArithmetic FactsOmega
  | Some KwAlgebra => facts self modes KwAlgebra FactsRing
  | Some KwCases => if bareCases modes then Atom KwCases bump() else modes.fail "an expression"
  | Some TypeU =>
    let keyword := bump()
    match left() with
      | [level, .._] if level.kind == Num && !modes.stops level =>
        if (level.text.toNat |> .getOrElse 0) > 65535 then fatal "universe level is too large"
        else Universe keyword bump()
      | _ => Atom TypeU keyword
  | Some LParen => parenAtom self modes
  | Some LBracket =>
    match modes.peekAt 1, modes.peekAt 2 with
      | Some Lower, Some ColonEq => namedArgument self modes RBracket "`]`"
      | Some KwDecreasing, Some ColonEq => namedArgument self modes RBracket "`]`"
      | _, _ => listExpr self modes
  | Some LBrace => recordExpr self modes
  | Some Dot => sectionStart modes
  | Some kind if isWord kind => Atom kind bump()
  | _ =>
    if modes.recover && modes.peek.isNone then
      modes.gap (if ranOutAtLine modes then ranOutLine else modes.unexpected "an expression")
    else if isSome FatArrow (modes.peekAt 1) then modes.failName "an expression"
    else modes.fail "an expression"

def isWord: Tok → Bool
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | Str => True
  | CharLit => True
  | Underscore => True
  | Question => True
  | PropU => True
  | _ => False

def negativeAtom (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  if negativeNumeral left() then
    let minus := bump()
    let kind := left().head.map Item.kind |> .getOrElse Num
    Prefix minus (Atom kind bump())
  else prefixAtom self modes (argumentMinus left())

--| A `-` or `!` negating an argument, if `negates`.
def prefixAtom (self: Goal → {Parse Item} Expr) (modes: Modes) (negates: Bool): {Parse Item} Expr :=
  if negates then
    let operator := bump()
    Prefix operator (self { modes, level = LevelArgument })
  else modes.failName "an expression"

--| `arithmetic` or `algebra`, and its facts if a list follows.
def facts (self: Goal → {Parse Item} Expr) (modes: Modes) (token: Tok) (kind: FactsKind): {Parse Item} Expr :=
  let keyword := bump()
  if modes.at LBracket then
    let list := listExpr self modes
    if hasSpread list then fatal "a list of facts can't have a `..` spread" else Facts kind keyword list
  else Atom token keyword

def hasSpread: Expr → Bool
  | ListOf _ items _ _ => items.any (matches
    | Spread _ _)
  | _ => False

--| `.name` with no receiver, starting a method section.
def sectionStart (modes: Modes): {Parse Item} Expr :=
  let dot := bump()
  match left() with
    | [name, .._] if name.kind == Lower && name.glued && !isQualified name && !modes.stops name =>
      FieldAccess None dot bump()
    | _ => fatal "expected a name right after `.`"

--| `(x := e)` or `[x := e]`.
def namedArgument (self: Goal → {Parse Item} Expr) (modes: Modes) (closer: Tok) (closeText: Text): {Parse Item} Expr :=
  let open := bump()
  let inner := modes.inBrackets
  let name := if inner.at KwDecreasing then bump() else inner.lower "a name"
  let colonEq := bump()
  let value := full self inner
  NamedArg open name colonEq value (inner.expect closer closeText)

--| What starts with `(`: `()`, a named argument, an operator section, a
--| bracketed expression, a tuple or an annotation.
def parenAtom (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let second := modes.peekAt 1
  let third := modes.peekAt 2
  match second, third with
    | Some RParen, _ =>
      let open := bump()
      Unit open bump()
    | Some Lower, Some ColonEq => namedArgument self modes RParen "`)`"
    | Some next, _ if next.isSectionOperator || (next.isOperator && isSome RParen third) => operatorSection self modes
    | _, _ =>
      match rightOperator left() with
        | Some inside => rightSection self modes inside
        | None => bracketed self modes

def bracketed (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let open := bump()
  let inner := modes.inBrackets
  let first := full self inner
  match inner.peek with
    | Some Comma =>
      let (items, trailingComma) :=
        commaList
          (Parse.mark().left + 1)
          inner
          (count => inner.at RParen && count >= 2)
          (() => full self inner)
          first
          []
      Tuple open items trailingComma (tupleClose inner)
    | Some Colon =>
      let colon := bump()
      let annotation := full self inner
      if inner.at Comma then fatal tupleAnnotation
      else Annotation open first colon annotation (inner.expect RParen "`)`")
    | _ => Paren open first (inner.expect RParen "`)`")

def tupleClose (modes: Modes): {Parse Item} Word :=
  if modes.at Colon then fatal tupleAnnotation else modes.expect RParen "`)`"

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
    | Succ more, Some Comma =>
      let comma := bump()
      let done := [current, ..found]
      if ends count then (done.reverse, True) else commaListFrom more modes ends next (count + 1) (next()) done
    | _, _ => ([current, ..found].reverse, False)

--| `(+ 1)`, `(&&)`: the operator first.
def operatorSection (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let open := bump()
  let inner := modes.inBrackets
  let operatorKind := left().head.map Item.kind |> .getOrElse Plus
  let operator := bump()
  if inner.at RParen then OperatorSection open None operator None bump()
  else
    let operand := sectionOperand self inner operatorKind
    if inner.at RParen then OperatorSection open None operator (Some operand) bump()
    else inner.fail "`)` after the operand of a section"

--| A left section's operand: what binds tighter than its operator.
def sectionOperand (self: Goal → {Parse Item} Expr) (modes: Modes) (operator: Tok): {Parse Item} Expr :=
  match operator with
    | Plus => self { modes, level = LevelMultiplicative }
    | Star => self { modes, level = LevelUnary }
    | Slash => self { modes, level = LevelUnary }
    | Percent => self { modes, level = LevelUnary }
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
  let inner := modes.inBrackets
  let start := offset()
  let operatorKind := match left().drop (inside - 1) with
    | [item, .._] => item.kind
    | [] => Plus
  let operand := match operatorKind with
    | Plus => self { modes = inner, level = LevelMultiplicative }
    | Star => self { modes = inner, level = LevelUnary }
    | Slash => self { modes = inner, level = LevelUnary }
    | Percent => self { modes = inner, level = LevelUnary }
    | PlusPlus => self { modes = inner, level = LevelAdditive }
    | AndAnd => self { modes = inner, level = LevelComparison }
    | OrOr => self { modes = inner, level = LevelComparison }
    | IffArrow => self { modes = inner, level = LevelComparison }
    | _ => self { modes = inner, level = LevelAppend }
  if offset() != start + inside - 1 then inner.fail "`)` after the operator of a section"
  else
    let operator := bump()
    OperatorSection open (Some operand) operator None (inner.expect RParen "`)`")

def listExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let open := bump()
  let inner := modes.inBrackets
  if inner.at RBracket then ListOf open [] False bump()
  else
    let first := listItem self inner
    let (items, trailingComma) :=
      commaList (Parse.mark().left + 1) inner (count => inner.at RBracket) (() => listItem self inner) first []
    ListOf open items trailingComma (inner.expect RBracket "`,` or `]`")

def listItem (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  if modes.at DotDot then
    let dots := bump()
    if modes.at Comma || modes.at RBracket then fatal "expected a list after `..`, as in `[x, ..xs]`"
    else Spread dots (full self modes)
  else full self modes

def recordExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let open := modes.expect LBrace "`{`"
  let inner := modes.inBrackets
  if inner.at RBrace then Record open None [] False bump()
  else
    let literal :=
      inner.at Lower
        && (match inner.peekAt 1 with
          | Some Equals => True
          | Some Comma => True
          | Some RBrace => True
          | _ => False)
    let base :=
      if literal then None
      else
        let record := full self inner
        Some (record, inner.expect Pipe "`|` and the fields to update")
    let first := recordField self inner
    let (fields, trailingComma) :=
      commaList (Parse.mark().left + 1) inner (count => inner.at RBrace) (() => recordField self inner) first []
    Record open base fields trailingComma (inner.expect RBrace "`,` or `}`")

def recordField (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let name := modes.lower "a field name"
  if modes.at Equals then
    let equals := bump()
    RecordField name equals (full self modes)
  else Atom Lower name

--| `C { … }` as an argument.
def braceArgument (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let ctor := atomBase self modes
  CtorFields ctor (recordExpr self modes)

def interpolated (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let start := bump()
  Interpolated [TextPiece start, ..interpolations self modes]

def interpolations (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} List Piece :=
  let pieces := Parse.loop (() =>
    if modes.at StrMid then Some (TextPiece bump())
    else if modes.at InterpOpen then
      let open := modes.expect InterpOpen "`\${`"
      let value := full self modes
      let close := modes.expect InterpClose "`}`"
      Some (Interpolation open value close)
    else if modes.at StrEnd then None
    else modes.fail "`\${` or the end of the text")
  let last := if modes.at StrEnd then bump() else modes.fail "`\${` or the end of the text"
  pieces ++ [TextPiece last]

-- `match` and clause lambdas.

type ClauseKind = | ClausePlain | ClauseSome | ClauseMatches

def wordAhead (modes: Modes) (word: Text): {Parse Item} Bool := match left() with
  | [item, .._] => item.kind == Lower && item.text == word && !modes.stops item
  | [] => False

def matchesBarAhead (modes: Modes): {Parse Item} Bool :=
  wordAhead modes "matches"
    && isSome Pipe (modes.peekAt 1)
    && !(isSome Lower (modes.peekAt 2) && isSome Equals (modes.peekAt 3))

--| `match induct` and `match reify`: the word, then not what a scrutinee
--| named `induct` would have after it.
def specialAhead (modes: Modes) (word: Text): {Parse Item} Bool :=
  wordAhead modes word
    && (match modes.peekAt 1 with
      | Some KwWith => False
      | Some Comma => False
      | Some Colon => False
      | None => False
      | _ => True)

def matchExpr (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word): {Parse Item} Expr :=
  if specialAhead modes "induct" then
    let induct := fixedFrom()
    inductExpr self modes keyword.comments induct
  else if specialAhead modes "reify" then
    let reify := fixedFrom()
    reifyExpr self modes keyword.comments reify
  else if modes.at Pipe then clauseLambda self modes keyword None ClausePlain
  else if wordAhead modes "some" && isSome Pipe (modes.peekAt 1) then
    let some := bump()
    clauseLambda self modes keyword (Some some) ClauseSome
  else
    let first := scrutinee self modes
    let (scrutinees, _) :=
      commaList (Parse.mark().left + 1) modes (count => False) (() => scrutinee self modes) first []
    let withKeyword := modes.expect KwWith "`with`"
    let arms := matchArms (Parse.mark().left + 1) self modes scrutinees.length None []
    if arms.isEmpty then modes.fail "`|` and an alternative" else Match keyword scrutinees withKeyword arms

def scrutinee (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Scrutinee :=
  let name := namedBinder modes
  { name, value = self { modes = modes.sealed, level = LevelInline } }

def plural (count: Nat) (noun: Text): Text := if count == 1 then "${count} ${noun}" else "${count} ${noun}s"

def matchArms (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (scrutinees: Nat)
    (column: Option Nat) (found: List Arm):
    {Parse Item} List Arm :=
  let (lined, column) := armColumn column
  let ahead := modes.at Pipe && lined
  match fuel with
    | Succ more if ahead =>
      let bar := bump()
      let patterns := armPatterns modes
      if patterns.length != scrutinees then
        fatal
          "this alternative has ${plural patterns.length "pattern"}, but the `match` has ${plural scrutinees "scrutinee"}"
      else
        let guard := guardOf self modes
        let body := armBody self modes (anyAbsurd patterns) "`=>`"
        matchArms more self modes scrutinees column [{ bar, patterns, guard, body }, ..found]
    | _ => found.reverse

--| Whether an arm's `|` starting a line lines up with the first arm that
--| did, and the column they line up at.
def armColumn (column: Option Nat): {Parse Item} (Bool, Option Nat) := match left() with
  | [item, .._] if item.leaf.token.lineStart =>
    match column with
      | None => (True, Some item.leaf.token.column)
      | Some first => (first == item.leaf.token.column, column)
  | _ => (True, column)

def armPatterns (modes: Modes): {Parse Item} List Pattern :=
  let first := altPattern modes
  let (patterns, _) := commaList (Parse.mark().left + 1) modes (count => False) (() => altPattern modes) first []
  patterns

--| `=> e`, or nothing after an absurd pattern with no `=>`.
def armBody (self: Goal → {Parse Item} Expr) (modes: Modes) (absurd: Bool) (what: Text):
    {Parse Item} Option (Word, Expr) :=
  if absurd && !modes.at FatArrow then None
  else
    let arrow := modes.expect FatArrow what
    Some (arrow, full self modes)

def guardOf (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Option Guard :=
  if modes.at KwIf then
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
  let (lined, column) := armColumn column
  let ahead := modes.at Pipe && lined
  match fuel with
    | Succ more if ahead =>
      let bar := bump()
      let patterns := armPatterns modes
      match count with
        | Some first if first != patterns.length =>
          fatal "this alternative has ${plural patterns.length "pattern"}, but the first has ${first}"
        | _ =>
          let guard := guardOf self modes
          let absurd := anyAbsurd patterns
          let body := match kind with
            | ClauseMatches => if modes.at FatArrow then armBody self modes False "`=>`" else None
            | ClausePlain => armBody self modes absurd "`=>`"
            | ClauseSome => armBody self modes False "`=>`"
          clauseArms more self modes kind (Some patterns.length) column [{ bar, patterns, guard, body }, ..found]
    | _ => found.reverse

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
    | PatternFieldValue =>
      if ctorAhead modes then
        let ctor := bump()
        ctorArgs pself modes ctor (kind => kind == Comma || kind == RBrace)
      else plainPattern pself modes

def Pattern.hasAbsurd: Pattern → Bool
  | PatternAbsurd _ _ => True
  | PatternCtor _ arguments => anyAbsurd arguments
  | PatternTuple _ items _ _ => anyAbsurd items
  | PatternList _ items _ _ _ => anyAbsurd items
  | PatternOr first rest => first.hasAbsurd || anyLinkAbsurd rest
  | PatternParen _ inner _ => inner.hasAbsurd
  | _ => False

def anyAbsurd: List Pattern → Bool
  | [] => False
  | [first, ..rest] => first.hasAbsurd || anyAbsurd rest

def anyLinkAbsurd: List (Word, Pattern) → Bool
  | [] => False
  | [(bar, item), ..rest] => item.hasAbsurd || anyLinkAbsurd rest

def ctorAhead (modes: Modes): {Parse Item} Bool := modes.at Upper || wordAhead modes "Quot.mk"

def plainPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  match modes.peek with
    | Some Upper => PatternWord Upper bump()
    | Some Lower => PatternWord Lower (if wordAhead modes "Quot.mk" then bump() else modes.lower "a pattern")
    | Some Underscore => PatternWord Underscore bump()
    | Some Num => PatternWord Num bump()
    | Some CharLit => PatternWord CharLit bump()
    | Some Str => PatternWord Str bump()
    | Some StrStart => fatal "a text pattern can't interpolate"
    | Some LBrace => PatternRecord (fieldsPattern pself modes)
    | Some LBracket =>
      match modes.peekAt 1, modes.peekAt 2 with
        | Some Lower, Some ColonEq =>
          let open := bump()
          let inner := modes.inBrackets
          let name := inner.lower "a field name"
          let colonEq := bump()
          let value := pself { modes = inner, level = PatternPlain }
          PatternNamed open name colonEq value (inner.expect RBracket "`]`")
        | _, _ => listPattern pself modes
    | Some LParen =>
      match modes.peekAt 1 with
        | Some RParen =>
          let open := bump()
          PatternAbsurd open bump()
        | Some Minus =>
          let open := bump()
          let inner := modes.inBrackets
          let first := tupleItem pself inner
          parenPatternEnd pself inner open first
        | _ =>
          let open := bump()
          let inner := modes.inBrackets
          let component :=
            if ctorAhead inner then
              let name := bump()
              ctorArgs pself inner name (kind => kind == RParen || kind == Comma || kind == Pipe || kind == PlusPlus)
            else pself { modes = inner, level = PatternPlain }
          let appended := patternAppend pself inner component PatternTupleComponent
          let first := alternatives pself inner appended PatternTupleComponent
          parenPatternEnd pself inner open first
    | _ => modes.failName "a pattern or `=`"

--| After a bracketed pattern's first part: a tuple's other items, or `)`.
def parenPatternEnd (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (open: Word) (first: Pattern):
    {Parse Item} Pattern :=
  if modes.at Comma then
    let (items, trailingComma) :=
      commaList
        (Parse.mark().left + 1)
        modes
        (count => modes.at RParen && count >= 2)
        (() => tupleItem pself modes)
        first
        []
    PatternTuple open items trailingComma (modes.expect RParen "`)`")
  else PatternParen open first (modes.expect RParen "`)`")

def listPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  let open := bump()
  let inner := modes.inBrackets
  let (items, trailingComma, tail) := listPatternItems (Parse.mark().left + 1) pself inner []
  let comma := inner.at Comma
  match tail with
    | Some _ if comma => fatal "a `..` tail must be the last item of a list pattern"
    | Some _ =>
      PatternList open items trailingComma tail (inner.expect RBracket "`]`: a `..` tail must be the last item")
    | None => PatternList open items trailingComma tail (inner.expect RBracket "`,` or `]`")

def listPatternItems (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (found: List Pattern):
    {Parse Item} (List Pattern, Bool, Option (Word, Pattern)) :=
  match fuel with
    | Zero => (found.reverse, False, None)
    | Succ more =>
      if modes.at RBracket then (found.reverse, !found.isEmpty, None)
      else if modes.at DotDot then
        let dots := bump()
        (found.reverse, False, Some (dots, pself { modes, level = PatternPlain }))
      else
        let item := listItemPattern pself modes
        match modes.eat Comma with
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
  if ctorAhead modes then
    let name := bump()
    let ctor :=
      ctorArgs pself modes name (kind => kind == Comma || kind == RBracket || kind == Pipe || kind == PlusPlus)
    patternAppend pself modes ctor PatternListComponent
  else tupleComponent pself modes

def tupleComponent (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  if ctorAhead modes then
    let name := bump()
    let ctor := ctorArgs pself modes name (kind => kind == Comma || kind == RParen || kind == Pipe || kind == PlusPlus)
    patternAppend pself modes ctor PatternTupleComponent
  else if !modes.at Minus then
    let plain := plainPattern pself modes
    patternAppend pself modes plain PatternTupleComponent
  else
    let minus := bump()
    if modes.at Num then PatternNegative minus bump() else modes.fail "a number"

def altPattern (modes: Modes): {Parse Item} Pattern :=
  let first := pattern { modes, level = PatternAltOne }
  alternatives pattern modes first PatternAltOne

def altPatternOne (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  if ctorAhead modes then
    let name := bump()
    let ctor := ctorArgs pself modes name endsAltArguments
    patternAppend pself modes ctor PatternAltOne
  else tupleComponent pself modes

def endsAltArguments: Tok → Bool
  | Comma => True
  | Arrow => True
  | FatArrow => True
  | Pipe => True
  | KwIf => True
  | PlusPlus => True
  | RParen => True
  | RBracket => True
  | RBrace => True
  | _ => False

--| A constructor's arguments, up to a token `stops` accepts (or the end).
def ctorArgs (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word) (stops: Tok → Bool):
    {Parse Item} Pattern :=
  if modes.at LBrace then
    let fields := fieldsPattern pself modes
    match modes.peek with
      | Some kind if !stops kind => fatal "braces after `${name.text}` in a pattern take no further arguments"
      | _ => PatternCtorFields name fields
  else
    match ctorArgList (Parse.mark().left + 1) pself modes name stops [] with
      | [] => PatternWord (if name.text == "Quot.mk" then Lower else Upper) name
      | arguments => PatternCtor name arguments

def ctorArgList (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Word)
    (stops: Tok → Bool) (found: List Pattern):
    {Parse Item} List Pattern :=
  match fuel, modes.peek with
    | Succ more, Some kind if !stops kind =>
      let argument :=
        if kind == LBrace then
          if lastIsUpper name found then
            fatal
              "a record pattern after a constructor in an argument of `${name.text}` is written in brackets: `({ … })`"
          else PatternRecord (fieldsPattern pself modes)
        else if argumentMinus left() then
          let minus := bump()
          if modes.at Num then PatternNegative minus bump() else modes.fail "a number"
        else pself { modes, level = PatternPlain }
      ctorArgList more pself modes name stops [argument, ..found]
    | _, _ => found.reverse

--| Whether the token before is an uppercase name (`found` is newest first).
def lastIsUpper (name: Word) (found: List Pattern): Bool := match found with
  | [] => name.text != "Quot.mk"
  | [PatternWord kind _, .._] => kind == Upper
  | _ => False

def fieldsPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} FieldsPattern :=
  let open := modes.expect LBrace "`{`"
  let inner := modes.inBrackets
  let (fields, trailingComma, rest) := fieldPatterns (Parse.mark().left + 1) pself inner []
  { open, fields, trailingComma, rest, close = inner.expect RBrace "`,` or `}`" }

def fieldPatterns (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (found: List FieldPattern):
    {Parse Item} (List FieldPattern, Bool, Option Word) :=
  match fuel with
    | Zero => (found.reverse, False, None)
    | Succ more =>
      if modes.at DotDot then (found.reverse, False, Some bump())
      else if modes.at RBrace then (found.reverse, !found.isEmpty, None)
      else
        let name := modes.lower "a field name, or `..`"
        let value := match modes.eat Equals with
          | Some equals => Some (equals, pself { modes, level = PatternFieldValue })
          | None => None
        let field := { name, value }
        match modes.eat Comma with
          | Some _ => fieldPatterns more pself modes [field, ..found]
          | None => ([field, ..found].reverse, False, None)

--| `"--" ++ rest`: only a text literal may stand before the `++`.
def patternAppend (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (start: Pattern) (next: PatternLevel):
    {Parse Item} Pattern :=
  if !modes.at PlusPlus then start
  else
    match start with
      | PatternWord kind _ if kind == Str =>
        let operator := bump()
        PatternAppend start operator (pself { modes, level = next })
      | _ => fatal "a text pattern can only take a fixed start"

--| `p | q`, with the `|` on the same line.
def alternatives (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (first: Pattern) (next: PatternLevel):
    {Parse Item} Pattern :=
  match alternativeLinks (Parse.mark().left + 1) pself modes next [] with
    | [] => first
    | links => PatternOr first links

def alternativeLinks (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (next: PatternLevel) (found: List (Word, Pattern)):
    {Parse Item} List (Word, Pattern) :=
  match fuel, left() with
    | Succ more, [bar, .._] if bar.kind == Pipe && !bar.leaf.token.lineStart && !modes.stops bar =>
      let barLeaf := bump()
      let alternative := pself { modes, level = next }
      alternativeLinks more pself modes next [(barLeaf, alternative), ..found]
    | _, _ => found.reverse

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
