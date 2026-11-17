--| The parser (stage 2a: expressions and patterns), on `Parse` over the
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
--| Stage 2a reads expressions on one line: a token starting a later line
--| (a block, a continued line), and the constructs of stages 2b and 2c
--| (`let`, `handle`, `calc`, `rewrite`, `cases`, `match induct`, function
--| types with named parameters, effect rows), are refused with a message
--| starting "not parsed yet".

namespace Syntax
import Std (Bool, Empty, List, Nat, Option, Parse, Result, Text)

--| A leaf as the parser reads it, with what the Rust parser learns from
--| spans: whether no space separates it from the token before on its line
--| (`glued`), and whether that token ends an operand (`afterOperand`), which
--| together decide what a `-`, `!` or `.` is.
type Item = { leaf: Leaf, glued: Bool, afterOperand: Bool }

def Item.kind (item: Item): Tok := item.leaf.token.kind

def Item.text (item: Item): Text := item.leaf.token.text

def items (leaves: List Leaf): List Item := itemsAfter None leaves

def itemsAfter (before: Option Token): List Leaf → List Item
  | [] => []
  | [leaf, ..rest] =>
    let token := leaf.token
    let glued := match before with
      | Some previous => !token.lineStart && previous.column + previous.text.utf8Length == token.column
      | None => False
    let afterOperand := before.map (previous => previous.kind.closesOperand) |> .getOrElse False
    [{ leaf, glued, afterOperand }, ..itemsAfter (Some token) rest]

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

--| What the Rust parser keeps in `Modes` that stage 2a needs: whether a
--| guard's condition is being read, outside brackets opened since (so a
--| `=>` ends it), and where a method section that starts an expression
--| starts (an offset), which its own parser marks.
type Modes = { guard: Bool, sectionHead: Option Nat }

def Modes.start: Modes := { guard = False, sectionHead = None }

--| The modes inside a bracket: a `=>` there is no guard's.
def Modes.inBrackets (modes: Modes): Modes := { modes | guard = False }

--| Whether `item` ends what is being read, whatever it is: the guard's `=>`.
def Modes.stops (modes: Modes) (item: Item): Bool := modes.guard && item.kind == FatArrow

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

def notYet (what: Text): {Parse Item} a := fatal "not parsed yet (stage 2b or 2c): ${what}"

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
def bump(): {Parse Item} Leaf := match Parse.next (item => True) with
  | Some item => item.leaf
  | None => fatal "the parser read past the end of its input"

def Modes.eat (modes: Modes) (wanted: Tok): {Parse Item} Option Leaf := if modes.at wanted then Some bump() else None

def Modes.expect (modes: Modes) (wanted: Tok) (what: Text): {Parse Item} Leaf :=
  if modes.at wanted then bump() else modes.fail what

--| "expected `what`, but …": the Rust parser's `unexpected`.
def Modes.unexpected (modes: Modes) (what: Text): {Parse Item} Text := match left() with
  | [] => "expected ${what}, but reached the end of the declaration"
  | [item, .._] =>
    if item.kind == At && !modes.stops item then "attributes can't be written here"
    else if modes.stops item then "expected ${what}, but the guard's `=>` starts here"
    else "expected ${what}, but found ${item.spelled}"

def Modes.fail (modes: Modes) (what: Text): {Parse Item} a := fatal (modes.unexpected what)

--| `unexpected`, naming a keyword as one (`unexpected_name`).
def Modes.failName (modes: Modes) (what: Text): {Parse Item} a := match left() with
  | [item, .._] if !modes.stops item && Tok.keyword item.text |> .isSome =>
    fatal "expected ${what}, but found the keyword `${item.text}`"
  | _ => modes.fail what

--| An unqualified lowercase name (the Rust parser's `lower`).
def Modes.lower (modes: Modes) (what: Text): {Parse Item} Leaf := match left() with
  | [item, .._] if item.kind == Lower && !modes.stops item =>
    if isQualified item then fatal "`${item.text}` is a qualified name, which can't be used here" else bump()
  | _ => modes.failName what

-- Looking ahead, as the Rust parser does by index.

--| The items after the bracket group `items` starts with, if it closes.
def skipGroup (depth: Nat): List Item → Option (List Item)
  | [] => None
  | [item, ..rest] =>
    if item.kind.isOpener then skipGroup (depth + 1) rest
    else if item.kind.isCloser then (if depth <= 1 then Some rest else skipGroup (depth - 1) rest)
    else skipGroup depth rest

--| The items inside the bracket group `items` starts with (after its
--| opener), if it closes.
def groupInside (depth: Nat) (found: List Item): List Item → Option (List Item)
  | [] => None
  | [item, ..rest] =>
    if item.kind.isOpener then groupInside (depth + 1) [item, ..found] rest
    else if item.kind.isCloser then
      (if depth <= 1 then Some found.reverse else groupInside (depth - 1) [item, ..found] rest)
    else groupInside depth [item, ..found] rest

def isQualified (item: Item): Bool := item.text.contains "."

--| `lambda_ahead`: names, `_` and bracket groups, then a `=>`.
def lambdaAhead (modes: Modes) (items: List Item): Bool := lambdaAheadFrom (items.length + 1) modes 0 items

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

def afterGroup (more: Nat) (modes: Modes) (count: Nat) (items: List Item): Bool := match skipGroup 0 items with
  | Some after => lambdaAheadFrom more modes (count + 1) after
  | None => False

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
def annotatedPatternAhead (items: List Item): Bool := match items with
  | [_, ..rest] => annotatedFrom (rest.length + 1) True rest
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
          match skipGroup 0 [item, ..rest] with
            | Some after => annotatedFrom more False after
            | None => False
        else if kind.isCloser then False
        else annotatedFrom more False rest

--| `[x: A]`, `[auto P]`, `[@[…] x: A]` starting a function type.
def implicitBinderAhead (items: List Item): Bool := match items with
  | [open, ..rest] if open.kind == LBracket =>
    namelessAutoAt items || namesThen (pastAttributes (rest.length + 1) rest) 0 (kind => kind == Colon)
  | _ => False

def pastAttributes (fuel: Nat) (items: List Item): List Item := match fuel, items with
  | Succ more, [at, ..rest] if at.kind == At =>
    match skipGroup 0 rest with
      | Some after => pastAttributes more after
      | None => items
  | _, _ => items

--| `(x: A) -> B`: names and `:` in brackets, an arrow after them.
def piBinderAhead (items: List Item): Bool := match items with
  | [open, ..rest] if open.kind == LParen && namesThen rest 0 (kind => kind == Colon) =>
    match skipGroup 0 items with
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
    match groupInside 1 [] rest with
      | Some inside =>
        match inside.reverse with
          | [last, .._] => if last.kind.isSectionOperator then Some inside.length else None
          | [] => None
      | None => None
  | [] => None

-- Expressions.

--| The fuel is twice the items left, and one more, since a level may hand
--| over to another without reading (`LevelArgument` after an argument).
def expression (modes: Modes): {Parse Item} Expr :=
  Parse.recursiveWithFuel (2 * Parse.mark().left + 2) expressionRule { modes, level = LevelFull }

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

def full (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := self { modes, level = LevelFull }

--| `expr`: a line after the first starting here would be a block.
def expr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let later: Bool := offset() > 0
  match left() with
    | [item, .._] if item.leaf.token.lineStart && later && !modes.stops item => notYet "a block or a continued line"
    | _ => exprInline self modes

def exprInline (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := match modes.peek with
  | Some KwHandle => notYet "`handle`"
  | Some KwLet => notYet "an expression `let`"
  | Some KwCalc => notYet "`calc`"
  | Some KwRewrite => notYet "`rewrite`"
  | Some KwCases => notYet "`cases`"
  | Some KwMatch =>
    let keyword := bump()
    let matched := matchExpr self modes keyword
    if atPipe modes then pipeChain self modes matched else matched
  | _ =>
    if lambdaAhead modes left() then lambda self modes None
    else
      match modes.peek with
        | Some KwExists => quantifier self modes
        | Some KwForall => quantifier self modes
        | Some KwIf =>
          let keyword := bump()
          ifExpr self modes keyword
        | _ =>
          if implicitBinderAhead left() || piBinderAhead left() then notYet "a function type with named parameters"
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
  match modes.peek with
    | Some Arrow =>
      let arrow := bump()
      if modes.at LBrace then notYet "an effect row" else ArrowType sectioned arrow (full self modes)
    | Some Semi =>
      let semicolon := bump()
      match modes.peek with
        | None => fatal semicolonAtEnd
        | Some RParen => fatal semicolonAtEnd
        | Some RBracket => fatal semicolonAtEnd
        | Some RBrace => fatal semicolonAtEnd
        | Some Comma => fatal semicolonAtEnd
        | _ => Seq sectioned semicolon (full self modes)
    | _ => sectioned

def semicolonAtEnd: Text := "`;` needs an expression after it: `(a; b)` runs `a`, then gives `b`'s value"

--| `a && b || c`: `&&` within each disjunct and `||` between them, both
--| grouped to the right.
def logicChain (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Expr): {Parse Item} Expr :=
  let links := logicLinks (left().length + 1) self modes []
  groupLogic (links.length + 1) first links

def logicLinks (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (found: List (Leaf, Expr)):
    {Parse Item} List (Leaf, Expr) :=
  let ahead := andOrAhead modes
  match fuel with
    | Succ more if ahead =>
      let operator := bump()
      let operand := if quantifierAhead modes then quantifier self modes else cmpExpr self modes
      logicLinks more self modes [(operator, operand), ..found]
    | _ => found.reverse

def groupLogic (fuel: Nat) (first: Expr) (links: List (Leaf, Expr)): Expr :=
  let (conjunction, after) := conjunctionOf first links
  match fuel, after with
    | Succ more, [(or, next), ..rest] => Binary conjunction or (groupLogic more next rest)
    | _, _ => conjunction

--| The `&&`s from `first` up to the next `||`, grouped to the right, and
--| the links from that `||` on.
def conjunctionOf (first: Expr): List (Leaf, Expr) → (Expr, List (Leaf, Expr))
  | [(and, next), ..rest] if and.token.kind == AndAnd =>
    let (right, after) := conjunctionOf next rest
    (Binary first and right, after)
  | links => (first, links)

--| `a <-> b`, which doesn't chain.
def iff (self: Goal → {Parse Item} Expr) (modes: Modes) (left: Expr): {Parse Item} Expr :=
  let operator := bump()
  let right :=
    if quantifierAhead modes then quantifier self modes
    else
      let compared := cmpExpr self modes
      if andOrAhead modes then logicChain self modes compared else compared
  if modes.at IffArrow then fatal "`<->` doesn't chain" else Iff left operator right

def quantifierAhead (modes: Modes): {Parse Item} Bool := modes.at KwExists || modes.at KwForall

def quantifier (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := match left() with
  | [item, .._] if item.kind == KwForall => forallExpr self modes
  | _ =>
    let keyword := bump()
    if lambdaAhead modes left() then lambda self modes (Some keyword)
    else modes.fail "a parameter and `=>` after `exists`"

--| `∀ (x: A) [b: B] n => P`: names and typed groups, but no patterns.
def forallExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let keyword := bump()
  let params := forallParams (left().length + 1) self modes []
  if params.isEmpty then modes.fail "a parameter after `${keyword.token.text}`"
  else if modes.at FatArrow then
    let arrow := bump()
    Lambda (Some keyword) params arrow (full self modes)
  else modes.fail "`=>` after the parameters of `${keyword.token.text}`"

def forallParams (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (found: List Param):
    {Parse Item} List Param :=
  let items := left()
  match fuel, items with
    | Succ more, [item, .._] if !modes.stops item =>
      match item.kind with
        | Lower if !isQualified item => forallParams more self modes [NameParam bump(), ..found]
        | Underscore => forallParams more self modes [NameParam bump(), ..found]
        | LParen if annotatedParamAhead items => forallParams more self modes [typedParam self modes False, ..found]
        | LBracket if implicitGroupAt items || namelessAutoAt items =>
          forallParams more self modes [typedParam self modes True, ..found]
        | _ => found.reverse
    | _, _ => found.reverse

--| A lambda's parameters, `=>` and body; with a keyword, an `∃`'s.
def lambda (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Option Leaf): {Parse Item} Expr :=
  let params := lambdaParams (left().length + 1) self modes []
  if params.isEmpty then modes.fail "a parameter name"
  else
    let arrow := modes.expect FatArrow "`=>`"
    Lambda keyword params arrow (full self modes)

def lambdaParams (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (found: List Param):
    {Parse Item} List Param :=
  let items := left()
  match fuel, items with
    | Succ more, [item, .._] if !modes.stops item =>
      match item.kind with
        | Lower => lambdaParams more self modes [NameParam (modes.lower "a name"), ..found]
        | Underscore => lambdaParams more self modes [NameParam bump(), ..found]
        | LParen =>
          if annotatedParamAhead left() then lambdaParams more self modes [typedParam self modes False, ..found]
          else if annotatedPatternAhead left() then
            let open := bump()
            let inner := modes.inBrackets
            let pattern := patternOf inner
            let colon := inner.expect Colon "`:`"
            let annotation := full self inner
            let close := inner.expect RParen "`)`"
            lambdaParams more self modes [TypedPattern open pattern colon annotation close, ..found]
          else lambdaParams more self modes [PatternParam (patternOf modes), ..found]
        | LBracket if implicitGroupAt items || namelessAutoAt items =>
          lambdaParams more self modes [typedParam self modes True, ..found]
        | LBrace => lambdaParams more self modes [PatternParam (patternOf modes), ..found]
        | _ => found.reverse
    | _, _ => found.reverse

--| `(x y: A)`, `[a: Type]`, `[auto h: P]` or `[auto P]` (the Rust
--| parser's `header_param_parts`, without defaults, which a lambda refuses).
def typedParam (self: Goal → {Parse Item} Expr) (modes: Modes) (implicit: Bool): {Parse Item} Param :=
  let open := bump()
  let inner := modes.inBrackets
  let names := leavesOf (left().length + 1) inner Lower []
  let closer := if implicit then RBracket else RParen
  let closeText := if implicit then "`]`" else "`)`"
  let typeFollows := !(inner.at Colon || inner.at RBracket || inner.peek.isNone)
  match names with
    | [auto] if implicit && auto.token.text == "auto" && typeFollows =>
      let annotation := full self inner
      let close := inner.expect RBracket "`]` to close the parameter `[auto …]`"
      TypedParam open names None annotation close
    | _ =>
      if inner.at Colon then
        let colon := bump()
        let annotation := full self inner
        if inner.at ColonEq then fatal "only a definition's parameter or a field can have a default value"
        else
          let texts := names.map (name => name.token.text)
          let written := match texts with
            | ["auto", second, ..more] if implicit => "auto ${[second, ..more].joinWith " "}"
            | _ => texts.joinWith " "
          let opener := if implicit then "[" else "("
          let close := inner.expect closer "${closeText} to close the parameter `${opener}${written}: …`"
          TypedParam open names (Some colon) annotation close
      else fatal "a parameter needs a type"

--| The tokens of kind `kind` that come next.
def leavesOf (fuel: Nat) (modes: Modes) (kind: Tok) (found: List Leaf): {Parse Item} List Leaf :=
  let ahead := modes.at kind
  match fuel with
    | Succ more if ahead => leavesOf more modes kind [bump(), ..found]
    | _ => found.reverse

def ifExpr (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Leaf): {Parse Item} Expr :=
  let binder := namedBinder modes
  let condition := full self modes
  let thenKeyword := modes.expect KwThen "`then`"
  let whenTrue := full self modes
  let elseKeyword := modes.expect KwElse "`else`"
  If keyword binder condition thenKeyword whenTrue elseKeyword (full self modes)

--| `h:` before a condition or scrutinee.
def namedBinder (modes: Modes): {Parse Item} Option (Leaf, Leaf) :=
  if modes.at Lower && isSome Colon (modes.peekAt 1) then
    let name := modes.lower "a name"
    Some (name, bump())
  else None

def atPipe (modes: Modes): {Parse Item} Bool := modes.at PipeGt

--| `x |> f |> g`, after `x`: grouped to the left.
def pipeChain (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr): {Parse Item} Expr :=
  pipesFrom (left().length + 1) self modes value

def pipesFrom (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (value: Expr): {Parse Item} Expr :=
  let ahead := atPipe modes
  match fuel with
    | Succ more if ahead =>
      let operator := bump()
      let function :=
        if lambdaAhead modes left() then lambda self modes None
        else
          let start := offset()
          let section := modes.at Dot
          let inner := if section then { modes | sectionHead = Some start } else modes
          let operand := appendExpr self inner
          if section then Section operand else operand
      pipesFrom more self modes (Piped value operator function)
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
        let keyword := bump()
        Binary lhs operator (ifExpr self modes keyword)
      else
        let second := pipedRange self modes
        match modes.peek with
          | Some next if next.isComparison || next == KwIn || next == NotIn =>
            comparisonChain self modes lhs operator second
          | _ => Binary lhs operator second
    | _ => lhs

def pipedRange (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let range := rangeExpr self modes
  if atPipe modes then pipeChain self modes range else range

def membership (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Option Tok) (element: Expr): {Parse Item} Expr :=
  if isSome Bang first then fatal "`!` here applies to the element, not to the membership test"
  else
    let operator := bump()
    Membership element operator (pipedRange self modes)

--| `a <= b < c …`, after `a <= b`.
def comparisonChain (self: Goal → {Parse Item} Expr) (modes: Modes) (first: Expr) (operator: Leaf) (second: Expr):
    {Parse Item} Expr :=
  let kind := operator.token.kind
  if kind == Equals || kind == EqEq || kind == NotEq then fatal (chainRefused kind)
  else
    let descending := kind == Gt || kind == Ge
    Chain first [(operator, second), ..chainLinks (left().length + 1) self modes descending []]

def chainRefused (kind: Tok): Text := "`${kind.written}` can't be part of a chain of comparisons"

def chainLinks (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (descending: Bool) (found: List (Leaf, Expr)):
    {Parse Item} List (Leaf, Expr) :=
  match fuel, modes.peek with
    | Succ more, Some kind =>
      let flip := kind == Gt || kind == Ge
      if kind == Equals || kind == EqEq then fatal (chainRefused kind)
      else if kind == NotEq then fatal "`!=` can't be part of a chain of comparisons"
      else if kind == KwIn || kind == NotIn then fatal "`in` can't be part of a chain of comparisons"
      else if !(kind == Lt || kind == Le || flip) then found.reverse
      else if flip != descending then
        fatal "a chain of comparisons goes one way: `<` and `<=` can't be mixed with `>` and `>=`"
      else
        let operator := bump()
        let operand := pipedRange self modes
        chainLinks more self modes descending [(operator, operand), ..found]
    | _, _ => found.reverse

def rangeExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let low := appendExpr self modes
  match modes.peek with
    | Some DotDot => fatal "a range is `a ..< b` (up to, not including, `b`) or `a ..= b` (through `b`)"
    | Some kind if kind == DotDotLt || kind == DotDotEq =>
      let operator := bump()
      let high := appendExpr self modes
      if modes.at DotDotLt || modes.at DotDotEq then fatal "ranges don't chain" else Range low operator high
    | _ => low

--| `a ++ b ++ c`, grouped to the right.
def appendExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let first := addExpr self modes
  rightNested first (operatorLinks (left().length + 1) modes (kind => kind == PlusPlus) (() => addExpr self modes) [])

def rightNested (first: Expr): List (Leaf, Expr) → Expr
  | [] => first
  | [(operator, next), ..rest] => Binary first operator (rightNested next rest)

--| The operators `takes` accepts that come next, each with its operand.
def operatorLinks (fuel: Nat) (modes: Modes) (takes: Tok → Bool)
    (operand: () → {Parse Item} Expr) (found: List (Leaf, Expr)):
    {Parse Item} List (Leaf, Expr) :=
  match fuel, modes.peek with
    | Succ more, Some kind if takes kind =>
      let operator := bump()
      let value := operand()
      operatorLinks more modes takes operand [(operator, value), ..found]
    | _, _ => found.reverse

def leftNested (first: Expr): List (Leaf, Expr) → Expr
  | [] => first
  | [(operator, next), ..rest] => leftNested (Binary first operator next) rest

def addExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let first := mulExpr self modes
  leftNested first
    (operatorLinks (left().length + 1) modes (kind => kind == Plus || kind == Minus) (() => mulExpr self modes) [])

def mulExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let first := unary self modes
  leftNested first
    (operatorLinks
      (left().length + 1)
      modes
      (kind => kind == Star || kind == Slash || kind == Percent)
      (() => unary self modes)
      [])

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
  let applied := if startsAtom modes then App head (arguments (left().length + 1) self modes []) else head
  if section then Section applied else applied

def arguments (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (found: List Expr): {Parse Item} List Expr :=
  match fuel with
    | Succ more =>
      let argument :=
        if modes.at Upper && isSome LBrace (modes.peekAt 1) then braceArgument self modes
        else self { modes, level = LevelArgument }
      if startsAtom modes then arguments more self modes [argument, ..found] else [argument, ..found].reverse
    | Zero => found.reverse

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
  let section := isSome Dot first
  let upper := isSome Upper first
  let paren := isSome LParen first
  let callable := isSome Lower first || upper || section
  let base := atomBase self modes
  let (based, callable) :=
    if upper && head && modes.at LBrace then (CtorFields base (recordExpr self modes), False) else (base, callable)
  let result := suffixes (left().length + 1) modes based callable paren
  if section && !head then Section result else result

def suffixes (fuel: Nat) (modes: Modes) (target: Expr) (callable paren: Bool): {Parse Item} Expr := match fuel with
  | Zero => target
  | Succ more =>
    let called :=
      if unitCall left() && (callable || paren && callableParen target) then
        let open := bump()
        App target [Unit open bump()]
      else target
    let items := left()
    match items with
      | [dot, field, .._] if dot.kind == Dot && !modes.stops dot && !sectionAt items =>
        if !((field.kind == Lower || field.kind == Upper) && !isQualified field && !modes.stops field) then
          fatal "expected a field name after `.`"
        else if !dot.glued || !field.glued then fatal "field access is written without spaces around the `.`"
        else
          let dotLeaf := bump()
          suffixes more modes (FieldAccess (Some called) dotLeaf bump()) True paren
      | [dot] if dot.kind == Dot && !modes.stops dot => fatal "expected a field name after `.`"
      | _ => called

--| Whether `(e)()` calls `e`: a name or a field access, in brackets.
def callableParen: Expr → Bool
  | Paren _ inner _ => callableInside inner
  | _ => False

def callableInside: Expr → Bool
  | Word leaf => leaf.token.kind == Lower || leaf.token.kind == Upper
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
  | Some KwArithmetic => facts self modes
  | Some KwAlgebra => facts self modes
  | Some KwCases => if bareCases modes then Word bump() else modes.fail "an expression"
  | Some TypeU =>
    let keyword := bump()
    match left() with
      | [level, .._] if level.kind == Num && !modes.stops level =>
        if (level.text.toNat |> .getOrElse 0) > 65535 then fatal "universe level is too large"
        else Universe keyword bump()
      | _ => Word keyword
  | Some LParen => parenAtom self modes
  | Some LBracket =>
    match modes.peekAt 1, modes.peekAt 2 with
      | Some Lower, Some ColonEq => namedArgument self modes RBracket "`]`"
      | Some KwDecreasing, Some ColonEq => namedArgument self modes RBracket "`]`"
      | _, _ => listExpr self modes
  | Some LBrace => recordExpr self modes
  | Some Dot => sectionStart modes
  | Some kind if isWord kind => Word bump()
  | _ => if isSome FatArrow (modes.peekAt 1) then modes.failName "an expression" else modes.fail "an expression"

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
    Prefix minus (Word bump())
  else prefixAtom self modes (argumentMinus left())

--| A `-` or `!` negating an argument, if `negates`.
def prefixAtom (self: Goal → {Parse Item} Expr) (modes: Modes) (negates: Bool): {Parse Item} Expr :=
  if negates then
    let operator := bump()
    Prefix operator (self { modes, level = LevelArgument })
  else modes.failName "an expression"

--| `arithmetic` or `algebra`, and its facts if a list follows.
def facts (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let keyword := bump()
  if modes.at LBracket then
    let list := listExpr self modes
    if hasSpread list then fatal "a list of facts can't have a `..` spread" else Facts keyword list
  else Word keyword

def hasSpread: Expr → Bool
  | ListOf _ items _ => items.any (sep =>
    sep.item
      |> matches
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
      let rest :=
        commaList (left().length + 1) inner (count => inner.at RParen && count >= 2) (() => full self inner) first []
      Tuple open rest (tupleClose inner)
    | Some Colon =>
      let colon := bump()
      let annotation := full self inner
      if inner.at Comma then fatal tupleAnnotation
      else Annotation open first colon annotation (inner.expect RParen "`)`")
    | _ => Paren open first (inner.expect RParen "`)`")

def tupleClose (modes: Modes): {Parse Item} Leaf :=
  if modes.at Colon then fatal tupleAnnotation else modes.expect RParen "`)`"

def tupleAnnotation: Text := "an annotation can't be written inside a tuple without brackets"

--| `current` and the items after it, each with the comma after it: while a
--| comma follows, it is read, and unless `ends` (given the number of items
--| so far) says the list ends there, another item.
def commaList (fuel: Nat) (modes: Modes) (ends: Nat → {Parse Item} Bool) (next: () → {Parse Item} a)
    (current: a) (found: List (Sep a)):
    {Parse Item} List (Sep a) :=
  match fuel, modes.peek with
    | Succ more, Some Comma =>
      let comma := bump()
      let done := [{ item = current, comma = Some comma }, ..found]
      if ends done.length then done.reverse else commaList more modes ends next (next()) done
    | _, _ => [{ item = current, comma = None }, ..found].reverse

--| `(+ 1)`, `(&&)`: the operator first.
def operatorSection (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let open := bump()
  let inner := modes.inBrackets
  let operator := bump()
  if inner.at RParen then OperatorSection open None operator None bump()
  else
    let operand := sectionOperand self inner operator.token.kind
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
      rightNested first
        (operatorLinks
          (left().length + 1)
          modes
          (kind => kind == AndAnd)
          (() => self { modes, level = LevelComparison })
          [])
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
  if inner.at RBracket then ListOf open [] bump()
  else
    let first := listItem self inner
    let rest := commaList (left().length + 1) inner (count => inner.at RBracket) (() => listItem self inner) first []
    ListOf open rest (inner.expect RBracket "`,` or `]`")

def listItem (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  if modes.at DotDot then
    let dots := bump()
    if modes.at Comma || modes.at RBracket then fatal "expected a list after `..`, as in `[x, ..xs]`"
    else Spread dots (full self modes)
  else full self modes

def recordExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let open := modes.expect LBrace "`{`"
  let inner := modes.inBrackets
  if inner.at RBrace then Record open None [] bump()
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
    let fields := commaList (left().length + 1) inner (count => inner.at RBrace) (() => recordField self inner) first []
    Record open base fields (inner.expect RBrace "`,` or `}`")

def recordField (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let name := modes.lower "a field name"
  if modes.at Equals then
    let equals := bump()
    RecordField name equals (full self modes)
  else Word name

--| `C { … }` as an argument.
def braceArgument (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let ctor := atomBase self modes
  CtorFields ctor (recordExpr self modes)

def interpolated (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let start := bump()
  Interpolated [TextPiece start, ..interpolations (left().length + 1) self modes []]

def interpolations (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (found: List Piece):
    {Parse Item} List Piece :=
  match fuel with
    | Zero => found.reverse
    | Succ more =>
      let open := modes.expect InterpOpen "`\${`"
      let value := full self modes
      let close := modes.expect InterpClose "`}`"
      let withMiddle :=
        if modes.at StrMid then [TextPiece bump(), Interpolation open value close, ..found]
        else [Interpolation open value close, ..found]
      if modes.at StrEnd then [TextPiece bump(), ..withMiddle].reverse
      else if modes.at InterpOpen then interpolations more self modes withMiddle
      else modes.fail "`\${` or the end of the text"

-- `match` and clause lambdas.

type ClauseKind = | ClausePlain | ClauseSome | ClauseMatches

def wordAhead (modes: Modes) (word: Text): {Parse Item} Bool := match left() with
  | [item, .._] => item.kind == Lower && item.text == word && !modes.stops item
  | [] => False

def matchesBarAhead (modes: Modes): {Parse Item} Bool :=
  wordAhead modes "matches"
    && isSome Pipe (modes.peekAt 1)
    && !(isSome Lower (modes.peekAt 2) && isSome Equals (modes.peekAt 3))

--| `match induct` and `match reify` (stage 2c): the word, then not what
--| a scrutinee named `induct` would have after it.
def specialMatchAhead (modes: Modes): {Parse Item} Bool :=
  (wordAhead modes "induct" || wordAhead modes "reify")
    && (match modes.peekAt 1 with
      | Some KwWith => False
      | Some Comma => False
      | Some Colon => False
      | None => False
      | _ => True)

def matchExpr (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Leaf): {Parse Item} Expr :=
  if specialMatchAhead modes then notYet "`match induct` and `match reify`"
  else if modes.at Pipe then clauseLambda self modes keyword None ClausePlain
  else if wordAhead modes "some" && isSome Pipe (modes.peekAt 1) then
    let some := bump()
    clauseLambda self modes keyword (Some some) ClauseSome
  else
    let first := scrutinee self modes
    let scrutinees := commaList (left().length + 1) modes (count => False) (() => scrutinee self modes) first []
    let withKeyword := modes.expect KwWith "`with`"
    let arms := matchArms (left().length + 1) self modes scrutinees.length []
    if arms.isEmpty then modes.fail "`|` and an alternative" else Match keyword scrutinees withKeyword arms

def scrutinee (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Scrutinee :=
  let name := namedBinder modes
  { name, value = self { modes, level = LevelInline } }

def plural (count: Nat) (noun: Text): Text := if count == 1 then "${count} ${noun}" else "${count} ${noun}s"

def matchArms (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (scrutinees: Nat) (found: List Arm):
    {Parse Item} List Arm :=
  let ahead := modes.at Pipe
  match fuel with
    | Succ more if ahead =>
      let bar := bump()
      let patterns := armPatterns modes
      if patterns.length != scrutinees then
        fatal
          "this alternative has ${plural patterns.length "pattern"}, but the `match` has ${plural scrutinees "scrutinee"}"
      else
        let guard := guardOf self modes
        let body := armBody self modes (patterns.any (sep => sep.item.hasAbsurd))
        matchArms more self modes scrutinees [{ bar, patterns, guard, body }, ..found]
    | _ => found.reverse

def armPatterns (modes: Modes): {Parse Item} List (Sep Pattern) :=
  let first := altPattern modes
  commaList (left().length + 1) modes (count => False) (() => altPattern modes) first []

--| `=> e`, or nothing after an absurd pattern with no `=>`.
def armBody (self: Goal → {Parse Item} Expr) (modes: Modes) (absurd: Bool): {Parse Item} Option (Leaf, Expr) :=
  if absurd && !modes.at FatArrow then None
  else
    let arrow := modes.expect FatArrow "`=>`"
    Some (arrow, full self modes)

def guardOf (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Option Guard :=
  if modes.at KwIf then
    let keyword := bump()
    let binder := namedBinder modes
    let condition := full self { modes | guard = True }
    Some { keyword, binder, condition }
  else None

def clauseLambda (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Leaf) (word: Option Leaf) (kind: ClauseKind):
    {Parse Item} Expr :=
  let arms := clauseArms (left().length + 1) self modes kind None []
  if arms.isEmpty then modes.fail "`|` and an alternative" else ClauseLambda keyword word arms

def clauseArms (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: ClauseKind)
    (count: Option Nat) (found: List Arm):
    {Parse Item} List Arm :=
  let ahead := modes.at Pipe
  match fuel with
    | Succ more if ahead =>
      let bar := bump()
      let patterns := armPatterns modes
      match count with
        | Some first if first != patterns.length =>
          fatal "this alternative has ${plural patterns.length "pattern"}, but the first has ${first}"
        | _ =>
          let guard := guardOf self modes
          let absurd := patterns.any (sep => sep.item.hasAbsurd)
          let body := match kind with
            | ClauseMatches => if modes.at FatArrow then armBody self modes False else None
            | ClausePlain => armBody self modes absurd
            | ClauseSome => armBody self modes False
          clauseArms more self modes kind (Some patterns.length) [{ bar, patterns, guard, body }, ..found]
    | _ => found.reverse

-- Patterns.

--| Twice the items left, and one more: a level may hand over to the plain
--| pattern without reading (`PatternAltOne` to `PatternTupleComponent` to
--| `PatternPlain`).
def pattern (goal: PatternGoal): {Parse Item} Pattern :=
  Parse.recursiveWithFuel (2 * Parse.mark().left + 2) patternRule goal

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
  | PatternTuple _ items _ => anySepAbsurd items
  | PatternList _ items _ _ => anySepAbsurd items
  | PatternOr first rest => first.hasAbsurd || anyLinkAbsurd rest
  | PatternParen _ inner _ => inner.hasAbsurd
  | _ => False

def anyAbsurd: List Pattern → Bool
  | [] => False
  | [first, ..rest] => first.hasAbsurd || anyAbsurd rest

def anySepAbsurd: List (Sep Pattern) → Bool
  | [] => False
  | [{ item, comma }, ..rest] => item.hasAbsurd || anySepAbsurd rest

def anyLinkAbsurd: List (Leaf, Pattern) → Bool
  | [] => False
  | [(bar, item), ..rest] => item.hasAbsurd || anyLinkAbsurd rest

def ctorAhead (modes: Modes): {Parse Item} Bool := modes.at Upper || wordAhead modes "Quot.mk"

def plainPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  match modes.peek with
    | Some Upper => PatternWord bump()
    | Some Lower => if wordAhead modes "Quot.mk" then PatternWord bump() else PatternWord (modes.lower "a pattern")
    | Some Underscore => PatternWord bump()
    | Some Num => PatternWord bump()
    | Some CharLit => PatternWord bump()
    | Some Str => PatternWord bump()
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
def parenPatternEnd (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (open: Leaf) (first: Pattern):
    {Parse Item} Pattern :=
  if modes.at Comma then
    let items :=
      commaList
        (left().length + 1)
        modes
        (count => modes.at RParen && count >= 2)
        (() => tupleItem pself modes)
        first
        []
    PatternTuple open items (modes.expect RParen "`)`")
  else PatternParen open first (modes.expect RParen "`)`")

def listPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  let open := bump()
  let inner := modes.inBrackets
  let (items, tail) := listPatternItems (left().length + 1) pself inner []
  let comma := inner.at Comma
  match tail with
    | Some _ if comma => fatal "a `..` tail must be the last item of a list pattern"
    | Some _ => PatternList open items tail (inner.expect RBracket "`]`: a `..` tail must be the last item")
    | None => PatternList open items tail (inner.expect RBracket "`,` or `]`")

def listPatternItems (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (found: List (Sep Pattern)):
    {Parse Item} (List (Sep Pattern), Option (Leaf, Pattern)) :=
  match fuel with
    | Zero => (found.reverse, None)
    | Succ more =>
      if modes.at RBracket then (found.reverse, None)
      else if modes.at DotDot then
        let dots := bump()
        (found.reverse, Some (dots, pself { modes, level = PatternPlain }))
      else
        let item := listItemPattern pself modes
        match modes.eat Comma with
          | Some comma => listPatternItems more pself modes [{ item, comma = Some comma }, ..found]
          | None => ([{ item, comma = None }, ..found].reverse, None)

def listItemPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  let first := listComponent pself modes
  alternatives pself modes first PatternListComponent

def tupleItem (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} Pattern :=
  let first := tupleComponent pself modes
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
    let plain := pself { modes, level = PatternPlain }
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
def ctorArgs (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Leaf) (stops: Tok → Bool):
    {Parse Item} Pattern :=
  if modes.at LBrace then
    let fields := fieldsPattern pself modes
    match modes.peek with
      | Some kind if !stops kind => fatal "braces after `${name.token.text}` in a pattern take no further arguments"
      | _ => PatternCtorFields name fields
  else
    match ctorArgList (left().length + 1) pself modes name stops [] with
      | [] => PatternWord name
      | arguments => PatternCtor name arguments

def ctorArgList (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (name: Leaf)
    (stops: Tok → Bool) (found: List Pattern):
    {Parse Item} List Pattern :=
  match fuel, modes.peek with
    | Succ more, Some kind if !stops kind =>
      let argument :=
        if kind == LBrace then
          if lastIsUpper name found then
            fatal
              "a record pattern after a constructor in an argument of `${name.token.text}` is written in brackets: `({ … })`"
          else PatternRecord (fieldsPattern pself modes)
        else if argumentMinus left() then
          let minus := bump()
          if modes.at Num then PatternNegative minus bump() else modes.fail "a number"
        else pself { modes, level = PatternPlain }
      ctorArgList more pself modes name stops [argument, ..found]
    | _, _ => found.reverse

--| Whether the token before is an uppercase name (`found` is newest first).
def lastIsUpper (name: Leaf) (found: List Pattern): Bool := match found with
  | [] => name.token.kind == Upper
  | [PatternWord leaf, .._] => leaf.token.kind == Upper
  | _ => False

def fieldsPattern (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes): {Parse Item} FieldsPattern :=
  let open := modes.expect LBrace "`{`"
  let inner := modes.inBrackets
  let (fields, rest) := fieldPatterns (left().length + 1) pself inner []
  { open, fields, rest, close = inner.expect RBrace "`,` or `}`" }

def fieldPatterns (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern)
    (modes: Modes) (found: List (Sep FieldPattern)):
    {Parse Item} (List (Sep FieldPattern), Option Leaf) :=
  match fuel with
    | Zero => (found.reverse, None)
    | Succ more =>
      if modes.at DotDot then (found.reverse, Some bump())
      else if modes.at RBrace then (found.reverse, None)
      else
        let name := modes.lower "a field name, or `..`"
        let value := match modes.eat Equals with
          | Some equals => Some (equals, pself { modes, level = PatternFieldValue })
          | None => None
        let field := { name, value }
        match modes.eat Comma with
          | Some comma => fieldPatterns more pself modes [{ item = field, comma = Some comma }, ..found]
          | None => ([{ item = field, comma = None }, ..found].reverse, None)

--| `"--" ++ rest`: only a text literal may stand before the `++`.
def patternAppend (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (start: Pattern) (next: PatternLevel):
    {Parse Item} Pattern :=
  if !modes.at PlusPlus then start
  else
    match start with
      | PatternWord leaf if leaf.token.kind == Str =>
        let operator := bump()
        PatternAppend start operator (pself { modes, level = next })
      | _ => fatal "a text pattern can only take a fixed start"

--| `p | q`, with the `|` on the same line.
def alternatives (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes) (first: Pattern) (next: PatternLevel):
    {Parse Item} Pattern :=
  match alternativeLinks (left().length + 1) pself modes next [] with
    | [] => first
    | links =>
      if first.binds || anyLinkBinds links then fatal "an or-pattern can't bind names" else PatternOr first links

def alternativeLinks (fuel: Nat) (pself: PatternGoal → {Parse Item} Pattern) (modes: Modes)
    (next: PatternLevel) (found: List (Leaf, Pattern)):
    {Parse Item} List (Leaf, Pattern) :=
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
  | Ok value => Ok value
  | Err failure => Err (failure.messages.head.getOrElse "the parser failed without a message")

def wholeExpression(): {Parse Item} Expr :=
  let value := expression Modes.start
  if left().isEmpty then value else Modes.start.fail "the end of the declaration"

-- The lowering's own error that stage 2a meets: an or-pattern binding a
-- name. The Rust side finds it after the parse, so a file with a syntax
-- error after the or-pattern gets the other message there.

--| Whether a pattern binds a name: a lowercase name, or a punned field.
def Pattern.binds: Pattern → Bool
  | PatternWord leaf => leaf.token.kind == Lower && leaf.token.text != "Quot.mk"
  | PatternCtor _ arguments => anyBinds arguments
  | PatternCtorFields _ fields => fieldsBind fields
  | PatternRecord fields => fieldsBind fields
  | PatternTuple _ items _ => anySepBinds items
  | PatternList _ items tail _ =>
    anySepBinds items
      || (match tail with
        | Some (_, rest) => rest.binds
        | None => False)
  | PatternNamed _ _ _ value _ => value.binds
  | PatternOr first rest => first.binds || anyLinkBinds rest
  | PatternParen _ inner _ => inner.binds
  | PatternNegative _ _ => False
  | PatternAbsurd _ _ => False
  | PatternAppend start _ rest => start.binds || rest.binds

def anyBinds: List Pattern → Bool
  | [] => False
  | [first, ..rest] => first.binds || anyBinds rest

def anySepBinds: List (Sep Pattern) → Bool
  | [] => False
  | [{ item, comma }, ..rest] => item.binds || anySepBinds rest

def anyLinkBinds: List (Leaf, Pattern) → Bool
  | [] => False
  | [(bar, item), ..rest] => item.binds || anyLinkBinds rest

def fieldsBind: FieldsPattern → Bool
  | { open, fields, rest, close } => anyFieldBinds fields

def anyFieldBinds: List (Sep FieldPattern) → Bool
  | [] => False
  | [{ item = { name, value }, comma }, ..rest] =>
    (match value with
      | Some (_, pattern) => pattern.binds
      | None => True)
      || anyFieldBinds rest
