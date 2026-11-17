--| The parser's layout constructs and proof steps (stage 2c): a block's
--| statements (`let`, local definitions), the expression `let`, `handle`,
--| `match induct` and `match reify`, `calc`, `rewrite` and its rule sets,
--| and `cases`: the Rust parser's `statement`, `let_statement`,
--| `local_def`, `handle`, `calc_body`, `rewrite_body` and their helpers,
--| function for function, as `Parser.sw` is for the rest.
--|
--| None of them holds a column. A block is its lines (`Block`), a `calc`
--| its steps and a handler its clauses: the columns that told the parser
--| where each starts are read from the items and left behind, so the
--| printer chooses them and reading its output back is a question about
--| the printer's indentation, not about the tree.

namespace Syntax
import Std (Bool, List, Nat, Option, Parse, Text)

--| The index and bracket depth of the next item: where a `rewrite` rule
--| or a `let` starts, for the ends that look back to it.
def here(): {Parse Item} (Nat, Nat) := match left() with
  | [item, .._] => (item.index, item.depth)
  | [] => (offset(), 0)

--| The next item's column, or 0 at the end.
def columnHere(): {Parse Item} Nat := left().head.map (item => item.leaf.token.column) |> .getOrElse 0

-- Statements.

--| One line of a block (`statement`).
def statement (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Statement := match modes.peek with
  | Some KwLet =>
    let binding := letStatement self modes
    if modes.at Semi then ExprStatement (letBody self modes binding) else LetStatement binding
  | Some KwDef => localDef self modes []
  | Some KwTheorem => localDef self modes []
  | Some At =>
    let attributes := attributesOf modes
    let allowed := match left(), modes.limit with
      | [next, .._], Some column if next.leaf.token.lineStart && next.leaf.token.column == column =>
        { modes | allow = Some next.index }
      | _, _ => modes
    if allowed.at KwDef || allowed.at KwTheorem then localDef self allowed attributes
    else fatal (misplaced "a statement that isn't a local definition")
  | Some KwExport => fatal "local definitions can't be exported: only top-level ones are"
  | Some KwOpaque => fatal "local definitions can't be `opaque`: only top-level ones can"
  | _ => ExprStatement (exprInline self modes)

--| `let p := e` or `let p: T := e` (`let_statement`). The value is read
--| with `letValue` at the `let`'s bracket depth, so a `;` there ends it.
def letStatement (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Let :=
  let (_, depth) := here()
  let keyword := fixedFrom()
  let pattern := letPattern modes
  let annotation :=
    if modes.at Colon then
      let colon := fixedFrom()
      Some (colon, self { modes = modes.sealed, level = LevelInline })
    else None
  if modes.at Equals then fatal defEquals
  else
    let colonEq := modes.expectFixed ColonEq "`:=`"
    { keyword, pattern, annotation, colonEq, value = full self { modes | letValue = Some depth } }

--| After `let`: a constructor takes its arguments without brackets, up
--| to the `:=` or `:` (`let_pattern`).
def letPattern (modes: Modes): {Parse Item} Pattern :=
  if ctorAhead modes then
    let name := bump()
    ctorArgs pattern modes name (kind => kind == Equals || kind == ColonEq || kind == Colon)
  else pattern { modes, level = PatternTupleComponent }

--| The `;` and body of an expression `let` (`let_body`).
def letBody (self: Goal → {Parse Item} Expr) (modes: Modes) (binding: Let): {Parse Item} Expr :=
  if !modes.at Semi then modes.fail "`;` after the value of `let`"
  else
    let semicolon := fixedFrom()
    let atEnd := match left() with
      | [next, .._] => next.kind == RParen || next.kind == RBracket || next.kind == RBrace || next.kind == Comma
      | [] => True
    if atEnd then fatal "`let` needs a body after `;`: `(let x := e; body)`"
    else LetIn binding semicolon (full self modes)

--| Whether a `;` next starts a sequence `a; b` (`sequence_ahead`): unless
--| a `let`'s value is being read and the `;` is at that `let`'s depth.
def sequenceAhead (modes: Modes): {Parse Item} Bool := match modes.letValue, left() with
  | Some depth, [next, .._] => next.depth > depth
  | _, _ => True

--| A local `def` or `theorem` (`local_def`), its attributes read.
def localDef (self: Goal → {Parse Item} Expr) (modes: Modes) (attributes: List Attributes): {Parse Item} Statement :=
  let d := columnHere()
  let (header, body) := definitionParts self modes None None (Some d)
  match header.unfoldingClause, body with
    | Some _, _ => fatal "a local definition can't have `unfolding`"
    | None, Primitive => fatal localNeedsBody
    | None, _ => LocalDef attributes header body

-- Handlers.

--| `handle e with | …`
def handleExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let keyword := fixedFrom()
  let computation := self { modes = modes.sealed, level = LevelInline }
  let withKeyword := modes.expectFixed KwWith "`with`"
  Handle keyword computation withKeyword (handlerClauses self modes)

--| `match reify t with | …`, after `match` and `reify`.
def reifyExpr (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword reify: Comments): {Parse Item} Expr :=
  let computation := self { modes = modes.sealed, level = LevelInline }
  if modes.at Comma then fatal "`match reify` takes one computation, with nothing else to match"
  else
    let withKeyword := modes.expectFixed KwWith "`with`"
    Reify keyword reify computation withKeyword (handlerClauses self modes)

--| At least one clause; clauses starting lines line up.
def handlerClauses (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} List HandlerClause :=
  match clausesFrom (Parse.mark().left + 1) self modes None [] with
    | [] => modes.fail "`|` and a handler clause"
    | clauses => clauses

def clausesFrom (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (column: Option Nat) (found: List HandlerClause):
    {Parse Item} List HandlerClause :=
  let (lined, column) := armColumn column
  let ahead := modes.at Pipe && lined
  match fuel with
    | Succ more if ahead =>
      let bar := fixedFrom()
      clausesFrom more self modes column [handlerClause self modes bar, ..found]
    | _ => found.reverse

--| `return x => e` or `op p, k => e`, after the `|` (`handler_clause`).
def handlerClause (self: Goal → {Parse Item} Expr) (modes: Modes) (bar: Comments): {Parse Item} HandlerClause :=
  if modes.at KwReturn then
    let keyword := fixedFrom()
    let name := if modes.at Underscore then bump() else modes.lower "a name for the result"
    let arrow := modes.expectFixed FatArrow "`=>`"
    ReturnClause bar keyword name arrow (full self modes)
  else
    let operation := modes.lowerQualified "an operation, or `return`"
    let argument := patternOf modes
    if modes.at FatArrow then fatal "name the continuation: `| ${operation.text} x, k => …`"
    else
      let comma := modes.expectFixed Comma "`,` and a name for the continuation"
      let continuation := if modes.at Underscore then bump() else modes.lower "a name for the continuation"
      if modes.at Comma then fatal "an operation takes one argument; bracket a tuple: `(a, b)`"
      else
        let arrow := modes.expectFixed FatArrow "`=>`"
        OperationClause bar operation argument comma continuation arrow (full self modes)

--| `match induct (f args) with | eqK x ih => …`, after `match` and
--| `induct`.
def inductExpr (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword induct: Comments): {Parse Item} Expr :=
  let call := self { modes = modes.sealed, level = LevelInline }
  if modes.at Comma then fatal "`match induct` takes one call, with nothing else to match"
  else
    let withKeyword := modes.expectFixed KwWith "`with`"
    match inductArms (Parse.mark().left + 1) self modes None [] with
      | [] => modes.fail "`|` and an alternative named after a case"
      | arms => Induct keyword induct call withKeyword arms

def inductArms (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Option Nat) (found: List InductArm):
    {Parse Item} List InductArm :=
  let (lined, column) := armColumn column
  let ahead := modes.at Pipe && lined
  match fuel with
    | Succ more if ahead =>
      let bar := fixedFrom()
      let case := modes.lower "the name of a case of `f.induct`"
      let names := caseNames (Parse.mark().left + 1) modes []
      let arrow := modes.expectFixed FatArrow "`=>`"
      let body := full self modes
      inductArms more self modes column [{ bar, case, names, arrow, body }, ..found]
    | _ => found.reverse

def caseNames (fuel: Nat) (modes: Modes) (found: List Word): {Parse Item} List Word := match fuel, modes.peek with
  | Succ more, Some Lower => caseNames more modes [modes.lower "a name", ..found]
  | Succ more, Some Underscore => caseNames more modes [bump(), ..found]
  | _, _ => found.reverse

-- `calc`.

--| `calc e0` and its steps (`calc_expr`, `calc_body`): one a line, lined
--| up, right of the line `calc` is on and of the enclosing block.
def calcExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let indent := headIndent()
  let keyword := fixedFrom()
  let inner := { modes | inCalc = True }
  let first := calcOperand self inner.sealed
  match inner.peek with
    | Some kind if kind.isComparison =>
      fatal "`calc` starts with one expression; each relation goes on a line of its own"
    | _ =>
      let (steps, ascending, descending) := calcSteps (Parse.mark().left + 1) self inner indent None [] False False
      if steps.isEmpty then inner.fail "a step `_ = e` on the next line, indented past `calc`"
      else if ascending && descending then
        fatal "a `calc` chain goes one way: `<` and `<=` can't be mixed with `>` and `>=`"
      else Calc keyword first steps

--| A `calc`'s operand: above the relations (`calc_operand`).
def calcOperand (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let indent := headIndent()
  let range := rangeExpr self modes
  let piped := if atPipe modes then pipeChain self modes indent range else range
  if andOrAhead modes then logicChain self modes piped else piped

--| The steps, and whether any goes up (`<`, `<=`) or down (`>`, `>=`).
def calcSteps (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (column: Option Nat)
    (found: List CalcStep) (ascending descending: Bool):
    {Parse Item} (List CalcStep, Bool, Bool) :=
  let next := match left() with
    | [item, .._] =>
      let token := item.leaf.token
      if item.kind == Underscore
        && token.lineStart
        && token.column > indent
        && modes.limit.map (limit => token.column > limit) |> .getOrElse True then
        Some token.column
      else None
    | [] => None
  match fuel, next with
    | Succ more, Some at =>
      match column with
        | Some first if first != at => fatal "this step isn't lined up with the steps above it"
        | _ =>
          let underscore := fixedFrom()
          let (up, down) := match modes.peek with
            | Some Equals => (False, False)
            | Some Le => (True, False)
            | Some Lt => (True, False)
            | Some Ge => (False, True)
            | Some Gt => (False, True)
            | Some NotEq => fatal calcRelations
            | Some EqEq => fatal calcRelations
            | _ => modes.fail "`=`, `<=`, `<`, `>=` or `>` after `_`"
          let relation := bump()
          let operand := calcOperand self modes
          let proof :=
            if modes.at ColonEq then
              let colonEq := fixedFrom()
              Some (colonEq, full self modes)
            else None
          calcSteps more self modes indent
            (Some at)
            [{ underscore, relation, operand, proof }, ..found]
            (ascending || up)
            (descending || down)
    | _, _ => (found.reverse, ascending, descending)

def calcRelations: Text := "a `calc` step is `=`, `<=`, `<`, `>=` or `>`: other relations can't be chained"

-- `rewrite` and `cases`.

--| `rewrite p, <- q at h then t` (`rewrite_expr`, `rewrite_body`).
def rewriteExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let column := columnHere()
  let keyword := fixedFrom()
  let outer := { modes | rewriteRule = None, rewriteAt = False }
  let rules :=
    if wordAhead outer "repeatedly" && isSome LBracket (outer.peekAt 1) then
      let word := fixedFrom()
      Repeatedly word (ruleSet self outer)
    else RuleList (rewriteRules (Parse.mark().left + 1) self outer [])
  let target := rewriteTarget self outer
  rewriteThen self outer column keyword rules target

--| `<-`, written as `<` and `-` with nothing between.
def reverseAhead (modes: Modes): {Parse Item} Bool := match left() with
  | [_, minus, .._] => modes.at Lt && isSome Minus (modes.peekAt 1) && minus.glued
  | _ => False

def reverseOf (modes: Modes): {Parse Item} Option (Comments, Comments) :=
  if reverseAhead modes then
    let less := fixedFrom()
    Some (less, fixedFrom())
  else None

--| Rules separated by commas, each read up to its end (`then`, `in`, `at`).
def rewriteRules (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (found: List RewriteRule):
    {Parse Item} List RewriteRule :=
  let reverse := reverseOf modes
  let rule := appendExpr self { modes | rewriteRule = Some here(), rewriteAt = True }
  let done := [{ reverse, rule }, ..found]
  let comma := modes.at Comma
  match fuel with
    | Succ more if comma =>
      let _ := bump()
      rewriteRules more self modes done
    | _ => done.reverse

--| `[r1, <- r2]` (`repeated_rules`): at least one rule, and may end
--| with a comma.
def ruleSet (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} RuleSet :=
  let open := fixedFrom()
  if modes.at RBracket then fatal "`rewrite repeatedly` needs at least one rule between its brackets"
  else
    let inner := modes.inBrackets
    let (rules, trailingComma) := setRules (Parse.mark().left + 1) self inner []
    { open, rules, trailingComma, close = inner.expectFixed RBracket "`,` or `]`" }

def setRules (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (found: List RewriteRule):
    {Parse Item} (List RewriteRule, Bool) :=
  let reverse := reverseOf modes
  let rule := full self modes
  let done := [{ reverse, rule }, ..found]
  let comma := modes.at Comma
  match fuel with
    | Succ more if comma =>
      let _ := bump()
      if modes.at RBracket then (done.reverse, True) else setRules more self modes done
    | _ => (done.reverse, False)

--| `at h` after the rules, if there.
def rewriteTarget (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Option (Comments, Expr) :=
  if wordAhead modes "at" then
    let at := fixedFrom()
    match modes.peek with
      | None => fatal atWithoutTarget
      | Some KwThen => fatal atWithoutTarget
      | Some KwIn => fatal atWithoutTarget
      | _ => Some (at, appendExpr self { modes | rewriteRule = Some here(), rewriteAt = False })
  else None

def atWithoutTarget: Text := "`at` after a `rewrite` rule names the hypothesis to rewrite, but no hypothesis follows it"

def oldIn (construct: Text): Text := "write `then`, not `in`, after `${construct}`"

--| `then t` after the rules and target, if there: `then` may start a line
--| of its own at the `rewrite`'s column or right of it (`rewrite_then`).
def rewriteThen (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (keyword: Comments)
    (rules: Rules) (target: Option (Comments, Expr)):
    {Parse Item} Expr :=
  if modes.at KwIn || ownLineAt KwIn column then fatal (oldIn "rewrite")
  else if modes.at KwThen || ownLineAt KwThen column then
    let thenKeyword := fixedFrom()
    Rewrite keyword rules target (Some (thenKeyword, self { modes, level = LevelThenBody }))
  else Rewrite keyword rules target None

--| Whether a `wanted` next starts a line at `column` or right of it.
def ownLineAt (wanted: Tok) (column: Nat): {Parse Item} Bool := match left() with
  | [next, .._] => next.kind == wanted && next.leaf.token.lineStart && next.leaf.token.column >= column
  | [] => False

--| `cases`, or `cases then t` (`cases_expr`).
def casesExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let keyword := bump()
  if modes.at KwIn then fatal (oldIn "cases")
  else if modes.at KwThen then
    let thenKeyword := fixedFrom()
    Cases keyword.comments thenKeyword (self { modes, level = LevelThenBody })
  else Atom KwCases keyword

--| The body after `then` (`then_body`): when the `then` ended its line
--| and the body starts at the enclosing block's column, the lines there
--| are the body, a block of their own; otherwise an expression.
def thenBody (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := match left() with
  | [next, .._] if next.leaf.token.lineStart
      && modes.allow != Some next.index
      && !modes.endsConstruct next
      && modes.limit == Some next.leaf.token.column => block self modes next.leaf.token.column True
  | _ => expr self modes
