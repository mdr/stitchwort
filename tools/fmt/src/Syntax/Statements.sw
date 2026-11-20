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
def here(): {Parse Item} (Nat, Nat) := hereOn left()

def hereOn (items: List Item): {Parse Item} (Nat, Nat) := match items with
  | [item, .._] => (item.index, item.depth)
  | [] => (offset(), 0)

--| The next item's column, or 0 at the end.
def columnHere(): {Parse Item} Nat := columnOn left()

def columnOn (items: List Item): Nat := items.head.map (item => item.leaf.token.column) |> .getOrElse 0

-- Statements.

--| One line of a block (`statement`).
def statement (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Statement :=
  statementOn self modes modes.peek

def statementOn (self: Goal → {Parse Item} Expr) (modes: Modes): Option Tok → {Parse Item} Statement
  | Some kind => if startsOtherStatement kind then statementOther self modes kind else statementValue self modes
  | None => statementValue self modes

--| The tokens that start a line of a block other than an expression: a `let`, a local definition, an attribute, or
--| what a block refuses.
def startsOtherStatement: Tok → Bool
  | KwLet | KwDef | KwTheorem | At | KwExport | KwOpaque => True
  | _ => False

def statementValue (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Statement :=
  ExprStatement (exprInline self modes)

def statementOther (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: Tok): {Parse Item} Statement :=
  if kind == KwLet then
    let binding := letStatement self modes
    letStatementEnd self modes binding (modes.at Semi)
  else if kind == KwDef || kind == KwTheorem then localDef self modes []
  else if kind == At then
    let attributes := attributesOf modes
    let items := left()
    attributedLocal self modes attributes items
  else if kind == KwExport then fatal "local definitions can't be exported: only top-level ones are"
  else fatal "local definitions can't be `opaque`: only top-level ones can"

def letStatementEnd (self: Goal → {Parse Item} Expr) (modes: Modes) (binding: Let) (atSemi: Bool):
    {Parse Item} Statement :=
  if atSemi then ExprStatement (letBody self modes binding) else LetStatement binding

--| A `def` or `theorem` after attributes may start a line at the block's column.
def allowedAt (modes: Modes) (items: List Item): Modes := match items, modes.limit with
  | [next, .._], Some column =>
    if next.leaf.token.lineStart && next.leaf.token.column == column then { modes | allow = Some next.index } else modes
  | _, _ => modes

def attributedLocal (self: Goal → {Parse Item} Expr) (modes: Modes) (attributes: List Attributes) (items: List Item):
    {Parse Item} Statement :=
  let allowed := allowedAt modes items
  localAttributed self allowed attributes (allowed.at KwDef) (allowed.at KwTheorem)

def localAttributed (self: Goal → {Parse Item} Expr) (allowed: Modes)
    (attributes: List Attributes) (atDef atTheorem: Bool):
    {Parse Item} Statement :=
  if atDef || atTheorem then localDef self allowed attributes
  else fatal (misplaced "a statement that isn't a local definition")

--| `let p := e` or `let p: T := e` (`let_statement`). The value is read
--| with `letValue` at the `let`'s bracket depth, so a `;` there ends it.
def letStatement (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Let :=
  let (_, depth) := here()
  let keyword := fixedFrom()
  let pattern := letPattern modes
  let annotation := letAnnotation self modes (modes.at Colon)
  letEquals self modes depth keyword pattern annotation (modes.at Equals)

def letAnnotation (self: Goal → {Parse Item} Expr) (modes: Modes) (atColon: Bool):
    {Parse Item} Option (Comments, Expr) :=
  if atColon then
    let colon := fixedFrom()
    let annotation := self { modes = modes.sealed, level = LevelInline }
    Some (colon, annotation)
  else None

def letEquals (self: Goal → {Parse Item} Expr) (modes: Modes) (depth: Nat) (keyword: Comments) (pattern: Pattern)
    (annotation: Option (Comments, Expr)) (atEquals: Bool):
    {Parse Item} Let :=
  if atEquals then fatal defEquals
  else
    let colonEq := modes.expectFixed ColonEq "`:=`"
    let value := full self { modes | letValue = Some depth }
    { keyword, pattern, annotation, colonEq, value }

--| After `let`: a constructor takes its arguments without brackets, up
--| to the `:=` or `:` (`let_pattern`).
def letPattern (modes: Modes): {Parse Item} Pattern := letPatternOf modes (ctorAhead modes)

def letPatternOf (modes: Modes) (isCtor: Bool): {Parse Item} Pattern :=
  if isCtor then
    let name := bump()
    ctorArgs pattern modes name (kind => kind == Equals || kind == ColonEq || kind == Colon)
  else pattern { modes, level = PatternTupleComponent }

--| The `;` and body of an expression `let` (`let_body`).
def letBody (self: Goal → {Parse Item} Expr) (modes: Modes) (binding: Let): {Parse Item} Expr :=
  letBodyOf self modes binding (modes.at Semi)

def letBodyOf (self: Goal → {Parse Item} Expr) (modes: Modes) (binding: Let) (atSemi: Bool): {Parse Item} Expr :=
  if !atSemi then modes.fail "`;` after the value of `let`"
  else
    let semicolon := fixedFrom()
    let items := left()
    letEnd self modes binding semicolon (letAtEnd items)

def letAtEnd (items: List Item): Bool := match items with
  | [next, .._] => next.kind == RParen || next.kind == RBracket || next.kind == RBrace || next.kind == Comma
  | [] => True

def letEnd (self: Goal → {Parse Item} Expr) (modes: Modes) (binding: Let) (semicolon: Comments) (atEnd: Bool):
    {Parse Item} Expr :=
  if atEnd then fatal "`let` needs a body after `;`: `(let x := e; body)`"
  else LetIn binding semicolon (full self modes)

--| Whether a `;` next starts a sequence `a; b` (`sequence_ahead`): unless
--| a `let`'s value is being read and the `;` is at that `let`'s depth.
def sequenceAhead (modes: Modes): {Parse Item} Bool := sequenceOn modes left()

def sequenceOn (modes: Modes) (items: List Item): Bool := match modes.letValue, items with
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
  reifyComma self modes keyword reify computation (modes.at Comma)

def reifyComma (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword reify: Comments)
    (computation: Expr) (comma: Bool):
    {Parse Item} Expr :=
  if comma then fatal "`match reify` takes one computation, with nothing else to match"
  else
    let withKeyword := modes.expectFixed KwWith "`with`"
    Reify keyword reify computation withKeyword (handlerClauses self modes)

--| At least one clause; clauses starting lines line up.
def handlerClauses (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} List HandlerClause :=
  let here := Parse.mark()
  handlerClausesEnd modes (clausesFrom (here.left + 1) self modes None [])

def handlerClausesEnd (modes: Modes) (clauses: List HandlerClause): {Parse Item} List HandlerClause :=
  if clauses.isEmpty then modes.fail "`|` and a handler clause" else clauses

def clausesFrom (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (column: Option Nat) (found: List HandlerClause):
    {Parse Item} List HandlerClause :=
  clausesLined fuel self modes found (armColumn column)

def clausesLined (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (found: List HandlerClause) (columned: (Bool, Option Nat)):
    {Parse Item} List HandlerClause :=
  match columned with | (lined, column) => clausesAhead fuel self modes column found lined (modes.at Pipe)

def clausesAhead (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Option Nat)
    (found: List HandlerClause) (lined atPipe: Bool):
    {Parse Item} List HandlerClause :=
  match fuel with
    | Succ more =>
      if atPipe && lined then
        let bar := fixedFrom()
        let clause := handlerClause self modes bar
        clausesFrom more self modes column [clause, ..found]
      else found.reverse
    | Zero => found.reverse

--| `return x => e` or `op p, k => e`, after the `|` (`handler_clause`).
def handlerClause (self: Goal → {Parse Item} Expr) (modes: Modes) (bar: Comments): {Parse Item} HandlerClause :=
  handlerClauseOf self modes bar (modes.at KwReturn)

def handlerClauseOf (self: Goal → {Parse Item} Expr) (modes: Modes) (bar: Comments) (atReturn: Bool):
    {Parse Item} HandlerClause :=
  if atReturn then
    let keyword := fixedFrom()
    let name := handlerName modes "a name for the result" (modes.at Underscore)
    let arrow := modes.expectFixed FatArrow "`=>`"
    ReturnClause bar keyword name arrow (full self modes)
  else
    let operation := modes.lowerQualified "an operation, or `return`"
    let argument := patternOf modes
    operationClause self modes bar operation argument (modes.at FatArrow)

def handlerName (modes: Modes) (what: Text) (underscore: Bool): {Parse Item} Word :=
  if underscore then bump() else modes.lower what

def operationClause (self: Goal → {Parse Item} Expr) (modes: Modes) (bar: Comments) (operation: Word)
    (argument: Pattern) (atArrow: Bool):
    {Parse Item} HandlerClause :=
  if atArrow then fatal "name the continuation: `| ${operation.text} x, k => …`"
  else
    let comma := modes.expectFixed Comma "`,` and a name for the continuation"
    let continuation := handlerName modes "a name for the continuation" (modes.at Underscore)
    operationEnd self modes bar operation argument comma continuation (modes.at Comma)

def operationEnd (self: Goal → {Parse Item} Expr) (modes: Modes) (bar: Comments) (operation: Word) (argument: Pattern)
    (comma: Comments) (continuation: Word) (atComma: Bool):
    {Parse Item} HandlerClause :=
  if atComma then fatal "an operation takes one argument; bracket a tuple: `(a, b)`"
  else
    let arrow := modes.expectFixed FatArrow "`=>`"
    OperationClause bar operation argument comma continuation arrow (full self modes)

--| `match induct (f args) with | eqK x ih => …`, after `match` and
--| `induct`.
def inductExpr (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword induct: Comments): {Parse Item} Expr :=
  let call := self { modes = modes.sealed, level = LevelInline }
  inductComma self modes keyword induct call (modes.at Comma)

def inductComma (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword induct: Comments) (call: Expr) (comma: Bool):
    {Parse Item} Expr :=
  if comma then fatal "`match induct` takes one call, with nothing else to match"
  else
    let withKeyword := modes.expectFixed KwWith "`with`"
    let here := Parse.mark()
    inductEnd modes keyword induct call withKeyword (inductArms (here.left + 1) self modes None [])

def inductEnd (modes: Modes) (keyword induct: Comments) (call: Expr) (withKeyword: Comments) (arms: List InductArm):
    {Parse Item} Expr :=
  if arms.isEmpty then modes.fail "`|` and an alternative named after a case"
  else Induct keyword induct call withKeyword arms

def inductArms (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Option Nat) (found: List InductArm):
    {Parse Item} List InductArm :=
  inductLined fuel self modes found (armColumn column)

def inductLined (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes)
    (found: List InductArm) (columned: (Bool, Option Nat)):
    {Parse Item} List InductArm :=
  match columned with | (lined, column) => inductAhead fuel self modes column found lined (modes.at Pipe)

def inductAhead (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Option Nat)
    (found: List InductArm) (lined atPipe: Bool):
    {Parse Item} List InductArm :=
  match fuel with
    | Succ more =>
      if atPipe && lined then
        let bar := fixedFrom()
        let case := modes.lower "the name of a case of `f.induct`"
        let here := Parse.mark()
        let names := caseNames (here.left + 1) modes []
        let arrow := modes.expectFixed FatArrow "`=>`"
        let body := full self modes
        inductArms more self modes column [{ bar, case, names, arrow, body }, ..found]
      else found.reverse
    | Zero => found.reverse

def caseNames (fuel: Nat) (modes: Modes) (found: List Word): {Parse Item} List Word :=
  caseNamesOn fuel modes found modes.peek

def caseNamesOn (fuel: Nat) (modes: Modes) (found: List Word) (seen: Option Tok): {Parse Item} List Word :=
  match fuel, seen with
    | Succ more, Some Lower =>
      let name := modes.lower "a name"
      caseNames more modes [name, ..found]
    | Succ more, Some Underscore =>
      let name := bump()
      caseNames more modes [name, ..found]
    | _, _ => found.reverse

-- `calc`.

--| `calc e0` and its steps (`calc_expr`, `calc_body`): one a line, lined
--| up, right of the line `calc` is on and of the enclosing block.
def calcExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := calcIndented self modes headIndent()

def calcIndented (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat): {Parse Item} Expr :=
  let keyword := fixedFrom()
  let inner := { modes | inCalc = True }
  let first := calcOperand self inner.sealed
  calcAfter self inner indent keyword first inner.peek

def calcAfter (self: Goal → {Parse Item} Expr) (inner: Modes) (indent: Nat) (keyword: Comments) (first: Expr):
    Option Tok → {Parse Item} Expr
  | Some kind =>
    if kind.isComparison then fatal "`calc` starts with one expression; each relation goes on a line of its own"
    else calcBody self inner indent keyword first
  | None => calcBody self inner indent keyword first

def calcBody (self: Goal → {Parse Item} Expr) (inner: Modes) (indent: Nat) (keyword: Comments) (first: Expr):
    {Parse Item} Expr :=
  let (steps, ascending, descending) := calcSteps (Parse.mark().left + 1) self inner indent None [] False False
  calcEnd inner keyword first steps ascending descending

def calcEnd (inner: Modes) (keyword: Comments) (first: Expr) (steps: List CalcStep) (ascending descending: Bool):
    {Parse Item} Expr :=
  if steps.isEmpty then inner.fail "a step `_ = e` on the next line, indented past `calc`"
  else if ascending && descending then
    fatal "a `calc` chain goes one way: `<` and `<=` can't be mixed with `>` and `>=`"
  else Calc keyword first steps

--| A `calc`'s operand: above the relations (`calc_operand`).
def calcOperand (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let piped := pipedRange self modes
  logicAfter self modes piped

--| The steps, and whether any goes up (`<`, `<=`) or down (`>`, `>=`).
def calcSteps (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (column: Option Nat)
    (found: List CalcStep) (ascending descending: Bool):
    {Parse Item} (List CalcStep, Bool, Bool) :=
  calcStep fuel self modes indent column found ascending descending (calcNextOn modes indent left())

--| The column of the next line when it is a step: a `_` starting a line past the `calc` and the enclosing block.
def calcNextOn (modes: Modes) (indent: Nat): List Item → Option Nat
  | [item, .._] =>
    let token := item.leaf.token
    if item.kind == Underscore
      && token.lineStart
      && token.column > indent
      && modes.limit.map (limit => token.column > limit) |> .getOrElse True then
      Some token.column
    else None
  | [] => None

def calcStep (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (indent: Nat) (column: Option Nat)
    (found: List CalcStep) (ascending descending: Bool) (next: Option Nat):
    {Parse Item} (List CalcStep, Bool, Bool) :=
  match fuel, next with
    | Succ more, Some at =>
      match column with
        | Some first if first != at => fatal "this step isn't lined up with the steps above it"
        | _ => calcLine more self modes indent at found ascending descending
    | _, _ => (found.reverse, ascending, descending)

--| One step, `_ = e`, and the steps after it.
def calcLine (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (indent at: Nat)
    (found: List CalcStep) (ascending descending: Bool):
    {Parse Item} (List CalcStep, Bool, Bool) :=
  let underscore := fixedFrom()
  let (up, down) := stepSign modes modes.peek
  calcRelation more self modes indent at found (ascending || up) (descending || down) underscore

def calcRelation (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (indent at: Nat) (found: List CalcStep)
    (ascending descending: Bool) (underscore: Comments):
    {Parse Item} (List CalcStep, Bool, Bool) :=
  let relation := bump()
  let operand := calcOperand self modes
  calcRecord more self modes indent at found ascending descending underscore relation operand (modes.at ColonEq)

def calcRecord (more: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (indent at: Nat) (found: List CalcStep)
    (ascending descending: Bool) (underscore: Comments) (relation: Word) (operand: Expr) (colonEq: Bool):
    {Parse Item} (List CalcStep, Bool, Bool) :=
  let proof := calcProof self modes colonEq
  calcSteps more self modes indent (Some at) [{ underscore, relation, operand, proof }, ..found] ascending descending

--| Whether a relation goes up (`<`, `<=`) or down (`>`, `>=`).
def stepSign (modes: Modes): Option Tok → {Parse Item} (Bool, Bool)
  | Some Equals => (False, False)
  | Some Le | Some Lt => (True, False)
  | Some Ge | Some Gt => (False, True)
  | Some NotEq | Some EqEq => fatal calcRelations
  | _ => modes.fail "`=`, `<=`, `<`, `>=` or `>` after `_`"

def calcProof (self: Goal → {Parse Item} Expr) (modes: Modes) (colonEq: Bool): {Parse Item} Option (Comments, Expr) :=
  if colonEq then
    let colonEqKeyword := fixedFrom()
    let proof := full self modes
    Some (colonEqKeyword, proof)
  else None

def calcRelations: Text := "a `calc` step is `=`, `<=`, `<`, `>=` or `>`: other relations can't be chained"

-- `rewrite` and `cases`.

--| `rewrite p, <- q at h then t` (`rewrite_expr`, `rewrite_body`).
def rewriteExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let column := columnHere()
  let keyword := fixedFrom()
  rewriteAfter self { modes | rewriteRule = None, rewriteAt = False } column keyword

def rewriteAfter (self: Goal → {Parse Item} Expr) (outer: Modes) (column: Nat) (keyword: Comments): {Parse Item} Expr :=
  rewriteWith self outer column keyword (repeatedlyAhead outer)

def rewriteWith (self: Goal → {Parse Item} Expr) (outer: Modes) (column: Nat) (keyword: Comments) (repeatedly: Bool):
    {Parse Item} Expr :=
  let rules := rewriteRulesOf self outer repeatedly
  let target := rewriteTarget self outer
  rewriteThen self outer column keyword rules target

--| `repeatedly [`: the rules are a set of rules in brackets.
def repeatedlyAhead (outer: Modes): {Parse Item} Bool := repeatedlyOn outer (wordAhead outer "repeatedly")

def repeatedlyOn (outer: Modes) (word: Bool): {Parse Item} Bool :=
  if word then isSome LBracket (outer.peekAt 1) else False

def rewriteRulesOf (self: Goal → {Parse Item} Expr) (outer: Modes) (repeatedly: Bool): {Parse Item} Rules :=
  if repeatedly then
    let word := fixedFrom()
    Repeatedly word (ruleSet self outer)
  else RuleList (rewriteRules (Parse.mark().left + 1) self outer [])

--| `<-`, written as `<` and `-` with nothing between.
def reverseAhead (modes: Modes): {Parse Item} Bool := reverseOn modes (modes.at Lt) left()

def reverseOn (modes: Modes) (less: Bool): List Item → {Parse Item} Bool
  | [_, minus, .._] => if less then reverseMinus minus.glued (modes.peekAt 1) else False
  | _ => False

def reverseMinus (glued: Bool) (second: Option Tok): Bool := isSome Minus second && glued

def reverseOf (modes: Modes): {Parse Item} Option (Comments, Comments) := reverseIf (reverseAhead modes)

def reverseIf (reverse: Bool): {Parse Item} Option (Comments, Comments) :=
  if reverse then
    let less := fixedFrom()
    let second := fixedFrom()
    Some (less, second)
  else None

--| Rules separated by commas, each read up to its end (`then`, `in`, `at`).
def rewriteRules (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (found: List RewriteRule):
    {Parse Item} List RewriteRule :=
  rewriteMore fuel self modes (rewriteRule self modes found) (modes.at Comma)

def rewriteRule (self: Goal → {Parse Item} Expr) (modes: Modes) (found: List RewriteRule):
    {Parse Item} List RewriteRule :=
  let reverse := reverseOf modes
  let start := here()
  let rule := appendExpr self { modes | rewriteRule = Some start, rewriteAt = True }
  [{ reverse, rule }, ..found]

def rewriteMore (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (done: List RewriteRule) (comma: Bool):
    {Parse Item} List RewriteRule :=
  match fuel with
    | Succ more if comma =>
      let _ := bump()
      rewriteRules more self modes done
    | _ => done.reverse

--| `[r1, <- r2]` (`repeated_rules`): at least one rule, and may end
--| with a comma.
def ruleSet (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} RuleSet :=
  let open := fixedFrom()
  ruleSetAfter self modes open (modes.at RBracket)

def ruleSetAfter (self: Goal → {Parse Item} Expr) (modes: Modes) (open: Comments) (empty: Bool): {Parse Item} RuleSet :=
  if empty then fatal "`rewrite repeatedly` needs at least one rule between its brackets"
  else
    let inner := modes.inBrackets
    let (rules, trailingComma) := setRules (Parse.mark().left + 1) self inner []
    let close := inner.expectFixed RBracket "`,` or `]`"
    { open, rules, trailingComma, close }

def setRules (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (found: List RewriteRule):
    {Parse Item} (List RewriteRule, Bool) :=
  setMore fuel self modes (setRule self modes found) (modes.at Comma)

def setRule (self: Goal → {Parse Item} Expr) (modes: Modes) (found: List RewriteRule): {Parse Item} List RewriteRule :=
  let reverse := reverseOf modes
  let rule := full self modes
  [{ reverse, rule }, ..found]

def setMore (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (done: List RewriteRule) (comma: Bool):
    {Parse Item} (List RewriteRule, Bool) :=
  match fuel with
    | Succ more if comma =>
      let _ := bump()
      setRulesAfter more self modes done (modes.at RBracket)
    | _ => (done.reverse, False)

def setRulesAfter (fuel: Nat) (self: Goal → {Parse Item} Expr) (modes: Modes) (done: List RewriteRule) (closed: Bool):
    {Parse Item} (List RewriteRule, Bool) :=
  if closed then (done.reverse, True) else setRules fuel self modes done

--| `at h` after the rules, if there.
def rewriteTarget (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Option (Comments, Expr) :=
  rewriteTargetIf self modes (wordAhead modes "at")

def rewriteTargetIf (self: Goal → {Parse Item} Expr) (modes: Modes) (atAhead: Bool):
    {Parse Item} Option (Comments, Expr) :=
  if atAhead then
    let at := fixedFrom()
    targetAfter self modes at modes.peek
  else None

def targetAfter (self: Goal → {Parse Item} Expr) (modes: Modes) (at: Comments):
    Option Tok → {Parse Item} Option (Comments, Expr)
  | Some kind => if kind == KwThen || kind == KwIn then fatal atWithoutTarget else targetOf self modes at
  | None => fatal atWithoutTarget

def targetOf (self: Goal → {Parse Item} Expr) (modes: Modes) (at: Comments): {Parse Item} Option (Comments, Expr) :=
  let start := here()
  let target := appendExpr self { modes | rewriteRule = Some start, rewriteAt = False }
  Some (at, target)

def atWithoutTarget: Text := "`at` after a `rewrite` rule names the hypothesis to rewrite, but no hypothesis follows it"

def oldIn (construct: Text): Text := "write `then`, not `in`, after `${construct}`"

--| `then t` after the rules and target, if there: `then` may start a line
--| of its own at the `rewrite`'s column or right of it (`rewrite_then`).
def rewriteThen (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (keyword: Comments)
    (rules: Rules) (target: Option (Comments, Expr)):
    {Parse Item} Expr :=
  rewriteOldIn self modes column keyword rules target (startsAt modes KwIn column)

def rewriteOldIn (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (keyword: Comments) (rules: Rules)
    (target: Option (Comments, Expr)) (old: Bool):
    {Parse Item} Expr :=
  if old then fatal (oldIn "rewrite")
  else rewriteBody self modes column keyword rules target (startsAt modes KwThen column)

def rewriteBody (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (keyword: Comments) (rules: Rules)
    (target: Option (Comments, Expr)) (hasThen: Bool):
    {Parse Item} Expr :=
  if hasThen then
    let thenKeyword := fixedFrom()
    let body := self { modes, level = LevelThenBody }
    Rewrite keyword rules target (Some (thenKeyword, body))
  else Rewrite keyword rules target None

--| Whether the next item is `wanted`, or one starts a line of its own at `column` or right of it.
def startsAt (modes: Modes) (wanted: Tok) (column: Nat): {Parse Item} Bool := startsOn (modes.at wanted) wanted column

def startsOn (here: Bool) (wanted: Tok) (column: Nat): {Parse Item} Bool :=
  if here then True else ownLineAt wanted column

--| Whether a `wanted` next starts a line at `column` or right of it.
def ownLineAt (wanted: Tok) (column: Nat): {Parse Item} Bool := ownLineOn wanted column left()

def ownLineOn (wanted: Tok) (column: Nat): List Item → Bool
  | [next, .._] => next.kind == wanted && next.leaf.token.lineStart && next.leaf.token.column >= column
  | [] => False

--| `cases`, or `cases then t` (`cases_expr`).
def casesExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let keyword := bump()
  casesIn self modes keyword (modes.at KwIn)

def casesIn (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word) (atIn: Bool): {Parse Item} Expr :=
  if atIn then fatal (oldIn "cases") else casesThen self modes keyword (modes.at KwThen)

def casesThen (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Word) (atThen: Bool): {Parse Item} Expr :=
  if atThen then
    let thenKeyword := fixedFrom()
    Cases keyword.comments thenKeyword (self { modes, level = LevelThenBody })
  else Atom KwCases keyword

--| `byWalking [items]` or `byWalking [items] then t` (`walk_expr`), at the word: the items are a list's (`[]` too,
--| with no `..` spread), and the body, as for `rewrite`, runs to the end of the expression. A `then` may start a line
--| of its own at the word's column or right of it.
def walkExpr (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let column := columnHere()
  let keyword := fixedFrom()
  let items := listExpr self modes
  walkFacts self modes column keyword items

def walkFacts (self: Goal → {Parse Item} Expr) (modes: Modes) (column: Nat) (keyword: Comments) (items: Expr):
    {Parse Item} Expr :=
  if hasSpread items then fatal "a list of facts can't have a `..` spread"
  else walkBody self modes keyword items (startsAt modes KwThen column)

def walkBody (self: Goal → {Parse Item} Expr) (modes: Modes) (keyword: Comments) (items: Expr) (hasThen: Bool):
    {Parse Item} Expr :=
  if hasThen then
    let thenKeyword := fixedFrom()
    let body := self { modes, level = LevelThenBody }
    Walk keyword items (Some (thenKeyword, body))
  else Walk keyword items None

--| The body after `then` (`then_body`): when the `then` ended its line
--| and the body starts at the enclosing block's column, the lines there
--| are the body, a block of their own; otherwise an expression.
def thenBody (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr := thenBodyOn self modes left()

def thenBodyOn (self: Goal → {Parse Item} Expr) (modes: Modes): List Item → {Parse Item} Expr
  | [next, .._] =>
    if next.leaf.token.lineStart
      && modes.allow != Some next.index
      && !modes.endsConstruct next
      && modes.limit == Some next.leaf.token.column then
      block self modes next.leaf.token.column True
    else expr self modes
  | _ => expr self modes
