--| The passes keep the meaning, finish in one run, and keep what came
--| before them: the parser's guarantees (`Parsed`) and each earlier
--| pass's work (toy-plus-plus.md §3.2).

namespace Toy.Fmt.Proofs
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, Eq, List, NonEmptyList, Option, Text)

-- What the printer needs of a tree beyond the parser's guarantees: no
-- trailing comma, since it writes none.

def NoTrailingCommas: Expr → Prop
  | Bracketed _ inner _ => NoTrailingCommas inner
  | ListLiteral _ items trailingComma _ => trailingComma = False ∧ NoTrailingCommasItems items
  | Call callee _ arguments trailingComma _ =>
    trailingComma = False ∧ NoTrailingCommas callee ∧ NoTrailingCommasItems arguments
  | Field target _ _ _ => NoTrailingCommas target
  | Negate _ operand => NoTrailingCommas operand
  | Binary _ _ left right => NoTrailingCommas left ∧ NoTrailingCommas right
  | If _ condition _ whenTrue _ whenFalse =>
    NoTrailingCommas condition ∧ NoTrailingCommasBody whenTrue ∧ NoTrailingCommasBody whenFalse
  | _ => True

def NoTrailingCommasItems: List Expr → Prop
  | [] => True
  | [value, ..rest] => NoTrailingCommas value ∧ NoTrailingCommasItems rest

def NoTrailingCommasBody: Body → Prop
  | { statements } => NoTrailingCommasLines statements

def NoTrailingCommasLines: List (Spaced Statement) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => NoTrailingCommasStatement line ∧ NoTrailingCommasLines rest

def NoTrailingCommasStatement: Statement → Prop
  | Let _ _ _ _ inner => NoTrailingCommasBody inner
  | Bare value => NoTrailingCommas value
  | StatementNote _ => True

def NoTrailingCommasDeclaration: Declaration → Prop
  | Function _ _ _ _ _ _ trailingComma _ _ found => trailingComma = False ∧ NoTrailingCommasBody found
  | Value _ _ _ _ found => NoTrailingCommasBody found
  | DeclarationNote _ => True

def NoTrailingCommasDeclarations: List (Spaced Declaration) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => NoTrailingCommasDeclaration line ∧ NoTrailingCommasDeclarations rest

def NoTrailingCommasFile: SourceFile → Prop
  | { declarations } => NoTrailingCommasDeclarations declarations

-- P2 leaves no trailing comma, and leaves alone a tree with none.

theorem exprCommasNone ∀ (expr: Expr): NoTrailingCommas expr.withoutTrailingCommas := match expr with
  | Var _ _ => byComputing
  | NumberLiteral _ _ => byComputing
  | StringLiteral _ _ => byComputing
  | Bracketed _ inner _ => exprCommasNone inner
  | ListLiteral _ items _ _ => (byComputing, itemsCommasNone items)
  | Call callee _ arguments _ _ => (byComputing, exprCommasNone callee, itemsCommasNone arguments)
  | Field target _ _ _ => exprCommasNone target
  | Negate _ operand => exprCommasNone operand
  | Binary _ _ left right => (exprCommasNone left, exprCommasNone right)
  | If _ condition _ whenTrue _ whenFalse =>
    (exprCommasNone condition, bodyCommasNone whenTrue, bodyCommasNone whenFalse)

theorem itemsCommasNone ∀ (items: List Expr): NoTrailingCommasItems (itemsWithoutTrailingCommas items) :=
  match items with
    | [] => byComputing
    | [value, ..rest] => (exprCommasNone value, itemsCommasNone rest)

theorem bodyCommasNone ∀ (body: Body): NoTrailingCommasBody body.withoutTrailingCommas := match body with
  | { statements } => linesCommasNone statements

theorem linesCommasNone ∀ (lines: List (Spaced Statement)): NoTrailingCommasLines (linesWithoutTrailingCommas lines) :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => (statementCommasNone line, linesCommasNone rest)

theorem statementCommasNone ∀ (line: Statement): NoTrailingCommasStatement line.withoutTrailingCommas := match line with
  | Let _ _ _ _ body => bodyCommasNone body
  | Bare value => exprCommasNone value
  | StatementNote _ => byComputing

theorem declarationCommasNone ∀ (line: Declaration): NoTrailingCommasDeclaration line.withoutTrailingCommas :=
  match line with
    | Function _ _ _ _ _ _ _ _ _ body => (byComputing, bodyCommasNone body)
    | Value _ _ _ _ body => bodyCommasNone body
    | DeclarationNote _ => byComputing

theorem declarationsCommasNone ∀ (lines: List (Spaced Declaration)):
    NoTrailingCommasDeclarations (declarationsWithoutTrailingCommas lines) :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => (declarationCommasNone line, declarationsCommasNone rest)

--| P2's result has no trailing comma.
theorem commasNone ∀ (file: SourceFile): NoTrailingCommasFile file.withoutTrailingCommas :=
  declarationsCommasNone file.declarations

theorem exprCommasFixed ∀ (expr: Expr) (none: NoTrailingCommas expr): expr.withoutTrailingCommas = expr :=
  match expr, none with
    | Var _ _, _ => byComputing
    | NumberLiteral _ _, _ => byComputing
    | StringLiteral _ _, _ => byComputing
    | Bracketed _ inner _, none => rewrite exprCommasFixed inner none
    | ListLiteral _ items _ _, (unwritten, itemsNone) => rewrite itemsCommasFixed items itemsNone, unwritten
    | Call callee _ arguments _ _, (unwritten, calleeNone, argumentsNone) =>
      rewrite exprCommasFixed callee calleeNone, itemsCommasFixed arguments argumentsNone, unwritten
    | Field target _ _ _, none => rewrite exprCommasFixed target none
    | Negate _ operand, none => rewrite exprCommasFixed operand none
    | Binary _ _ left right, (leftNone, rightNone) =>
      rewrite exprCommasFixed left leftNone, exprCommasFixed right rightNone
    | If _ condition _ whenTrue _ whenFalse, (conditionNone, trueNone, falseNone) =>
      rewrite exprCommasFixed condition conditionNone,
          bodyCommasFixed whenTrue trueNone,
          bodyCommasFixed whenFalse falseNone

theorem itemsCommasFixed ∀ (items: List Expr)
    (none: NoTrailingCommasItems items):
    itemsWithoutTrailingCommas items = items :=
  match items, none with
    | [], _ => byComputing
    | [value, ..rest], (valueNone, restNone) => rewrite exprCommasFixed value valueNone, itemsCommasFixed rest restNone

theorem bodyCommasFixed ∀ (body: Body) (none: NoTrailingCommasBody body): body.withoutTrailingCommas = body :=
  match body, none with | { statements }, none => rewrite linesCommasFixed statements none

theorem linesCommasFixed ∀ (lines: List (Spaced Statement))
    (none: NoTrailingCommasLines lines):
    linesWithoutTrailingCommas lines = lines :=
  match lines, none with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineNone, restNone) =>
      rewrite statementCommasFixed line lineNone, linesCommasFixed rest restNone

theorem statementCommasFixed ∀ (line: Statement)
    (none: NoTrailingCommasStatement line):
    line.withoutTrailingCommas = line :=
  match line, none with
    | Let _ _ _ _ body, none => rewrite bodyCommasFixed body none
    | Bare value, none => rewrite exprCommasFixed value none
    | StatementNote _, _ => byComputing

theorem declarationCommasFixed ∀ (line: Declaration)
    (none: NoTrailingCommasDeclaration line):
    line.withoutTrailingCommas = line :=
  match line, none with
    | Function _ _ _ _ _ _ _ _ _ body, (unwritten, bodyNone) => rewrite bodyCommasFixed body bodyNone, unwritten
    | Value _ _ _ _ body, none => rewrite bodyCommasFixed body none
    | DeclarationNote _, _ => byComputing

theorem declarationsCommasFixed ∀ (lines: List (Spaced Declaration))
    (none: NoTrailingCommasDeclarations lines):
    declarationsWithoutTrailingCommas lines = lines :=
  match lines, none with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineNone, restNone) =>
      rewrite declarationCommasFixed line lineNone, declarationsCommasFixed rest restNone

--| A file with no trailing comma is P2-tidy.
theorem commasFixed ∀ (file: SourceFile) (none: NoTrailingCommasFile file): file.withoutTrailingCommas = file :=
  match file, none with | { declarations }, none => rewrite declarationsCommasFixed declarations none

--| A P2-tidy file has no trailing comma.
theorem commasTidyNone ∀ (file: SourceFile) (tidy: file.withoutTrailingCommas = file): NoTrailingCommasFile file :=
  let none := commasNone file
  rewrite tidy at none then none

--| P2 finishes in one run.
theorem commasIdempotent ∀ (file: SourceFile):
    file.withoutTrailingCommas.withoutTrailingCommas = file.withoutTrailingCommas :=
  commasFixed file.withoutTrailingCommas (commasNone file)

-- P2 keeps the parser's guarantees: what they read of a tree, a trailing
-- comma doesn't change.

theorem exprCommasPostfix ∀ (expr: Expr): expr.withoutTrailingCommas.isPostfix = expr.isPostfix := match expr with
  | Var _ _ => byComputing
  | NumberLiteral _ _ => byComputing
  | StringLiteral _ _ => byComputing
  | Bracketed _ _ _ => byComputing
  | ListLiteral _ _ _ _ => byComputing
  | Call _ _ _ _ _ => byComputing
  | Field _ _ _ _ => byComputing
  | Negate _ _ => byComputing
  | Binary _ _ _ _ => byComputing
  | If _ _ _ _ _ _ => byComputing

theorem exprCommasOperand ∀ (expr: Expr): expr.withoutTrailingCommas.isOperand = expr.isOperand := match expr with
  | Var _ _ => byComputing
  | NumberLiteral _ _ => byComputing
  | StringLiteral _ _ => byComputing
  | Bracketed _ _ _ => byComputing
  | ListLiteral _ _ _ _ => byComputing
  | Call _ _ _ _ _ => byComputing
  | Field _ _ _ _ => byComputing
  | Negate _ _ => byComputing
  | Binary _ _ _ _ => byComputing
  | If _ _ _ _ _ _ => byComputing

theorem exprCommasChain ∀ (expr: Expr): expr.withoutTrailingCommas.isChain = expr.isChain := match expr with
  | Var _ _ => byComputing
  | NumberLiteral _ _ => byComputing
  | StringLiteral _ _ => byComputing
  | Bracketed _ _ _ => byComputing
  | ListLiteral _ _ _ _ => byComputing
  | Call _ _ _ _ _ => byComputing
  | Field _ _ _ _ => byComputing
  | Negate _ _ => byComputing
  | Binary _ _ _ _ => byComputing
  | If _ _ _ _ _ _ => byComputing

theorem exprCommasLevel ∀ (expr: Expr): expr.withoutTrailingCommas.chainLevel = expr.chainLevel := match expr with
  | Var _ _ => byComputing
  | NumberLiteral _ _ => byComputing
  | StringLiteral _ _ => byComputing
  | Bracketed _ _ _ => byComputing
  | ListLiteral _ _ _ _ => byComputing
  | Call _ _ _ _ _ => byComputing
  | Field _ _ _ _ => byComputing
  | Negate _ _ => byComputing
  | Binary _ _ _ _ => byComputing
  | If _ _ _ _ _ _ => byComputing

theorem exprCommasFirstAbove ∀ (expr: Expr): expr.withoutTrailingCommas.firstAbove = expr.firstAbove := match expr with
  | Var _ _ => byComputing
  | NumberLiteral _ _ => byComputing
  | StringLiteral _ _ => byComputing
  | Bracketed _ _ _ => byComputing
  | ListLiteral _ _ _ _ => byComputing
  | Call callee _ _ _ _ => exprCommasFirstAbove callee
  | Field target _ _ _ => exprCommasFirstAbove target
  | Negate _ _ => byComputing
  | Binary _ _ left _ => exprCommasFirstAbove left
  | If _ _ _ _ _ _ => byComputing

theorem exprCommasEnds ∀ (expr: Expr): expr.withoutTrailingCommas.endsWithComment = expr.endsWithComment :=
  match expr with
    | Var _ _ => byComputing
    | NumberLiteral _ _ => byComputing
    | StringLiteral _ _ => byComputing
    | Bracketed _ _ _ => byComputing
    | ListLiteral _ _ _ _ => byComputing
    | Call _ _ _ _ _ => byComputing
    | Field _ _ _ _ => byComputing
    | Negate _ operand => exprCommasEnds operand
    | Binary _ _ _ right => exprCommasEnds right
    | If _ _ _ _ _ whenFalse => bodyCommasEnds whenFalse

theorem bodyCommasEnds ∀ (body: Body): body.withoutTrailingCommas.endsWithComment = body.endsWithComment :=
  match body with | { statements } => linesCommasEnds statements

theorem linesCommasEnds ∀ (lines: List (Spaced Statement)):
    statementsEndWithComment (linesWithoutTrailingCommas lines) = statementsEndWithComment lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }] => statementCommasEnds line
    | [first, second, ..rest] => linesCommasEnds [second, ..rest]

theorem statementCommasEnds ∀ (line: Statement): line.withoutTrailingCommas.endsWithComment = line.endsWithComment :=
  match line with
    | Let _ _ _ _ body => bodyCommasEnds body
    | Bare value => exprCommasEnds value
    | StatementNote _ => byComputing

theorem itemsCommasEnd ∀ (open: Comments) (items: List Expr):
    itemsEndWithComment open (itemsWithoutTrailingCommas items) = itemsEndWithComment open items :=
  match items with
    | [] => byComputing
    | [last] => exprCommasEnds last
    | [first, second, ..rest] => itemsCommasEnd open [second, ..rest]

theorem statementCommasCoded ∀ (line: Statement) (coded: Coded line): Coded line.withoutTrailingCommas :=
  match line, coded with
    | Let _ _ _ _ _, _ => byComputing
    | Bare _, _ => byComputing
    | StatementNote _, coded => coded

theorem linesCommasClosed ∀ (lines: List (Spaced Statement))
    (closed: ClosedLines lines):
    ClosedLines (linesWithoutTrailingCommas lines) :=
  match lines, closed with
    | [], closed => closed
    | [{ blankBefore, line }], coded => statementCommasCoded line coded
    | [first, second, ..rest], closed => linesCommasClosed [second, ..rest] closed

theorem exprCommasShaped ∀ (expr: Expr) (shaped: Shaped expr): Shaped expr.withoutTrailingCommas :=
  match expr, shaped with
    | Var _ _, _ => byComputing
    | NumberLiteral _ _, _ => byComputing
    | StringLiteral _ _, _ => byComputing
    | Bracketed _ inner _, (innerShaped, settled) =>
      (exprCommasShaped inner innerShaped, (rewrite exprCommasEnds inner then settled))
    | ListLiteral open items _ _, (itemsShaped, settled) =>
      (itemsCommasShaped items itemsShaped, (rewrite itemsCommasEnd open items then settled))
    | Call callee open arguments _ _, (postfix, calleeShaped, argumentsShaped, settled) => (
      (rewrite exprCommasPostfix callee then postfix),
      exprCommasShaped callee calleeShaped,
      itemsCommasShaped arguments argumentsShaped,
      (rewrite itemsCommasEnd open arguments then settled)
    )
    | Field target _ _ _, (postfix, targetShaped) =>
      ((rewrite exprCommasPostfix target then postfix), exprCommasShaped target targetShaped)
    | Negate _ operand, (isOperand, operandShaped) =>
      ((rewrite exprCommasOperand operand then isOperand), exprCommasShaped operand operandShaped)
    | Binary _ _ left right, (leftLevel, rightLevel, leftChain, rightChain, leftShaped, rightShaped) => (
      (rewrite exprCommasLevel left then leftLevel),
      (rewrite exprCommasLevel right then rightLevel),
      (rewrite exprCommasChain left then leftChain),
      (rewrite exprCommasChain right then rightChain),
      exprCommasShaped left leftShaped,
      exprCommasShaped right rightShaped
    )
    | If _ condition _ whenTrue _ whenFalse, (conditionShaped, trueShaped, falseShaped) => (
      exprCommasShaped condition conditionShaped,
      bodyCommasShaped whenTrue trueShaped,
      bodyCommasShaped whenFalse falseShaped
    )

theorem itemsCommasShaped ∀ (items: List Expr)
    (shaped: ShapedItems items):
    ShapedItems (itemsWithoutTrailingCommas items) :=
  match items, shaped with
    | [], _ => byComputing
    | [value, ..rest], (valueShaped, restShaped) =>
      (exprCommasShaped value valueShaped, itemsCommasShaped rest restShaped)

theorem bodyCommasShaped ∀ (body: Body) (shaped: ShapedBody body): ShapedBody body.withoutTrailingCommas :=
  match body, shaped with
    | { statements }, (linesShaped, closed) =>
      (linesCommasShaped statements linesShaped, linesCommasClosed statements closed)

theorem linesCommasShaped ∀ (lines: List (Spaced Statement))
    (shaped: ShapedLines lines):
    ShapedLines (linesWithoutTrailingCommas lines) :=
  match lines, shaped with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineShaped, restShaped) =>
      (statementCommasShaped line lineShaped, linesCommasShaped rest restShaped)

theorem statementCommasShaped ∀ (line: Statement)
    (shaped: ShapedStatement line):
    ShapedStatement line.withoutTrailingCommas :=
  match line, shaped with
    | Let _ _ _ _ body, shaped => bodyCommasShaped body shaped
    | Bare value, shaped => exprCommasShaped value shaped
    | StatementNote _, _ => byComputing

theorem declarationCommasShaped ∀ (line: Declaration)
    (shaped: ShapedDeclaration line):
    ShapedDeclaration line.withoutTrailingCommas :=
  match line, shaped with
    | Function _ _ _ _ _ _ _ _ _ body, (parameters, bodyShaped) => (parameters, bodyCommasShaped body bodyShaped)
    | Value _ _ _ _ body, shaped => bodyCommasShaped body shaped
    | DeclarationNote _, _ => byComputing

theorem declarationsCommasShaped ∀ (lines: List (Spaced Declaration))
    (shaped: ShapedDeclarations lines):
    ShapedDeclarations (declarationsWithoutTrailingCommas lines) :=
  match lines, shaped with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineShaped, restShaped) =>
      (declarationCommasShaped line lineShaped, declarationsCommasShaped rest restShaped)

theorem exprCommasLexical ∀ (expr: Expr) (lexical: Lexical expr): Lexical expr.withoutTrailingCommas :=
  match expr, lexical with
    | Var _ _, lexical => lexical
    | NumberLiteral _ _, lexical => lexical
    | StringLiteral _ _, lexical => lexical
    | Bracketed _ inner _, (open, innerLexical, close) => (open, exprCommasLexical inner innerLexical, close)
    | ListLiteral _ items _ _, (open, itemsLexical, close) => (open, itemsCommasLexical items itemsLexical, close)
    | Call callee _ arguments _ _, (calleeLexical, open, argumentsLexical, close) =>
      (exprCommasLexical callee calleeLexical, open, itemsCommasLexical arguments argumentsLexical, close)
    | Field target _ _ _, (targetLexical, others) => (exprCommasLexical target targetLexical, others)
    | Negate _ operand, (minus, operandLexical) => (minus, exprCommasLexical operand operandLexical)
    | Binary _ _ left right, (sign, leftLexical, rightLexical) =>
      (sign, exprCommasLexical left leftLexical, exprCommasLexical right rightLexical)
    | If _ condition _ whenTrue _ whenFalse, (ifFine, conditionLexical, thenFine, trueLexical, elseFine,
        falseLexical) => (
      ifFine,
      exprCommasLexical condition conditionLexical,
      thenFine,
      bodyCommasLexical whenTrue trueLexical,
      elseFine,
      bodyCommasLexical whenFalse falseLexical
    )

theorem itemsCommasLexical ∀ (items: List Expr)
    (lexical: LexicalItems items):
    LexicalItems (itemsWithoutTrailingCommas items) :=
  match items, lexical with
    | [], _ => byComputing
    | [value, ..rest], (valueLexical, restLexical) =>
      (exprCommasLexical value valueLexical, itemsCommasLexical rest restLexical)

theorem bodyCommasLexical ∀ (body: Body) (lexical: LexicalBody body): LexicalBody body.withoutTrailingCommas :=
  match body, lexical with
    | { statements }, (linesLexical, closed) =>
      (linesCommasLexical statements linesLexical, linesCommasClosed statements closed)

theorem linesCommasLexical ∀ (lines: List (Spaced Statement))
    (lexical: LexicalLines lines):
    LexicalLines (linesWithoutTrailingCommas lines) :=
  match lines, lexical with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineLexical, restLexical) =>
      (statementCommasLexical line lineLexical, linesCommasLexical rest restLexical)

theorem statementCommasLexical ∀ (line: Statement)
    (lexical: LexicalStatement line):
    LexicalStatement line.withoutTrailingCommas :=
  match line, lexical with
    | Let _ _ _ _ body, (letFine, isName, nameFine, equalsFine, bodyLexical) =>
      (letFine, isName, nameFine, equalsFine, bodyCommasLexical body bodyLexical)
    | Bare value, lexical => exprCommasLexical value lexical
    | StatementNote _, lexical => lexical

theorem declarationCommasLexical ∀ (line: Declaration)
    (lexical: LexicalDeclaration line):
    LexicalDeclaration line.withoutTrailingCommas :=
  match line, lexical with
    | Function _ _ _ _ _ _ _ _ _ body, (fnFine, isName, nameFine, takesFine, openFine, parameters, closeFine,
        equalsFine, bodyLexical) => (
      fnFine,
      isName,
      nameFine,
      takesFine,
      openFine,
      parameters,
      closeFine,
      equalsFine,
      bodyCommasLexical body bodyLexical
    )
    | Value _ _ _ _ body, (letFine, isName, nameFine, equalsFine, bodyLexical) =>
      (letFine, isName, nameFine, equalsFine, bodyCommasLexical body bodyLexical)
    | DeclarationNote _, lexical => lexical

theorem declarationsCommasLexical ∀ (lines: List (Spaced Declaration))
    (lexical: LexicalDeclarations lines):
    LexicalDeclarations (declarationsWithoutTrailingCommas lines) :=
  match lines, lexical with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineLexical, restLexical) =>
      (declarationCommasLexical line lineLexical, declarationsCommasLexical rest restLexical)

theorem linesCommasUnspaced ∀ (lines: List (Spaced Statement))
    (unspaced: Unspaced lines):
    Unspaced (linesWithoutTrailingCommas lines) :=
  match lines, unspaced with
    | [], _ => byComputing
    | [{ blankBefore = False, line }, ..rest], _ => byComputing
    | [{ blankBefore = True, line }, ..rest], unspaced => cases

theorem declarationsCommasUnspaced ∀ (lines: List (Spaced Declaration))
    (unspaced: Unspaced lines):
    Unspaced (declarationsWithoutTrailingCommas lines) :=
  match lines, unspaced with
    | [], _ => byComputing
    | [{ blankBefore = False, line }, ..rest], _ => byComputing
    | [{ blankBefore = True, line }, ..rest], unspaced => cases

theorem linesCommasOne ∀ (lines: List (Spaced Statement))
    (one: OneExpression lines):
    OneExpression (linesWithoutTrailingCommas lines) :=
  match lines, one with | [{ blankBefore, line = Bare _ }], _ => byComputing

theorem exprCommasHeaded ∀ (bracketed: Bool) (expr: Expr)
    (headed: HeadedExpr bracketed expr):
    HeadedExpr bracketed expr.withoutTrailingCommas :=
  match expr, headed with
    | Var _ _, _ => byComputing
    | NumberLiteral _ _, _ => byComputing
    | StringLiteral _ _, _ => byComputing
    | Bracketed _ inner _, headed => exprCommasHeaded True inner headed
    | ListLiteral _ items _ _, headed => itemsCommasHeaded items headed
    | Call callee _ arguments _ _, (calleeHeaded, argumentsHeaded) =>
      (exprCommasHeaded bracketed callee calleeHeaded, itemsCommasHeaded arguments argumentsHeaded)
    | Field target _ _ _, headed => exprCommasHeaded bracketed target headed
    | Negate _ operand, headed => exprCommasHeaded bracketed operand headed
    | Binary _ _ left right, (leftHeaded, rightHeaded) =>
      (exprCommasHeaded bracketed left leftHeaded, exprCommasHeaded bracketed right rightHeaded)
    | If _ condition _ whenTrue _ whenFalse, (conditionHeaded, trueHeaded, falseHeaded) => (
      exprCommasHeaded bracketed condition conditionHeaded,
      bodyCommasHeaded bracketed whenTrue trueHeaded,
      bodyCommasHeaded bracketed whenFalse falseHeaded
    )

theorem itemsCommasHeaded ∀ (items: List Expr)
    (headed: HeadedItems items):
    HeadedItems (itemsWithoutTrailingCommas items) :=
  match items, headed with
    | [], _ => byComputing
    | [value, ..rest], (valueHeaded, restHeaded) =>
      (exprCommasHeaded True value valueHeaded, itemsCommasHeaded rest restHeaded)

theorem bodyCommasHeaded ∀ (bracketed: Bool) (body: Body)
    (headed: HeadedBody bracketed body):
    HeadedBody bracketed body.withoutTrailingCommas :=
  match body, headed with
    | { statements }, (linesHeaded, unspaced, one) => (
      linesCommasHeaded bracketed statements linesHeaded,
      linesCommasUnspaced statements unspaced,
      (inside => linesCommasOne statements (one inside))
    )

theorem linesCommasHeaded ∀ (bracketed: Bool) (lines: List (Spaced Statement))
    (headed: HeadedLines bracketed lines):
    HeadedLines bracketed (linesWithoutTrailingCommas lines) :=
  match lines, headed with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineHeaded, restHeaded) =>
      (statementCommasHeaded bracketed line lineHeaded, linesCommasHeaded bracketed rest restHeaded)

theorem statementCommasHeaded ∀ (bracketed: Bool) (line: Statement)
    (headed: HeadedStatement bracketed line):
    HeadedStatement bracketed line.withoutTrailingCommas :=
  match line, headed with
    | Let _ _ _ _ body, (letAbove, bodyHeaded) => (letAbove, bodyCommasHeaded False body bodyHeaded)
    | Bare value, (noAbove, valueHeaded) => (
      (outside => rewrite exprCommasFirstAbove value then noAbove outside),
      exprCommasHeaded bracketed value valueHeaded
    )
    | StatementNote _, _ => byComputing

theorem declarationCommasHeaded ∀ (line: Declaration)
    (headed: HeadedDeclaration line):
    HeadedDeclaration line.withoutTrailingCommas :=
  match line, headed with
    | Function _ _ _ _ _ _ _ _ _ body, (fnAbove, bodyHeaded) => (fnAbove, bodyCommasHeaded False body bodyHeaded)
    | Value _ _ _ _ body, (letAbove, bodyHeaded) => (letAbove, bodyCommasHeaded False body bodyHeaded)
    | DeclarationNote _, _ => byComputing

theorem declarationsCommasHeaded ∀ (lines: List (Spaced Declaration))
    (headed: HeadedDeclarations lines):
    HeadedDeclarations (declarationsWithoutTrailingCommas lines) :=
  match lines, headed with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineHeaded, restHeaded) =>
      (declarationCommasHeaded line lineHeaded, declarationsCommasHeaded rest restHeaded)

--| P2 keeps the parser's guarantees: what each says of a tree, dropping
--| a trailing comma doesn't change.
theorem commasKeepParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withoutTrailingCommas :=
  match file, parsed with
    | { declarations }, (shaped, lexical, (headed, unspaced)) => (
      declarationsCommasShaped declarations shaped,
      declarationsCommasLexical declarations lexical,
      (declarationsCommasHeaded declarations headed, declarationsCommasUnspaced declarations unspaced)
    )

-- P2 keeps the meaning: `plain` sets every trailing comma's flag to
-- `False` already.

theorem exprCommasPlain ∀ (expr: Expr): expr.withoutTrailingCommas.plain = expr.plain := match expr with
  | Var _ _ => byComputing
  | NumberLiteral _ _ => byComputing
  | StringLiteral _ _ => byComputing
  | Bracketed _ inner _ => rewrite exprCommasPlain inner
  | ListLiteral _ items _ _ => rewrite itemsCommasPlain items
  | Call callee _ arguments _ _ => rewrite exprCommasPlain callee, itemsCommasPlain arguments
  | Field target _ _ _ => rewrite exprCommasPlain target
  | Negate _ operand => rewrite exprCommasPlain operand
  | Binary _ _ left right => rewrite exprCommasPlain left, exprCommasPlain right
  | If _ condition _ whenTrue _ whenFalse =>
    rewrite exprCommasPlain condition, bodyCommasPlain whenTrue, bodyCommasPlain whenFalse

theorem itemsCommasPlain ∀ (items: List Expr): plainItems (itemsWithoutTrailingCommas items) = plainItems items :=
  match items with
    | [] => byComputing
    | [value, ..rest] => rewrite exprCommasPlain value, itemsCommasPlain rest

theorem bodyCommasPlain ∀ (body: Body): body.withoutTrailingCommas.plain = body.plain := match body with
  | { statements } => rewrite linesCommasPlain statements

theorem linesCommasPlain ∀ (lines: List (Spaced Statement)):
    plainLines (linesWithoutTrailingCommas lines) = plainLines lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => rewrite statementCommasPlain line, linesCommasPlain rest

theorem statementCommasPlain ∀ (line: Statement): line.withoutTrailingCommas.plain = line.plain := match line with
  | Let _ _ _ _ body => rewrite bodyCommasPlain body
  | Bare value => rewrite exprCommasPlain value
  | StatementNote _ => byComputing

theorem declarationCommasPlain ∀ (line: Declaration): line.withoutTrailingCommas.plain = line.plain := match line with
  | Function _ _ _ _ _ _ _ _ _ body => rewrite bodyCommasPlain body
  | Value _ _ _ _ body => rewrite bodyCommasPlain body
  | DeclarationNote _ => byComputing

theorem declarationsCommasPlain ∀ (lines: List (Spaced Declaration)):
    plainDeclarations (declarationsWithoutTrailingCommas lines) = plainDeclarations lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => rewrite declarationCommasPlain line, declarationsCommasPlain rest

--| P2 keeps the meaning, on every tree.
theorem commasKeepMeaning ∀ (file: SourceFile): file.withoutTrailingCommas.meaning = file.meaning :=
  rewrite declarationsCommasPlain file.declarations

-- P1: `takes` on every function with parameters.

theorem takesForPlain ∀ (takes: Option Comments) (parameters: List ParameterGroup):
    (takesFor takes parameters).getOrElse Comments.none = takes.getOrElse Comments.none :=
  match parameters with
    | [] => byComputing
    | [_, .._] => byComputing

theorem takesForTwice ∀ (takes: Option Comments) (parameters: List ParameterGroup):
    takesFor (takesFor takes parameters) parameters = takesFor takes parameters :=
  match parameters with
    | [] => byComputing
    | [_, .._] => byComputing

theorem takesForFine ∀ (takes: Option Comments) (parameters: List ParameterGroup)
    (fine: FineTakes takes):
    FineTakes (takesFor takes parameters) :=
  match parameters, takes, fine with
    | [], _, fine => fine
    | [_, .._], None, _ => fineNone
    | [_, .._], Some comments, fine => fine

theorem declarationTakesPlain ∀ (line: Declaration): line.withTakes.plain = line.plain := match line with
  | Function _ _ _ takes _ parameters _ _ _ _ => rewrite takesForPlain takes parameters
  | Value _ _ _ _ _ => byComputing
  | DeclarationNote _ => byComputing

theorem declarationsTakesPlain ∀ (lines: List (Spaced Declaration)):
    plainDeclarations (declarationsWithTakes lines) = plainDeclarations lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => rewrite declarationTakesPlain line, declarationsTakesPlain rest

--| P1 keeps the meaning, on every tree: `plain` writes `takes` on every
--| function already.
theorem takesKeepMeaning ∀ (file: SourceFile): file.withTakes.meaning = file.meaning :=
  rewrite declarationsTakesPlain file.declarations

theorem declarationTakesTwice ∀ (line: Declaration): line.withTakes.withTakes = line.withTakes := match line with
  | Function _ _ _ takes _ parameters _ _ _ _ => rewrite takesForTwice takes parameters
  | Value _ _ _ _ _ => byComputing
  | DeclarationNote _ => byComputing

theorem declarationsTakesTwice ∀ (lines: List (Spaced Declaration)):
    declarationsWithTakes (declarationsWithTakes lines) = declarationsWithTakes lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => rewrite declarationTakesTwice line, declarationsTakesTwice rest

--| P1 finishes in one run.
theorem takesIdempotent ∀ (file: SourceFile): file.withTakes.withTakes = file.withTakes :=
  rewrite declarationsTakesTwice file.declarations

theorem declarationTakesParsed ∀ (line: Declaration)
    (shaped: ShapedDeclaration line)
    (lexical: LexicalDeclaration line)
    (headed: HeadedDeclaration line):
    ShapedDeclaration line.withTakes ∧ LexicalDeclaration line.withTakes ∧ HeadedDeclaration line.withTakes :=
  match line, lexical with
    | Function _ _ _ takes _ parameters _ _ _ _, (fnFine, isName, nameFine, takesFine, others) =>
      (shaped, (fnFine, isName, nameFine, takesForFine takes parameters takesFine, others), headed)
    | Value _ _ _ _ _, lexical => (shaped, lexical, headed)
    | DeclarationNote _, lexical => (shaped, lexical, headed)

theorem declarationsTakesParsed ∀ (lines: List (Spaced Declaration))
    (shaped: ShapedDeclarations lines)
    (lexical: LexicalDeclarations lines)
    (headed: HeadedDeclarations lines):
    ShapedDeclarations (declarationsWithTakes lines)
      ∧ LexicalDeclarations (declarationsWithTakes lines)
      ∧ HeadedDeclarations (declarationsWithTakes lines) :=
  match lines, shaped, lexical, headed with
    | [], _, _, _ => (byComputing, byComputing, byComputing)
    | [{ blankBefore, line }, ..rest], (lineShaped, restShaped), (lineLexical, restLexical), (lineHeaded, restHeaded) =>
      let (lineShaped1, lineLexical1, lineHeaded1) := declarationTakesParsed line lineShaped lineLexical lineHeaded
      let (restShaped1, restLexical1, restHeaded1) := declarationsTakesParsed rest restShaped restLexical restHeaded
      ((lineShaped1, restShaped1), (lineLexical1, restLexical1), (lineHeaded1, restHeaded1))

theorem declarationsTakesUnspaced ∀ (lines: List (Spaced Declaration))
    (unspaced: Unspaced lines):
    Unspaced (declarationsWithTakes lines) :=
  match lines, unspaced with
    | [], _ => byComputing
    | [{ blankBefore = False, line }, ..rest], _ => byComputing
    | [{ blankBefore = True, line }, ..rest], unspaced => cases

--| P1 keeps the parser's guarantees: none of them reads `takes` but for
--| its comments, and the `takes` it adds holds none.
theorem takesKeepParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withTakes := match file, parsed with
  | { declarations }, (shaped, lexical, (headed, unspaced)) =>
    let (shaped1, lexical1, headed1) := declarationsTakesParsed declarations shaped lexical headed
    (shaped1, lexical1, (headed1, declarationsTakesUnspaced declarations unspaced))

-- P2 keeps P1's work: the two passes change different fields.

theorem declarationTakesCommas ∀ (line: Declaration):
    line.withoutTrailingCommas.withTakes = line.withTakes.withoutTrailingCommas :=
  match line with
    | Function _ _ _ _ _ _ _ _ _ _ => byComputing
    | Value _ _ _ _ _ => byComputing
    | DeclarationNote _ => byComputing

theorem declarationsTakesCommas ∀ (lines: List (Spaced Declaration)):
    declarationsWithTakes (declarationsWithoutTrailingCommas lines)
      = declarationsWithoutTrailingCommas (declarationsWithTakes lines) :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => rewrite declarationTakesCommas line, declarationsTakesCommas rest

--| P1 and P2 commute.
theorem takesCommasCommute ∀ (file: SourceFile):
    file.withoutTrailingCommas.withTakes = file.withTakes.withoutTrailingCommas :=
  rewrite declarationsTakesCommas file.declarations

--| P2 keeps P1's work: a tree P1 leaves alone, P1 leaves alone after P2.
theorem commasKeepTakes ∀ (file: SourceFile)
    (tidy: file.withTakes = file):
    file.withoutTrailingCommas.withTakes = file.withoutTrailingCommas :=
  rewrite takesCommasCommute file, tidy

-- The passes together (toy-plus-plus.md §3.3).

--| The passes keep the meaning, on every tree.
theorem tidyKeepsMeaning ∀ (file: SourceFile): file.tidy.meaning = file.meaning := calc file.tidy.meaning
  _ = file.withTakes.withoutTrailingCommas.meaning := bracketsKeepMeaning file.withTakes.withoutTrailingCommas
  _ = file.withTakes.meaning := commasKeepMeaning file.withTakes
  _ = file.meaning := takesKeepMeaning file

--| The passes keep the parser's guarantees.
theorem tidyParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.tidy :=
  bracketsKeepParsed file.withTakes.withoutTrailingCommas (commasKeepParsed file.withTakes (takesKeepParsed file parsed))

--| A tidy tree has no trailing comma, as the printer needs: P3 kept P2's
--| work.
theorem tidyBare ∀ (file: SourceFile): file.tidy.withoutTrailingCommas = file.tidy :=
  bracketsKeepCommas file.withTakes.withoutTrailingCommas (commasIdempotent file.withTakes)

--| A tidy tree is P1-tidy too: P2 and P3 kept P1's work.
theorem tidyTakes ∀ (file: SourceFile): file.tidy.withTakes = file.tidy :=
  bracketsKeepTakes file.withTakes.withoutTrailingCommas (commasKeepTakes file.withTakes (takesIdempotent file))

--| A tidy tree has no spare brackets.
theorem tidyBrackets ∀ (file: SourceFile): file.tidy.withoutSpareBrackets = file.tidy :=
  bracketsIdempotent file.withTakes.withoutTrailingCommas

--| The passes finish in one run: a tidy tree is tidy for each pass.
theorem tidyIdempotent ∀ (file: SourceFile): file.tidy.tidy = file.tidy := calc file.tidy.tidy
  _ = file.tidy.withTakes.withoutTrailingCommas.withoutSpareBrackets := byComputing
  _ = file.tidy.withoutTrailingCommas.withoutSpareBrackets :=
    Eq.cong ((tree: SourceFile) => tree.withoutTrailingCommas.withoutSpareBrackets) (tidyTakes file)
  _ = file.tidy.withoutSpareBrackets := Eq.cong ((tree: SourceFile) => tree.withoutSpareBrackets) (tidyBare file)
  _ = file.tidy := tidyBrackets file
