--| What `Expr.traverse` keeps (toy-plus-plus.md §3.4), proved once for
--| every `step`: a fact the step keeps at one node, wherever it stands,
--| the traversal keeps for the whole expression, body or file. A pass
--| written as a step then proves its family from its step's one-node
--| facts (`BracketProofs.sw` for P3).
--|
--| The facts are the meaning (`plain`), the parser's guarantees
--| (`Shaped`, `Lexical`, `HeadedExpr`), no trailing commas, and being
--| done: a property `done` of each node at its position (`AllAt`), which
--| the traversal reaches and then leaves alone, so it finishes in one run.

namespace Toy.Fmt.Proofs
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, Eq, List, Nat, Option, Text)

-- The meaning.

--| The step keeps the meaning at every node.
def StepKeepsPlain (step: Position → Expr → Expr): Prop :=
  ∀ (position: Position) (expr: Expr) => (step position expr).plain = expr.plain

theorem traversePlain ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsPlain step)
    (expr: Expr) (position: Position):
    (expr.traverse step position).plain = expr.plain :=
  rewrite keeps position (expr.traverseInside step position.bracketed) then
    insidePlain step keeps expr position.bracketed

--| By cases on the node: each child is traversed and keeps its meaning
--| (`traversePlain`, mutually), and the node's own fields are unchanged.
theorem insidePlain ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsPlain step)
    (expr: Expr) (bracketed: Bool):
    (expr.traverseInside step bracketed).plain = expr.plain :=
  match expr with
    | Bracketed _ inner _ => rewrite traversePlain step keeps inner { bracketed = True, slot = Whole }
    | ListLiteral _ items _ _ => rewrite itemsTraversePlain step keeps items
    | Call callee _ arguments _ _ =>
      rewrite traversePlain step keeps callee { bracketed, slot = PostfixSlot }, itemsTraversePlain step keeps arguments
    | Field target _ _ _ => rewrite traversePlain step keeps target { bracketed, slot = PostfixSlot }
    | Negate _ operand => rewrite traversePlain step keeps operand { bracketed, slot = OperandSlot }
    | Binary operator _ left right =>
      rewrite traversePlain step keeps left { bracketed, slot = LeftOf operator.level },
          traversePlain step keeps right { bracketed, slot = RightOf operator.level }
    | If _ condition _ whenTrue _ whenFalse =>
      rewrite traversePlain step keeps condition { bracketed, slot = Whole },
          bodyTraversePlain step keeps whenTrue bracketed,
          bodyTraversePlain step keeps whenFalse bracketed
    | _ => cases

theorem itemsTraversePlain ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsPlain step) (items: List Expr):
    plainItems (traverseItems step items) = plainItems items :=
  match items with
    | [] => byComputing
    | [value, ..rest] =>
      rewrite traversePlain step keeps value { bracketed = True, slot = Whole }, itemsTraversePlain step keeps rest

theorem bodyTraversePlain ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsPlain step)
    (body: Body) (bracketed: Bool):
    (body.traverse step bracketed).plain = body.plain :=
  match body with | { statements } => rewrite linesTraversePlain step keeps statements bracketed

theorem linesTraversePlain ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsPlain step)
    (lines: List (Spaced Statement)) (bracketed: Bool):
    plainLines (traverseLines step bracketed lines) = plainLines lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] =>
      rewrite statementTraversePlain step keeps line bracketed, linesTraversePlain step keeps rest bracketed

theorem statementTraversePlain ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsPlain step)
    (line: Statement) (bracketed: Bool):
    (line.traverse step bracketed).plain = line.plain :=
  match line with
    | Let _ _ _ _ body => rewrite bodyTraversePlain step keeps body False
    | Bare value => rewrite traversePlain step keeps value { bracketed, slot = Whole }
    | StatementNote _ => byComputing

-- The lexer's texts, and bodies that end in a statement.

def StepKeepsLexical (step: Position → Expr → Expr): Prop :=
  ∀ (position: Position) (expr: Expr) (lexical: Lexical expr) => Lexical (step position expr)

theorem traverseLexical ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsLexical step)
    (expr: Expr) (position: Position)
    (lexical: Lexical expr):
    Lexical (expr.traverse step position) :=
  keeps position
    (expr.traverseInside step position.bracketed)
    (insideLexical step keeps expr position.bracketed lexical)

--| By cases on the node: each child keeps its texts (`traverseLexical`,
--| mutually), the node's own tokens are unchanged, and a body's lines
--| stay statements (`linesTraverseClosed`).
theorem insideLexical ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsLexical step)
    (expr: Expr) (bracketed: Bool)
    (lexical: Lexical expr):
    Lexical (expr.traverseInside step bracketed) :=
  match expr, lexical with
    | Var _ _, lexical => lexical
    | NumberLiteral _ _, lexical => lexical
    | StringLiteral _ _, lexical => lexical
    | Bracketed _ inner _, (open, innerLexical, close) =>
      (open, traverseLexical step keeps inner { bracketed = True, slot = Whole } innerLexical, close)
    | ListLiteral _ items _ _, (open, itemsLexical, close) =>
      (open, itemsTraverseLexical step keeps items itemsLexical, close)
    | Call callee _ arguments _ _, (calleeLexical, open, argumentsLexical, close) => (
      traverseLexical step keeps callee { bracketed, slot = PostfixSlot } calleeLexical,
      open,
      itemsTraverseLexical step keeps arguments argumentsLexical,
      close
    )
    | Field target _ _ _, (targetLexical, others) =>
      (traverseLexical step keeps target { bracketed, slot = PostfixSlot } targetLexical, others)
    | Negate _ operand, (minus, operandLexical) =>
      (minus, traverseLexical step keeps operand { bracketed, slot = OperandSlot } operandLexical)
    | Binary operator _ left right, (sign, leftLexical, rightLexical) => (
      sign,
      traverseLexical step keeps left { bracketed, slot = LeftOf operator.level } leftLexical,
      traverseLexical step keeps right { bracketed, slot = RightOf operator.level } rightLexical
    )
    | If _ condition _ whenTrue _ whenFalse, (ifFine, conditionLexical, thenFine, trueLexical, elseFine,
        falseLexical) => (
      ifFine,
      traverseLexical step keeps condition { bracketed, slot = Whole } conditionLexical,
      thenFine,
      bodyTraverseLexical step keeps whenTrue bracketed trueLexical,
      elseFine,
      bodyTraverseLexical step keeps whenFalse bracketed falseLexical
    )

theorem itemsTraverseLexical ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsLexical step) (items: List Expr)
    (lexical: LexicalItems items):
    LexicalItems (traverseItems step items) :=
  match items, lexical with
    | [], _ => byComputing
    | [value, ..rest], (valueLexical, restLexical) => (
      traverseLexical step keeps value { bracketed = True, slot = Whole } valueLexical,
      itemsTraverseLexical step keeps rest restLexical
    )

theorem bodyTraverseLexical ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsLexical step)
    (body: Body) (bracketed: Bool)
    (lexical: LexicalBody body):
    LexicalBody (body.traverse step bracketed) :=
  match body, lexical with
    | { statements }, (linesLexical, closed) => (
      linesTraverseLexical step keeps statements bracketed linesLexical,
      linesTraverseClosed step statements bracketed closed
    )

theorem linesTraverseLexical ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsLexical step)
    (lines: List (Spaced Statement)) (bracketed: Bool)
    (lexical: LexicalLines lines):
    LexicalLines (traverseLines step bracketed lines) :=
  match lines, lexical with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineLexical, restLexical) => (
      statementTraverseLexical step keeps line bracketed lineLexical,
      linesTraverseLexical step keeps rest bracketed restLexical
    )

theorem statementTraverseLexical ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsLexical step)
    (line: Statement) (bracketed: Bool)
    (lexical: LexicalStatement line):
    LexicalStatement (line.traverse step bracketed) :=
  match line, lexical with
    | Let _ _ _ _ body, (letFine, isName, nameFine, equalsFine, bodyLexical) =>
      (letFine, isName, nameFine, equalsFine, bodyTraverseLexical step keeps body False bodyLexical)
    | Bare value, lexical => traverseLexical step keeps value { bracketed, slot = Whole } lexical
    | StatementNote _, lexical => lexical

theorem statementTraverseCoded ∀ (step: Position → Expr → Expr) (line: Statement) (bracketed: Bool)
    (coded: Coded line):
    Coded (line.traverse step bracketed) :=
  match line, coded with
    | StatementNote _, coded => coded
    | _, _ => cases

--| The traversal keeps every statement a statement, so a body still ends
--| in one.
theorem linesTraverseClosed ∀ (step: Position → Expr → Expr) (lines: List (Spaced Statement)) (bracketed: Bool)
    (closed: ClosedLines lines):
    ClosedLines (traverseLines step bracketed lines) :=
  match lines, closed with
    | [], closed => closed
    | [{ blankBefore, line }], coded => statementTraverseCoded step line bracketed coded
    | [first, second, ..rest], closed => linesTraverseClosed step [second, ..rest] bracketed closed

-- No trailing commas.

def StepKeepsCommas (step: Position → Expr → Expr): Prop :=
  ∀ (position: Position) (expr: Expr) (none: NoTrailingCommas expr) => NoTrailingCommas (step position expr)

theorem traverseCommas ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsCommas step)
    (expr: Expr) (position: Position)
    (none: NoTrailingCommas expr):
    NoTrailingCommas (expr.traverse step position) :=
  keeps position (expr.traverseInside step position.bracketed) (insideCommas step keeps expr position.bracketed none)

--| By cases on the node: each child keeps having no trailing comma
--| (`traverseCommas`, mutually), and the node's own flags are unchanged.
theorem insideCommas ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsCommas step)
    (expr: Expr) (bracketed: Bool)
    (none: NoTrailingCommas expr):
    NoTrailingCommas (expr.traverseInside step bracketed) :=
  match expr, none with
    | Bracketed _ inner _, none => traverseCommas step keeps inner { bracketed = True, slot = Whole } none
    | ListLiteral _ items _ _, (unwritten, itemsNone) => (unwritten, itemsTraverseCommas step keeps items itemsNone)
    | Call callee _ arguments _ _, (unwritten, calleeNone, argumentsNone) => (
      unwritten,
      traverseCommas step keeps callee { bracketed, slot = PostfixSlot } calleeNone,
      itemsTraverseCommas step keeps arguments argumentsNone
    )
    | Field target _ _ _, none => traverseCommas step keeps target { bracketed, slot = PostfixSlot } none
    | Negate _ operand, none => traverseCommas step keeps operand { bracketed, slot = OperandSlot } none
    | Binary operator _ left right, (leftNone, rightNone) => (
      traverseCommas step keeps left { bracketed, slot = LeftOf operator.level } leftNone,
      traverseCommas step keeps right { bracketed, slot = RightOf operator.level } rightNone
    )
    | If _ condition _ whenTrue _ whenFalse, (conditionNone, trueNone, falseNone) => (
      traverseCommas step keeps condition { bracketed, slot = Whole } conditionNone,
      bodyTraverseCommas step keeps whenTrue bracketed trueNone,
      bodyTraverseCommas step keeps whenFalse bracketed falseNone
    )
    | _, _ => cases

theorem itemsTraverseCommas ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsCommas step) (items: List Expr)
    (none: NoTrailingCommasItems items):
    NoTrailingCommasItems (traverseItems step items) :=
  match items, none with
    | [], _ => byComputing
    | [value, ..rest], (valueNone, restNone) => (
      traverseCommas step keeps value { bracketed = True, slot = Whole } valueNone,
      itemsTraverseCommas step keeps rest restNone
    )

theorem bodyTraverseCommas ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsCommas step)
    (body: Body) (bracketed: Bool)
    (none: NoTrailingCommasBody body):
    NoTrailingCommasBody (body.traverse step bracketed) :=
  match body, none with | { statements }, none => linesTraverseCommas step keeps statements bracketed none

theorem linesTraverseCommas ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsCommas step)
    (lines: List (Spaced Statement)) (bracketed: Bool)
    (none: NoTrailingCommasLines lines):
    NoTrailingCommasLines (traverseLines step bracketed lines) :=
  match lines, none with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineNone, restNone) => (
      statementTraverseCommas step keeps line bracketed lineNone,
      linesTraverseCommas step keeps rest bracketed restNone
    )

theorem statementTraverseCommas ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsCommas step)
    (line: Statement) (bracketed: Bool)
    (none: NoTrailingCommasStatement line):
    NoTrailingCommasStatement (line.traverse step bracketed) :=
  match line, none with
    | Let _ _ _ _ body, none => bodyTraverseCommas step keeps body False none
    | Bare value, none => traverseCommas step keeps value { bracketed, slot = Whole } none
    | StatementNote _, _ => byComputing

-- The parser's shape. A step may change a node's form, so the fact kept
-- at a node is `Shaped` together with fitting the node's slot, which is
-- what its parent's `Shaped` asks of it, and a closer's `settledCloser`
-- asks that the last token's trailing comment stays where it is.

--| Of the parser's shape, and read as it stands in `slot`.
def ShapedAt (slot: Slot) (expr: Expr): Prop := Shaped expr ∧ expr.fits slot = True

--| A trailing comment on `before`'s last token is still on `after`'s.
def EndKept (before after: Expr): Prop := before.endsWithComment = True → after.endsWithComment = True

def StepKeepsShaped (step: Position → Expr → Expr): Prop :=
  ∀ (position: Position) (expr: Expr) (shaped: ShapedAt position.slot expr) => ShapedAt position.slot
    (step position expr)
    ∧ EndKept expr (step position expr)

theorem fitsLeftOf ∀ (expr: Expr) (level: Nat)
    (chain: expr.isChain = True)
    (low: level ≤ expr.chainLevel):
    expr.fits (LeftOf level) = True :=
  (chain, low)

theorem leftOfFits ∀ (expr: Expr) (level: Nat)
    (fits: expr.fits (LeftOf level) = True):
    expr.isChain = True ∧ level ≤ expr.chainLevel :=
  fits.read

theorem fitsRightOf ∀ (expr: Expr) (level: Nat)
    (chain: expr.isChain = True)
    (low: level < expr.chainLevel):
    expr.fits (RightOf level) = True :=
  (chain, low)

theorem rightOfFits ∀ (expr: Expr) (level: Nat)
    (fits: expr.fits (RightOf level) = True):
    expr.isChain = True ∧ level < expr.chainLevel :=
  fits.read

--| A closer's comment stays settled when the token before it gains a
--| trailing comment.
theorem settledGrows ∀ (before after: Bool) (close: Comments)
    (settled: settledCloser before close = True)
    (grows: before = True → after = True):
    settledCloser after close = True :=
  cases

--| Traversing inside a node keeps its form, so it fits the same slots.
theorem insideFits ∀ (step: Position → Expr → Expr) (expr: Expr) (bracketed: Bool) (slot: Slot):
    (expr.traverseInside step bracketed).fits slot = expr.fits slot :=
  cases

theorem traverseShaped ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsShaped step)
    (expr: Expr) (position: Position)
    (shaped: ShapedAt position.slot expr):
    ShapedAt position.slot (expr.traverse step position) ∧ EndKept expr (expr.traverse step position) :=
  let (insideShaped, insideEnd) := insideShaped step keeps expr position.bracketed shaped.left
  let insideFits: (expr.traverseInside step position.bracketed).fits position.slot = True := cases
  let (stepShaped, stepEnd) := keeps position (expr.traverseInside step position.bracketed) (insideShaped, insideFits)
  (stepShaped, (ends => stepEnd (insideEnd ends)))

--| A node's children traversed keep their shape where they stand, so the
--| node keeps its own: by cases on the node, each child traversed at the
--| slot its parent's `Shaped` asks of it (`traverseShaped`, mutually),
--| and each closer settled still, since the token before it keeps its
--| trailing comment (`settledGrows`).
theorem insideShaped ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsShaped step)
    (expr: Expr) (bracketed: Bool)
    (shaped: Shaped expr):
    Shaped (expr.traverseInside step bracketed) ∧ EndKept expr (expr.traverseInside step bracketed) :=
  match expr, shaped with
    | Var _ _, shaped => (shaped, (ends => ends))
    | NumberLiteral _ _, shaped => (shaped, (ends => ends))
    | StringLiteral _ _, shaped => (shaped, (ends => ends))
    | Bracketed _ inner close, (innerShaped, settled) =>
      let (innerAt, innerEnd) :=
        traverseShaped step keeps inner { bracketed = True, slot = Whole } (innerShaped, byComputing)
      ((innerAt.left, settledGrows _ _ close settled innerEnd), (ends => ends))
    | ListLiteral open items _ close, (itemsShaped, settled) =>
      let (itemsAt, itemsEnd) := itemsTraverseShaped step keeps open items itemsShaped
      ((itemsAt, settledGrows _ _ close settled itemsEnd), (ends => ends))
    | Call callee open arguments _ close, (postfix, calleeShaped, argumentsShaped, settled) =>
      let (calleeAt, _) := traverseShaped step keeps callee { bracketed, slot = PostfixSlot } (calleeShaped, postfix)
      let (argumentsAt, argumentsEnd) := itemsTraverseShaped step keeps open arguments argumentsShaped
      ((calleeAt.right, calleeAt.left, argumentsAt, settledGrows _ _ close settled argumentsEnd), (ends => ends))
    | Field target _ _ _, (postfix, targetShaped) =>
      let (targetAt, _) := traverseShaped step keeps target { bracketed, slot = PostfixSlot } (targetShaped, postfix)
      ((targetAt.right, targetAt.left), (ends => ends))
    | Negate _ operand, (isOperand, operandShaped) =>
      let (operandAt, operandEnd) :=
        traverseShaped step keeps operand { bracketed, slot = OperandSlot } (operandShaped, isOperand)
      ((operandAt.right, operandAt.left), operandEnd)
    | Binary operator _ left right, (leftLevel, rightLevel, leftChain, rightChain, leftShaped, rightShaped) =>
      let (leftAt, _) := traverseShaped step keeps left { bracketed, slot = LeftOf operator.level } (
        leftShaped,
        fitsLeftOf left operator.level leftChain leftLevel
      )
      let (rightAt, rightEnd) := traverseShaped step keeps right { bracketed, slot = RightOf operator.level } (
        rightShaped,
        fitsRightOf right operator.level rightChain rightLevel
      )
      let (leftChain1, leftLevel1) := leftOfFits _ operator.level leftAt.right
      let (rightChain1, rightLevel1) := rightOfFits _ operator.level rightAt.right
      ((leftLevel1, rightLevel1, leftChain1, rightChain1, leftAt.left, rightAt.left), rightEnd)
    | If _ condition _ whenTrue _ whenFalse, (conditionShaped, trueShaped, falseShaped) =>
      let (conditionAt, _) :=
        traverseShaped step keeps condition { bracketed, slot = Whole } (conditionShaped, byComputing)
      let (trueAt, _) := bodyTraverseShaped step keeps whenTrue bracketed trueShaped
      let (falseAt, falseEnd) := bodyTraverseShaped step keeps whenFalse bracketed falseShaped
      ((conditionAt.left, trueAt, falseAt), falseEnd)

theorem itemsTraverseShaped ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsShaped step)
    (open: Comments) (items: List Expr)
    (shaped: ShapedItems items):
    ShapedItems (traverseItems step items)
      ∧ (itemsEndWithComment open items = True → itemsEndWithComment open (traverseItems step items) = True) :=
  match items, shaped with
    | [], _ => (byComputing, (ends => ends))
    | [value], (valueShaped, _) =>
      let (valueAt, valueEnd) :=
        traverseShaped step keeps value { bracketed = True, slot = Whole } (valueShaped, byComputing)
      ((valueAt.left, byComputing), valueEnd)
    | [first, second, ..rest], (firstShaped, restShaped) =>
      let (firstAt, _) := traverseShaped step keeps first { bracketed = True, slot = Whole } (firstShaped, byComputing)
      let (restAt, restEnd) := itemsTraverseShaped step keeps open [second, ..rest] restShaped
      ((firstAt.left, restAt), restEnd)

theorem bodyTraverseShaped ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsShaped step)
    (body: Body) (bracketed: Bool)
    (shaped: ShapedBody body):
    ShapedBody (body.traverse step bracketed)
      ∧ (body.endsWithComment = True → (body.traverse step bracketed).endsWithComment = True) :=
  match body, shaped with
    | { statements }, (linesShaped, closed) =>
      let (linesAt, linesEnd) := linesTraverseShaped step keeps statements bracketed linesShaped
      ((linesAt, linesTraverseClosed step statements bracketed closed), linesEnd)

theorem linesTraverseShaped ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsShaped step)
    (lines: List (Spaced Statement)) (bracketed: Bool)
    (shaped: ShapedLines lines):
    ShapedLines (traverseLines step bracketed lines)
      ∧ (statementsEndWithComment lines = True
        → statementsEndWithComment (traverseLines step bracketed lines) = True) :=
  match lines, shaped with
    | [], _ => (byComputing, (ends => ends))
    | [{ blankBefore, line }], (lineShaped, _) =>
      let (lineAt, lineEnd) := statementTraverseShaped step keeps line bracketed lineShaped
      ((lineAt, byComputing), lineEnd)
    | [{ blankBefore, line }, second, ..rest], (lineShaped, restShaped) =>
      let (lineAt, _) := statementTraverseShaped step keeps line bracketed lineShaped
      let (restAt, restEnd) := linesTraverseShaped step keeps [second, ..rest] bracketed restShaped
      ((lineAt, restAt), restEnd)

theorem statementTraverseShaped ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsShaped step)
    (line: Statement) (bracketed: Bool)
    (shaped: ShapedStatement line):
    ShapedStatement (line.traverse step bracketed)
      ∧ (line.endsWithComment = True → (line.traverse step bracketed).endsWithComment = True) :=
  match line, shaped with
    | Let _ _ _ _ body, shaped => bodyTraverseShaped step keeps body False shaped
    | Bare value, shaped =>
      let (valueAt, valueEnd) := traverseShaped step keeps value { bracketed, slot = Whole } (shaped, byComputing)
      (valueAt.left, valueEnd)
    | StatementNote _, _ => (byComputing, (ends => ends))

-- Where comments and blocks are. A step keeps `HeadedExpr` at the
-- node's own flag, and the comments above the node's first token, which
-- its statement asks of it outside brackets.

def StepKeepsHeaded (step: Position → Expr → Expr): Prop :=
  ∀ (position: Position) (expr: Expr) (headed: HeadedExpr position.bracketed expr) => HeadedExpr position.bracketed
    (step position expr)
    ∧ (step position expr).firstAbove = expr.firstAbove

theorem traverseHeaded ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsHeaded step)
    (expr: Expr) (position: Position)
    (headed: HeadedExpr position.bracketed expr):
    HeadedExpr position.bracketed (expr.traverse step position)
      ∧ (expr.traverse step position).firstAbove = expr.firstAbove :=
  let (insideHeaded, insideAbove) := insideHeaded step keeps expr position.bracketed headed
  let (stepHeaded, stepAbove) := keeps position (expr.traverseInside step position.bracketed) insideHeaded
  (stepHeaded, stepAbove.trans insideAbove)

--| By cases on the node: each child is traversed at the flag `HeadedExpr`
--| reads it at (the node's own, or `True` inside its brackets), so
--| `traverseHeaded` (mutually) keeps it, and the node's first token is
--| its first child's, whose comments the step keeps.
theorem insideHeaded ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsHeaded step)
    (expr: Expr) (bracketed: Bool)
    (headed: HeadedExpr bracketed expr):
    HeadedExpr bracketed (expr.traverseInside step bracketed)
      ∧ (expr.traverseInside step bracketed).firstAbove = expr.firstAbove :=
  match expr, headed with
    | Var _ _, headed => (headed, byComputing)
    | NumberLiteral _ _, headed => (headed, byComputing)
    | StringLiteral _ _, headed => (headed, byComputing)
    | Bracketed _ inner _, headed =>
      ((traverseHeaded step keeps inner { bracketed = True, slot = Whole } headed).left, byComputing)
    | ListLiteral _ items _ _, headed => (itemsTraverseHeaded step keeps items headed, byComputing)
    | Call callee _ arguments _ _, (calleeHeaded, argumentsHeaded) =>
      let (calleeHeaded1, calleeAbove) :=
        traverseHeaded step keeps callee { bracketed, slot = PostfixSlot } calleeHeaded
      ((calleeHeaded1, itemsTraverseHeaded step keeps arguments argumentsHeaded), calleeAbove)
    | Field target _ _ _, headed => traverseHeaded step keeps target { bracketed, slot = PostfixSlot } headed
    | Negate _ operand, headed =>
      ((traverseHeaded step keeps operand { bracketed, slot = OperandSlot } headed).left, byComputing)
    | Binary operator _ left right, (leftHeaded, rightHeaded) =>
      let (leftHeaded1, leftAbove) :=
        traverseHeaded step keeps left { bracketed, slot = LeftOf operator.level } leftHeaded
      let (rightHeaded1, _) := traverseHeaded step keeps right { bracketed, slot = RightOf operator.level } rightHeaded
      ((leftHeaded1, rightHeaded1), leftAbove)
    | If _ condition _ whenTrue _ whenFalse, (conditionHeaded, trueHeaded, falseHeaded) => (
      (
        (traverseHeaded step keeps condition { bracketed, slot = Whole } conditionHeaded).left,
        bodyTraverseHeaded step keeps whenTrue bracketed trueHeaded,
        bodyTraverseHeaded step keeps whenFalse bracketed falseHeaded
      ),
      byComputing
    )

theorem itemsTraverseHeaded ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsHeaded step) (items: List Expr)
    (headed: HeadedItems items):
    HeadedItems (traverseItems step items) :=
  match items, headed with
    | [], _ => byComputing
    | [value, ..rest], (valueHeaded, restHeaded) => (
      (traverseHeaded step keeps value { bracketed = True, slot = Whole } valueHeaded).left,
      itemsTraverseHeaded step keeps rest restHeaded
    )

theorem bodyTraverseHeaded ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsHeaded step)
    (body: Body) (bracketed: Bool)
    (headed: HeadedBody bracketed body):
    HeadedBody bracketed (body.traverse step bracketed) :=
  match body, headed with
    | { statements }, (linesHeaded, unspaced, one) => (
      linesTraverseHeaded step keeps statements bracketed linesHeaded,
      linesTraverseUnspaced step statements bracketed unspaced,
      (inside => linesTraverseOne step statements bracketed (one inside))
    )

theorem linesTraverseHeaded ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsHeaded step)
    (lines: List (Spaced Statement)) (bracketed: Bool)
    (headed: HeadedLines bracketed lines):
    HeadedLines bracketed (traverseLines step bracketed lines) :=
  match lines, headed with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineHeaded, restHeaded) => (
      statementTraverseHeaded step keeps line bracketed lineHeaded,
      linesTraverseHeaded step keeps rest bracketed restHeaded
    )

theorem statementTraverseHeaded ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsHeaded step)
    (line: Statement) (bracketed: Bool)
    (headed: HeadedStatement bracketed line):
    HeadedStatement bracketed (line.traverse step bracketed) :=
  match line, headed with
    | Let _ _ _ _ body, (letAbove, bodyHeaded) => (letAbove, bodyTraverseHeaded step keeps body False bodyHeaded)
    | Bare value, (noAbove, valueHeaded) =>
      let (valueHeaded1, valueAbove) := traverseHeaded step keeps value { bracketed, slot = Whole } valueHeaded
      ((outside => rewrite valueAbove then noAbove outside), valueHeaded1)
    | StatementNote _, _ => byComputing

theorem linesTraverseUnspaced ∀ (step: Position → Expr → Expr) (lines: List (Spaced Statement)) (bracketed: Bool)
    (unspaced: Unspaced lines):
    Unspaced (traverseLines step bracketed lines) :=
  match lines, unspaced with
    | [{ blankBefore = True, line }, ..rest], unspaced => cases
    | _, _ => cases

theorem linesTraverseOne ∀ (step: Position → Expr → Expr) (lines: List (Spaced Statement)) (bracketed: Bool)
    (one: OneExpression lines):
    OneExpression (traverseLines step bracketed lines) :=
  match lines, one with | [{ blankBefore, line = Bare _ }], _ => byComputing

-- Done in one run. `done` is a property of a node at its position;
-- `AllAt done` says it of every node, each at its own position.

def AllAt (done: Position → Expr → Prop) (position: Position) (expr: Expr): Prop :=
  done position expr ∧ AllInside done position.bracketed expr

def AllInside (done: Position → Expr → Prop) (bracketed: Bool): Expr → Prop
  | Bracketed _ inner _ => AllAt done { bracketed = True, slot = Whole } inner
  | ListLiteral _ items _ _ => AllItems done items
  | Call callee _ arguments _ _ => AllAt done { bracketed, slot = PostfixSlot } callee ∧ AllItems done arguments
  | Field target _ _ _ => AllAt done { bracketed, slot = PostfixSlot } target
  | Negate _ operand => AllAt done { bracketed, slot = OperandSlot } operand
  | Binary operator _ left right =>
    AllAt done { bracketed, slot = LeftOf operator.level } left
      ∧ AllAt done { bracketed, slot = RightOf operator.level } right
  | If _ condition _ whenTrue _ whenFalse =>
    AllAt done { bracketed, slot = Whole } condition
      ∧ AllBody done bracketed whenTrue
      ∧ AllBody done bracketed whenFalse
  | _ => True

def AllItems (done: Position → Expr → Prop): List Expr → Prop
  | [] => True
  | [value, ..rest] => AllAt done { bracketed = True, slot = Whole } value ∧ AllItems done rest

def AllBody (done: Position → Expr → Prop) (bracketed: Bool): Body → Prop
  | { statements } => AllLines done bracketed statements

def AllLines (done: Position → Expr → Prop) (bracketed: Bool): List (Spaced Statement) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => AllStatement done bracketed line ∧ AllLines done bracketed rest

def AllStatement (done: Position → Expr → Prop) (bracketed: Bool): Statement → Prop
  | Let _ _ _ _ body => AllBody done False body
  | Bare value => AllAt done { bracketed, slot = Whole } value
  | StatementNote _ => True

--| The step leaves a node that is done alone.
def StepFixes (step: Position → Expr → Expr) (done: Position → Expr → Prop): Prop :=
  ∀ (position: Position) (expr: Expr) (isDone: done position expr) => step position expr = expr

--| Once every node inside is done, the step's result is done throughout.
def StepReaches (step: Position → Expr → Expr) (done: Position → Expr → Prop): Prop :=
  ∀ (position: Position) (expr: Expr) (inside: AllInside done position.bracketed expr) => AllAt done position
    (step position expr)

theorem traverseFixed ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (fixes: StepFixes step done)
    (expr: Expr) (position: Position)
    (all: AllAt done position expr):
    expr.traverse step position = expr :=
  rewrite insideFixed step done fixes expr position.bracketed all.right then fixes position expr all.left

--| By cases on the node: each child is done throughout, so its traversal
--| leaves it alone (`traverseFixed`, mutually).
theorem insideFixed ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (fixes: StepFixes step done)
    (expr: Expr) (bracketed: Bool)
    (all: AllInside done bracketed expr):
    expr.traverseInside step bracketed = expr :=
  match expr, all with
    | Bracketed _ inner _, all => rewrite traverseFixed step done fixes inner { bracketed = True, slot = Whole } all
    | ListLiteral _ items _ _, all => rewrite itemsFixed step done fixes items all
    | Call callee _ arguments _ _, (calleeAll, argumentsAll) =>
      rewrite traverseFixed step done fixes callee { bracketed, slot = PostfixSlot } calleeAll,
          itemsFixed step done fixes arguments argumentsAll
    | Field target _ _ _, all => rewrite traverseFixed step done fixes target { bracketed, slot = PostfixSlot } all
    | Negate _ operand, all => rewrite traverseFixed step done fixes operand { bracketed, slot = OperandSlot } all
    | Binary operator _ left right, (leftAll, rightAll) =>
      rewrite traverseFixed step done fixes left { bracketed, slot = LeftOf operator.level } leftAll,
          traverseFixed step done fixes right { bracketed, slot = RightOf operator.level } rightAll
    | If _ condition _ whenTrue _ whenFalse, (conditionAll, trueAll, falseAll) =>
      rewrite traverseFixed step done fixes condition { bracketed, slot = Whole } conditionAll,
          bodyFixed step done fixes whenTrue bracketed trueAll,
          bodyFixed step done fixes whenFalse bracketed falseAll
    | _, _ => cases

theorem itemsFixed ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (fixes: StepFixes step done) (items: List Expr)
    (all: AllItems done items):
    traverseItems step items = items :=
  match items, all with
    | [], _ => byComputing
    | [value, ..rest], (valueAll, restAll) =>
      rewrite traverseFixed step done fixes value { bracketed = True, slot = Whole } valueAll,
          itemsFixed step done fixes rest restAll

theorem bodyFixed ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (fixes: StepFixes step done)
    (body: Body) (bracketed: Bool)
    (all: AllBody done bracketed body):
    body.traverse step bracketed = body :=
  match body, all with | { statements }, all => rewrite linesFixed step done fixes statements bracketed all

theorem linesFixed ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (fixes: StepFixes step done)
    (lines: List (Spaced Statement)) (bracketed: Bool)
    (all: AllLines done bracketed lines):
    traverseLines step bracketed lines = lines :=
  match lines, all with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineAll, restAll) =>
      rewrite statementFixed step done fixes line bracketed lineAll, linesFixed step done fixes rest bracketed restAll

theorem statementFixed ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (fixes: StepFixes step done)
    (line: Statement) (bracketed: Bool)
    (all: AllStatement done bracketed line):
    line.traverse step bracketed = line :=
  match line, all with
    | Let _ _ _ _ body, all => rewrite bodyFixed step done fixes body False all
    | Bare value, all => rewrite traverseFixed step done fixes value { bracketed, slot = Whole } all
    | StatementNote _, _ => byComputing

theorem traverseReaches ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (reaches: StepReaches step done)
    (expr: Expr) (position: Position):
    AllAt done position (expr.traverse step position) :=
  reaches position
    (expr.traverseInside step position.bracketed)
    (insideReaches step done reaches expr position.bracketed)

--| By cases on the node: each child's traversal is done throughout
--| (`traverseReaches`, mutually), at the position it stands in.
theorem insideReaches ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (reaches: StepReaches step done)
    (expr: Expr) (bracketed: Bool):
    AllInside done bracketed (expr.traverseInside step bracketed) :=
  match expr with
    | Bracketed _ inner _ => traverseReaches step done reaches inner { bracketed = True, slot = Whole }
    | ListLiteral _ items _ _ => itemsReaches step done reaches items
    | Call callee _ arguments _ _ => (
      traverseReaches step done reaches callee { bracketed, slot = PostfixSlot },
      itemsReaches step done reaches arguments
    )
    | Field target _ _ _ => traverseReaches step done reaches target { bracketed, slot = PostfixSlot }
    | Negate _ operand => traverseReaches step done reaches operand { bracketed, slot = OperandSlot }
    | Binary operator _ left right => (
      traverseReaches step done reaches left { bracketed, slot = LeftOf operator.level },
      traverseReaches step done reaches right { bracketed, slot = RightOf operator.level }
    )
    | If _ condition _ whenTrue _ whenFalse => (
      traverseReaches step done reaches condition { bracketed, slot = Whole },
      bodyReaches step done reaches whenTrue bracketed,
      bodyReaches step done reaches whenFalse bracketed
    )
    | _ => cases

theorem itemsReaches ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (reaches: StepReaches step done) (items: List Expr):
    AllItems done (traverseItems step items) :=
  match items with
    | [] => byComputing
    | [value, ..rest] =>
      (traverseReaches step done reaches value { bracketed = True, slot = Whole }, itemsReaches step done reaches rest)

theorem bodyReaches ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (reaches: StepReaches step done)
    (body: Body) (bracketed: Bool):
    AllBody done bracketed (body.traverse step bracketed) :=
  match body with | { statements } => linesReaches step done reaches statements bracketed

theorem linesReaches ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (reaches: StepReaches step done)
    (lines: List (Spaced Statement)) (bracketed: Bool):
    AllLines done bracketed (traverseLines step bracketed lines) :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] =>
      (statementReaches step done reaches line bracketed, linesReaches step done reaches rest bracketed)

theorem statementReaches ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (reaches: StepReaches step done)
    (line: Statement) (bracketed: Bool):
    AllStatement done bracketed (line.traverse step bracketed) :=
  match line with
    | Let _ _ _ _ body => bodyReaches step done reaches body False
    | Bare value => traverseReaches step done reaches value { bracketed, slot = Whole }
    | StatementNote _ => byComputing

--| A traversed body is left alone by a second traversal.
theorem bodyTraverseTwice ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (fixes: StepFixes step done)
    (reaches: StepReaches step done)
    (body: Body) (bracketed: Bool):
    (body.traverse step bracketed).traverse step bracketed = body.traverse step bracketed :=
  bodyFixed step done fixes (body.traverse step bracketed) bracketed (bodyReaches step done reaches body bracketed)

-- What is done inside brackets is done outside them, for a `done` that
-- asks no more of a node inside brackets than outside.

--| `done` asks no more of a node inside brackets than outside them.
def DoneOutside (done: Position → Expr → Prop): Prop :=
  ∀ (slot: Slot) (bracketed: Bool) (expr: Expr) (isDone: done { bracketed = True, slot } expr) => done
    { bracketed, slot }
    expr

theorem allOutside ∀ (done: Position → Expr → Prop)
    (outside: DoneOutside done)
    (expr: Expr) (slot: Slot) (bracketed: Bool)
    (all: AllAt done { bracketed = True, slot } expr):
    AllAt done { bracketed, slot } expr :=
  (outside slot bracketed expr all.left, insideOutside done outside expr bracketed all.right)

--| By cases on the node: inside brackets, and in an item, the flag is
--| `True` whatever is outside; elsewhere each child is at the node's
--| flag, so `allOutside` (mutually) moves it.
theorem insideOutside ∀ (done: Position → Expr → Prop)
    (outside: DoneOutside done)
    (expr: Expr) (bracketed: Bool)
    (all: AllInside done True expr):
    AllInside done bracketed expr :=
  match expr, all with
    | Bracketed _ _ _, all => all
    | ListLiteral _ _ _ _, all => all
    | Call callee _ _ _ _, (calleeAll, argumentsAll) =>
      (allOutside done outside callee PostfixSlot bracketed calleeAll, argumentsAll)
    | Field target _ _ _, all => allOutside done outside target PostfixSlot bracketed all
    | Negate _ operand, all => allOutside done outside operand OperandSlot bracketed all
    | Binary operator _ left right, (leftAll, rightAll) => (
      allOutside done outside left (LeftOf operator.level) bracketed leftAll,
      allOutside done outside right (RightOf operator.level) bracketed rightAll
    )
    | If _ condition _ whenTrue _ whenFalse, (conditionAll, trueAll, falseAll) => (
      allOutside done outside condition Whole bracketed conditionAll,
      bodyOutside done outside whenTrue bracketed trueAll,
      bodyOutside done outside whenFalse bracketed falseAll
    )
    | _, _ => cases

theorem bodyOutside ∀ (done: Position → Expr → Prop)
    (outside: DoneOutside done)
    (body: Body) (bracketed: Bool)
    (all: AllBody done True body):
    AllBody done bracketed body :=
  match body, all with | { statements }, all => linesOutside done outside statements bracketed all

theorem linesOutside ∀ (done: Position → Expr → Prop)
    (outside: DoneOutside done)
    (lines: List (Spaced Statement)) (bracketed: Bool)
    (all: AllLines done True lines):
    AllLines done bracketed lines :=
  match lines, all with
    | [], _ => byComputing
    | [{ blankBefore, line = Let _ _ _ _ body }, ..rest], (lineAll, restAll) =>
      (lineAll, linesOutside done outside rest bracketed restAll)
    | [{ blankBefore, line = Bare value }, ..rest], (lineAll, restAll) =>
      (allOutside done outside value Whole bracketed lineAll, linesOutside done outside rest bracketed restAll)
    | [{ blankBefore, line = StatementNote _ }, ..rest], (_, restAll) =>
      (byComputing, linesOutside done outside rest bracketed restAll)

-- Declarations and the file: each body traversed, then `declare` at each
-- declaration.

theorem declarationTraversePlain ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsPlain step) (line: Declaration):
    (line.traverseBody step).plain = line.plain :=
  match line with
    | Function _ _ _ _ _ _ _ _ _ body => rewrite bodyTraversePlain step keeps body False
    | Value _ _ _ _ body => rewrite bodyTraversePlain step keeps body False
    | DeclarationNote _ => byComputing

theorem declarationsTraversePlain ∀ (step: Position → Expr → Expr) (declare: Declaration → Declaration)
    (keeps: StepKeepsPlain step)
    (declareKeeps: ∀ (line: Declaration) => (declare line).plain = line.plain) (lines: List (Spaced Declaration)):
    plainDeclarations (traverseDeclarations step declare lines) = plainDeclarations lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] =>
      rewrite declareKeeps (line.traverseBody step),
          declarationTraversePlain step keeps line,
          declarationsTraversePlain step declare keeps declareKeeps rest

--| A traversal whose step and `declare` keep the meaning keeps the
--| file's.
theorem traverseKeepsMeaning ∀ (step: Position → Expr → Expr) (declare: Declaration → Declaration)
    (keeps: StepKeepsPlain step)
    (declareKeeps: ∀ (line: Declaration) => (declare line).plain = line.plain) (file: SourceFile):
    (file.traverse step declare).meaning = file.meaning :=
  rewrite declarationsTraversePlain step declare keeps declareKeeps file.declarations

--| What `declare` must keep of the parser's guarantees.
def DeclareKeepsParsed (declare: Declaration → Declaration): Prop :=
  ∀ (line: Declaration) (shaped: ShapedDeclaration line) (lexical: LexicalDeclaration line) (headed: HeadedDeclaration
      line) => ShapedDeclaration (declare line) ∧ LexicalDeclaration (declare line) ∧ HeadedDeclaration (declare line)

--| By cases on the declaration: its body is traversed outside brackets, so
--| the body lemmas give each guarantee; its other parts are unchanged.
theorem declarationTraverseParsed ∀ (step: Position → Expr → Expr)
    (shapedKeeps: StepKeepsShaped step)
    (lexicalKeeps: StepKeepsLexical step)
    (headedKeeps: StepKeepsHeaded step) (line: Declaration)
    (shaped: ShapedDeclaration line)
    (lexical: LexicalDeclaration line)
    (headed: HeadedDeclaration line):
    ShapedDeclaration (line.traverseBody step)
      ∧ LexicalDeclaration (line.traverseBody step)
      ∧ HeadedDeclaration (line.traverseBody step) :=
  match line, shaped, lexical, headed with
    | Function _ _ _ _ _ _ _ _ _ body, (parameters, bodyShaped), (fnFine, isName, nameFine, takesFine, openFine, groups,
        closeFine, equalsFine, bodyLexical), (fnAbove, bodyHeaded) => (
      (parameters, (bodyTraverseShaped step shapedKeeps body False bodyShaped).left),
      (
        fnFine,
        isName,
        nameFine,
        takesFine,
        openFine,
        groups,
        closeFine,
        equalsFine,
        bodyTraverseLexical step lexicalKeeps body False bodyLexical
      ),
      (fnAbove, bodyTraverseHeaded step headedKeeps body False bodyHeaded)
    )
    | Value _ _ _ _ body, bodyShaped, (letFine, isName, nameFine, equalsFine, bodyLexical), (letAbove, bodyHeaded) => (
      (bodyTraverseShaped step shapedKeeps body False bodyShaped).left,
      (letFine, isName, nameFine, equalsFine, bodyTraverseLexical step lexicalKeeps body False bodyLexical),
      (letAbove, bodyTraverseHeaded step headedKeeps body False bodyHeaded)
    )
    | DeclarationNote _, shaped, lexical, headed => (shaped, lexical, headed)

--| By induction on the declarations: each body traversed
--| (`declarationTraverseParsed`), then `declare`.
theorem declarationsTraverseParsed ∀ (step: Position → Expr → Expr) (declare: Declaration → Declaration)
    (shapedKeeps: StepKeepsShaped step)
    (lexicalKeeps: StepKeepsLexical step)
    (headedKeeps: StepKeepsHeaded step)
    (declareKeeps: DeclareKeepsParsed declare) (lines: List (Spaced Declaration))
    (shaped: ShapedDeclarations lines)
    (lexical: LexicalDeclarations lines)
    (headed: HeadedDeclarations lines):
    ShapedDeclarations (traverseDeclarations step declare lines)
      ∧ LexicalDeclarations (traverseDeclarations step declare lines)
      ∧ HeadedDeclarations (traverseDeclarations step declare lines) :=
  match lines, shaped, lexical, headed with
    | [], _, _, _ => (byComputing, byComputing, byComputing)
    | [{ blankBefore, line }, ..rest], (lineShaped, restShaped), (lineLexical, restLexical), (lineHeaded, restHeaded) =>
      let (bodyShaped, bodyLexical, bodyHeaded) :=
        declarationTraverseParsed step shapedKeeps lexicalKeeps headedKeeps line lineShaped lineLexical lineHeaded
      let (lineShaped1, lineLexical1, lineHeaded1) :=
        declareKeeps (line.traverseBody step) bodyShaped bodyLexical bodyHeaded
      let (restShaped1, restLexical1, restHeaded1) :=
        declarationsTraverseParsed step declare shapedKeeps lexicalKeeps headedKeeps declareKeeps rest restShaped
            restLexical restHeaded
      ((lineShaped1, restShaped1), (lineLexical1, restLexical1), (lineHeaded1, restHeaded1))

theorem declarationsTraverseUnspaced ∀ (step: Position → Expr → Expr)
    (declare: Declaration → Declaration) (lines: List (Spaced Declaration))
    (unspaced: Unspaced lines):
    Unspaced (traverseDeclarations step declare lines) :=
  match lines, unspaced with
    | [{ blankBefore = True, line }, ..rest], unspaced => cases
    | _, _ => cases

--| A traversal whose step and `declare` keep the parser's guarantees
--| keeps the file's.
theorem traverseKeepsParsed ∀ (step: Position → Expr → Expr) (declare: Declaration → Declaration)
    (shapedKeeps: StepKeepsShaped step)
    (lexicalKeeps: StepKeepsLexical step)
    (headedKeeps: StepKeepsHeaded step)
    (declareKeeps: DeclareKeepsParsed declare) (file: SourceFile)
    (parsed: Parsed file):
    Parsed (file.traverse step declare) :=
  match file, parsed with
    | { declarations }, (shaped, lexical, (headed, unspaced)) =>
      let (shaped1, lexical1, headed1) :=
        declarationsTraverseParsed step declare shapedKeeps lexicalKeeps headedKeeps declareKeeps declarations shaped
            lexical headed
      (shaped1, lexical1, (headed1, declarationsTraverseUnspaced step declare declarations unspaced))

theorem declarationTraverseCommas ∀ (step: Position → Expr → Expr)
    (keeps: StepKeepsCommas step) (line: Declaration)
    (none: NoTrailingCommasDeclaration line):
    NoTrailingCommasDeclaration (line.traverseBody step) :=
  match line, none with
    | Function _ _ _ _ _ _ _ _ _ body, (unwritten, bodyNone) =>
      (unwritten, bodyTraverseCommas step keeps body False bodyNone)
    | Value _ _ _ _ body, none => bodyTraverseCommas step keeps body False none
    | DeclarationNote _, _ => byComputing

theorem declarationsTraverseCommas ∀ (step: Position → Expr → Expr) (declare: Declaration → Declaration)
    (keeps: StepKeepsCommas step)
    (declareKeeps: ∀ (line: Declaration) (none: NoTrailingCommasDeclaration line) => NoTrailingCommasDeclaration
      (declare line)) (lines: List (Spaced Declaration))
    (none: NoTrailingCommasDeclarations lines):
    NoTrailingCommasDeclarations (traverseDeclarations step declare lines) :=
  match lines, none with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineNone, restNone) => (
      declareKeeps (line.traverseBody step) (declarationTraverseCommas step keeps line lineNone),
      declarationsTraverseCommas step declare keeps declareKeeps rest restNone
    )

--| A traversal whose step and `declare` add no trailing comma leaves a
--| file with none without one.
theorem traverseKeepsCommas ∀ (step: Position → Expr → Expr) (declare: Declaration → Declaration)
    (keeps: StepKeepsCommas step)
    (declareKeeps: ∀ (line: Declaration) (none: NoTrailingCommasDeclaration line) => NoTrailingCommasDeclaration
      (declare line)) (file: SourceFile)
    (none: NoTrailingCommasFile file):
    NoTrailingCommasFile (file.traverse step declare) :=
  match file, none with
    | { declarations }, none => declarationsTraverseCommas step declare keeps declareKeeps declarations none

theorem declarationTraverseTwice ∀ (step: Position → Expr → Expr) (done: Position → Expr → Prop)
    (fixes: StepFixes step done)
    (reaches: StepReaches step done) (line: Declaration):
    (line.traverseBody step).traverseBody step = line.traverseBody step :=
  match line with
    | Function _ _ _ _ _ _ _ _ _ body => rewrite bodyTraverseTwice step done fixes reaches body False
    | Value _ _ _ _ body => rewrite bodyTraverseTwice step done fixes reaches body False
    | DeclarationNote _ => byComputing

--| What `declare` must be for the traversal to finish in one run: it
--| doesn't touch bodies, and finishes in one run itself.
def DeclareSettles (step: Position → Expr → Expr) (declare: Declaration → Declaration): Prop :=
  (∀ (line: Declaration) => (declare line).traverseBody step = declare (line.traverseBody step))
    ∧ (∀ (line: Declaration) => declare (declare line) = declare line)

theorem declarationsTraverseTwice ∀ (step: Position → Expr → Expr)
    (declare: Declaration → Declaration) (done: Position → Expr → Prop)
    (fixes: StepFixes step done)
    (reaches: StepReaches step done)
    (settles: DeclareSettles step declare) (lines: List (Spaced Declaration)):
    traverseDeclarations step declare (traverseDeclarations step declare lines)
      = traverseDeclarations step declare lines :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] =>
      let once: declare ((declare (line.traverseBody step)).traverseBody step) = declare (line.traverseBody step) :=
        rewrite settles.left (line.traverseBody step),
            settles.right ((line.traverseBody step).traverseBody step),
            declarationTraverseTwice step done fixes reaches line
      rewrite once, declarationsTraverseTwice step declare done fixes reaches settles rest

--| A traversal finishes in one run when its step leaves what it has done
--| alone and `declare` settles.
theorem traverseIdempotent ∀ (step: Position → Expr → Expr)
    (declare: Declaration → Declaration) (done: Position → Expr → Prop)
    (fixes: StepFixes step done)
    (reaches: StepReaches step done)
    (settles: DeclareSettles step declare) (file: SourceFile):
    (file.traverse step declare).traverse step declare = file.traverse step declare :=
  rewrite declarationsTraverseTwice step declare done fixes reaches settles file.declarations
