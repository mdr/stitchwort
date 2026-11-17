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

--| By induction on the expression: the step clears the node's own flag,
--| and each child was traversed first.
theorem exprCommasNone ∀ (expr: Expr) (position: Position): NoTrailingCommas (expr.traverse dropComma position) :=
  match expr with
    | Var _ _ => byComputing
    | NumberLiteral _ _ => byComputing
    | StringLiteral _ _ => byComputing
    | Bracketed _ inner _ => exprCommasNone inner { bracketed = True, slot = Whole }
    | ListLiteral _ items _ _ => (byComputing, itemsCommasNone items)
    | Call callee _ arguments _ _ => (
      byComputing,
      exprCommasNone callee { bracketed = position.bracketed, slot = PostfixSlot },
      itemsCommasNone arguments
    )
    | Field target _ _ _ => exprCommasNone target { bracketed = position.bracketed, slot = PostfixSlot }
    | Negate _ operand => exprCommasNone operand { bracketed = position.bracketed, slot = OperandSlot }
    | Binary operator _ left right => (
      exprCommasNone left { bracketed = position.bracketed, slot = LeftOf operator.level },
      exprCommasNone right { bracketed = position.bracketed, slot = RightOf operator.level }
    )
    | If _ condition _ whenTrue _ whenFalse => (
      exprCommasNone condition { bracketed = position.bracketed, slot = Whole },
      bodyCommasNone whenTrue position.bracketed,
      bodyCommasNone whenFalse position.bracketed
    )

theorem itemsCommasNone ∀ (items: List Expr): NoTrailingCommasItems (traverseItems dropComma items) := match items with
  | [] => byComputing
  | [value, ..rest] => (exprCommasNone value { bracketed = True, slot = Whole }, itemsCommasNone rest)

theorem bodyCommasNone ∀ (body: Body) (bracketed: Bool): NoTrailingCommasBody (body.traverse dropComma bracketed) :=
  match body with | { statements } => linesCommasNone statements bracketed

theorem linesCommasNone ∀ (lines: List (Spaced Statement)) (bracketed: Bool):
    NoTrailingCommasLines (traverseLines dropComma bracketed lines) :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => (statementCommasNone line bracketed, linesCommasNone rest bracketed)

theorem statementCommasNone ∀ (line: Statement) (bracketed: Bool):
    NoTrailingCommasStatement (line.traverse dropComma bracketed) :=
  match line with
    | Let _ _ _ _ body => bodyCommasNone body False
    | Bare value => exprCommasNone value { bracketed, slot = Whole }
    | StatementNote _ => byComputing

theorem declarationsCommasNone ∀ (lines: List (Spaced Declaration)):
    NoTrailingCommasDeclarations (traverseDeclarations dropComma (line => line.withoutTrailingComma) lines) :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line = Function _ _ _ _ _ _ _ _ _ body }, ..rest] =>
      ((byComputing, bodyCommasNone body False), declarationsCommasNone rest)
    | [{ blankBefore, line = Value _ _ _ _ body }, ..rest] => (bodyCommasNone body False, declarationsCommasNone rest)
    | [{ blankBefore, line = DeclarationNote _ }, ..rest] => (byComputing, declarationsCommasNone rest)

--| P2's result has no trailing comma.
theorem commasNone ∀ (file: SourceFile): NoTrailingCommasFile file.withoutTrailingCommas :=
  declarationsCommasNone file.declarations

--| By induction on the expression: each child is left alone, and the
--| node's flag is already `False`, so the step changes nothing.
theorem exprCommasFixed ∀ (expr: Expr) (position: Position)
    (none: NoTrailingCommas expr):
    expr.traverse dropComma position = expr :=
  match expr, none with
    | Var _ _, _ => byComputing
    | NumberLiteral _ _, _ => byComputing
    | StringLiteral _ _, _ => byComputing
    | Bracketed _ inner _, none => rewrite exprCommasFixed inner { bracketed = True, slot = Whole } none
    | ListLiteral _ items _ _, (unwritten, itemsNone) => rewrite itemsCommasFixed items itemsNone, unwritten
    | Call callee _ arguments _ _, (unwritten, calleeNone, argumentsNone) =>
      rewrite exprCommasFixed callee { bracketed = position.bracketed, slot = PostfixSlot } calleeNone,
          itemsCommasFixed arguments argumentsNone,
          unwritten
    | Field target _ _ _, none =>
      rewrite exprCommasFixed target { bracketed = position.bracketed, slot = PostfixSlot } none
    | Negate _ operand, none =>
      rewrite exprCommasFixed operand { bracketed = position.bracketed, slot = OperandSlot } none
    | Binary operator _ left right, (leftNone, rightNone) =>
      rewrite exprCommasFixed left { bracketed = position.bracketed, slot = LeftOf operator.level } leftNone,
          exprCommasFixed right { bracketed = position.bracketed, slot = RightOf operator.level } rightNone
    | If _ condition _ whenTrue _ whenFalse, (conditionNone, trueNone, falseNone) =>
      rewrite exprCommasFixed condition { bracketed = position.bracketed, slot = Whole } conditionNone,
          bodyCommasFixed whenTrue position.bracketed trueNone,
          bodyCommasFixed whenFalse position.bracketed falseNone

theorem itemsCommasFixed ∀ (items: List Expr)
    (none: NoTrailingCommasItems items):
    traverseItems dropComma items = items :=
  match items, none with
    | [], _ => byComputing
    | [value, ..rest], (valueNone, restNone) =>
      rewrite exprCommasFixed value { bracketed = True, slot = Whole } valueNone, itemsCommasFixed rest restNone

theorem bodyCommasFixed ∀ (body: Body) (bracketed: Bool)
    (none: NoTrailingCommasBody body):
    body.traverse dropComma bracketed = body :=
  match body, none with | { statements }, none => rewrite linesCommasFixed statements bracketed none

theorem linesCommasFixed ∀ (lines: List (Spaced Statement)) (bracketed: Bool)
    (none: NoTrailingCommasLines lines):
    traverseLines dropComma bracketed lines = lines :=
  match lines, none with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineNone, restNone) =>
      rewrite statementCommasFixed line bracketed lineNone, linesCommasFixed rest bracketed restNone

theorem statementCommasFixed ∀ (line: Statement) (bracketed: Bool)
    (none: NoTrailingCommasStatement line):
    line.traverse dropComma bracketed = line :=
  match line, none with
    | Let _ _ _ _ body, none => rewrite bodyCommasFixed body False none
    | Bare value, none => rewrite exprCommasFixed value { bracketed, slot = Whole } none
    | StatementNote _, _ => byComputing

theorem declarationsCommasFixed ∀ (lines: List (Spaced Declaration))
    (none: NoTrailingCommasDeclarations lines):
    traverseDeclarations dropComma (line => line.withoutTrailingComma) lines = lines :=
  match lines, none with
    | [], _ => byComputing
    | [{ blankBefore, line = Function _ _ _ _ _ _ _ _ _ body }, ..rest], ((unwritten, bodyNone), restNone) =>
      rewrite bodyCommasFixed body False bodyNone, unwritten, declarationsCommasFixed rest restNone
    | [{ blankBefore, line = Value _ _ _ _ body }, ..rest], (bodyNone, restNone) =>
      rewrite bodyCommasFixed body False bodyNone, declarationsCommasFixed rest restNone
    | [{ blankBefore, line = DeclarationNote _ }, ..rest], (_, restNone) =>
      rewrite declarationsCommasFixed rest restNone

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

-- P2's step and `declare` keep, at one node, what the traversal's lemmas
-- ask: they change only a flag that nothing but `NoTrailingCommas`
-- reads.

theorem dropCommaPlain: StepKeepsPlain dropComma := position expr => cases

--| A list or call keeps its form, and so the slots it fits, without its
--| trailing comma.
theorem dropCommaFits ∀ (position: Position) (expr: Expr) (slot: Slot):
    (dropComma position expr).fits slot = expr.fits slot :=
  cases

theorem dropCommaShaped: StepKeepsShaped dropComma := position expr shaped =>
  match expr, shaped with
    | Var _ _, shaped => (shaped, (ends => ends))
    | NumberLiteral _ _, shaped => (shaped, (ends => ends))
    | StringLiteral _ _, shaped => (shaped, (ends => ends))
    | Bracketed _ _ _, shaped => (shaped, (ends => ends))
    | ListLiteral _ _ _ _, (shaped, fits) =>
      ((shaped, (rewrite dropCommaFits position expr position.slot then fits)), (ends => ends))
    | Call _ _ _ _ _, (shaped, fits) =>
      ((shaped, (rewrite dropCommaFits position expr position.slot then fits)), (ends => ends))
    | Field _ _ _ _, shaped => (shaped, (ends => ends))
    | Negate _ _, shaped => (shaped, (ends => ends))
    | Binary _ _ _ _, shaped => (shaped, (ends => ends))
    | If _ _ _ _ _ _, shaped => (shaped, (ends => ends))

theorem dropCommaLexical: StepKeepsLexical dropComma := position expr lexical =>
  match expr, lexical with
    | Var _ _, lexical => lexical
    | NumberLiteral _ _, lexical => lexical
    | StringLiteral _ _, lexical => lexical
    | Bracketed _ _ _, lexical => lexical
    | ListLiteral _ _ _ _, lexical => lexical
    | Call _ _ _ _ _, lexical => lexical
    | Field _ _ _ _, lexical => lexical
    | Negate _ _, lexical => lexical
    | Binary _ _ _ _, lexical => lexical
    | If _ _ _ _ _ _, lexical => lexical

theorem dropCommaHeaded: StepKeepsHeaded dropComma := position expr headed =>
  match expr, headed with
    | Var _ _, headed => (headed, byComputing)
    | NumberLiteral _ _, headed => (headed, byComputing)
    | StringLiteral _ _, headed => (headed, byComputing)
    | Bracketed _ _ _, headed => (headed, byComputing)
    | ListLiteral _ _ _ _, headed => (headed, byComputing)
    | Call _ _ _ _ _, headed => (headed, byComputing)
    | Field _ _ _ _, headed => (headed, byComputing)
    | Negate _ _, headed => (headed, byComputing)
    | Binary _ _ _ _, headed => (headed, byComputing)
    | If _ _ _ _ _ _, headed => (headed, byComputing)

theorem declareCommaPlain ∀ (line: Declaration): line.withoutTrailingComma.plain = line.plain := cases

theorem declareCommaParsed: DeclareKeepsParsed (line => line.withoutTrailingComma) := line shaped lexical headed =>
  match line with
    | Function _ _ _ _ _ _ _ _ _ _ => (shaped, lexical, headed)
    | Value _ _ _ _ _ => (shaped, lexical, headed)
    | DeclarationNote _ => (shaped, lexical, headed)

--| P2 keeps the parser's guarantees: what each says of a tree, dropping
--| a trailing comma doesn't change.
theorem commasKeepParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withoutTrailingCommas :=
  traverseKeepsParsed dropComma
    (line => line.withoutTrailingComma)
    dropCommaShaped
    dropCommaLexical
    dropCommaHeaded
    declareCommaParsed
    file
    parsed

--| P2 keeps the meaning, on every tree: `plain` sets every trailing
--| comma's flag to `False` already.
theorem commasKeepMeaning ∀ (file: SourceFile): file.withoutTrailingCommas.meaning = file.meaning :=
  traverseKeepsMeaning dropComma (line => line.withoutTrailingComma) dropCommaPlain declareCommaPlain file

-- P1: `takes` on every function with parameters.

theorem takesForPlain ∀ (takes: Option Comments) (parameters: List ParameterGroup):
    (takesFor takes parameters).getOrElse Comments.none = takes.getOrElse Comments.none := cases

theorem takesForTwice ∀ (takes: Option Comments) (parameters: List ParameterGroup):
    takesFor (takesFor takes parameters) parameters = takesFor takes parameters := cases

theorem takesForFine ∀ (takes: Option Comments) (parameters: List ParameterGroup)
    (fine: FineTakes takes):
    FineTakes (takesFor takes parameters) :=
  match parameters, takes, fine with
    | [], _, fine => fine
    | [_, .._], None, _ => fineNone
    | [_, .._], Some comments, fine => fine

theorem declarationTakesPlain ∀ (line: Declaration): line.withTakes.plain = line.plain := match line with
  | Function _ _ _ takes _ parameters _ _ _ _ => rewrite takesForPlain takes parameters
  | _ => cases

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
  | _ => cases

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
    (line.traverseBody dropComma).withoutTrailingComma.withTakes
      = line.withTakes.traverseBody dropComma |>.withoutTrailingComma :=
  cases

theorem declarationsTakesCommas ∀ (lines: List (Spaced Declaration)):
    declarationsWithTakes (traverseDeclarations dropComma (line => line.withoutTrailingComma) lines)
      = traverseDeclarations dropComma (line => line.withoutTrailingComma) (declarationsWithTakes lines) :=
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
  _ = file.withTakes.withoutTrailingCommas.withoutSpareBrackets.meaning :=
    mergeKeepMeaning file.withTakes.withoutTrailingCommas.withoutSpareBrackets
  _ = file.withTakes.withoutTrailingCommas.meaning := bracketsKeepMeaning file.withTakes.withoutTrailingCommas
  _ = file.withTakes.meaning := commasKeepMeaning file.withTakes
  _ = file.meaning := takesKeepMeaning file

--| The passes keep the parser's guarantees.
theorem tidyParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.tidy :=
  mergeKeepParsed file.withTakes.withoutTrailingCommas.withoutSpareBrackets
    (bracketsKeepParsed file.withTakes.withoutTrailingCommas
      (commasKeepParsed file.withTakes (takesKeepParsed file parsed)))

--| A tidy tree has no trailing comma, as the printer needs: P3 and P4
--| kept P2's work.
theorem tidyBare ∀ (file: SourceFile): file.tidy.withoutTrailingCommas = file.tidy :=
  mergeKeepCommas file.withTakes.withoutTrailingCommas.withoutSpareBrackets
    (bracketsKeepCommas file.withTakes.withoutTrailingCommas (commasIdempotent file.withTakes))

--| A tidy tree is P1-tidy too: P2, P3 and P4 kept P1's work.
theorem tidyTakes ∀ (file: SourceFile): file.tidy.withTakes = file.tidy :=
  mergeKeepTakes file.withTakes.withoutTrailingCommas.withoutSpareBrackets
    (bracketsKeepTakes file.withTakes.withoutTrailingCommas (commasKeepTakes file.withTakes (takesIdempotent file)))

--| A tidy tree has no spare brackets: P4 kept P3's work.
theorem tidyBrackets ∀ (file: SourceFile): file.tidy.withoutSpareBrackets = file.tidy :=
  mergeKeepBrackets file.withTakes.withoutTrailingCommas.withoutSpareBrackets
    (bracketsIdempotent file.withTakes.withoutTrailingCommas)

--| A tidy tree has no parameter groups left to merge.
theorem tidyMerged ∀ (file: SourceFile): file.tidy.withMergedParameters = file.tidy :=
  mergeIdempotent file.withTakes.withoutTrailingCommas.withoutSpareBrackets

--| The passes finish in one run: a tidy tree is tidy for each pass.
theorem tidyIdempotent ∀ (file: SourceFile): file.tidy.tidy = file.tidy := calc file.tidy.tidy
  _ = file.tidy.withTakes.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters := byComputing
  _ = file.tidy.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters :=
    Eq.cong
      ((tree: SourceFile) => tree.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters)
      (tidyTakes file)
  _ = file.tidy.withoutSpareBrackets.withMergedParameters :=
    Eq.cong ((tree: SourceFile) => tree.withoutSpareBrackets.withMergedParameters) (tidyBare file)
  _ = file.tidy.withMergedParameters := Eq.cong ((tree: SourceFile) => tree.withMergedParameters) (tidyBrackets file)
  _ = file.tidy := tidyMerged file
