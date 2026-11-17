--| P3, spare brackets dropped: its family (toy-plus-plus.md §3.2), from
--| its step's one-node facts and `TraverseProofs.sw`.
--|
--| The content is `dropShaped`, the precedence argument: a pair is
--| dropped only where its content is read as it stands (`spare`, through
--| `Expr.fits`), so the tree keeps the parser's shape, and with
--| `printParses` the printed text reads back as the tree with the pair
--| gone. Outside brackets the content must also read the same
--| (`standsOutsideHeaded`): there an own-line comment above a branch's
--| first statement would start a block.

namespace Toy.Fmt.Proofs
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, Eq, List, NonEmptyList, Nat, Option, Text)

-- A token that holds no comment.

theorem noneAbove ∀ (comments: Comments) (none: comments.isNone = True): comments.above = [] :=
  match comments, none with | { above = [], after = None }, _ => byComputing

theorem noneAfter ∀ (comments: Comments) (none: comments.isNone = True): comments.after.isSome = False :=
  match comments, none with | { above = [], after = None }, _ => byComputing

--| What a spare pair's test says, part by part.
theorem spareParts ∀ (position: Position) (open: Comments) (inner: Expr) (close: Comments)
    (isSpare: spare position open inner close = True):
    open.isNone = True
      ∧ close.isNone = True
      ∧ inner.firstAbove.isEmpty = True
      ∧ inner.fits position.slot = True
      ∧ (position.bracketed || inner.standsOutside) = True :=
  let (openNone, rest) := isSpare.read
  let (closeNone, rest1) := rest.read
  let (noAbove, rest2) := rest1.read
  let (fits, outside) := rest2.read
  (openNone, closeNone, noAbove, fits, outside)

-- The step keeps the meaning: `plain` forgets a pair with no comments.

--| A pair the step drops has no comments, and `plain` forgets such a
--| pair; every other node is left as it is.
theorem dropPlain: StepKeepsPlain dropPair := position expr =>
  match expr with
    | Bracketed open inner close =>
      match isSpare: spare position open inner close with
        | True =>
          let (openNone, closeNone, _) := spareParts position open inner close isSpare
          rewrite openNone, closeNone
        | False => byComputing
    | _ => cases

-- The step keeps the parser's shape: the precedence argument. A pair is
-- dropped only where its content fits the pair's slot, and a pair with
-- no comments has none on its `)` for a closer outside it to rely on.

--| A dropped pair's content is `Shaped` (it was inside the pair) and fits
--| the slot (`spare` asks it); the pair's `)` held no comment, so no
--| trailing comment is lost for a closer outside to rely on.
theorem dropShaped: StepKeepsShaped dropPair := position expr shaped =>
  match expr, shaped with
    | Bracketed open inner close, ((innerShaped, settled), fits) =>
      match isSpare: spare position open inner close with
        | True =>
          let (_, closeNone, _, innerFits, _) := spareParts position open inner close isSpare
          let noComment: close.after.isSome = False := noneAfter close closeNone
          ((innerShaped, innerFits), (ends => (Bool.falseNotTrue (rewrite noComment at ends then ends)).impossible))
        | False => (((innerShaped, settled), fits), (ends => ends))
    | Var _ _, shaped => (shaped, (ends => ends))
    | NumberLiteral _ _, shaped => (shaped, (ends => ends))
    | StringLiteral _ _, shaped => (shaped, (ends => ends))
    | ListLiteral _ _ _ _, shaped => (shaped, (ends => ends))
    | Call _ _ _ _ _, shaped => (shaped, (ends => ends))
    | Field _ _ _ _, shaped => (shaped, (ends => ends))
    | Negate _ _, shaped => (shaped, (ends => ends))
    | Binary _ _ _ _, shaped => (shaped, (ends => ends))
    | If _ _ _ _ _ _, shaped => (shaped, (ends => ends))

-- The step keeps where comments and blocks are. Inside brackets an
-- expression's bodies are one expression and its statements' first
-- tokens may hold own-line comments; `standsOutside` says there are
-- none, which is all `HeadedExpr` asks more outside brackets.

--| By induction on the expression: `HeadedExpr` differs inside and
--| outside brackets only at a branch's statements, whose first tokens
--| `standsOutside` says hold no own-line comments.
theorem standsOutsideHeaded ∀ (expr: Expr)
    (stands: expr.standsOutside = True)
    (headed: HeadedExpr True expr):
    HeadedExpr False expr :=
  match expr, headed with
    | Var _ _, headed => headed
    | NumberLiteral _ _, headed => headed
    | StringLiteral _ _, headed => headed
    | Bracketed _ _ _, headed => headed
    | ListLiteral _ _ _ _, headed => headed
    | Call callee _ _ _ _, (calleeHeaded, argumentsHeaded) =>
      (standsOutsideHeaded callee stands calleeHeaded, argumentsHeaded)
    | Field target _ _ _, headed => standsOutsideHeaded target stands headed
    | Negate _ operand, headed => standsOutsideHeaded operand stands headed
    | Binary _ _ left right, (leftHeaded, rightHeaded) =>
      let (leftStands, rightStands) := stands.read
      (standsOutsideHeaded left leftStands leftHeaded, standsOutsideHeaded right rightStands rightHeaded)
    | If _ condition _ whenTrue _ whenFalse, (conditionHeaded, trueHeaded, falseHeaded) =>
      let (conditionStands, branches) := stands.read
      let (trueStands, falseStands) := branches.read
      (
        standsOutsideHeaded condition conditionStands conditionHeaded,
        bodyOutsideHeaded whenTrue trueStands trueHeaded,
        bodyOutsideHeaded whenFalse falseStands falseHeaded
      )

theorem bodyOutsideHeaded ∀ (body: Body)
    (stands: body.standsOutside = True)
    (headed: HeadedBody True body):
    HeadedBody False body :=
  match body, headed with
    | { statements }, (linesHeaded, unspaced, _) =>
      (linesOutsideHeaded statements stands linesHeaded, unspaced, (never => (Bool.falseNotTrue never).impossible))

theorem linesOutsideHeaded ∀ (lines: List (Spaced Statement))
    (stands: linesStandOutside lines = True)
    (headed: HeadedLines True lines):
    HeadedLines False lines :=
  match lines, headed with
    | [], _ => byComputing
    | [{ blankBefore, line }, ..rest], (lineHeaded, restHeaded) =>
      let (lineStands, restStands) := stands.read
      (statementOutsideHeaded line lineStands lineHeaded, linesOutsideHeaded rest restStands restHeaded)

theorem statementOutsideHeaded ∀ (line: Statement)
    (stands: line.standsOutside = True)
    (headed: HeadedStatement True line):
    HeadedStatement False line :=
  match line, headed with
    | Let _ _ _ _ _, headed => headed
    | Bare value, (_, valueHeaded) =>
      let (noAbove, valueStands) := stands.read
      (
        (outside => (List.isEmptyReads value.firstAbove).forward noAbove),
        standsOutsideHeaded value valueStands valueHeaded
      )
    | StatementNote _, _ => byComputing

--| A dropped pair's content was headed inside brackets; at a position
--| inside brackets that is enough, and outside them `standsOutside`
--| gives it (`standsOutsideHeaded`). The first token's comments are
--| none either way: the `(` held none and `spare` asks the content's
--| first token to hold none above it.
theorem dropHeaded: StepKeepsHeaded dropPair := position expr headed =>
  match expr with
    | Bracketed open inner close =>
      match isSpare: spare position open inner close with
        | True =>
          let (openNone, _, noAbove, _, outside) := spareParts position open inner close isSpare
          let innerAbove: inner.firstAbove = [] := (List.isEmptyReads inner.firstAbove).forward noAbove
          let headedThere: HeadedExpr position.bracketed inner := match bracketed: position.bracketed with
            | True => headed
            | False => standsOutsideHeaded inner outside headed
          (headedThere, (rewrite innerAbove, noneAbove open openNone))
        | False => (headed, byComputing)
    | Var _ _ => (headed, byComputing)
    | NumberLiteral _ _ => (headed, byComputing)
    | StringLiteral _ _ => (headed, byComputing)
    | ListLiteral _ _ _ _ => (headed, byComputing)
    | Call _ _ _ _ _ => (headed, byComputing)
    | Field _ _ _ _ => (headed, byComputing)
    | Negate _ _ => (headed, byComputing)
    | Binary _ _ _ _ => (headed, byComputing)
    | If _ _ _ _ _ _ => (headed, byComputing)

theorem dropLexical: StepKeepsLexical dropPair := position expr lexical =>
  match expr, lexical with
    | Bracketed open inner close, (openFine, innerLexical, closeFine) =>
      match isSpare: spare position open inner close with
        | True => innerLexical
        | False => (openFine, innerLexical, closeFine)
    | Var _ _, lexical => lexical
    | NumberLiteral _ _, lexical => lexical
    | StringLiteral _ _, lexical => lexical
    | ListLiteral _ _ _ _, lexical => lexical
    | Call _ _ _ _ _, lexical => lexical
    | Field _ _ _ _, lexical => lexical
    | Negate _ _, lexical => lexical
    | Binary _ _ _ _, lexical => lexical
    | If _ _ _ _ _ _, lexical => lexical

theorem dropCommas: StepKeepsCommas dropPair := position expr none =>
  match expr, none with
    | Bracketed open inner close, none =>
      match isSpare: spare position open inner close with
        | True => none
        | False => none
    | Var _ _, none => none
    | NumberLiteral _ _, none => none
    | StringLiteral _ _, none => none
    | ListLiteral _ _ _ _, none => none
    | Call _ _ _ _ _, none => none
    | Field _ _ _ _, none => none
    | Negate _ _, none => none
    | Binary _ _ _ _, none => none
    | If _ _ _ _ _ _, none => none

-- Done in one run. A node is done when it is not a spare pair where it
-- stands. A pair kept inside brackets as a whole expression held a
-- comment, so it is kept wherever it stands, and what was done inside
-- brackets is done outside: dropping a pair leaves its content done.

--| The node is not a pair that could go where it stands.
def pairKept (position: Position) (expr: Expr): Bool := match expr with
  | Bracketed open inner close => not (spare position open inner close)
  | _ => True

def NoSparePair (position: Position) (expr: Expr): Prop := pairKept position expr = True

theorem dropFixes: StepFixes dropPair NoSparePair := position expr kept =>
  match expr with
    | Bracketed open inner close =>
      match isSpare: spare position open inner close with
        | False => byComputing
    | _ => cases

--| A pair spare somewhere is spare inside brackets as a whole expression.
theorem spareWhole ∀ (position: Position) (open: Comments) (inner: Expr) (close: Comments)
    (kept: (not (spare { bracketed = True, slot = Whole } open inner close)) = True):
    (not (spare position open inner close)) = True :=
  match openNone: open.isNone with
    | False => byComputing
    | True =>
      match closeNone: close.isNone with
        | False => byComputing
        | True =>
          match noAbove: inner.firstAbove.isEmpty with
            | False => byComputing

theorem keptAnywhere ∀ (expr: Expr) (position: Position) (kept: NoSparePair { bracketed = True, slot = Whole } expr):
    NoSparePair position expr :=
  match expr with
    | Bracketed open inner close => spareWhole position open inner close kept
    | _ => cases

--| A pair kept inside brackets is kept outside them: `spare` asks more
--| outside (`standsOutside`), so by cases on the parts it asks for.
theorem keptOutside: DoneOutside NoSparePair := slot bracketed expr kept =>
  match expr with
    | Bracketed open inner close =>
      match bracketed with
        | True => kept
        | False =>
          match openNone: open.isNone with
            | False => byComputing
            | True =>
              match closeNone: close.isNone with
                | False => byComputing
                | True =>
                  match noAbove: inner.firstAbove.isEmpty with
                    | False => byComputing
                    | True =>
                      match fits: inner.fits slot with
                        | False => byComputing
    | _ => cases

--| A pair kept is done, and its content was done inside it. A pair dropped
--| leaves its content, done as a whole expression inside brackets, and
--| so done wherever it now stands (`keptAnywhere`, `insideOutside`).
theorem dropReaches: StepReaches dropPair NoSparePair := position expr inside =>
  match expr, inside with
    | Bracketed open inner close, inside =>
      match isSpare: spare position open inner close with
        | True => (
          keptAnywhere inner position inside.left,
          insideOutside NoSparePair keptOutside inner position.bracketed inside.right
        )
        | False => (Eq.cong (kept => not kept) isSpare, inside)
    | Var _ _, inside => (byComputing, inside)
    | NumberLiteral _ _, inside => (byComputing, inside)
    | StringLiteral _ _, inside => (byComputing, inside)
    | ListLiteral _ _ _ _, inside => (byComputing, inside)
    | Call _ _ _ _ _, inside => (byComputing, inside)
    | Field _ _ _ _, inside => (byComputing, inside)
    | Negate _ _, inside => (byComputing, inside)
    | Binary _ _ _ _, inside => (byComputing, inside)
    | If _ _ _ _ _ _, inside => (byComputing, inside)

-- Types: a pair with no comments always goes, so P3 on a type is
-- `plain` on it.

theorem typeSpareIsPlain ∀ (annotation: TypeExpr): annotation.withoutSpareBrackets = annotation.plain :=
  match annotation with
    | TypeName _ _ => byComputing
    | TypeBracketed _ inner _ => rewrite typeSpareIsPlain inner

theorem typePlainTwice ∀ (annotation: TypeExpr): annotation.plain.plain = annotation.plain := match annotation with
  | TypeName _ _ => byComputing
  | TypeBracketed open inner close =>
    match none: open.isNone && close.isNone with
      | True => typePlainTwice inner
      | False => rewrite typePlainTwice inner, none

theorem typeSparePlain ∀ (annotation: TypeExpr): annotation.withoutSpareBrackets.plain = annotation.plain :=
  rewrite typeSpareIsPlain annotation then typePlainTwice annotation

theorem typeSpareTwice ∀ (annotation: TypeExpr):
    annotation.withoutSpareBrackets.withoutSpareBrackets = annotation.withoutSpareBrackets :=
  rewrite typeSpareIsPlain annotation.withoutSpareBrackets, typeSpareIsPlain annotation then typePlainTwice annotation

theorem typeSpareShaped ∀ (annotation: TypeExpr)
    (shaped: ShapedType annotation):
    ShapedType annotation.withoutSpareBrackets
      ∧ (annotation.endsWithComment = True → annotation.withoutSpareBrackets.endsWithComment = True) :=
  match annotation, shaped with
    | TypeName _ _, shaped => (shaped, (ends => ends))
    | TypeBracketed open inner close, (innerShaped, settled) =>
      let (innerShaped1, innerEnd) := typeSpareShaped inner innerShaped
      match none: open.isNone && close.isNone with
        | True =>
          let noComment: close.after.isSome = False := noneAfter close none.read.right
          (innerShaped1, (ends => (Bool.falseNotTrue (rewrite noComment at ends then ends)).impossible))
        | False => ((innerShaped1, settledGrows _ _ close settled innerEnd), (ends => ends))

theorem typeSpareLexical ∀ (annotation: TypeExpr)
    (lexical: LexicalType annotation):
    LexicalType annotation.withoutSpareBrackets :=
  match annotation, lexical with
    | TypeName _ _, lexical => lexical
    | TypeBracketed open inner close, (openFine, innerLexical, closeFine) =>
      match none: open.isNone && close.isNone with
        | True => typeSpareLexical inner innerLexical
        | False => (openFine, typeSpareLexical inner innerLexical, closeFine)

theorem groupSparePlain ∀ (group: ParameterGroup): group.withoutSpareBrackets.plain = group.plain := match group with
  | Untyped _ => byComputing
  | Typed _ _ annotation => rewrite typeSparePlain annotation

theorem groupsSparePlain ∀ (groups: List ParameterGroup):
    plainGroups (groupsWithoutSpareBrackets groups) = plainGroups groups :=
  match groups with
    | [] => byComputing
    | [group, ..rest] => rewrite groupSparePlain group, groupsSparePlain rest

theorem groupsSpareTwice ∀ (groups: List ParameterGroup):
    groupsWithoutSpareBrackets (groupsWithoutSpareBrackets groups) = groupsWithoutSpareBrackets groups :=
  match groups with
    | [] => byComputing
    | [Untyped _, ..rest] => rewrite groupsSpareTwice rest
    | [Typed _ _ annotation, ..rest] => rewrite typeSpareTwice annotation, groupsSpareTwice rest

theorem groupSpareShaped ∀ (group: ParameterGroup)
    (shaped: ShapedGroup group):
    ShapedGroup group.withoutSpareBrackets
      ∧ (group.endsWithComment = True → group.withoutSpareBrackets.endsWithComment = True) :=
  match group, shaped with
    | Untyped _, shaped => (shaped, (ends => ends))
    | Typed _ _ annotation, shaped => typeSpareShaped annotation shaped

theorem groupsSpareShaped ∀ (open: Comments) (groups: List ParameterGroup)
    (shaped: ShapedGroups groups):
    ShapedGroups (groupsWithoutSpareBrackets groups)
      ∧ (groupsEndWithComment open groups = True
        → groupsEndWithComment open (groupsWithoutSpareBrackets groups) = True) :=
  match groups, shaped with
    | [], _ => (byComputing, (ends => ends))
    | [group], (groupShaped, _) =>
      let (groupShaped1, groupEnd) := groupSpareShaped group groupShaped
      ((groupShaped1, byComputing), groupEnd)
    | [group, second, ..rest], (groupShaped, restShaped) =>
      let (restShaped1, restEnd) := groupsSpareShaped open [second, ..rest] restShaped
      (((groupSpareShaped group groupShaped).left, restShaped1), restEnd)

theorem groupsSpareLexical ∀ (groups: List ParameterGroup)
    (lexical: LexicalParameters groups):
    LexicalParameters (groupsWithoutSpareBrackets groups) :=
  match groups, lexical with
    | [], _ => byComputing
    | [Untyped _, ..rest], (groupLexical, restLexical) => (groupLexical, groupsSpareLexical rest restLexical)
    | [Typed _ _ annotation, ..rest], ((head, tail, colon, annotationLexical), restLexical) =>
      ((head, tail, colon, typeSpareLexical annotation annotationLexical), groupsSpareLexical rest restLexical)

-- P3 on a declaration: its parameters' types.

theorem declareSparePlain ∀ (line: Declaration): line.withoutSpareTypeBrackets.plain = line.plain := match line with
  | Function _ _ _ _ _ parameters _ _ _ _ => rewrite groupsSparePlain parameters
  | Value _ _ _ _ _ => byComputing
  | DeclarationNote _ => byComputing

--| Only the parameters' types change: each keeps its shape and texts
--| (`groupsSpareShaped`, `groupsSpareLexical`), and the list's `)` stays
--| settled because the last token's trailing comment is kept.
theorem declareSpareParsed: DeclareKeepsParsed (line => line.withoutSpareTypeBrackets) := line shaped lexical headed =>
  match line, shaped, lexical with
    | Function _ _ _ _ open parameters _ close _ _, ((groupsShaped, settled), bodyShaped), (fnFine, isName, nameFine,
        takesFine, openFine, groupsLexical, closeFine, equalsFine, bodyLexical) =>
      let (groupsShaped1, groupsEnd) := groupsSpareShaped open parameters groupsShaped
      (
        ((groupsShaped1, settledGrows _ _ close settled groupsEnd), bodyShaped),
        (
          fnFine,
          isName,
          nameFine,
          takesFine,
          openFine,
          groupsSpareLexical parameters groupsLexical,
          closeFine,
          equalsFine,
          bodyLexical
        ),
        headed
      )
    | Value _ _ _ _ _, shaped, lexical => (shaped, lexical, headed)
    | DeclarationNote _, shaped, lexical => (shaped, lexical, headed)

theorem declareSpareCommas ∀ (line: Declaration)
    (none: NoTrailingCommasDeclaration line):
    NoTrailingCommasDeclaration line.withoutSpareTypeBrackets :=
  match line, none with
    | Function _ _ _ _ _ _ _ _ _ _, none => none
    | Value _ _ _ _ _, none => none
    | DeclarationNote _, none => none

theorem declareSpareSettles: DeclareSettles dropPair (line => line.withoutSpareTypeBrackets) := (
  (line =>
    match line with
      | Function _ _ _ _ _ _ _ _ _ _ => byComputing
      | Value _ _ _ _ _ => byComputing
      | DeclarationNote _ => byComputing),
  (line =>
    match line with
      | Function _ _ _ _ _ parameters _ _ _ _ => rewrite groupsSpareTwice parameters
      | Value _ _ _ _ _ => byComputing
      | DeclarationNote _ => byComputing)
)

-- P3's family.

--| P3 keeps the meaning, on every tree: `plain` forgets every pair with
--| no comments.
theorem bracketsKeepMeaning ∀ (file: SourceFile): file.withoutSpareBrackets.meaning = file.meaning :=
  traverseKeepsMeaning dropPair (line => line.withoutSpareTypeBrackets) dropPlain declareSparePlain file

--| P3 keeps the parser's guarantees: a pair goes only where its content
--| is read as it stands (precedence), and reads the same outside
--| brackets.
theorem bracketsKeepParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withoutSpareBrackets :=
  traverseKeepsParsed dropPair
    (line => line.withoutSpareTypeBrackets)
    dropShaped
    dropLexical
    dropHeaded
    declareSpareParsed
    file
    parsed

--| P3 finishes in one run: nested pairs go together, the inner first.
theorem bracketsIdempotent ∀ (file: SourceFile):
    file.withoutSpareBrackets.withoutSpareBrackets = file.withoutSpareBrackets :=
  traverseIdempotent dropPair
    (line => line.withoutSpareTypeBrackets)
    NoSparePair
    dropFixes
    dropReaches
    declareSpareSettles
    file

--| P3 keeps P2's work: dropping a pair adds no trailing comma.
theorem bracketsKeepCommas ∀ (file: SourceFile)
    (tidy: file.withoutTrailingCommas = file):
    file.withoutSpareBrackets.withoutTrailingCommas = file.withoutSpareBrackets :=
  commasFixed file.withoutSpareBrackets
    (traverseKeepsCommas dropPair
      (line => line.withoutSpareTypeBrackets)
      dropCommas
      declareSpareCommas
      file
      (commasTidyNone file tidy))

theorem declarationTakesBrackets ∀ (line: Declaration):
    (line.traverseBody dropPair).withoutSpareTypeBrackets.withTakes
      = line.withTakes.traverseBody dropPair |>.withoutSpareTypeBrackets :=
  cases

theorem declarationsTakesBrackets ∀ (lines: List (Spaced Declaration)):
    declarationsWithTakes (traverseDeclarations dropPair (line => line.withoutSpareTypeBrackets) lines)
      = traverseDeclarations dropPair (line => line.withoutSpareTypeBrackets) (declarationsWithTakes lines) :=
  match lines with
    | [] => byComputing
    | [{ blankBefore, line }, ..rest] => rewrite declarationTakesBrackets line, declarationsTakesBrackets rest

--| P1 and P3 commute: P3 keeps whether a function has parameters.
theorem takesBracketsCommute ∀ (file: SourceFile):
    file.withoutSpareBrackets.withTakes = file.withTakes.withoutSpareBrackets :=
  rewrite declarationsTakesBrackets file.declarations

--| P3 keeps P1's work.
theorem bracketsKeepTakes ∀ (file: SourceFile)
    (tidy: file.withTakes = file):
    file.withoutSpareBrackets.withTakes = file.withoutSpareBrackets :=
  rewrite takesBracketsCommute file, tidy
