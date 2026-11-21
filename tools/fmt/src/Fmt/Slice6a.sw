--| Slice 6a of the proved formatter (docs/proposals/
--| self-hosted-fmt-proof-plan.md §1.2), on top of slices 1 to 5a, 4b and
--| 4c: the proof steps `rewrite` (its rules, `<-`, `at` and `then`
--| chains), `cases then t` and `cases x, y then t`, `byWalking [h] then t`,
--| `arithmetic [h]` and `algebra [h]`, and `↔`.
--|
--| `calc` is in too, its first expression one that can't hug.
--|
--| Left out: comments on a rule's `<-` and above a `calc` step's `:=`. A gap Rust copies that the tree can't say: the one after `<-`
--| (`<-h` against `<- h`), printed as a space.
--|
--| As in the earlier slices, the slice is a test on the real tree,
--| `within6a`, and a token alphabet, `Tok.within6a`, which `formatWithin`
--| checks before parsing.

namespace Fmt.Later
import Fmt (..)
import Std (Bool, Doc, List, Nat, Option, Result, Text)
import Syntax (
  Arm,
  BindingKind,
  CalcStep,
  Decl,
  DefBody,
  DefKind,
  Expr,
  FieldPattern,
  FieldsPattern,
  GroupKind,
  Guard,
  Header,
  InfixKind,
  Let,
  Param,
  Pattern,
  RewriteRule,
  Rules,
  SourceFile,
  Statement,
  Tok,
  Word,
  anyAbsurd,
  lex
)

-- The slice.

--| Whether the expression is one of slices 1 to 5a's, 4b's, 4c's and 6a's,
--| all the way down: as `within4c`, with `rewrite`, `cases` with names or
--| `then` or both, facts, walks (`byWalking [h] then t`) and `↔`.
def Expr.within6a: Expr → Bool
  | Atom kind word => kind.wordWithin6a || (kind == Str || kind == CharLit) && !word.text.contains "\n"
  | Paren _ inner _ => inner.within6a
  | Tuple _ items _ _ | ListOf _ items _ _ => allInline6a items
  | App head arguments => head.inline6a && allInline6a arguments
  | Infix InfixBinary left _ right | Infix InfixArrow left _ right => left.inline6a && right.within6a
  | Infix InfixMembership left _ right => left.inline6a && right.inline6a
  | Prefix operator operand => operand.inline6a && !(operator.text == "-" && operand.numeralField)
  | Binding BindsLambda None params _ body => !params.isEmpty && paramsWithin6a params && body.within6a
  | Binding BindsForall (Some _) params _ body | Binding BindsExists (Some _) params _ body =>
    !params.isEmpty && paramsWithin6a params && body.inline6a
  | Block first rest result =>
    first.within6a && statementsWithin6a rest && result.inline6a && laterLinesPlain rest result
  | LetIn binding _ body => binding.within6a && keepsLine binding.value && body.within6a
  | If _ None condition _ whenTrue _ whenFalse => condition.inline6a && whenTrue.within6a && whenFalse.within6a
  | Match _ scrutinees _ arms => !arms.isEmpty && scrutineesWithin6a scrutinees && armsWithin6a arms
  | FieldAccess (Some target) _ _ => target.inline6a && !target.trails
  | NamedArg _ _ _ value _ => value.inline6a
  | Annotation _ value _ annotation _ => value.inline6a && annotation.inline6a
  | Spread dots list => !dots.trails && list.spreadStart && list.inline6a
  | Record _ base fields _ _ => !fields.isEmpty && baseWithin6a base && fieldsWithin6a fields
  | CtorFields (Atom Upper ctor) record => !ctor.trails && record.isRecord && record.within6a
  | Infix InfixIff left _ right => left.inline6a && right.within6a
  | Facts _ _ facts => facts.inline6a
  | Cases _ _ body => afterWithin6a True body
  | Walk _ items body => items.inline6a && afterWithin6a True body
  | Rewrite _ (RuleList rules) target body | Rewrite _ (Repeatedly _ { rules, .. }) target body =>
    !rules.isEmpty && rulesWithin6a rules && afterWithin6a False target && afterWithin6a True body
  | Calc _ first steps => first.inline6a && first.hugsNowhere && !steps.isEmpty && stepsWithin6a steps
  | _ => False

--| Whether no call in the expression could hug its last argument; a
--| `calc`'s first expression never hugs, which `calcDoc` leaves to the
--| slice. Anything but names, calls, operators, brackets and fields is
--| kept out.
def Expr.hugsNowhere: Expr → Bool
  | Atom _ _ => True
  | Paren _ inner _ => inner.hugsNowhere
  | App head arguments => head.hugsNowhere && argumentsHugNowhere arguments
  | Infix _ left _ right => left.hugsNowhere && right.hugsNowhere
  | Prefix _ operand | FieldAccess (Some operand) _ _ => operand.hugsNowhere
  | _ => False

--| Each argument hugs nowhere, and the last can't hug: no tuple, list or
--| record (a lambda or block in brackets is no `hugsNowhere` already).
def argumentsHugNowhere: List Expr → Bool
  | [] => True
  | [last] => last.hugsNowhere
  | [argument, ..rest] => argument.hugsNowhere && argumentsHugNowhere rest

--| A `calc`'s steps: no comment above a `:=`.
def stepsWithin6a: List CalcStep → Bool
  | [] => True
  | [{ operand, proof = None, .. }, ..rest] => operand.inline6a && stepsWithin6a rest
  | [{ operand, proof = Some (colonEq, value), .. }, ..rest] =>
    operand.inline6a && colonEq.above.isEmpty && value.within6a && stepsWithin6a rest

--| A `rewrite`'s rules: each an expression, `<-` with no comments.
def rulesWithin6a: List RewriteRule → Bool
  | [] => True
  | [{ reverse = None, rule }, ..rest] => rule.inline6a && rulesWithin6a rest
  | [{ reverse = Some (less, minus), rule }, ..rest] =>
    less.above.isEmpty
      && less.after.isNone
      && minus.above.isEmpty
      && minus.after.isNone
      && rule.inline6a
      && rulesWithin6a rest

--| What follows `at` (inline) or `then` (a block too), if there.
def afterWithin6a (block: Bool): Option (Syntax.Comments, Expr) → Bool
  | None => True
  | Some (_, value) => if block then value.within6a else value.inline6a

--| A token alone: slice 2's, and `arithmetic`, `algebra` and `cases`
--| with nothing after them.
def Tok.wordWithin6a (kind: Tok): Bool :=
  kind.wordWithin2 || kind == KwArithmetic || kind == KwAlgebra || kind == KwCases

--| Within slice 6a, and not a block.
def Expr.inline6a (expr: Expr): Bool := expr.within6a && !expr.isBlock

def allInline6a: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.inline6a && allInline6a rest

--| An update's record, with no comment after it (Rust prints that one
--| after the `|`).
def baseWithin6a: Option (Expr, Word) → Bool
  | None => True
  | Some (record, _) => record.inline6a && !record.trails

--| A record's fields: `name = value`, or a name alone (punned).
def fieldsWithin6a: List Expr → Bool
  | [] => True
  | [RecordField _ _ value, ..rest] => value.inline6a && fieldsWithin6a rest
  | [Atom Lower _, ..rest] => fieldsWithin6a rest
  | [_, .._] => False

def Statement.within6a: Statement → Bool
  | LetStatement binding => binding.within6a
  | ExprStatement value => value.inline6a
  | _ => False

def statementsWithin6a: List Statement → Bool
  | [] => True
  | [statement, ..rest] => statement.within6a && statementsWithin6a rest

def Let.within6a (binding: Let): Bool := match binding with
  | { pattern, annotation = Some (_, annotation), value, .. } =>
    pattern.within6a && annotation.inline6a && value.within6a
  | { pattern, annotation = None, value, .. } => pattern.within6a && value.within6a

def scrutineesWithin6a: List Syntax.Scrutinee → Bool
  | [] => True
  | [{ name = None, value }, ..rest] => value.inline6a && scrutineesWithin6a rest
  | [_, .._] => False

def armsWithin6a: List Arm → Bool
  | [] => True
  | [arm, ..rest] => arm.within6a && armsWithin6a rest

--| An arm with a body, or an absurd one with none.
def Arm.within6a (arm: Arm): Bool := match arm with
  | { patterns, guard, body = Some (_, body), .. } =>
    !patterns.isEmpty && patternsWithin6a patterns && guardWithin6a guard && body.within6a
  | { patterns, guard, body = None, .. } =>
    !patterns.isEmpty && patternsWithin6a patterns && guardWithin6a guard && anyAbsurd patterns

def guardWithin6a: Option Guard → Bool
  | Some { binder = None, condition, .. } => condition.inline6a
  | Some _ => False
  | None => True

--| A pattern of slices 3, 4b and 4c: as `within4c`.
def Pattern.within6a: Pattern → Bool
  | PatternWord kind word => kind.patternWord4b word
  | PatternCtor _ arguments => !arguments.isEmpty && argumentsWithin6a arguments
  | PatternParen _ inner _ => inner.within6a
  | PatternAbsurd _ _ => True
  | PatternTuple _ items False _ => !items.isEmpty && patternsWithin6a items
  | PatternList _ items False tail _ => patternsWithin6a items && tailWithin6a tail
  | PatternRecord fields => fields.within6a
  | PatternCtorFields name fields => fields.within6a && !([name, ..fields.words].any Word.commented)
  | _ => False

def patternsWithin6a: List Pattern → Bool
  | [] => True
  | [pattern, ..rest] => pattern.within6a && patternsWithin6a rest

--| A constructor's arguments: as `argumentsWithin4c`.
def argumentsWithin6a: List Pattern → Bool
  | [] => True
  | [PatternAbsurd _ _, .._] | [PatternCtor _ _, .._] => False
  | [pattern, ..rest] => pattern.within6a && argumentsWithin6a rest

def tailWithin6a: Option (Word, Pattern) → Bool
  | None => True
  | Some (dots, rest) => !dots.noted && !dots.trails && rest.tailStart && rest.within6a

--| A record pattern with a field or a `..` (Rust copies the gap of `{}`).
def FieldsPattern.within6a (fields: FieldsPattern): Bool := match fields with
  | { fields = items, rest, trailingComma = False, .. } =>
    (!items.isEmpty || rest.isSome) && fieldPatternsWithin6a items
  | _ => False

def fieldPatternsWithin6a: List FieldPattern → Bool
  | [] => True
  | [{ value = Some (_, pattern), .. }, ..rest] => pattern.within6a && fieldPatternsWithin6a rest
  | [{ value = None, .. }, ..rest] => fieldPatternsWithin6a rest

--| A binder's parameters: names, `_`, and typed groups.
def paramsWithin6a: List Param → Bool
  | [] => True
  | [NameParam _, ..rest] | [PatternParam (PatternWord _ _), ..rest] => paramsWithin6a rest
  | [Grouped group, ..rest] => groupWithin6a GroupLambda group && paramsWithin6a rest
  | [_, ..rest] => False

def groupWithin6a (kind: GroupKind) (group: Syntax.Group): Bool := match group with
  | { attributes = [], auto = None, colon = Some _, annotation = Some annotation, default = None, .. } =>
    group.kind == kind && !group.names.isEmpty && annotation.inline6a
  | _ => False

def resultWithin6a: Expr → Bool
  | Effect ({ abilities, variable = None, .. }) result => !abilities.isEmpty && allWithin2 abilities && result.inline6a
  | result => result.inline6a

--| As `within4c`.
def Header.within6a (header: Header): Bool := match header with
  | {
      exportKeyword = None,
      opaqueKeyword = None,
      kind,
      params,
      result,
      decreasingClause = None,
      unfoldingClause = None,
      ..
    } => kind != DefInstance && params.all (groupWithin6a GroupParam) && resultWithin6a result
  | _ => False

--| A definition with a body or arms, a namespace line, an import, or a
--| test.
def Decl.within6a: Decl → Bool
  | Definition [] header (Assigned _ value) => header.within6a && value.within6a
  | Definition [] header (Arms arms) => header.within6a && !arms.isEmpty && armsWithin6a arms
  | Namespace _ _ | Import _ _ _ _ _ => True
  | Test _ name _ body => !name.text.contains "\n" && body.within6a
  | _ => False

def SourceFile.within6a (file: SourceFile): Bool := file.decls.all Decl.within6a

--| Slice 6a's tokens: slice 4c's, `rewrite`, `cases`, `calc`,
--| `arithmetic`, `algebra` and `↔`.
def Tok.within6a: Tok → Bool
  | KwRewrite | KwCases | KwCalc | KwByWalking | KwArithmetic | KwAlgebra | IffArrow => True
  | kind => kind.within4c

-- Printing.

--| A declaration printed in 120 columns, if it is within slices 1 to 5a,
--| 4b, 4c and 6a.
def Decl.printed6a (decl: Decl): Option Text :=
  if decl.within6a then decl.doc5a.map (doc => Doc.print doc width) else None

def SourceFile.printed6a (file: SourceFile): Text := file.printedBy Decl.printed6a

--| The source formatted, if it is within slices 1 to 5a, 4b, 4c and 6a: lexed,
--| refused if a token is outside the alphabet, then parsed, tidied and
--| printed as `format` does.
def formatWithin (source: Text): Result Text Text := match lex source with
  | Err message => Err message
  | Ok lexed =>
    match lexed.leaves.find (leaf => !leaf.token.kind.within6a) with
      | Some leaf => Err "outside slice 6a: `${leaf.token.text}`"
      | None =>
        match lexed.tidied with
          | Err message => Err message
          | Ok tidied =>
            if tidied.fourth.within6a then Ok tidied.fourth.printed6a
            else Err "outside slice 6a: a construct slices 1 to 5a, 4b, 4c and 6a don't have"
