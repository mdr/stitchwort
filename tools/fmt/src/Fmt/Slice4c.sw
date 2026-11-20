--| Slice 4c of the proved formatter (docs/proposals/
--| self-hosted-fmt-proof-plan.md §1.2, the records of S4), on top of
--| slices 1 to 5a and 4b: record literals `{ a = 1, b }`, updates
--| `{ r | a = 1 }`, a constructor's named fields `C { a = 1 }`, a list's
--| spread `[x, ..xs]`, record patterns `{ a, b = p, .. }` and `C { a, .. }`,
--| and membership `x ∈ s`.
--|
--| Left out: the empty record `{}` (Rust copies the gap between the
--| braces), a spread whose list starts with anything but a name or a
--| bracket (Rust copies the gap after `..`, as for patterns), comments
--| after a spread's `..` and after an update's record (Rust moves that one
--| past the `|`), comments in `C { … }` patterns, and a constructor's
--| fields after a dotted or applied constructor.
--|
--| As in the earlier slices, the slice is a test on the real tree,
--| `within4c`, and a token alphabet, `Tok.within4c`.

namespace Fmt.Later
import Fmt (..)
import Std (Bool, Doc, List, Nat, Option, Text)
import Syntax (
  Arm,
  BindingKind,
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
  SourceFile,
  Statement,
  Tok,
  Word,
  anyAbsurd
)

-- The slice.

--| Whether the expression is one of slices 1 to 5a's, 4b's and 4c's, all
--| the way down: as `within4b`, with records, spreads and membership.
def Expr.within4c: Expr → Bool
  | Atom kind word => kind.wordWithin2 || (kind == Str || kind == CharLit) && !word.text.contains "\n"
  | Paren _ inner _ => inner.within4c
  | Tuple _ items _ _ | ListOf _ items _ _ => allInline4c items
  | App head arguments => head.inline4c && allInline4c arguments
  | Infix InfixBinary left _ right | Infix InfixArrow left _ right => left.inline4c && right.within4c
  | Infix InfixMembership left _ right => left.inline4c && right.inline4c
  | Prefix operator operand => operand.inline4c && !(operator.text == "-" && operand.numeralField)
  | Binding BindsLambda None params _ body => !params.isEmpty && paramsWithin4c params && body.within4c
  | Binding BindsForall (Some _) params _ body | Binding BindsExists (Some _) params _ body =>
    !params.isEmpty && paramsWithin4c params && body.inline4c
  | Block first rest result =>
    first.within4c && statementsWithin4c rest && result.inline4c && laterLinesPlain rest result
  | LetIn binding _ body => binding.within4c && keepsLine binding.value && body.within4c
  | If _ None condition _ whenTrue _ whenFalse => condition.inline4c && whenTrue.within4c && whenFalse.within4c
  | Match _ scrutinees _ arms => !arms.isEmpty && scrutineesWithin4c scrutinees && armsWithin4c arms
  | FieldAccess (Some target) _ _ => target.inline4c && !target.trails
  | NamedArg _ _ _ value _ => value.inline4c
  | Annotation _ value _ annotation _ => value.inline4c && annotation.inline4c
  | Spread dots list => !dots.trails && list.spreadStart && list.inline4c
  | Record _ base fields _ _ => !fields.isEmpty && baseWithin4c base && fieldsWithin4c fields
  | CtorFields (Atom Upper ctor) record => !ctor.trails && record.isRecord && record.within4c
  | _ => False

--| Within slice 4c, and not a block.
def Expr.inline4c (expr: Expr): Bool := expr.within4c && !expr.isBlock

def allInline4c: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.inline4c && allInline4c rest

--| Whether the expression starts with a name or a bracket, after which
--| Rust glues a spread's `..` (`..xs`, `..(f x)`); before anything else it
--| copies the source's gap.
def Expr.spreadStart: Expr → Bool
  | Atom Lower _ | Atom Upper _ | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _ => True
  | App head _ | FieldAccess (Some head) _ _ => head.spreadStart
  | _ => False

def Expr.isRecord: Expr → Bool
  | Record _ _ _ _ _ => True
  | _ => False

--| An update's record, with no comment after it (Rust prints that one
--| after the `|`).
def baseWithin4c: Option (Expr, Word) → Bool
  | None => True
  | Some (record, _) => record.inline4c && !record.trails

--| A record's fields: `name = value`, or a name alone (punned).
def fieldsWithin4c: List Expr → Bool
  | [] => True
  | [RecordField _ _ value, ..rest] => value.inline4c && fieldsWithin4c rest
  | [Atom Lower _, ..rest] => fieldsWithin4c rest
  | [_, .._] => False

def Statement.within4c: Statement → Bool
  | LetStatement binding => binding.within4c
  | ExprStatement value => value.inline4c
  | _ => False

def statementsWithin4c: List Statement → Bool
  | [] => True
  | [statement, ..rest] => statement.within4c && statementsWithin4c rest

def Let.within4c (binding: Let): Bool := match binding with
  | { pattern, annotation = Some (_, annotation), value, .. } =>
    pattern.within4c && annotation.inline4c && value.within4c
  | { pattern, annotation = None, value, .. } => pattern.within4c && value.within4c

def scrutineesWithin4c: List Syntax.Scrutinee → Bool
  | [] => True
  | [{ name = None, value }, ..rest] => value.inline4c && scrutineesWithin4c rest
  | [_, .._] => False

def armsWithin4c: List Arm → Bool
  | [] => True
  | [arm, ..rest] => arm.within4c && armsWithin4c rest

--| An arm with a body, or an absurd one with none.
def Arm.within4c (arm: Arm): Bool := match arm with
  | { patterns, guard, body = Some (_, body), .. } =>
    !patterns.isEmpty && patternsWithin4c patterns && guardWithin4c guard && body.within4c
  | { patterns, guard, body = None, .. } =>
    !patterns.isEmpty && patternsWithin4c patterns && guardWithin4c guard && anyAbsurd patterns

def guardWithin4c: Option Guard → Bool
  | Some { binder = None, condition, .. } => condition.inline4c
  | Some _ => False
  | None => True

--| A pattern of slices 3, 4b and 4c: as `within4b`, with record patterns
--| and a constructor's named fields.
def Pattern.within4c: Pattern → Bool
  | PatternWord kind word => kind.patternWord4b word
  | PatternCtor _ arguments => !arguments.isEmpty && argumentsWithin4c arguments
  | PatternParen _ inner _ => inner.within4c
  | PatternAbsurd _ _ => True
  | PatternTuple _ items False _ => !items.isEmpty && patternsWithin4c items
  | PatternList _ items False tail _ => patternsWithin4c items && tailWithin4c tail
  | PatternRecord fields => fields.within4c
  | PatternCtorFields name fields => fields.within4c && !([name, ..fields.words].any Word.commented)
  | _ => False

def patternsWithin4c: List Pattern → Bool
  | [] => True
  | [pattern, ..rest] => pattern.within4c && patternsWithin4c rest

--| A constructor's arguments: as `argumentsWithin4b`.
def argumentsWithin4c: List Pattern → Bool
  | [] => True
  | [PatternAbsurd _ _, .._] | [PatternCtor _ _, .._] => False
  | [pattern, ..rest] => pattern.within4c && argumentsWithin4c rest

def tailWithin4c: Option (Word, Pattern) → Bool
  | None => True
  | Some (dots, rest) => !dots.noted && !dots.trails && rest.tailStart && rest.within4c

--| A record pattern with a field or a `..` (Rust copies the gap of `{}`).
def FieldsPattern.within4c (fields: FieldsPattern): Bool := match fields with
  | { fields = items, rest, trailingComma = False, .. } =>
    (!items.isEmpty || rest.isSome) && fieldPatternsWithin4c items
  | _ => False

def fieldPatternsWithin4c: List FieldPattern → Bool
  | [] => True
  | [{ value = Some (_, pattern), .. }, ..rest] => pattern.within4c && fieldPatternsWithin4c rest
  | [{ value = None, .. }, ..rest] => fieldPatternsWithin4c rest

def Word.commented (word: Word): Bool := word.noted || word.trails

--| A binder's parameters: names, `_`, and typed groups.
def paramsWithin4c: List Param → Bool
  | [] => True
  | [NameParam _, ..rest] | [PatternParam (PatternWord _ _), ..rest] => paramsWithin4c rest
  | [Grouped group, ..rest] => groupWithin4c GroupLambda group && paramsWithin4c rest
  | [_, ..rest] => False

def groupWithin4c (kind: GroupKind) (group: Syntax.Group): Bool := match group with
  | { attributes = [], auto = None, colon = Some _, annotation = Some annotation, default = None, .. } =>
    group.kind == kind && !group.names.isEmpty && annotation.inline4c
  | _ => False

def resultWithin4c: Expr → Bool
  | Effect ({ abilities, variable = None, .. }) result => !abilities.isEmpty && allWithin2 abilities && result.inline4c
  | result => result.inline4c

--| As `within4b`.
def Header.within4c (header: Header): Bool := match header with
  | {
      exportKeyword = None,
      opaqueKeyword = None,
      kind,
      params,
      result,
      decreasingClause = None,
      unfoldingClause = None,
      ..
    } => kind != DefInstance && params.all (groupWithin4c GroupParam) && resultWithin4c result
  | _ => False

--| A definition with a body or arms, a namespace line, an import, or a
--| test.
def Decl.within4c: Decl → Bool
  | Definition [] header (Assigned _ value) => header.within4c && value.within4c
  | Definition [] header (Arms arms) => header.within4c && !arms.isEmpty && armsWithin4c arms
  | Namespace _ _ | Import _ _ _ _ _ => True
  | Test _ name _ body => !name.text.contains "\n" && body.within4c
  | _ => False

def SourceFile.within4c (file: SourceFile): Bool := file.decls.all Decl.within4c

--| Slice 4c's tokens: slice 4b's and membership's `∈` and `∉` (`in` and
--| `!in`).
def Tok.within4c: Tok → Bool
  | KwIn | NotIn => True
  | kind => kind.within4b

-- Printing.

--| A declaration printed in 120 columns, if it is within slices 1 to 5a,
--| 4b and 4c.
def Decl.printed4c (decl: Decl): Option Text :=
  if decl.within4c then decl.doc5a.map (doc => Doc.print doc width) else None

def SourceFile.printed4c (file: SourceFile): Text := file.printedBy Decl.printed4c
