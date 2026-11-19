--| Slice 4b of the proved formatter (docs/proposals/
--| self-hosted-fmt-proof-plan.md §1.2, the patterns of S4), on top of
--| slices 1 to 5a: list patterns (`[]`, `[x, ..xs]`), tuple patterns,
--| `(p)`, the absurd pattern `()` and arms ending at it, and a constructor
--| applied to any of those, in a match's or a definition's arms and after
--| `let`; and two bracketed expressions printed by `join`, a named
--| argument `(n := e)` and a type annotation `(e: T)`.
--|
--| Left out: record patterns and a constructor's named fields (records),
--| `p | q` alternatives inside brackets, `-1`, `"a" ++ rest`, `(n := p)`,
--| a list's `.._` (Rust copies the source's gap after `..` before `_`),
--| `()` as a constructor's argument and the unit `()` (Rust copies the
--| gap of `f ()`, which the tree can't say), and comments on a list's
--| `..`.
--|
--| As in the earlier slices, the slice is a test on the real tree,
--| `within4b`, and a token alphabet, `Tok.within4b`.

namespace Fmt
import Std (Bool, Doc, List, Nat, Option, Text)
import Syntax (
  Arm,
  BindingKind,
  Decl,
  DefBody,
  DefKind,
  Expr,
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

--| Whether the expression is one of slices 1 to 5a's and 4b's, all the way
--| down: as `within5a`, with slice 4b's patterns in arms and `let`, named
--| arguments and annotations.
def Expr.within4b: Expr → Bool
  | Atom kind word => kind.wordWithin2 || (kind == Str || kind == CharLit) && !word.text.contains "\n"
  | Paren _ inner _ => inner.within4b
  | Tuple _ items _ _ | ListOf _ items _ _ => allInline4b items
  | App head arguments => head.inline4b && allInline4b arguments
  | Infix InfixBinary left _ right | Infix InfixArrow left _ right => left.inline4b && right.within4b
  | Prefix operator operand => operand.inline4b && !(operator.text == "-" && operand.numeralField)
  | Binding BindsLambda None params _ body => !params.isEmpty && paramsWithin4b params && body.within4b
  | Binding BindsForall (Some _) params _ body | Binding BindsExists (Some _) params _ body =>
    !params.isEmpty && paramsWithin4b params && body.inline4b
  | Block first rest result =>
    first.within4b && statementsWithin4b rest && result.inline4b && laterLinesPlain rest result
  | LetIn binding _ body => binding.within4b && keepsLine binding.value && body.within4b
  | If _ None condition _ whenTrue _ whenFalse => condition.inline4b && whenTrue.within4b && whenFalse.within4b
  | Match _ scrutinees _ arms => !arms.isEmpty && scrutineesWithin4b scrutinees && armsWithin4b arms
  | FieldAccess (Some target) _ _ => target.inline4b && !target.trails
  | NamedArg _ _ _ value _ => value.inline4b
  | Annotation _ value _ annotation _ => value.inline4b && annotation.inline4b
  | _ => False

--| Within slice 4b, and not a block.
def Expr.inline4b (expr: Expr): Bool := expr.within4b && !expr.isBlock

def allInline4b: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.inline4b && allInline4b rest

def Statement.within4b: Statement → Bool
  | LetStatement binding => binding.within4b
  | ExprStatement value => value.inline4b
  | _ => False

def statementsWithin4b: List Statement → Bool
  | [] => True
  | [statement, ..rest] => statement.within4b && statementsWithin4b rest

def Let.within4b (binding: Let): Bool := match binding with
  | { pattern, annotation = Some (_, annotation), value, .. } =>
    pattern.within4b && annotation.inline4b && value.within4b
  | { pattern, annotation = None, value, .. } => pattern.within4b && value.within4b

def scrutineesWithin4b: List Syntax.Scrutinee → Bool
  | [] => True
  | [{ name = None, value }, ..rest] => value.inline4b && scrutineesWithin4b rest
  | [_, .._] => False

def armsWithin4b: List Arm → Bool
  | [] => True
  | [arm, ..rest] => arm.within4b && armsWithin4b rest

--| An arm with a body, or an absurd one with none.
def Arm.within4b (arm: Arm): Bool := match arm with
  | { patterns, guard, body = Some (_, body), .. } =>
    !patterns.isEmpty && patternsWithin4b patterns && guardWithin4b guard && body.within4b
  | { patterns, guard, body = None, .. } =>
    !patterns.isEmpty && patternsWithin4b patterns && guardWithin4b guard && anyAbsurd patterns

def guardWithin4b: Option Guard → Bool
  | Some { binder = None, condition, .. } => condition.inline4b
  | Some _ => False
  | None => True

--| A pattern of slices 3 and 4b: a name, `_`, a numeral, a one-line text
--| or character literal, `()`, `(p)`, a tuple, a list with perhaps a
--| `..rest`, or a constructor applied to those.
def Pattern.within4b: Pattern → Bool
  | PatternWord kind word => kind.patternWord4b word
  | PatternCtor _ arguments => !arguments.isEmpty && argumentsWithin4b arguments
  | PatternParen _ inner _ => inner.within4b
  | PatternAbsurd _ _ => True
  | PatternTuple _ items False _ => !items.isEmpty && patternsWithin4b items
  | PatternList _ items False tail _ => patternsWithin4b items && tailWithin4b tail
  | _ => False

def patternsWithin4b: List Pattern → Bool
  | [] => True
  | [pattern, ..rest] => pattern.within4b && patternsWithin4b rest

--| A constructor's arguments: as `within4b`, but not `()`, where Rust
--| copies the source's gap (`f ()` against `f()`).
def argumentsWithin4b: List Pattern → Bool
  | [] => True
  | [PatternAbsurd _ _, .._] | [PatternCtor _ _, .._] => False
  | [pattern, ..rest] => pattern.within4b && argumentsWithin4b rest

--| A list's `..rest`: a name or a bracket after a `..` with no comments
--| (Rust copies the gap after `..` before anything else, `.._`).
def tailWithin4b: Option (Word, Pattern) → Bool
  | None => True
  | Some (dots, rest) => !dots.noted && !dots.trails && rest.tailStart && rest.within4b

def Pattern.tailStart: Pattern → Bool
  | PatternWord Lower _ | PatternWord Upper _ | PatternParen _ _ _ | PatternTuple _ _ _ _ | PatternList _ _ _ _ _ =>
    True
  | _ => False

def Tok.patternWord4b (kind: Tok) (word: Word): Bool :=
  kind.patternWord3 || (kind == Str || kind == CharLit) && !word.text.contains "\n"

--| A binder's parameters: names, `_`, and typed groups.
def paramsWithin4b: List Param → Bool
  | [] => True
  | [NameParam _, ..rest] | [PatternParam (PatternWord _ _), ..rest] => paramsWithin4b rest
  | [Grouped group, ..rest] => groupWithin4b GroupLambda group && paramsWithin4b rest
  | [_, ..rest] => False

def groupWithin4b (kind: GroupKind) (group: Syntax.Group): Bool := match group with
  | { attributes = [], auto = None, colon = Some _, annotation = Some annotation, default = None, .. } =>
    group.kind == kind && !group.names.isEmpty && annotation.inline4b
  | _ => False

def resultWithin4b: Expr → Bool
  | Effect ({ abilities, variable = None, .. }) result => !abilities.isEmpty && allWithin2 abilities && result.inline4b
  | result => result.inline4b

--| As `within5a`.
def Header.within4b (header: Header): Bool := match header with
  | {
      exportKeyword = None,
      opaqueKeyword = None,
      kind,
      params,
      result,
      decreasingClause = None,
      unfoldingClause = None,
      ..
    } => kind != DefInstance && params.all (groupWithin4b GroupParam) && resultWithin4b result
  | _ => False

--| A definition with a body or arms, a namespace line, an import, or a
--| test.
def Decl.within4b: Decl → Bool
  | Definition [] header (Assigned _ value) => header.within4b && value.within4b
  | Definition [] header (Arms arms) => header.within4b && !arms.isEmpty && armsWithin4b arms
  | Namespace _ _ | Import _ _ _ _ _ => True
  | Test _ name _ body => !name.text.contains "\n" && body.within4b
  | _ => False

def SourceFile.within4b (file: SourceFile): Bool := file.decls.all Decl.within4b

--| Slice 4b's tokens: slice 5a's, which already has the brackets, `,`, `_`
--| and `..`.
def Tok.within4b (kind: Tok): Bool := kind.within5a

-- Printing.

--| A declaration printed in 120 columns, if it is within slices 1 to 5a
--| and 4b.
def Decl.printed4b (decl: Decl): Option Text :=
  if decl.within4b then decl.doc5a.map (doc => Doc.print doc width) else None

def SourceFile.printed4b (file: SourceFile): Text := file.printedBy Decl.printed4b
