--| Slice 4a of the proved formatter (docs/proposals/
--| self-hosted-fmt-proof-plan.md §1.2, the first part of S4), field
--| access, on top of slices 1 to 3: `pass.seatId`, `x.f.g`, and dot calls
--| `xs.map f`, which are calls whose function is a field access. Rust
--| prints a field access by `join`, its `.` glued on both sides (the
--| parser refuses a spaced one), so it never breaks.
--|
--| Left out: a method section `.f` (a `FieldAccess` without a receiver,
--| inside a `Section`) and `f()`, which are S4's sections and unit; a
--| field after a bracket whose contents end their line with a comment,
--| `(x -- c⏎).f`, whose closer Rust keeps on a line of its own
--| (`glued_field`); and `- 1.f`, whose gap after the `-` Rust copies from
--| the source.
--|
--| As in the earlier slices, the slice is a test on the real tree,
--| `within4a`, and a token alphabet, `Tok.within4a`. `formatWithin` is
--| `Fmt.Slice5a`'s.

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
  Tok
)

-- The slice.

--| Whether the expression is one of slices 1 to 4a's, all the way down: as
--| `within3`, and a field of an expression of the slice.
def Expr.within4a: Expr → Bool
  | Atom kind _ => kind.wordWithin2
  | Paren _ inner _ => inner.within4a
  | Tuple _ items _ _ | ListOf _ items _ _ => allInline4a items
  | App head arguments => head.inline4a && allInline4a arguments
  | Infix InfixBinary left _ right | Infix InfixArrow left _ right => left.inline4a && right.within4a
  | Prefix operator operand => operand.inline4a && !(operator.text == "-" && operand.numeralField)
  | Binding BindsLambda None params _ body => !params.isEmpty && paramsWithin4a params && body.within4a
  | Binding BindsForall (Some _) params _ body | Binding BindsExists (Some _) params _ body =>
    !params.isEmpty && paramsWithin4a params && body.inline4a
  | Block first rest result =>
    first.within4a && statementsWithin4a rest && result.inline4a && laterLinesPlain rest result
  | LetIn binding _ body => binding.within4a && keepsLine binding.value && body.within4a
  | If _ None condition _ whenTrue _ whenFalse => condition.inline4a && whenTrue.within4a && whenFalse.within4a
  | Match _ scrutinees _ arms => !arms.isEmpty && scrutineesWithin4a scrutinees && armsWithin4a arms
  | FieldAccess (Some target) _ _ => target.inline4a && !target.trails
  | _ => False

--| Within slice 4a, and not a block.
def Expr.inline4a (expr: Expr): Bool := expr.within4a && !expr.isBlock

--| Whether the expression starts with a numeral and a `.`: after a `-`,
--| Rust copies the source's gap there (`- 1.abs` is not `-1.abs`), which
--| the tree doesn't keep.
def Expr.numeralField (expr: Expr): Bool := match expr.words with
  | [first, dot, .._] => dot.text == "." && (first.text.toList.headOr ' ').isAsciiDigit
  | _ => False

def allInline4a: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.inline4a && allInline4a rest

def Statement.within4a: Statement → Bool
  | LetStatement binding => binding.within4a
  | ExprStatement value => value.inline4a
  | _ => False

def statementsWithin4a: List Statement → Bool
  | [] => True
  | [statement, ..rest] => statement.within4a && statementsWithin4a rest

def Let.within4a (binding: Let): Bool := match binding with
  | { pattern, annotation = Some (_, annotation), value, .. } =>
    pattern.within3 && annotation.inline4a && value.within4a
  | { pattern, annotation = None, value, .. } => pattern.within3 && value.within4a

def scrutineesWithin4a: List Syntax.Scrutinee → Bool
  | [] => True
  | [{ name = None, value }, ..rest] => value.inline4a && scrutineesWithin4a rest
  | [_, .._] => False

def armsWithin4a: List Arm → Bool
  | [] => True
  | [arm, ..rest] => arm.within4a && armsWithin4a rest

def Arm.within4a (arm: Arm): Bool := match arm with
  | { patterns, guard, body = Some (_, body), .. } =>
    !patterns.isEmpty && patterns.all Pattern.within3 && guardWithin4a guard && body.within4a
  | _ => False

def guardWithin4a: Option Guard → Bool
  | Some { binder = None, condition, .. } => condition.inline4a
  | Some _ => False
  | None => True

--| A binder's parameters: names, `_`, and typed groups.
def paramsWithin4a: List Param → Bool
  | [] => True
  | [NameParam _, ..rest] | [PatternParam (PatternWord _ _), ..rest] => paramsWithin4a rest
  | [Grouped group, ..rest] => groupWithin4a GroupLambda group && paramsWithin4a rest
  | [_, ..rest] => False

def groupWithin4a (kind: GroupKind) (group: Syntax.Group): Bool := match group with
  | { attributes = [], auto = None, colon = Some _, annotation = Some annotation, default = None, .. } =>
    group.kind == kind && !group.names.isEmpty && annotation.inline4a
  | _ => False

def resultWithin4a: Expr → Bool
  | Effect ({ abilities, variable = None, .. }) result => !abilities.isEmpty && allWithin2 abilities && result.inline4a
  | result => result.inline4a

--| As `within2`, with field access in the types.
def Header.within4a (header: Header): Bool := match header with
  | {
      exportKeyword = None,
      opaqueKeyword = None,
      kind,
      params,
      result,
      decreasingClause = None,
      unfoldingClause = None,
      ..
    } => kind != DefInstance && params.all (groupWithin4a GroupParam) && resultWithin4a result
  | _ => False

def Decl.within4a: Decl → Bool
  | Definition [] header (Assigned _ value) => header.within4a && value.within4a
  | _ => False

def SourceFile.within4a (file: SourceFile): Bool := file.decls.all Decl.within4a

--| Slice 4a's tokens: slice 3's and `.`.
def Tok.within4a (kind: Tok): Bool := kind == Dot || kind.within3

-- Printing.

--| A declaration printed in 120 columns, if it is within slices 1 to 4a.
def Decl.printed4a (decl: Decl): Option Text :=
  if decl.within4a then decl.doc1.map (doc => Doc.print doc width) else None

def SourceFile.printed4a (file: SourceFile): Text := file.printedBy Decl.printed4a
