--| Slice 5a of the proved formatter (docs/proposals/
--| self-hosted-fmt-proof-plan.md §1.2, the first part of S5), on top of
--| slices 1 to 4a: the declarations around definitions, `namespace`,
--| `import` and `test`, and a definition's own arms (`def f: A → B` then
--| `| p => e` lines) whose patterns are slice 3's. Tests name themselves
--| with text, and most compare texts, so text and character literals of
--| one line are in the slice too: each prints as its token.
--|
--| Left out: a text block (a literal spanning lines, which Rust moves with
--| its line), interpolated text, attributes, `export`, `opaque`,
--| `decreasing`, `unfolding`, `instance`, and arms whose patterns are
--| tuples, lists or records (S4's patterns).
--|
--| As in the earlier slices, the slice is a test on the real tree,
--| `within5a`, and a token alphabet, `Tok.within5a`, which `formatWithin`
--| checks before parsing.

namespace Fmt
import Std (Bool, Doc, List, Nat, Option, Result, Text)
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
  lex
)

-- The slice.

--| Whether the expression is one of slices 1 to 5a's, all the way down: as
--| `within4a`, and text and character literals of one line.
def Expr.within5a: Expr → Bool
  | Atom kind word => kind.wordWithin2 || (kind == Str || kind == CharLit) && !word.text.contains "\n"
  | Paren _ inner _ => inner.within5a
  | Tuple _ items _ _ => allInline5a items
  | ListOf _ items _ _ => allInline5a items
  | App head arguments => head.inline5a && allInline5a arguments
  | Infix InfixBinary left _ right => left.inline5a && right.within5a
  | Infix InfixArrow left _ right => left.inline5a && right.within5a
  | Prefix operator operand => operand.inline5a && !(operator.text == "-" && operand.numeralField)
  | Binding BindsLambda None params _ body => !params.isEmpty && paramsWithin5a params && body.within5a
  | Binding BindsForall (Some _) params _ body => !params.isEmpty && paramsWithin5a params && body.inline5a
  | Binding BindsExists (Some _) params _ body => !params.isEmpty && paramsWithin5a params && body.inline5a
  | Block first rest result =>
    first.within5a && statementsWithin5a rest && result.inline5a && laterLinesPlain rest result
  | LetIn binding _ body => binding.within5a && keepsLine binding.value && body.within5a
  | If _ None condition _ whenTrue _ whenFalse => condition.inline5a && whenTrue.within5a && whenFalse.within5a
  | Match _ scrutinees _ arms => !arms.isEmpty && scrutineesWithin5a scrutinees && armsWithin5a arms
  | FieldAccess (Some target) _ _ => target.inline5a && !target.trails
  | _ => False

--| Within slice 5a, and not a block.
def Expr.inline5a (expr: Expr): Bool := expr.within5a && !expr.isBlock

def allInline5a: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.inline5a && allInline5a rest

def Statement.within5a: Statement → Bool
  | LetStatement binding => binding.within5a
  | ExprStatement value => value.inline5a
  | _ => False

def statementsWithin5a: List Statement → Bool
  | [] => True
  | [statement, ..rest] => statement.within5a && statementsWithin5a rest

def Let.within5a (binding: Let): Bool := match binding with
  | { pattern, annotation = Some (_, annotation), value, .. } =>
    pattern.within3 && annotation.inline5a && value.within5a
  | { pattern, annotation = None, value, .. } => pattern.within3 && value.within5a

def scrutineesWithin5a: List Syntax.Scrutinee → Bool
  | [] => True
  | [{ name = None, value }, ..rest] => value.inline5a && scrutineesWithin5a rest
  | [_, .._] => False

def armsWithin5a: List Arm → Bool
  | [] => True
  | [arm, ..rest] => arm.within5a && armsWithin5a rest

def Arm.within5a (arm: Arm): Bool := match arm with
  | { patterns, guard, body = Some (_, body), .. } =>
    !patterns.isEmpty && patterns.all Pattern.within3 && guardWithin5a guard && body.within5a
  | _ => False

def guardWithin5a: Option Guard → Bool
  | Some { binder = None, condition, .. } => condition.inline5a
  | Some _ => False
  | None => True

--| A binder's parameters: names, `_`, and typed groups.
def paramsWithin5a: List Param → Bool
  | [] => True
  | [NameParam _, ..rest] => paramsWithin5a rest
  | [PatternParam (PatternWord _ _), ..rest] => paramsWithin5a rest
  | [Grouped group, ..rest] => groupWithin5a GroupLambda group && paramsWithin5a rest
  | [_, ..rest] => False

def groupWithin5a (kind: GroupKind) (group: Syntax.Group): Bool := match group with
  | { attributes = [], auto = None, colon = Some _, annotation = Some annotation, default = None, .. } =>
    group.kind == kind && !group.names.isEmpty && annotation.inline5a
  | _ => False

def resultWithin5a: Expr → Bool
  | Effect ({ abilities, variable = None, .. }) result => !abilities.isEmpty && allWithin2 abilities && result.inline5a
  | result => result.inline5a

--| As `within2`, with field access in the types.
def Header.within5a (header: Header): Bool := match header with
  | {
      exportKeyword = None,
      opaqueKeyword = None,
      kind,
      params,
      result,
      decreasingClause = None,
      unfoldingClause = None,
      ..
    } => kind != DefInstance && params.all (groupWithin5a GroupParam) && resultWithin5a result
  | _ => False

--| A definition with a body or arms, a namespace line, an import, or a
--| test.
def Decl.within5a: Decl → Bool
  | Definition [] header (Assigned _ value) => header.within5a && value.within5a
  | Definition [] header (Arms arms) => header.within5a && !arms.isEmpty && armsWithin5a arms
  | Namespace _ _ => True
  | Import _ _ _ _ _ => True
  | Test _ name _ body => !name.text.contains "\n" && body.within5a
  | _ => False

def SourceFile.within5a (file: SourceFile): Bool := file.decls.all Decl.within5a

--| Slice 5a's tokens: slice 4a's, `namespace`, `import`, `test`, `..`
--| (for `import M (..)`), and text and character literals.
def Tok.within5a: Tok → Bool
  | KwNamespace => True
  | KwImport => True
  | KwTest => True
  | DotDot => True
  | Str => True
  | CharLit => True
  | kind => kind.within4a

-- Printing.

--| A declaration's document (slices 1 to 5a), or `None` for another.
def Decl.doc5a: Decl → Option Doc
  | Definition [] header (Assigned colonEq value) => Some (defDoc header colonEq value)
  | Definition [] header (Arms arms) => Some (defArmsDoc header arms)
  | Namespace keyword name => Some (namespaceDoc keyword name)
  | Import keyword path open imported close => Some (importDoc keyword path open imported close)
  | Test keyword name colonEq body => Some (testDoc keyword name colonEq body)
  | _ => None

--| A declaration printed in 120 columns, if it is within slices 1 to 5a.
def Decl.printed5a (decl: Decl): Option Text :=
  if decl.within5a then decl.doc5a.map (doc => Doc.print doc width) else None

def SourceFile.printed5a (file: SourceFile): Text := file.printedBy Decl.printed5a

--| The source formatted, if it is within slices 1 to 5a: lexed, refused if
--| a token is outside the alphabet, then parsed, tidied and printed as
--| `format` does.
def formatWithin (source: Text): Result Text Text := match lex source with
  | Err message => Err message
  | Ok lexed =>
    match lexed.leaves.find (leaf => !leaf.token.kind.within5a) with
      | Some leaf => Err "outside slice 5a: `${leaf.token.text}`"
      | None =>
        match lexed.tidied with
          | Err message => Err message
          | Ok tidied =>
            if tidied.fourth.within5a then Ok tidied.fourth.printed5a
            else Err "outside slice 5a: a construct slices 1 to 5a don't have"
