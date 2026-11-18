--| Slice 2 of the proved formatter (docs/proposals/
--| self-hosted-fmt-proof-plan.md §1.2), binders, on top of slice 1:
--| `def` and `theorem` headers with parameter groups and a theorem's `∀`;
--| lambdas, `∀` and `∃` whose parameters are names, `_` or typed groups;
--| an ability row before a result type (`{Fail} T`); and `Type` and
--| `Prop` as words, which most parameter groups need.
--|
--| As in slice 1 (`Fmt.Slice1`), the slice is a test on the real tree,
--| `within2`, and a token alphabet, `Tok.within2`, which `formatWithin`
--| checks before parsing.

namespace Fmt
import Std (Bool, Doc, List, Nat, Option, Result, Text)
import Syntax (
  BindingKind,
  Decl,
  DefBody,
  DefKind,
  Expr,
  GroupKind,
  Header,
  InfixKind,
  Param,
  Pattern,
  Row,
  SourceFile,
  Tok,
  lex
)

-- The slice.

--| Whether the expression is one of slices 1 and 2's, all the way down.
--| An ability row is not: it stands only before a header's result type
--| (`Header.within2`), where Rust's spacing gives its braces no spaces.
def Expr.within2: Expr → Bool
  | Atom kind _ => kind.wordWithin2
  | Paren _ inner _ => inner.within2
  | Tuple _ items _ _ => allWithin2 items
  | ListOf _ items _ _ => allWithin2 items
  | App head arguments => head.within2 && allWithin2 arguments
  | Infix InfixBinary left _ right => left.within2 && right.within2
  | Infix InfixArrow left _ right => left.within2 && right.within2
  | Prefix _ operand => operand.within2
  | Binding BindsLambda None params _ body => !params.isEmpty && paramsWithin2 params && body.within2
  | Binding BindsForall (Some _) params _ body => !params.isEmpty && paramsWithin2 params && body.within2
  | Binding BindsExists (Some _) params _ body => !params.isEmpty && paramsWithin2 params && body.within2
  | _ => False

def allWithin2: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.within2 && allWithin2 rest

--| A binder's parameters: names, `_`, and typed groups.
def paramsWithin2: List Param → Bool
  | [] => True
  | [NameParam _, ..rest] => paramsWithin2 rest
  | [PatternParam (PatternWord _ _), ..rest] => paramsWithin2 rest
  | [Grouped group, ..rest] => groupWithin2 GroupLambda group && paramsWithin2 rest
  | [_, ..rest] => False

--| `(x y: A)` or `[a: Type]`: names, a type, and nothing else (no
--| attributes, `auto` or default).
def groupWithin2 (kind: GroupKind) (group: Syntax.Group): Bool := match group with
  | { attributes = [], auto = None, colon = Some _, annotation = Some annotation, default = None, .. } =>
    group.kind == kind && !group.names.isEmpty && annotation.within2
  | _ => False

--| The token kinds a slice 2 `Atom` may have: names, numerals, `Type` and
--| `Prop`.
def Tok.wordWithin2 (kind: Tok): Bool := kind.wordWithin1 || kind == TypeU || kind == PropU

--| A result type, perhaps after an ability row of abilities in the slice.
def resultWithin2: Expr → Bool
  | Effect ({ abilities, variable = None, .. }) result => !abilities.isEmpty && allWithin2 abilities && result.within2
  | result => result.within2

--| `def name (x: A) [b: B]: T` or `theorem name ∀ (x: A): P`: no
--| attributes, `export`, `opaque`, `decreasing` or `unfolding`.
def Header.within2 (header: Header): Bool := match header with
  | {
      exportKeyword = None,
      opaqueKeyword = None,
      kind,
      params,
      result,
      decreasingClause = None,
      unfoldingClause = None,
      ..
    } => kind != DefInstance && params.all (groupWithin2 GroupParam) && resultWithin2 result
  | _ => False

def Decl.within2: Decl → Bool
  | Definition [] header (Assigned _ value) => header.within2 && value.within2
  | _ => False

def SourceFile.within2 (file: SourceFile): Bool := file.decls.all Decl.within2

--| Slice 2's tokens: slice 1's, `theorem`, `∀`, `∃`, `=>`, `_`, `{`, `}`,
--| `Type` and `Prop`.
def Tok.within2 (kind: Tok): Bool := match kind with
  | KwTheorem => True
  | KwForall => True
  | KwExists => True
  | FatArrow => True
  | Underscore => True
  | LBrace => True
  | RBrace => True
  | TypeU => True
  | PropU => True
  | _ => kind.within1

-- Printing.

--| A declaration printed in 120 columns, if it is within slices 1 and 2.
def Decl.printed2 (decl: Decl): Option Text := if decl.within2 then decl.doc1.map (doc => Doc.print doc width) else None

--| The file loop of `SourceFile.printed1`, for slices 1 and 2.
def SourceFile.printed2 (file: SourceFile): Text :=
  let body := printDecls2 { pieces = [], empty = True } file.decls
  let done := body.notes file.end.above
  if done.empty then "" else Text.concat ["\n", ..done.pieces].reverse

def printDecls2 (output: Output): List Decl → Output
  | [] => output
  | [decl, ..rest] =>
    let first := decl.firstComments
    let noted := output.notes first.above
    printDecls2 (noted.item first.blankBefore (decl.printed2.getOrElse "")) rest

--| The source formatted, if it is within slices 1 and 2: lexed, refused if
--| a token is outside the alphabet, then parsed, tidied and printed as
--| `format` does.
def formatWithin (source: Text): Result Text Text := match lex source with
  | Err message => Err message
  | Ok lexed =>
    match lexed.leaves.find (leaf => !leaf.token.kind.within2) with
      | Some leaf => Err "outside slice 2: `${leaf.token.text}`"
      | None =>
        match lexed.tidied with
          | Err message => Err message
          | Ok tidied =>
            if tidied.fourth.within2 then Ok tidied.fourth.printed2
            else Err "outside slice 2: a construct slices 1 and 2 don't have"
