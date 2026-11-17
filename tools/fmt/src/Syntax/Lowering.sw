--| The lowering's three checks on what parsed (`crates/syntax/src/lower`),
--| as functions of the tree that `parseFile` calls on each declaration
--| once it has parsed: an or-pattern that binds a name
--| (`E-OR-PATTERN-BINDS`), a header's parameter named twice
--| (`E-DUPLICATE-PARAMETER`), and an arm with `()`, a condition and no
--| body. The first two are checked by the traversal's steps, which fail at
--| the first node they refuse.

namespace Syntax
import Std (Bool, Fail, List, Option, Result, Text)

def orPatternBinds: Text := "an or-pattern can't bind names"

def guardWithoutBody: Text := "an arm with `()` and no body can't have a condition"

--| The first of the lowering's errors in a declaration, if any.
def Decl.loweringError (decl: Decl): Option Text := match decl with
  | Definition _ header _ =>
    match duplicateParameter header with
      | Some message => Some message
      | None => traversalError decl
  | _ => traversalError decl

--| The first of the lowering's errors in a file.
def SourceFile.loweringError (file: SourceFile): Option Text := firstLoweringError file.decls

def firstLoweringError: List Decl → Option Text
  | [] => None
  | [decl, ..rest] =>
    match decl.loweringError with
      | Some message => Some message
      | None => firstLoweringError rest

--| The first of the lowering's errors in an expression read on its own.
def Expr.loweringError (expr: Expr): Option Text :=
  match Fail.toResult (() => expr.traverse checkExpr checkPattern) with
    | Err message => Some message
    | Ok _ => None

def traversalError (decl: Decl): Option Text := match Fail.toResult (() => decl.traverse checkExpr checkPattern) with
  | Err message => Some message
  | Ok _ => None

def checkPattern (pattern: Pattern): {Fail} Pattern := match pattern with
  | PatternOr first rest => if first.binds || anyLinkBinds rest then Fail.fail orPatternBinds else pattern
  | _ => pattern

def checkExpr (expr: Expr): {Fail} Expr := match expr with
  | Match _ _ _ arms => if anyGuardWithoutBody arms then Fail.fail guardWithoutBody else expr
  | ClauseLambda keyword _ arms =>
    if keyword.text != "matches" && anyGuardWithoutBody arms then Fail.fail guardWithoutBody else expr
  | _ => expr

def anyGuardWithoutBody: List Arm → Bool
  | [] => False
  | [{ bar, patterns, guard = Some _, body = None }, .._] => True
  | [_, ..rest] => anyGuardWithoutBody rest

--| `E-DUPLICATE-PARAMETER`: the header's parameters, and the implicit and
--| `auto` ones on the result type's spine, all have different names
--| (`check_duplicates`). The spine's own names may repeat each other, as
--| the Rust check only compares them with the header's.
def duplicateParameter (header: Header): Option Text :=
  let named := groupNames header.params
  match repeatedIn [] named with
    | Some name => Some (alreadyParameter name header.name)
    | None =>
      match spineRepeat named header.result with
        | Some name => Some (alreadyParameter name header.name)
        | None => None

def alreadyParameter (name: Text) (definition: Word): Text := "`${name}` is already a parameter of `${definition.text}`"

def groupNames: List Group → List Text
  | [] => []
  | [group, ..rest] => group.names.map (name => name.text) ++ groupNames rest

--| The first name that repeats one before it.
def repeatedIn (seen: List Text): List Text → Option Text
  | [] => None
  | [name, ..rest] => if seen.contains name then Some name else repeatedIn [name, ..seen] rest

--| The first implicit binder's name on `type`'s spine that is a header's
--| parameter.
def spineRepeat (header: List Text): Expr → Option Text
  | FunctionType binder _ result =>
    let clash :=
      if binder.implicit then binder.names.map (name => name.text) |> .find (name => header.contains name) else None
    match clash with
      | Some name => Some name
      | None => spineRepeat header result
  | Infix InfixArrow _ _ result => spineRepeat header result
  | _ => None

--| Whether a pattern binds a name: a lowercase name, or a punned field.
def Pattern.binds: Pattern → Bool
  | PatternWord kind word => kind == Lower && word.text != "Quot.mk"
  | PatternCtor _ arguments => anyBinds arguments
  | PatternCtorFields _ fields => fieldsBind fields
  | PatternRecord fields => fieldsBind fields
  | PatternTuple _ items _ _ => anyBinds items
  | PatternList _ items _ tail _ =>
    anyBinds items
      || (match tail with
        | Some (_, rest) => rest.binds
        | None => False)
  | PatternNamed _ _ _ value _ => value.binds
  | PatternOr first rest => first.binds || anyLinkBinds rest
  | PatternParen _ inner _ => inner.binds
  | PatternNegative _ _ => False
  | PatternAbsurd _ _ => False
  | PatternAppend start _ rest => start.binds || rest.binds

def anyBinds: List Pattern → Bool
  | [] => False
  | [first, ..rest] => first.binds || anyBinds rest

def anyLinkBinds: List (Word, Pattern) → Bool
  | [] => False
  | [(bar, item), ..rest] => item.binds || anyLinkBinds rest

def fieldsBind: FieldsPattern → Bool
  | { open, fields, trailingComma, rest, close } => anyFieldBinds fields

def anyFieldBinds: List FieldPattern → Bool
  | [] => False
  | [{ name, value }, ..rest] =>
    (match value with
      | Some (_, pattern) => pattern.binds
      | None => True)
      || anyFieldBinds rest
