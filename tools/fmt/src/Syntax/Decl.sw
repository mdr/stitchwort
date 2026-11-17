--| The tree's declarations, headers, parameter groups and the file (stage
--| 2b), and their dump in `stitchwort dev tree --print`'s form.
--|
--| A token with one spelling (a keyword, a bracket, `:=`, `:`) is held as
--| its `Comments` only: the constructor and the slot say which token it
--| is, and the dump writes its text. A token with a choice of spelling
--| (`->` or `→`, `∀` or `forall`) or a text of its own (a name) is a `Word`,
--| since the formatter keeps what was written. Stage 2a's expressions still
--| hold every token as a `Word`; the new constructors there (`FunctionType`,
--| `Effect`) follow this rule.

namespace Syntax
import Std (Bool, List, Nat, Option, Text)

--| The file: its declarations, and the comments after the last token.
type SourceFile = { decls: List Decl, end: Comments }

--| Which of the parameter groups the dump names it: a header's `Param`, a
--| type's, constructor's or function type's `Binder`, or a lambda's or
--| `∀`'s `LambdaParam`.
type GroupKind = | GroupParam | GroupBinder | GroupLambda

def GroupKind.name: GroupKind → Text
  | GroupParam => "Param"
  | GroupBinder => "Binder"
  | GroupLambda => "LambdaParam"

--| A parameter group in brackets: `(x y: A)`, `(x: A := v)`, `[a: Type]`,
--| `[auto h: P]`, `[auto P]` (an `auto` and no names or colon), `()` (no
--| names, colon or type), with a constructor field's attributes before its
--| names. `implicit` says the brackets are `[` and `]`. `bare` says no token
--| of a header group (`(x: A)`) has a comment, except above the opening
--| bracket: the parameter-merging pass reads it, so it needn't walk the
--| type for comments (the Rust pass reads the trivia of the group's tokens).
type Group = {
  kind: GroupKind,
  implicit: Bool,
  open: Comments,
  attributes: List Attributes,
  auto: Option Comments,
  names: List Word,
  colon: Option Comments,
  annotation: Option Expr,
  default: Option (Comments, Expr),
  close: Comments,
  bare: Bool
}

--| One group of attributes, `@[js.name "x", inline]`.
type Attributes = {
  at: Comments,
  open: Comments,
  items: List Attribute,
  trailingComma: Bool,
  close: Comments
}

--| `js.name "x"`: the name's first part, each `.` and part after it, and
--| the argument.
type Attribute = {
  name: Word,
  parts: List (Comments, Word),
  argument: Option Word
}

--| `{IO, State s | e}`: the abilities, and the row variable after `|`.
type Row = {
  open: Comments,
  abilities: List Expr,
  variable: Option (Comments, Word),
  close: Comments
}

type Decl =
  | Namespace (keyword: Comments) (name: Word)
  | Import (keyword: Comments) (path: Word) (open: Comments) (imported: Imported) (close: Comments)
  | Definition (attributes: List Attributes) (header: Header) (body: DefBody)
  --| `type` or (with `interface`) `interface`, its name, parameters,
  --| indices, and what follows `=`.
  | Data
      (attributes: List Attributes)
      (isInterface: Bool)
      (keyword: Comments)
      (name: Word)
      (params: List Group)
      (indices: Option Indices)
      (body: DataBody)
  | Ability (keyword: Comments) (name: Word) (params: List Group) (whereKeyword: Comments) (operations: List Operation)
  | Test (keyword: Comments) (name: Word) (colonEq: Comments) (body: Expr)
  --| `rules name := [r1, <- r2]`
  | RuleSetDecl (keyword: Comments) (name: Word) (colonEq: Comments) (set: RuleSet)

--| `(..)`, or the names imported.
type Imported =
  | ImportAll (dots: Comments)
  | ImportItems (items: List ImportItem)

--| `filter` or `filter as f`.
type ImportItem = { name: Word, alias: Option (Comments, Word) }

type DefKind = | DefPlain | DefTheorem | DefInstance

--| What comes before a definition's body.
type Header = {
  exportKeyword: Option Comments,
  opaqueKeyword: Option Comments,
  kind: DefKind,
  keyword: Comments,
  name: Word,
  forallKeyword: Option Word,
  params: List Group,
  colon: Comments,
  result: Expr,
  decreasingClause: Option (Comments, Expr),
  unfoldingClause: Option (Comments, List Word)
}

--| `:= e`, arms, or nothing (a primitive's signature).
type DefBody =
  | Primitive
  | Assigned (colonEq: Comments) (value: Expr)
  | Arms (arms: List Arm)

--| After a data type's `:`: each index and its arrow, then the universe.
type Indices = { colon: Comments, steps: List (Index, Word), last: Expr }

type Index = | IndexBinder (binder: Group) | IndexType (annotation: Expr)

type DataBody =
  --| No `=`: a type without constructors.
  | Abstract
  | Synonym (equals: Comments) (annotation: Expr)
  | RecordBody (equals: Comments) (fields: Fields)
  | Sum (equals: Comments) (constructors: List Constructor)

type Constructor = {
  bar: Comments,
  attributes: List Attributes,
  name: Word,
  fields: List ConstructorPart,
  result: Option (Comments, Expr)
}

--| A constructor's fields: a group in brackets, or braces.
type ConstructorPart = | PartGroup (group: Group) | PartFields (fields: Fields)

type Fields = {
  open: Comments,
  fields: List Field,
  trailingComma: Bool,
  close: Comments
}

type Field = {
  attributes: List Attributes,
  name: Word,
  colon: Comments,
  annotation: Expr,
  default: Option (Comments, Expr)
}

--| `get: () -> {State s} s`
type Operation = { name: Word, colon: Comments, annotation: Expr }

-- The dump.

--| A fixed token's line: its one spelling.
def fixed (depth: Nat) (text: Text): List Text := ["${indent depth}${text}\n"]

def fixedIf (depth: Nat) (text: Text): Option Comments → List Text
  | Some _ => fixed depth text
  | None => []

def Group.lines (group: Group) (depth: Nat): List Text := match group with
  | { kind, implicit, open, attributes, auto, names, colon, annotation, default, close, bare } =>
    let d := depth + 1
    let (opener, closer) := if implicit then ("[", "]") else ("(", ")")
    let annotated := match annotation with
      | Some written => written.lines d
      | None => []
    node depth kind.name
      (fixed d opener
        ++ attributesLines d attributes
        ++ fixedIf d "auto" auto
        ++ wordsLines d names
        ++ fixedIf d ":" colon
        ++ annotated
        ++ defaultLines d default
        ++ fixed d closer)

def defaultLines (depth: Nat): Option (Comments, Expr) → List Text
  | Some (_, value) => node depth "Default" (fixed (depth + 1) ":=" ++ value.lines (depth + 1))
  | None => []

def groupsLines (depth: Nat): List Group → List Text
  | [] => []
  | [group, ..rest] => group.lines depth ++ groupsLines depth rest

def attributesLines (depth: Nat): List Attributes → List Text
  | [] => []
  | [{ at, open, items, trailingComma, close }, ..rest] =>
    let d := depth + 1
    node depth "Attributes" (fixed d "@" ++ fixed d "[" ++ attributeLines d trailingComma items ++ fixed d "]")
      ++ attributesLines depth rest

def attributeLines (depth: Nat) (trailingComma: Bool): List Attribute → List Text
  | [] => []
  | [last] => attributeLine depth last ++ (if trailingComma then commaLine depth else [])
  | [first, ..rest] => attributeLine depth first ++ commaLine depth ++ attributeLines depth trailingComma rest

def attributeLine (depth: Nat): Attribute → List Text
  | { name, parts, argument } =>
    let d := depth + 1
    let named := match parts with
      | [] => name.line d
      | _ => node d "AttributeName" (name.line (d + 1) ++ partLines (d + 1) parts)
    node depth "Attribute" (named ++ wordLines d argument)

def partLines (depth: Nat): List (Comments, Word) → List Text
  | [] => []
  | [(_, part), ..rest] => fixed depth "." ++ part.line depth ++ partLines depth rest

def Row.lines (row: Row) (depth: Nat): List Text := match row with
  | { open, abilities, variable, close } =>
    let d := depth + 1
    let named := match variable with
      | Some (_, name) => fixed d "|" ++ name.line d
      | None => []
    node depth "Row" (fixed d "{" ++ commaExprs d False abilities ++ named ++ fixed d "}")

def SourceFile.dump (file: SourceFile): Text := Text.concat (declsLines file.decls)

def declsLines: List Decl → List Text
  | [] => []
  | [decl, ..rest] => decl.lines ++ declsLines rest

def Decl.lines (decl: Decl): List Text := match decl with
  | Namespace _ name => node 0 "Namespace" (fixed 1 "namespace" ++ name.line 1)
  | Import _ path _ imported _ =>
    let items := match imported with
      | ImportAll _ => fixed 1 ".."
      | ImportItems items => importLines 1 items
    node 0 "Import" (fixed 1 "import" ++ path.line 1 ++ fixed 1 "(" ++ items ++ fixed 1 ")")
  | Definition attributes header body => definitionLines 0 attributes header body
  | Data attributes isInterface _ name params indices body =>
    let keyword := if isInterface then "interface" else "type"
    let kind := if isInterface then "Interface" else body.kind
    let indexed := match indices with
      | Some indices => indices.lines 1
      | None => []
    node 0 kind
      (attributesLines 1 attributes
        ++ fixed 1 keyword
        ++ name.line 1
        ++ groupsLines 1 params
        ++ indexed
        ++ body.lines 1)
  | Ability _ name params _ operations =>
    node 0 "Ability"
      (fixed 1 "ability" ++ name.line 1 ++ groupsLines 1 params ++ fixed 1 "where" ++ operationLines 1 operations)
  | Test _ name _ body => node 0 "Test" (fixed 1 "test" ++ name.line 1 ++ node 1 "Body" (fixed 2 ":=" ++ body.lines 2))
  | RuleSetDecl _ name _ set =>
    node 0 "Rules" (fixed 1 "rules" ++ name.line 1 ++ node 1 "Body" (fixed 2 ":=" ++ set.lines 2))

--| A definition, at the top level or in a block.
def definitionLines (depth: Nat) (attributes: List Attributes) (header: Header) (body: DefBody): List Text :=
  let d := depth + 1
  node depth header.kind.name (attributesLines d attributes ++ header.lines d ++ body.lines d)

def importLines (depth: Nat): List ImportItem → List Text
  | [] => []
  | [item] => importItem depth item
  | [item, ..rest] => importItem depth item ++ commaLine depth ++ importLines depth rest

def importItem (depth: Nat): ImportItem → List Text
  | { name, alias } =>
    let aliased := match alias with
      | Some (_, other) => fixed (depth + 1) "as" ++ other.line (depth + 1)
      | None => []
    node depth "ImportItem" (name.line (depth + 1) ++ aliased)

def DefKind.name: DefKind → Text
  | DefPlain => "Def"
  | DefTheorem => "Theorem"
  | DefInstance => "Instance"

def DefKind.keyword: DefKind → Text
  | DefPlain => "def"
  | DefTheorem => "theorem"
  | DefInstance => "instance"

def Header.lines (header: Header) (depth: Nat): List Text := match header with
  | {
      exportKeyword,
      opaqueKeyword,
      kind,
      keyword,
      name,
      forallKeyword,
      params,
      colon,
      result,
      decreasingClause,
      unfoldingClause
    } =>
    let d := depth + 1
    let decreasingLines := match decreasingClause with
      | Some (_, measure) => node depth "Decreasing" (fixed d "decreasing" ++ measure.lines d)
      | None => []
    let unfoldingLines := match unfoldingClause with
      | Some (_, names) => node depth "Unfolding" (fixed d "unfolding" ++ commaWords d names)
      | None => []
    fixedIf depth "export" exportKeyword
      ++ fixedIf depth "opaque" opaqueKeyword
      ++ fixed depth kind.keyword
      ++ name.line depth
      ++ wordLines depth forallKeyword
      ++ groupsLines depth params
      ++ node depth "ResultType" (fixed d ":" ++ result.lines d)
      ++ decreasingLines
      ++ unfoldingLines

def commaWords (depth: Nat): List Word → List Text
  | [] => []
  | [last] => last.line depth
  | [first, ..rest] => first.line depth ++ commaLine depth ++ commaWords depth rest

def DefBody.lines (body: DefBody) (depth: Nat): List Text := match body with
  | Primitive => []
  | Assigned _ value => node depth "Body" (fixed (depth + 1) ":=" ++ value.lines (depth + 1))
  | Arms arms => node depth "Arms" (armLines (depth + 1) arms)

def Indices.lines (indices: Indices) (depth: Nat): List Text :=
  let d := depth + 1
  node depth "ResultType" (fixed d ":" ++ indexLines d indices.steps ++ indices.last.lines d)

def indexLines (depth: Nat): List (Index, Word) → List Text
  | [] => []
  | [(IndexBinder binder, arrow), ..rest] => binder.lines depth ++ arrow.line depth ++ indexLines depth rest
  | [(IndexType annotation, arrow), ..rest] => annotation.lines depth ++ arrow.line depth ++ indexLines depth rest

def DataBody.kind: DataBody → Text
  | Abstract => "DataType"
  | Synonym _ _ => "TypeSynonym"
  | RecordBody _ _ => "RecordType"
  | Sum _ _ => "DataType"

def DataBody.lines (body: DataBody) (depth: Nat): List Text := match body with
  | Abstract => []
  | Synonym _ annotation => node depth "Body" (fixed (depth + 1) "=" ++ annotation.lines (depth + 1))
  | RecordBody _ fields => fixed depth "=" ++ fields.lines depth
  | Sum _ constructors => fixed depth "=" ++ constructorLines depth constructors

def constructorLines (depth: Nat): List Constructor → List Text
  | [] => []
  | [{ bar, attributes, name, fields, result }, ..rest] =>
    let d := depth + 1
    let typed := match result with
      | Some (_, annotation) => node d "ResultType" (fixed (d + 1) ":" ++ annotation.lines (d + 1))
      | None => []
    node depth "Constructor"
      (fixed d "|" ++ attributesLines d attributes ++ name.line d ++ partsLines d fields ++ typed)
      ++ constructorLines depth rest

def partsLines (depth: Nat): List ConstructorPart → List Text
  | [] => []
  | [PartGroup group, ..rest] => group.lines depth ++ partsLines depth rest
  | [PartFields fields, ..rest] => fields.lines depth ++ partsLines depth rest

def Fields.lines (fields: Fields) (depth: Nat): List Text :=
  let d := depth + 1
  node depth "Fields" (fixed d "{" ++ fieldLinesOf d fields.trailingComma fields.fields ++ fixed d "}")

def fieldLinesOf (depth: Nat) (trailingComma: Bool): List Field → List Text
  | [] => []
  | [last] => fieldLine depth last ++ (if trailingComma then commaLine depth else [])
  | [first, ..rest] => fieldLine depth first ++ commaLine depth ++ fieldLinesOf depth trailingComma rest

def fieldLine (depth: Nat): Field → List Text
  | { attributes, name, colon, annotation, default } =>
    let d := depth + 1
    node depth "Field"
      (attributesLines d attributes ++ name.line d ++ fixed d ":" ++ annotation.lines d ++ defaultLines d default)

def operationLines (depth: Nat): List Operation → List Text
  | [] => []
  | [{ name, colon, annotation }, ..rest] =>
    let d := depth + 1
    node depth "AbilityOp" (name.line d ++ fixed d ":" ++ annotation.lines d) ++ operationLines depth rest
