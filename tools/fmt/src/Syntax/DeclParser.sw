--| The parser's declarations, headers, parameter groups and types (stage
--| 2b), and the file loop: the Rust parser's `declarations.rs`, `data`,
--| `ability`, the binders, `result_type`, `row`, `pi_expr`, `split_decls`
--| and `parse_tokens`, function for function, as stage 2a's expressions
--| are.
--|
--| The functions shared with expressions take the expression parser as
--| `self`, a `Goal` to an expression: inside an expression it is the
--| recursion's own, and at a declaration's level `expressionAt`, which
--| starts a recursion with fuel from the items left.

namespace Syntax
import Std (Bool, List, Nat, Option, Parse, Result, Text)

--| An expression at `goal` read from a declaration's level, with
--| `Parse.recursiveWith`'s fuel, as `expression` has (which says why it
--| is enough).
def expressionAt (goal: Goal): {Parse Item} Expr := Parse.recursiveWith expressionRule goal

def fixedFrom(): {Parse Item} Comments := bump().comments

def Modes.expectFixed (modes: Modes) (wanted: Tok) (what: Text): {Parse Item} Comments :=
  (modes.expect wanted what).comments

--| Whether the next item is a line at or left of the block's column, where
--| a recovering body reports a missing expression as "the line ends here"
--| (`ran_out_after`).
def ranOutAtLine (modes: Modes): {Parse Item} Bool := match modes.peek, left(), modes.limit with
  | None, [item, .._], Some limit =>
    !modes.endsGuard item && item.leaf.token.lineStart && item.leaf.token.column <= limit
  | _, _, _ => False

def defaultPlaces: Text := "only a definition's parameter or a field can have a default value"

def forallDefault: Text := "a `forall` parameter can't have a default"

--| `E-ATTRIBUTE`'s first line.
def misplaced (what: Text): Text := "attributes can't be used on ${what}"

-- Attributes.

--| The attribute groups next, `@[a, b "x"] @[c]`.
def attributesOf (modes: Modes): {Parse Item} List Attributes := attributeGroups modes

def attributeGroups (modes: Modes): {Parse Item} List Attributes := Parse.loop (() =>
  if modes.at At then
    let at := fixedFrom()
    let open := modes.expectFixed LBracket "`[`"
    let (items, trailingComma) := attributeItems (Parse.mark().left + 1) modes []
    let close := modes.expectFixed RBracket "`,` or `]` after the attribute"
    Some { at, open, items, trailingComma, close }
  else None)

--| The attributes in one group, and whether a comma ended them.
def attributeItems (fuel: Nat) (modes: Modes) (found: List Attribute): {Parse Item} (List Attribute, Bool) :=
  match fuel with
    | Succ more =>
      if modes.at RBracket && !found.isEmpty then (found.reverse, True)
      else
        let name := modes.lowerQualified "an attribute's name, such as `js.name`"
        let parts := attributeParts modes
        let argument :=
          if modes.at Str then Some bump()
          else if modes.at StrStart then fatal "an attribute's argument is a plain string, without `\${…}`"
          else None
        let done := [{ name, parts, argument }, ..found]
        if modes.at Comma then
          let _ := bump()
          attributeItems more modes done
        else (done.reverse, False)
    | Zero => (found.reverse, False)

def attributeParts (modes: Modes): {Parse Item} List (Comments, Word) := Parse.loop (() =>
  if modes.at Dot then
    let dot := fixedFrom()
    let part := modes.lowerQualified "the rest of the attribute's name"
    Some (dot, part)
  else None)

--| A lowercase name, possibly qualified (`lower_q`).
def Modes.lowerQualified (modes: Modes) (what: Text): {Parse Item} Word :=
  if modes.at Lower then bump() else modes.failName what

--| An uppercase name, possibly qualified (`upper_q`).
def Modes.upperQualified (modes: Modes) (what: Text): {Parse Item} Word :=
  if modes.at Upper then bump() else modes.fail what

--| An unqualified uppercase name (`upper`).
def Modes.upper (modes: Modes) (what: Text): {Parse Item} Word :=
  let name := modes.upperQualified what
  if name.text.contains "." then fatal "`${name.text}` is a qualified name, which can't be used here" else name

--| The first attribute's name, for `E-ATTRIBUTE`'s message.
def refuseAttributes (attributes: List Attributes) (what: Text): {Parse Item} () := match attributes with
  | [] => ()
  | _ => fatal (misplaced what)

-- Parameter groups.

--| A header's, lambda's or `∀`'s group (`header_param_parts`): `(x y: A)`,
--| `[x: A]`, `[auto h: P]`, `[auto P]`, or in a header `()`, and in a
--| header a default, `(x: A := v)`. `refused` is the message for a default
--| where none may be written.
def headerGroup (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: GroupKind) (refused: Option Text):
    {Parse Item} Group :=
  match modes.peek, modes.peekAt 1 with
    | Some LParen, Some RParen =>
      let open := fixedFrom()
      let close := fixedFrom()
      {
        kind,
        implicit = False,
        open,
        attributes = [],
        auto = None,
        names = [],
        colon = None,
        annotation = None,
        default = None,
        close,
        bare = False
      }
    | Some LParen, _ => headerGroupParts self modes kind refused False
    | Some LBracket, _ => headerGroupParts self modes kind refused True
    | _, _ => modes.fail "a parameter such as `(x: Nat)`, or `:` and the definition's type"

def headerGroupParts (self: Goal → {Parse Item} Expr) (modes: Modes) (kind: GroupKind)
    (refused: Option Text) (implicit: Bool):
    {Parse Item} Group :=
  let started := Parse.mark()
  let open := fixedFrom()
  let inner := modes.inBrackets
  refuseAttributes (attributesOf inner) "a definition's parameter"
  let first := paramName inner
  let names := [first, ..paramNames inner]
  let typeFollows := !(inner.at Colon || inner.at RBracket || inner.peek.isNone)
  match names with
    | [auto] if implicit && auto.text == "auto" && typeFollows =>
      let annotation := full self inner
      let close := inner.expectFixed RBracket "`]` to close the parameter `[auto …]`"
      {
        kind,
        implicit,
        open,
        attributes = [],
        auto = Some auto.comments,
        names = [],
        colon = None,
        annotation = Some annotation,
        default = None,
        close,
        bare = False
      }
    | _ =>
      let (auto, named) := match names with
        | [word, second, ..more] if implicit && word.text == "auto" => (Some word.comments, [second, ..more])
        | _ => (None, names)
      let (opener, closer, closeText) := if implicit then ("[", RBracket, "]") else ("(", RParen, ")")
      let written := "${opener}${if auto.isSome then "auto " else ""}${(named.map (name => name.text)).joinWith " "}: …"
      if !inner.at Colon then fatal "a parameter needs a type"
      else
        let colon := fixedFrom()
        let annotation := binderType self inner
        let default :=
          if inner.at ColonEq then
            if implicit then fatal defaultPlaces
            else
              let colonEq := fixedFrom()
              Some (colonEq, full self inner)
          else None
        let close := inner.expectFixed closer "`${closeText}` to close the parameter `${written}`"
        match refused, default with
          | Some message, Some _ => fatal message
          | _, _ => {
            kind,
            implicit,
            open,
            attributes = [],
            auto,
            names = named,
            colon = Some colon,
            annotation = Some annotation,
            default,
            close,
            bare = default.isNone && consumedBare started
          }

--| Whether the items read since `started` have no comments, except above
--| the first: the trivia the Rust merge pass checks on a group's tokens.
def consumedBare (started: Parse.Mark Item): {Parse Item} Bool :=
  let taken := (started.rest).take (Parse.mark().offset - started.offset)
  match taken with
    | [] => True
    | [first, ..rest] => first.leaf.trivia.trailing.isNone && itemsBare rest

def itemsBare: List Item → Bool
  | [] => True
  | [item, ..rest] => item.leaf.trivia.leading.isEmpty && item.leaf.trivia.trailing.isNone && itemsBare rest

--| A parameter's name (`param_name`).
def paramName (modes: Modes): {Parse Item} Word := match modes.peek with
  | Some Upper => modes.fail "a parameter's name"
  | Some LParen => modes.fail "a parameter's name"
  | Some LBrace => modes.fail "a parameter's name"
  | _ => modes.lower "a parameter's name"

def paramNames (modes: Modes): {Parse Item} List Word :=
  Parse.loop (() => if modes.at Lower then Some (paramName modes) else None)

def lowerNames (modes: Modes): {Parse Item} List Word :=
  Parse.loop (() => if modes.at Lower then Some (modes.lower "a name") else None)

--| A type's, constructor's or function type's `(x y: A)` (`binder_with_default`),
--| with a default only if `defaults`.
def binderGroup (self: Goal → {Parse Item} Expr) (modes: Modes) (defaults: Bool): {Parse Item} Group :=
  let open := modes.expectFixed LParen "`(`"
  let inner := modes.inBrackets
  let attributes := attributesOf inner
  let first := inner.lower "a name"
  let names := [first, ..lowerNames inner]
  let colon := inner.expectFixed Colon "`:`"
  let annotation := binderType self inner
  let default :=
    if inner.at ColonEq then
      let colonEq := fixedFrom()
      Some (colonEq, full self inner)
    else None
  let close := inner.expectFixed RParen "`)`"
  if !defaults && default.isSome then fatal defaultPlaces
  else
    {
      kind = GroupBinder,
      implicit = False,
      open,
      attributes,
      auto = None,
      names,
      colon = Some colon,
      annotation = Some annotation,
      default,
      close,
      bare = False
    }

--| `[x y: A]`, `[auto x: P]` or `[auto P]` (`implicit_binder_parts`).
def implicitBinder (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Group :=
  if namelessAutoAt left() then
    let open := fixedFrom()
    let auto := fixedFrom()
    let annotation := full self modes.inBrackets
    let close := modes.inBrackets.expectFixed RBracket "`]`"
    {
      kind = GroupBinder,
      implicit = True,
      open,
      attributes = [],
      auto = Some auto,
      names = [],
      colon = None,
      annotation = Some annotation,
      default = None,
      close,
      bare = False
    }
  else
    let open := modes.expectFixed LBracket "`[`"
    let inner := modes.inBrackets
    let attributes := attributesOf inner
    let first := inner.lower "a name"
    let rest := lowerNames inner
    let (auto, names) := match rest with
      | [_, .._] if first.text == "auto" => (Some first.comments, rest)
      | _ => (None, [first, ..rest])
    let colon := inner.expectFixed Colon "`:`"
    let annotation := binderType self inner
    let close := inner.expectFixed RBracket "`]`"
    {
      kind = GroupBinder,
      implicit = True,
      open,
      attributes,
      auto,
      names,
      colon = Some colon,
      annotation = Some annotation,
      default = None,
      close,
      bare = False
    }

--| A `{` starting a line at the block's own column may start the type
--| (`allow_brace_at_block_column`).
def allowBrace (modes: Modes): {Parse Item} Modes := allowBraceOn modes left()

def allowBraceOn (modes: Modes) (items: List Item): Modes := match items, modes.limit with
  | [item, .._], Some limit =>
    if item.kind == LBrace && item.leaf.token.lineStart && item.leaf.token.column == limit && !modes.endsGuard item then
      { modes | allow = Some item.index }
    else modes
  | _, _ => modes

--| A binder's type (`binder_type`): an ability row there is refused.
def binderType (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  let allowed := allowBrace modes
  match allowed.peek, left() with
    | Some LBrace, [open, ..rest] =>
      match skipGroup [] [open, ..rest] with
        | Some [next, .._] if typeStarts next.kind => fatal "an ability row can't be written in a parameter's type"
        | _ => full self allowed
    | _, _ => full self allowed

def typeStarts: Tok → Bool
  | Upper => True
  | Lower => True
  | LParen => True
  | LBracket => True
  | TypeU => True
  | PropU => True
  | _ => False

-- Types.

--| A result type, possibly with abilities, `{State s} Nat` (`result_type`).
def resultType (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Expr :=
  resultAllowed self (allowBrace modes)

def resultAllowed (self: Goal → {Parse Item} Expr) (allowed: Modes): {Parse Item} Expr :=
  resultRow self allowed (rowAhead allowed)

def rowAhead (allowed: Modes): {Parse Item} Bool := rowOn (allowed.at LBrace) left()

def rowOn (atBrace: Bool) (items: List Item): Bool := atBrace && !recordBracesAhead items

def resultRow (self: Goal → {Parse Item} Expr) (allowed: Modes) (row: Bool): {Parse Item} Expr :=
  if row then effectResult self allowed else full self allowed

def effectResult (self: Goal → {Parse Item} Expr) (allowed: Modes): {Parse Item} Expr :=
  let row := rowOf self allowed
  Effect row (full self allowed)

--| Whether the `{` the items start with is a record literal or update, not
--| an ability row (`record_braces`).
def recordBracesAhead (items: List Item): Bool := match items with
  | [_, first, second, .._] if first.kind == Lower && second.kind == Colon => False
  | [_, ..rest] =>
    let firstUpper := match rest with
      | [first, .._] => first.kind == Upper
      | [] => False
    match recordScan 0 rest with
      | Some True => True
      | Some False => False
      | None =>
        match afterCloseBrace 0 rest with
          | Some after =>
            if firstUpper then False
            else
              match after with
                | [next, .._] => !(next.kind.opensAtom || next.kind == TypeU || next.kind == PropU)
                | [] => False
          | None => False
  | [] => False

--| `Some True` if an `=` comes at the braces' own depth before their `}`,
--| `Some False` if no `}` closes them, `None` if one does with no `=`
--| before it.
def recordScan (depth: Nat): List Item → Option Bool
  | [] => Some False
  | [item, ..rest] =>
    if item.kind == Equals && depth == 0 then Some True
    else if item.kind.isOpener then recordScan (depth + 1) rest
    else if item.kind.isCloser && depth > 0 then recordScan (depth - 1) rest
    else if item.kind == RBrace then None
    else recordScan depth rest

--| The items after the `}` closing braces already open.
def afterCloseBrace (depth: Nat): List Item → Option (List Item)
  | [] => None
  | [item, ..rest] =>
    if item.kind.isOpener then afterCloseBrace (depth + 1) rest
    else if item.kind.isCloser && depth > 0 then afterCloseBrace (depth - 1) rest
    else if item.kind == RBrace then Some rest
    else afterCloseBrace depth rest

--| `{A, B args | e}`, `{e}` or `{}` (`row`).
def rowOf (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Row :=
  let open := modes.expectFixed LBrace "`{`"
  if modes.at Lower && isSome Colon (modes.peekAt 1) then
    fatal "a record type can't be written here: `{` in a type starts an ability row"
  else
    let abilities :=
      if modes.at RBrace || modes.at Pipe then []
      else
        let first := self { modes, level = LevelApp }
        let (entries, _) :=
          commaList (Parse.mark().left + 1) modes (count => False) (() => self { modes, level = LevelApp }) first []
        entries
    let variable :=
      if modes.at Pipe then
        let bar := fixedFrom()
        Some (bar, modes.lower "a row variable")
      else None
    let close := modes.expectFixed RBrace "`}`"
    { open, abilities, variable, close }

--| `(x: A) -> B` or `[x: A] -> B` (`pi_expr`).
def piExpr (self: Goal → {Parse Item} Expr) (modes: Modes) (implicit: Bool): {Parse Item} Expr :=
  let binder := if implicit then implicitBinder self modes else binderGroup self modes False
  refuseAttributes binder.attributes "a function type's parameter"
  let arrow := modes.expect Arrow "`->`"
  FunctionType binder arrow (resultType self modes)

-- Declarations.

--| What came before a declaration: a namespace line, an import, a
--| declaration that parsed.
type Seen = { hasNamespace: Bool, hasImports: Bool, hasDecls: Bool }

def Seen.start: Seen := { hasNamespace = False, hasImports = False, hasDecls = False }

def Seen.after (seen: Seen): Decl → Seen
  | Namespace _ _ => { seen | hasNamespace = True }
  | Import _ _ _ _ _ => { seen | hasImports = True }
  | _ => { seen | hasDecls = True }

--| One declaration group, whole (`parse_tokens`' loop body, then `finish`).
def declaration (seen: Seen): {Parse Item} Decl :=
  let modes := Modes.start
  let attributes := attributesOf modes
  let refusedOn := match attributes, modes.peek with
    | [], _ => None
    | _, None => Some "attributes must be followed by the declaration they apply to"
    | _, Some KwNamespace => Some (misplaced "a namespace line")
    | _, Some KwImport => Some (misplaced "an import")
    | _, Some KwTest => Some (misplaced "a test")
    | _, Some KwAbility => Some (misplaced "an ability")
    | _, _ => None
  match refusedOn with
    | Some message => fatal message
    | None =>
      let decl := match modes.peek with
        | Some KwNamespace =>
          if seen.hasNamespace then fatal "a file has only one namespace line"
          else if seen.hasImports || seen.hasDecls then
            fatal "the namespace line must come first, before imports and declarations"
          else namespaceLine modes
        | Some KwImport => if seen.hasDecls then fatal "imports go at the top of the file" else importLine modes
        | _ => declarationBody modes attributes
      if left().isEmpty then decl else modes.fail "the end of the declaration"

def namespaceLine (modes: Modes): {Parse Item} Decl :=
  let keyword := fixedFrom()
  match modes.peek with
    | Some Upper => Namespace keyword bump()
    | Some Lower => fatal "each part of a namespace's name starts with a capital letter"
    | _ => modes.fail "a namespace, such as `Day05`"

def importLine (modes: Modes): {Parse Item} Decl :=
  let keyword := fixedFrom()
  let path := if modes.at Upper then bump() else modes.fail "a namespace, such as `List`"
  if wordAhead modes "as" then
    fatal "`import M as A` isn't Stitchwort: a namespace is imported as an item of the namespace above it"
  else
    let open := modes.expectFixed LParen "`(` and the names to import"
    let imported :=
      if modes.at DotDot then
        let dots := fixedFrom()
        if modes.at RParen then ImportAll dots else fatal (mixedImport path)
      else ImportItems (importItems (Parse.mark().left + 1) modes path [])
    Import keyword path open imported (modes.expectFixed RParen "`)`")

def mixedImport (path: Word): Text :=
  "`..` imports everything from a namespace, so it goes on its own: `import ${path.text} (..)`"

def importItems (fuel: Nat) (modes: Modes) (path: Word) (found: List ImportItem): {Parse Item} List ImportItem :=
  match fuel, left() with
    | Succ more, [item, .._] if (item.kind == Lower || item.kind == Upper) && !isQualified item && !modes.stops item =>
      let name := bump()
      let alias := importAlias modes name
      let done := [{ name, alias }, ..found]
      if modes.at Comma then
        let _ := bump()
        importItems more modes path done
      else done.reverse
    | _, _ => if modes.at DotDot && !found.isEmpty then fatal (mixedImport path) else modes.fail "a name to import"

def importAlias (modes: Modes) (name: Word): {Parse Item} Option (Comments, Word) :=
  if wordAhead modes "as" then
    let asWord := fixedFrom()
    match left() with
      | [alias, .._] if (alias.kind == Lower || alias.kind == Upper) && !isQualified alias && !modes.stops alias =>
        if startsUpper name.text != startsUpper alias.text then
          let case := if startsUpper name.text then "a capital letter" else "a lower-case letter"
          fatal "`${name.text}` starts with ${case}, so its new name must too"
        else Some (asWord, bump())
      | _ => modes.fail "the name to use instead, as in `x as y`"
  else None

def startsUpper (text: Text): Bool := match text.toList with
  | [first, .._] => first.isAsciiUppercase
  | [] => False

--| A declaration other than a namespace line or an import (`decl`).
def declarationBody (modes: Modes) (attributes: List Attributes): {Parse Item} Decl := match modes.peek with
  | Some KwType => dataDecl modes attributes
  | Some KwInterface => dataDecl modes attributes
  | Some KwInstance => definition modes attributes None None
  | Some KwAbility => abilityDecl modes
  | Some KwTest => testDecl modes
  | Some KwExport =>
    let exported := fixedFrom()
    if modes.at KwOpaque then
      let opaqued := fixedFrom()
      afterOpaque modes
      definition modes attributes (Some exported) (Some opaqued)
    else if modes.at KwDef || modes.at KwTheorem then definition modes attributes (Some exported) None
    else modes.fail "`def`, `theorem` or `opaque` after `export`"
  | Some KwOpaque =>
    let opaqued := fixedFrom()
    afterOpaque modes
    definition modes attributes None (Some opaqued)
  | Some KwDef => definition modes attributes None None
  | Some KwTheorem => definition modes attributes None None
  | Some Lower =>
    if wordAhead modes "rules" && isSome Lower (modes.peekAt 1) then ruleSetDecl modes else fatal missingKeyword
  | Some Upper => fatal missingKeyword
  | _ => modes.fail "a declaration"

--| `rules name := [r1, <- r2]` (`rule_set`).
def ruleSetDecl (modes: Modes): {Parse Item} Decl :=
  let keyword := fixedFrom()
  let name := if modes.at Upper then modes.upperQualified "a name" else modes.lowerQualified "a name"
  if modes.at Equals then fatal defEquals
  else
    let colonEq := modes.expectFixed ColonEq "`:=`"
    if !modes.at LBracket then modes.fail "the set's rules, in brackets: `[r1, <- r2]`"
    else RuleSetDecl keyword name colonEq (ruleSet expressionAt modes)

def missingKeyword: Text :=
  "expected a declaration: `def`, `theorem`, `type`, `ability`, `interface`, `instance` or `test`"

def afterOpaque (modes: Modes): {Parse Item} () := match modes.peek with
  | Some KwDef => ()
  | Some KwTheorem => fatal "a theorem can't be `opaque`"
  | Some KwInstance => fatal "an instance can't be `opaque`"
  | Some KwExport => fatal "`export` goes before `opaque`"
  | _ => modes.fail "`def` after `opaque`"

--| `test "name" := e`
def testDecl (modes: Modes): {Parse Item} Decl :=
  let keyword := fixedFrom()
  let name := if modes.at Str then bump() else modes.fail "the test's name, in quotes"
  if modes.at Equals then fatal defEquals
  else
    let colonEq := modes.expectFixed ColonEq "`:=`"
    Test keyword name colonEq (expressionAt { modes, level = LevelFull })

def defEquals: Text := "a definition's body follows `:=`; `=` is equality"

--| `def`, `theorem` or `instance` at the top level.
def definition (modes: Modes) (attributes: List Attributes) (exportKeyword opaqueKeyword: Option Comments):
    {Parse Item} Decl :=
  let (header, body) := definitionParts expressionAt modes exportKeyword opaqueKeyword None
  Definition attributes header body

--| The header, then the body (`definition`). `local` is the column of a
--| local definition's keyword, `d`; a top-level one's is column 0, and its
--| body is where the Rust parser recovers from errors (`recover`).
def definitionParts (self: Goal → {Parse Item} Expr) (modes: Modes)
    (exportKeyword opaqueKeyword: Option Comments) (local: Option Nat):
    {Parse Item} (Header, DefBody) :=
  let kind := match modes.peek with
    | Some KwTheorem => DefTheorem
    | Some KwInstance => DefInstance
    | _ => DefPlain
  let keyword := fixedFrom()
  let name := if modes.at Upper then modes.upperQualified "a name" else modes.lowerQualified "a name"
  let forallKeyword :=
    if modes.at KwForall then
      if kind != DefTheorem then fatal "`∀` before the parameters is only for theorems"
      else
        let word := bump()
        if modes.at LParen || modes.at LBracket then Some word
        else modes.fail "a parameter such as `(x: Nat)` after `∀`"
    else None
  let params := headerParams self modes.sealed
  let colon := fixedFrom()
  let headerModes := match local with
    | Some _ => { modes | lines = [{ column = 0, many = False, kind = DefHeaderLine }] }
    | None => modes
  let result := resultType self headerModes
  let isInstance := kind == DefInstance
  let decreasingClause :=
    if modes.at KwDecreasing then
      if isInstance then fatal "an instance can't have `decreasing`"
      else
        let keyword := fixedFrom()
        Some (keyword, self { modes = headerModes, level = LevelFull })
    else None
  let afterDecreasing := if decreasingClause.isSome then allowColonEq modes else modes
  let unfoldingClause :=
    if afterDecreasing.at KwUnfolding then
      if isInstance then fatal "an instance can't have `unfolding`"
      else
        let keyword := fixedFrom()
        Some (keyword, unfoldingNames (Parse.mark().left + 1) afterDecreasing [])
    else None
  let afterUnfolding := if unfoldingClause.isSome then allowColonEq afterDecreasing else afterDecreasing
  if afterUnfolding.at KwDecreasing && unfoldingClause.isSome then fatal "`decreasing` goes before `unfolding`"
  else
    let header := {
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
    }
    let bodyModes := match local with
      | Some _ => afterUnfolding
      | None => { afterUnfolding | recover = !isInstance && (afterUnfolding.at ColonEq || afterUnfolding.at Pipe) }
    (header, definitionBody self bodyModes result isInstance (local.getOrElse 0))

--| After `decreasing` or `unfolding`, `:=` may start a line of its own,
--| at the declaration's column.
def allowColonEq (modes: Modes): {Parse Item} Modes := match left() with
  | [next, .._] if next.kind == ColonEq && next.leaf.token.lineStart => { modes | allow = Some next.index }
  | _ => modes

def headerParams (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} List Group :=
  Parse.loop (() => if !modes.at Colon then Some (headerGroup self modes GroupParam None) else None)

def unfoldingNames (fuel: Nat) (modes: Modes) (found: List Word): {Parse Item} List Word := match fuel with
  | Succ more =>
    let name :=
      if modes.at Upper then modes.upperQualified "the name of an opaque definition"
      else modes.lowerQualified "the name of an opaque definition"
    if modes.at Comma then
      let _ := bump()
      unfoldingNames more modes [name, ..found]
    else [name, ..found].reverse
  | Zero => found.reverse

--| `:= e`, arms, or nothing (`definition_body`).
def definitionBody (self: Goal → {Parse Item} Expr) (modes: Modes) (result: Expr) (isInstance: Bool) (d: Nat):
    {Parse Item} DefBody :=
  let body := match modes.peek with
    | Some ColonEq =>
      let colonEq := fixedFrom()
      let value := self { modes, level = LevelFull }
      if modes.at Pipe then fatal "a definition has a `:=` body or arms, not both" else Assigned colonEq value
    | Some Pipe => Arms (definitionArms self modes d)
    | Some Equals => fatal defEquals
    | None => if isEquation result then fatal defEquals else Primitive
    | _ => modes.fail "`:=` and the body, or arms starting with `|` on their own lines"
  match body, left() with
    | Primitive, _ if isInstance => fatal "an instance needs a body"
    | _, [next, .._] if next.kind == KwWhere =>
      fatal "`where` isn't part of Stitchwort: declare helpers with a local `def`"
    | _, _ => body

--| Whether a definition's type is an equation, which swallowed its body.
def isEquation: Expr → Bool
  | Infix InfixBinary _ operator _ => operator.text == "="
  | Paren _ inner _ => isEquation inner
  | _ => False

--| The arms under a header (`arms`): each `|` starts a line at one
--| column, right of `d`, the column of the definition's keyword.
def definitionArms (self: Goal → {Parse Item} Expr) (modes: Modes) (d: Nat): {Parse Item} List Arm := match left() with
  | [first, .._] =>
    if !first.leaf.token.lineStart then fatal "arms start on their own lines"
    else if first.leaf.token.column <= d then fatal "arms are indented further than the definition they belong to"
    else definitionArmsFrom self { modes | limit = Some first.leaf.token.column } d
  | [] => modes.fail "`|`"

def definitionArmsFrom (self: Goal → {Parse Item} Expr) (modes: Modes) (d: Nat): {Parse Item} List Arm :=
  let column := modes.limit.getOrElse 0
  Parse.loop (() =>
    match left() with
      | [] => None
      | [next, .._] =>
        if !next.leaf.token.lineStart then modes.fail "the end of the arm"
        else if next.leaf.token.column <= d || next.kind == KwWhere then None
        else if next.kind == Pipe && next.leaf.token.column == column then
          Some (definitionArm self { modes | allow = Some offset() })
        else if next.kind == Pipe then fatal "this `|` doesn't line up with the definition's arms"
        else fatal "expected `|` and another arm, or the end of the definition, but found ${next.spelled}")

def definitionArm (self: Goal → {Parse Item} Expr) (modes: Modes): {Parse Item} Arm :=
  let bar := bump()
  let patterns := armPatterns modes
  let guard := guardOf self modes
  let body := armBody self modes (anyAbsurd patterns) "`=>` and the arm's body"
  { bar, patterns, guard, body }

--| `type T …` or `interface I …` (`data`).
def dataDecl (modes: Modes) (attributes: List Attributes): {Parse Item} Decl :=
  let isInterface := modes.at KwInterface
  let keyword := fixedFrom()
  let name :=
    if isInterface then modes.upperQualified "an interface name (starting with an uppercase letter)"
    else modes.upperQualified "a data type name (starting with an uppercase letter)"
  let word := if isInterface then "interface" else "type"
  let params := dataParams modes word name
  let indices :=
    if modes.at Colon then
      let colon := fixedFrom()
      let (steps, last) := dataIndices (Parse.mark().left + 1) modes []
      Some { colon, steps, last }
    else None
  let indexed := indices.map (found => !found.steps.isEmpty) |> .getOrElse False
  if isInterface then
    if indexed then fatal "an interface can't have indices"
    else
      let equals := modes.expectFixed Equals "`=` and the interface's fields, `{ … }`"
      if !modes.at LBrace then modes.fail "`{` and the interface's fields"
      else Data attributes True keyword name params indices (RecordBody equals (bracedFields modes))
  else if !modes.at Equals then Data attributes False keyword name params indices Abstract
  else
    let equals := fixedFrom()
    if !(modes.at LBrace || modes.at Pipe) then
      if indexed then fatal "a type synonym can't have indices: `->` after the colon is only for a data type's indices"
      else Data attributes False keyword name params indices (Synonym equals (typeSynonym modes name))
    else if modes.at LBrace then
      match abilityRowInBraces left() with
        | Some row =>
          fatal
            "an ability row like `{${row}}` can't be given a name with `type` yet; write the row where it's used, such as `() -> {${row}} Nat`"
        | None => Data attributes False keyword name params indices (RecordBody equals (bracedFields modes))
    else
      let constructors := constructorsOf modes
      Data attributes False keyword name params indices (Sum equals constructors)

def dataParams (modes: Modes) (word: Text) (name: Word): {Parse Item} List Group := Parse.loop (() =>
  if modes.at LParen then
    let binder := binderGroup expressionAt modes False
    refuseAttributes binder.attributes "a data type's parameter"
    Some binder
  else if modes.at LBracket && implicitBinderAhead (Parse.mark().left + 1) left() then
    let binder := implicitBinder expressionAt modes
    refuseAttributes binder.attributes "a data type's parameter"
    if binder.auto.isNone then fatal "a type's parameters in brackets must be `auto`, like `[auto ord: Ord k]`"
    else if binder.names.isEmpty then
      fatal "a type's `auto` parameter needs a name, so it can be given by name: `[auto ord: Ord k]`"
    else Some binder
  else
    match left() with
      | [param, .._] if param.kind == Lower && !isQualified param && !modes.stops param =>
        fatal "a ${word}'s parameter `${param.text}` needs its type, in brackets"
      | _ => None)

--| The indices after a data type's `:`, each with its arrow, and the last
--| type.
def dataIndices (fuel: Nat) (modes: Modes) (found: List (Index, Word)): {Parse Item} (List (Index, Word), Expr) :=
  match fuel with
    | Zero => (found.reverse, fatal "the parser ran out of fuel in a data type's indices")
    | Succ more =>
      if isSome LParen modes.peek && piBinderAhead left() then
        let binder := binderGroup expressionAt modes False
        refuseAttributes binder.attributes "a data type's index"
        let arrow := modes.expect Arrow "`->`"
        dataIndices more modes [(IndexBinder binder, arrow), ..found]
      else
        let index := expressionAt { modes, level = LevelApp }
        if modes.at Arrow then
          let arrow := bump()
          dataIndices more modes [(IndexType index, arrow), ..found]
        else (found.reverse, index)

--| After `type S =`: the type, and checks for a sum or a constructor
--| written without its `|` (`type_synonym`).
def typeSynonym (modes: Modes) (name: Word): {Parse Item} Expr :=
  let synonym := expressionAt { modes, level = LevelFull }
  if modes.at Pipe then fatal (ambiguousSynonym name "a sum type without its leading `|`")
  else if annotatedArgument synonym then
    fatal (ambiguousSynonym name "a constructor with named fields, without its leading `|`")
  else synonym

def ambiguousSynonym (name: Word) (what: Text): Text :=
  "`type ${name.text} = …` names a type, but this looks like ${what}"

def annotatedArgument: Expr → Bool
  | App _ arguments => arguments.any (matches
    | Annotation _ _ _ _ _)
  | _ => False

--| `{IO, Fail}` after `type T =`: the row's names, `IO, Fail` or `IO, …`.
def abilityRowInBraces: List Item → Option Text
  | [_, first, after, ..rest] if first.kind == Upper && (after.kind == Comma || after.kind == RBrace) =>
    Some (rowNames [first.text] [after, ..rest])
  | _ => None

def rowNames (found: List Text): List Item → Text
  | [comma, name, after, ..rest] if comma.kind == Comma
      && name.kind == Upper
      && (after.kind == Comma || after.kind == RBrace) => rowNames [name.text, ..found] [after, ..rest]
  | [close, .._] if close.kind == RBrace => found.reverse.joinWith ", "
  | _ => "${found.reverse.joinWith ", "}, …"

--| `{ name: Text, step: Nat := 1 }` (`braced_fields`).
def bracedFields (modes: Modes): {Parse Item} Fields :=
  let open := modes.expectFixed LBrace "`{`"
  let inner := modes.inBrackets
  let (fields, trailingComma) := if inner.at RBrace then ([], False) else fieldsFrom (Parse.mark().left + 1) inner []
  { open, fields, trailingComma, close = inner.expectFixed RBrace "`,` or `}`" }

def fieldsFrom (fuel: Nat) (modes: Modes) (found: List Field): {Parse Item} (List Field, Bool) := match fuel with
  | Zero => (found.reverse, False)
  | Succ more =>
    if modes.at RBrace then (found.reverse, True)
    else
      let attributes := attributesOf modes
      let name := modes.lower "a field name"
      let colon := modes.expectFixed Colon "`:`"
      let annotation := expressionAt { modes, level = LevelFull }
      let default :=
        if modes.at ColonEq then
          let colonEq := fixedFrom()
          Some (colonEq, expressionAt { modes, level = LevelFull })
        else None
      let done := [{ attributes, name, colon, annotation, default }, ..found]
      if modes.at Comma then
        let _ := bump()
        fieldsFrom more modes done
      else (done.reverse, False)

def constructorsOf (modes: Modes): {Parse Item} List Constructor :=
  if modes.at Pipe then
    Parse.loop (() =>
      if modes.at Pipe then
        let bar := fixedFrom()
        let attributes := attributesOf modes
        let name := modes.upper "a constructor name (starting with an uppercase letter)"
        let fields := constructorParts (Parse.mark().left + 1) modes name False False []
        let result :=
          if modes.at Colon then
            let colon := fixedFrom()
            Some (colon, expressionAt { modes, level = LevelApp })
          else None
        Some { bar, attributes, name, fields, result }
      else None)
  else modes.fail "`|` and a constructor, or `{` and a record's fields"

--| A constructor's fields: in brackets or in braces, not both, and its
--| implicit ones.
def constructorParts (fuel: Nat) (modes: Modes) (name: Word) (bracketed braced: Bool) (found: List ConstructorPart):
    {Parse Item} List ConstructorPart :=
  match fuel with
    | Zero => found.reverse
    | Succ more =>
      if modes.at LBrace && !braced then
        if bracketed then
          fatal
            "`${name.text}` has fields in brackets already; declare all of its explicit fields in brackets or all in braces"
        else
          let fields := bracedFields modes
          if fields.fields.isEmpty then fatal "`${name.text}` declares no fields in its braces"
          else constructorParts more modes name bracketed True [PartFields fields, ..found]
      else if modes.at LParen then
        if braced then
          fatal
            "`${name.text}` has its fields in braces already; declare all of its explicit fields in braces or all in brackets"
        else constructorParts more modes name True braced [PartGroup (binderGroup expressionAt modes True), ..found]
      else if modes.at LBracket && implicitBinderAhead (Parse.mark().left + 1) left() then
        let binder := implicitBinder expressionAt modes
        if binder.auto.isSome then fatal "a constructor's implicit fields can't be `auto`"
        else constructorParts more modes name bracketed braced [PartGroup binder, ..found]
      else found.reverse

--| `ability Name (params) where`, then one operation a line (`ability`).
def abilityDecl (modes: Modes): {Parse Item} Decl :=
  let keyword := fixedFrom()
  let name := modes.upperQualified "an ability name (starting with an uppercase letter)"
  let params := abilityParams modes
  let whereKeyword := modes.expectFixed KwWhere "`where`"
  match modes.peek, left() with
    | Some _, [first, .._] =>
      let column := first.leaf.token.column
      Ability keyword name params whereKeyword (operations { modes | limit = Some column } column)
    | _, _ => modes.fail "the ability's operations"

def abilityParams (modes: Modes): {Parse Item} List Group := Parse.loop (() =>
  if modes.at LParen then
    let binder := binderGroup expressionAt modes False
    refuseAttributes binder.attributes "an ability's parameter"
    Some binder
  else None)

--| One operation, with the `allow` that keeps its first token.
def operation (modes: Modes): {Parse Item} Operation :=
  let opModes := { modes | allow = Some offset() }
  let name := opModes.lower "an operation name"
  let colon := opModes.expectFixed Colon "`:`"
  let annotation := expressionAt { modes = opModes, level = LevelInline }
  { name, colon, annotation }

def operations (modes: Modes) (column: Nat): {Parse Item} List Operation :=
  let first := operation modes
  let rest := Parse.loop (() =>
    match left() with
      | [next, .._] if next.leaf.token.lineStart && next.leaf.token.column == column => Some (operation modes)
      | _ => None)
  [first, ..rest]

-- The file.

--| Splits a file's leaves into declaration groups (`split_decls`): a
--| token in column 0 starts one, except `:=`, a token inside an open `@[`
--| that isn't a declaration's keyword, a `,` or closer while a bracket of
--| the declaration is open, and the token after a group that is only
--| attributes so far.
type Splitter = {
  depth: Nat,
  opening: Bool,
  attributesOnly: Bool,
  openBrackets: Nat
}

def Splitter.start: Splitter := { depth = 0, opening = False, attributesOnly = False, openBrackets = 0 }

def groupsOf (leaves: List Leaf): List (List Leaf) := splitFrom Splitter.start [] [] leaves

def splitFrom (state: Splitter) (current: List Leaf) (groups: List (List Leaf)): List Leaf → List (List Leaf)
  | [] => (if current.isEmpty then groups else [current.reverse, ..groups]).reverse
  | [leaf, ..rest] =>
    let token := leaf.token
    let kind := token.kind
    let inside := state.depth > 0 || state.opening
    let continues := state.openBrackets > 0 && (kind == Comma || kind.isCloser)
    let starts :=
      token.column == 0
        && kind != ColonEq
        && ((!inside && !state.attributesOnly && !continues) || (inside && kind.startsGroup))
    let (began, current, groups) :=
      if starts then
        (
          { depth = 0, opening = False, attributesOnly = True, openBrackets = 0 },
          [],
          if current.isEmpty then groups else [current.reverse, ..groups]
        )
      else (state, current, groups)
    let brackets :=
      if kind.isOpener then began.openBrackets + 1
      else if kind.isCloser then began.openBrackets - 1
      else began.openBrackets
    let next :=
      if kind == At && began.depth == 0 then { began | opening = True, openBrackets = brackets }
      else if kind.isOpener && (began.depth > 0 || began.opening) then
        { began | depth = began.depth + 1, opening = False, openBrackets = brackets }
      else if kind.isCloser && began.depth > 0 then { began | depth = began.depth - 1, openBrackets = brackets }
      else if began.depth == 0 then { began | attributesOnly = False, opening = False, openBrackets = brackets }
      else { began | openBrackets = brackets }
    splitFrom next [leaf, ..current] groups rest

--| A declaration's keyword, which starts a group even inside an open `@[`.
def Tok.startsGroup: Tok → Bool
  | KwType => True
  | KwInterface => True
  | KwDef => True
  | KwTheorem => True
  | KwExport => True
  | KwOpaque => True
  | KwInstance => True
  | KwAbility => True
  | KwTest => True
  | KwNamespace => True
  | KwImport => True
  | _ => False

--| A file's tree (`parse_tokens`, then the lowering's checks): the first
--| error, in file order, if any declaration has one. Each declaration is
--| parsed on its own items, as the Rust parser parses each group, and
--| checked as the lowering checks it once it has parsed, so a lowering
--| error comes before a later declaration's syntax error.
def parseFile (lexed: Lexed): Result SourceFile Text := match lexed.leaves with
  | [first, .._] if first.token.column != 0 => Err "declarations must start at the beginning of a line"
  | [first, .._] if first.token.kind == ColonEq => Err "`:=` can't start a declaration"
  | leaves =>
    match parseGroups Seen.start (groupsOf leaves) [] with
      | Ok decls => Ok { decls, end = lexed.end.comments }
      | Err message => Err message

def parseGroups (seen: Seen) (groups: List (List Leaf)) (found: List Decl): Result (List Decl) Text := match groups with
  | [] => Ok found.reverse
  | [group, ..rest] =>
    match Parse.run (items group) (() => declaration seen) with
      | Err failure => Err (failure.messages.head.getOrElse "the parser failed without a message")
      | Ok decl =>
        match decl.loweringError with
          | Some message => Err message
          | None => parseGroups (seen.after decl) rest [decl, ..found]

--| Trivia's comments, without layout.
def Trivia.comments (trivia: Trivia): Comments :=
  let above := trivia.leading.map (comment => { text = comment.text, blankBefore = comment.blankLines > 0 })
  { above, after = trivia.trailing.map (comment => comment.text), blankBefore = trivia.blankLines > 0 }

--| The diagnostic code the Rust side gives a message, for `fmt`'s first
--| line: `E-PARSE` but for the few messages with codes of their own.
def codeOf (message: Text): Text :=
  if message.startsWith "attributes can't be used on" || message == "attributes can't be written here" then
    "E-ATTRIBUTE"
  else if message == defEquals then "E-DEF-EQUALS"
  else if message.startsWith "a `calc` chain goes one way" then "E-CALC-RELATION"
  else if message.startsWith "the namespace line must come first" then "E-NAMESPACE-NOT-FIRST"
  else if message.startsWith "`where` isn't part of Stitchwort" then "E-WHERE"
  else if message == orPatternBinds then "E-OR-PATTERN-BINDS"
  else if message.contains "` is already a parameter of `" then "E-DUPLICATE-PARAMETER"
  else "E-PARSE"
