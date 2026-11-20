--| The four tidy passes (docs/proposals/self-hosted-fmt.md §2,
--| `crates/fmt/src/passes.rs`), each the shared traversal
--| (`Syntax/Traverse.sw`) with steps, so that a pass's correctness is the
--| traversal's one generic fact and a few facts about its steps:
--|
--| - P1: a `∀` after the name of every theorem with explicit parameters;
--| - P2: no comma before a closer (a tuple has two items at least, so
--|   none becomes a bracketed item);
--| - P3: no redundant round brackets after a row or around a binder's whole
--|   type;
--| - P4: adjacent parameters of one type merge into one group.
--|
--| Each pass reads the tree the pass before it left, as Rust re-parses
--| the text between passes.
--|
--| The Rust P3 asks the parser whether a candidate's text still reads as the
--| same declaration. Here the same answer is the grammar's precedence
--| table, `Expr.level` and `leftNeeds`: bare, an expression stands at the
--| left end of an operator only if it binds at least as tightly as the
--| operator's left side needs (the table was read off the Rust pass's
--| answers, and checked against its levels in `Syntax/Parser.sw`).

namespace Fmt
import Std (Bool, Fail, List, Nat, Option, Result, Text)
import Syntax (
  BindingKind,
  Comments,
  Decl,
  DefKind,
  Expr,
  Group,
  GroupKind,
  Header,
  Leaf,
  Lexed,
  InfixKind,
  Param,
  Row,
  Pattern,
  SourceFile,
  Steps,
  Tok,
  Word,
  parseFile
)

-- Running a pass.

--| The declarations traversed with `on`. A step that never fails (every
--| tidy pass's) leaves nothing for the `Err` case, so a declaration is
--| kept if one did.
def SourceFile.apply (file: SourceFile) (on: Steps): SourceFile := { file | decls = applyDecls on file.decls }

def applyDecls (on: Steps): List Decl → List Decl
  | [] => []
  | [decl, ..rest] =>
    match Fail.toResult (() => decl.traverse on) with
      | Ok done => [done, ..applyDecls on rest]
      | Err _ => [decl, ..applyDecls on rest]

--| A token with no comment on it.
def Word.bare (word: Word): Bool := word.comments.above.isEmpty && word.comments.after.isNone

-- P1: `∀` after a theorem's name.

--| A group written with `(`: a theorem's explicit parameter.
def Group.explicit (group: Group): Bool := group.kind == GroupParam && !group.implicit

def withForall (header: Header): Header := match header with
  | { kind = DefTheorem, forallKeyword = None, params, .. } =>
    if params.any Group.explicit then { header | forallKeyword = Some { text = "∀", comments = Comments.none } }
    else header
  | _ => header

def SourceFile.withForall (file: SourceFile): SourceFile := file.apply { Steps.keep | header = withForall }

-- P2: no comma before a closer.

def withoutCommaExpr: Expr → Expr
  | Tuple open items _ close => Tuple open items False close
  | ListOf open items _ close => ListOf open items False close
  | Record open base fields _ close => Record open base fields False close
  | other => other

def withoutCommaPattern: Pattern → Pattern
  | PatternTuple open items _ close => PatternTuple open items False close
  | PatternList open items _ tail close => PatternList open items False tail close
  | PatternRecord fields => PatternRecord { fields | trailingComma = False }
  | PatternCtorFields name fields => PatternCtorFields name { fields | trailingComma = False }
  | other => other

def SourceFile.withoutTrailingCommas (file: SourceFile): SourceFile := file.apply { Steps.keep |
  expr = withoutCommaExpr,
  pattern = withoutCommaPattern,
  fields = (fields => { fields | trailingComma = False }),
  attributes = (attributes => { attributes | trailingComma = False }),
  ruleSet = (set => { set | trailingComma = False })
}

-- P3: no spare bracket pair after a row or around a parameter's whole type.

--| How tightly an expression binds at its top, in `Syntax/Parser.sw`'s
--| ladder (higher is tighter); `0` for what reads as far to the right as it
--| can (`fun`, `match`, `if`, a block) and so stands bare only at the very
--| end.
def Expr.level: Expr → Nat
  | Infix kind _ operator _ => infixLevel kind operator.text
  | Chain _ _ => 6
  | Prefix _ _ => 18
  | App _ _ | CtorFields _ (Record _ (Some _) _ _ _) => 20
  | Binding _ _ _ _ _ |
      If _ _ _ _ _ _ _ |
      Match _ _ _ _ |
      ClauseLambda _ _ _ |
      Section _ |
      Facts _ _ _ |
      FieldAccess None _ _ |
      Block _ _ _ |
      LetIn _ _ _ |
      Handle _ _ _ _ |
      Reify _ _ _ _ _ |
      Induct _ _ _ _ _ |
      Calc _ _ _ |
      Rewrite _ _ _ _ |
      Cases _ _ _ |
      Walk _ _ _ => 0
  | FunctionType _ _ _ | Effect _ _ => 1
  | _ => 22

def infixLevel (kind: InfixKind) (operator: Text): Nat := match kind with
  | InfixSeq => 0
  | InfixArrow => 1
  | InfixIff => 2
  | InfixPipe => 8
  | InfixRange => 10
  | InfixMembership => 6
  | InfixBinary =>
    if operator == "||" || operator == "∨" then 4
    else if operator == "&&" || operator == "∧" then 5
    else if operator == "++" then 12
    else if operator == "+" || operator == "-" then 14
    else if operator == "*" || operator == "/" || operator == "%" then 16
    else 6

--| The least level an expression needs to stand bare as the left operand of
--| an infix operator: one above the operator's own where it nests to the
--| right or doesn't chain (`++`, `∧`, `∨`, `↔`), its own where it nests to
--| the left (`+`, `*`, `|>`).
def leftNeeds (kind: InfixKind) (operator: Text): Nat := match kind with
  | InfixSeq | InfixArrow => 2
  | InfixIff => 3
  | InfixPipe => 8
  | InfixRange => 12
  | InfixMembership => 8
  | InfixBinary =>
    if operator == "||" || operator == "∨" then 5
    else if operator == "&&" || operator == "∧" then 6
    else if operator == "++" then 14
    else if operator == "+" || operator == "-" then 14
    else if operator == "*" || operator == "/" || operator == "%" then 16
    else 8

--| Whether the expression reads as a function type with bare tokens: an
--| `→` among the operators outside any bracket, or its whole inside
--| brackets of its own. Rust's `holds_function`.
def holdsFunction: Expr → Bool
  | Paren _ inner _ => holdsFunction inner
  | other => arrowAtTop other

def arrowAtTop: Expr → Bool
  | Infix InfixArrow _ _ _ => True
  | Infix _ left _ right => arrowAtTop left || arrowAtTop right
  | FunctionType _ _ _ => True
  | Binding _ _ _ _ body => arrowAtTop body
  | If _ _ condition _ whenTrue _ whenFalse => arrowAtTop condition || arrowAtTop whenTrue || arrowAtTop whenFalse
  | Prefix _ operand => arrowAtTop operand
  | Chain first rest => arrowAtTop first || chainHasArrow rest
  | _ => False

def chainHasArrow: List (Word, Expr) → Bool
  | [] => False
  | [(_, operand), ..rest] => arrowAtTop operand || chainHasArrow rest

--| Whether `{…}` reads as a record rather than a row on its own: the
--| first ability starts with a lowercase name (`{e}`, `{e, f}`, `{f x}`,
--| `{E.e}`) or there is none (`{}`). What follows such a row must not start
--| like the continuation of a record's expression.
def rowReadsAsRecord (row: Row): Bool := match row.abilities with
  | [] => True
  | [first, ..rest] => headIsLower first

def headIsLower: Expr → Bool
  | Atom kind _ => kind == Lower
  | App head _ => headIsLower head
  | _ => False

--| Whether the expression starts with a token (or a keyword) that a bare
--| `{e}` before it would swallow: a section's `.`, a prefix operator,
--| `match`, `if`, `include` and the like. A `fun`, `facts` and the atoms
--| read fine after it.
def startsApart: Expr → Bool
  | Prefix _ _ |
      Section _ |
      FieldAccess None _ _ |
      Include _ _ |
      If _ _ _ _ _ _ _ |
      Match _ _ _ _ |
      ClauseLambda _ _ _ |
      LetIn _ _ _ |
      Block _ _ _ |
      Handle _ _ _ _ |
      Reify _ _ _ _ _ |
      Induct _ _ _ _ _ |
      Calc _ _ _ |
      Rewrite _ _ _ _ |
      Cases _ _ _ |
      Walk _ _ _ => True
  | _ => False

--| A bracket pair that stays: a negative numeral (`{Fail} -1` doesn't read
--| as the number), before a membership test a `!` (which the grammar
--| refuses to apply to the element), and after a row that reads as a record
--| (`recordRow`) whatever `startsApart`.
def keepsBrackets (membership recordRow: Bool): Expr → Bool
  | Prefix operator (Atom Num _) | Prefix operator (Atom Float _) => operator.text == "-"
  | Prefix operator _ => (membership && operator.text != "-") || recordRow
  | other => recordRow && startsApart other

--| The result of a row, with the redundant brackets at its left end
--| removed: `floor` is the level the ancestors on the way down need of what
--| stands at the left (`membership` keeps a prefix operator's bracket).
def dropLeft (floor: Nat) (membership recordRow: Bool): Expr → Expr
  | Paren open inner close =>
    if open.bare
      && close.bare
      && !holdsFunction inner
      && floor <= inner.level
      && !keepsBrackets membership recordRow inner then
      dropLeft floor membership recordRow inner
    else Paren open inner close
  | Infix kind left operator right =>
    let needs := leftNeeds kind operator.text
    let nested := dropLeft (Nat.max floor needs) (membership || kind == InfixMembership) recordRow left
    Infix kind nested operator right
  | Chain first rest => Chain (dropLeft (Nat.max floor 8) membership recordRow first) rest
  | App head arguments => App (dropLeft (Nat.max floor 22) membership recordRow head) arguments
  | FieldAccess (Some target) dot field =>
    FieldAccess (Some (dropLeft (Nat.max floor 22) membership recordRow target)) dot field
  | other => other

def dropAfterRow: Expr → Expr
  | Effect row result => Effect row (dropLeft 0 False (rowReadsAsRecord row) result)
  | other => other

--| `(x: ((T)))` and its kin: the brackets around a binder's whole type,
--| while none has a comment. A layer with a comment stays, the ones inside
--| it still go.
def stripBinderType: Expr → Expr
  | Paren open inner close =>
    if open.bare && close.bare then stripBinderType inner else Paren open (stripBinderType inner) close
  | other => other

--| A group in round brackets with names, a type and no default.
def dropGroupParens (group: Group): Group :=
  if !group.implicit && group.colon.isSome && group.default.isNone && group.auto.isNone then
    { group | annotation = group.annotation.map stripBinderType }
  else group

def dropParam: Param → Param
  | Grouped group => Grouped (dropGroupParens group)
  | TypedPattern open pattern colon annotation close =>
    TypedPattern open pattern colon (stripBinderType annotation) close
  | other => other

--| The binders reached from a header's type without going inside brackets:
--| the declaration's own parameters, function types' binders, `∀`'s and
--| lambdas' groups and a typed `(x: T)`.
def spineBinders: Expr → Expr
  | FunctionType binder arrow result => FunctionType (dropGroupParens binder) arrow (spineBinders result)
  | Effect row result => Effect row (spineBinders result)
  | Infix kind left operator right => Infix kind (spineBinders left) operator (spineBinders right)
  | Binding kind keyword params arrow body => Binding kind keyword (params.map dropParam) arrow (spineBinders body)
  | Annotation open value colon annotation close => Annotation open value colon (stripBinderType annotation) close
  | App head arguments => App (spineBinders head) (spineAll arguments)
  | Prefix operator operand => Prefix operator (spineBinders operand)
  | other => other

def spineAll: List Expr → List Expr
  | [] => []
  | [first, ..rest] => [spineBinders first, ..spineAll rest]

def dropBinderBrackets (header: Header): Header := match header with
  | { params, result, decreasingClause, .. } => { header |
    params = params.map dropGroupParens,
    result = spineBinders result,
    decreasingClause = decreasingClause.map ((word, measure) => (word, spineBinders measure))
  }

def dropDeclBinders: Decl → {Fail} Decl
  | Definition attributes header body => Definition attributes (dropBinderBrackets header) body
  | other => other

def SourceFile.withoutSpareBrackets (file: SourceFile): SourceFile :=
  file.apply { Steps.keep | expr = dropAfterRow, decl = dropDeclBinders }

-- P4: adjacent parameters of one type merge.

--| A group that may be merged: names, a type, no `auto`, no default, no
--| attributes, and no comment on it except above its opening bracket.
def Group.mergeable (group: Group): Bool :=
  group.bare
    && group.auto.isNone
    && group.attributes.isEmpty
    && group.colon.isSome
    && group.default.isNone
    && !group.names.isEmpty
    && group.names.all (name => name.text != "auto")
    && group.annotation.isSome

--| The tokens of a group's type, as its dump's lines show them.
def Group.typeLines (group: Group): List Text := match group.annotation with
  | Some written => written.lines 0
  | None => []

--| Whether `next` goes into the group `current` is the merge of so far:
--| the same kind of group, the same brackets and the same type, no comment
--| between them, and a type that doesn't name any of their names (a
--| dependent `(x: P x) (y: P x)`); and `meaning` reading them alike. So
--| P4 merges what the Rust pass merges, or less: never two types that
--| differ only in what `meaning` forgets, such as a comment.
def joins (current next: Group): Bool := rustJoins current next && meaningJoins current next

--| `joins`' test as the Rust pass has it, on the groups' tokens.
def rustJoins (current next: Group): Bool :=
  current.mergeable
    && next.mergeable
    && current.kind == next.kind
    && current.implicit == next.implicit
    && next.open.above.isEmpty
    && current.typeLines == next.typeLines
    && !next.typeLines.any (line => (current.names ++ next.names).any (name => line.trim == name.text))

--| Whether `meaning` reads the two groups alike but for their names, and
--| splits each of them and their merge into one group a name, so that
--| merging them keeps `meaning`. On a parsed file `rustJoins` implies it
--| (`meaning` blanks comments and forgets brackets the earlier passes have
--| already dropped); it is checked so that the proof needn't go through
--| the dump.
def meaningJoins (current next: Group): Bool :=
  !current.names.isEmpty
    && !next.names.isEmpty
    && next.meaningForm.map Group.withoutNames == current.meaningForm.map Group.withoutNames
    && current.meaningSplits
    && next.meaningSplits
    && { current | names = current.names ++ next.names }.meaningSplits

--| The group as `meaning` reads it: its type walked with `meaning`'s
--| steps, its comments blanked and its whole type unwrapped.
def Group.meaningForm (group: Group): Option Group := match Fail.toResult (() => group.traverse meaningSteps) with
  | Ok done => Some done.blank.plainType
  | Err _ => None

def Group.withoutNames (group: Group): Group := { group | names = [] }

def Group.meaningSplits (group: Group): Bool := match group.meaningForm with
  | Some form => form.splits
  | None => False

def mergeGroups: List Group → List Group
  | [] => []
  | [first, ..rest] => mergeFrom first rest

def mergeFrom (current: Group): List Group → List Group
  | [] => [current]
  | [next, ..rest] =>
    if joins current next then mergeFrom { current | names = current.names ++ next.names } rest
    else [current, ..mergeFrom next rest]

def mergeParams: List Param → List Param
  | [] => []
  | [Grouped first, ..rest] => mergeParamsFrom first rest
  | [other, ..rest] => [other, ..mergeParams rest]

def mergeParamsFrom (current: Group): List Param → List Param
  | [] => [Grouped current]
  | [Grouped next, ..rest] =>
    if joins current next then mergeParamsFrom { current | names = current.names ++ next.names } rest
    else [Grouped current, ..mergeParamsFrom next rest]
  | [other, ..rest] => [Grouped current, other, ..mergeParams rest]

def mergeHeader (header: Header): Header := match header.kind with
  | DefInstance => header
  | _ => { header | params = mergeGroups header.params }

def mergeBinding: Expr → Expr
  | Binding BindsExists keyword params arrow body => Binding BindsExists keyword params arrow body
  | Binding kind keyword params arrow body => Binding kind keyword (mergeParams params) arrow body
  | other => other

def SourceFile.withMergedParameters (file: SourceFile): SourceFile :=
  file.apply { Steps.keep | header = mergeHeader, expr = mergeBinding }

--| The four passes in order.
def SourceFile.tidy (file: SourceFile): SourceFile :=
  file.withForall.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters

-- The passes on a lexed file.

--| The tree after each pass, in order.
type Tidied = {
  first: SourceFile,
  second: SourceFile,
  third: SourceFile,
  fourth: SourceFile
}

--| The passes on one parse of the leaves settled with their last commas
--| bare (`Lexed.settledOnce`): the comments are where the Rust P2 leaves
--| them, deleting those commas from the text and settling again, and the
--| tree is the one the source reads as.
def Lexed.tidied (lexed: Lexed): Result Tidied Text := match parseFile lexed.settledOnce with
  | Err message => Err message
  | Ok parsed =>
    let first := parsed.withForall
    let second := first.withoutTrailingCommas
    let third := second.withoutSpareBrackets
    Ok { first, second, third, fourth = third.withMergedParameters }
