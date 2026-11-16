--| Sprig's printing rules, P1 to P10 (toy-formatter.md §1): each construct
--| of the tree as a layout document. The rules read only the tree, so the
--| output can't depend on the author's layout.
--|
--| P1 (every construct is a group) and P10 (strings and names never split,
--| width in characters) are the engine's; the rest are below, each where
--| its construct is laid out. Every token is printed by `token`, with its
--| comments beside it (P8).
--|
--| The tree nests through lists (a call's arguments, a block's statements),
--| so the functions recurse through a helper for each list, defined with
--| them, rather than with `map`: the termination checker sees a list's
--| items as smaller only when they are taken apart by a pattern.

namespace Toy.Fmt
import Toy.Doc (..)
import Toy.Syntax (..)
import Std (List, Option, Text)

--| The width `toyfmt` prints in unless told otherwise.
def defaultWidth: Nat := 80

def SourceFile.print (file: SourceFile) (width: Nat): Text := Toy.Doc.print file.layout width

--| P9: declarations one a line at column 0, with the kept blank lines.
def SourceFile.layout (file: SourceFile): Doc := match file.declarations with
  | [] => Empty
  | declarations => Doc.concat [Doc.concat (declarationLines 0 declarations), HardLine]

--| Each declaration on its line, the first of them the `index`th of the file.
def declarationLines (index: Nat): List (Spaced Declaration) → List Doc
  | [] => []
  | [{ blankBefore, line }, ..rest] =>
    [Doc.concat [lineStart index blankBefore, line.layout], ..declarationLines (index + 1) rest]

--| What starts a line of a vertical list: nothing for the first, which
--| starts where the list does; a line break, and the kept blank line, for
--| the others (P9).
def lineStart (index: Nat) (blankBefore: Bool): Doc :=
  if index == 0 then Empty else Doc.concat [HardLine, if blankBefore then Blank else Empty]

--| P8: a token with its comments, the own-line ones each on a line of
--| their own above it and the trailing one after it. Where the layout
--| didn't start a line at the token, the engine starts one for the
--| comments above it, and where it would put code after the trailing one,
--| it starts one for that code: comment breaks, indented as continuation
--| lines.
def token (comments: Comments) (text: Text): Doc :=
  Doc.concat [commentsAbove comments.above, Doc.text text, trailingComment comments.after]

def commentsAbove (comments: List Comment): Doc := match comments with
  | [] => Empty
  | _ => Doc.concat [LineStart, ..comments.map (comment => Doc.concat [Doc.text comment.text, CommentEnd])]

--| A trailing comment stays at the end of its line after one space, so
--| the group around it breaks if anything would follow it there.
def trailingComment: Option Comment → Doc
  | None => Empty
  | Some comment => LineSuffix comment.text

--| A closing bracket: as any token, except that own-line comments above
--| it are about the items before it, so they go at the items'
--| indentation, and the bracket on a line of its own below them.
def closer (comments: Comments) (text: Text): Doc := match comments.above with
  | [] => token comments text
  | above =>
    let lines := above.map (comment => Doc.text comment.text) |> joined HardLine
    Doc.concat [Nest 2 (Doc.concat [LineStartHere, lines]), HardLine, Doc.text text, trailingComment comments.after]

def Declaration.layout: Declaration → Doc
  | Function fnComments name nameComments takes open parameters close equals body =>
    Doc.concat [header fnComments name nameComments takes open parameters close equals, body.afterEquals equals]
  | Value letComments name nameComments equals body => binding letComments name nameComments equals body
  | DeclarationNote comment => Doc.text comment.text

--| `let name = body`, a declaration or a statement.
def binding (letComments: Comments) (name: Text) (nameComments equals: Comments) (body: Body): Doc := Doc.concat [
  token letComments "let",
  Doc.text " ",
  token nameComments name,
  Doc.text " ",
  token equals "=",
  body.afterEquals equals
]

--| P2: the parameters on the header's line, else one a line at +4, with
--| `) =` back at the header's column.
def header (fnComments: Comments) (name: Text) (nameComments: Comments) (takes: Option Comments) (open: Comments)
    (parameters: List ParameterGroup) (close equals: Comments):
    Doc :=
  let opening :=
    Doc.concat [token fnComments "fn", Doc.text " ", token nameComments name, takesDoc takes, token open "("]
  let closing := Doc.concat [closer close ")", Doc.text " ", token equals "="]
  match parameters with
    | [] => Doc.concat [opening, closing]
    | _ =>
      let listed := parameterDocs parameters |> joined Line
      Doc.group (Doc.concat [opening, Nest 4 (Doc.concat [SoftLine, listed]), SoftLine, closing])

--| ` takes ` where it was written, as written.
def takesDoc: Option Comments → Doc
  | None => Empty
  | Some comments => Doc.concat [Doc.text " ", token comments "takes", Doc.text " "]

--| Each parameter group, and its comma but the last's.
def parameterDocs: List ParameterGroup → List Doc
  | [] => []
  | [group] => [group.layout]
  | [group, ..rest] => [Doc.concat [group.layout, token Comments.none ","], ..parameterDocs rest]

--| A group's names a space apart, then `: ` and their type.
def ParameterGroup.layout: ParameterGroup → Doc
  | Untyped { name, comments } => token comments name
  | Typed names colon annotation => Doc.concat [
    token names.head.comments names.head.name,
    namesAfter names.tail,
    token colon ":",
    Doc.text " ",
    annotation.layout
  ]

def namesAfter: List Named → Doc
  | [] => Empty
  | [{ name, comments }, ..rest] => Doc.concat [Doc.text " ", token comments name, namesAfter rest]

def TypeExpr.layout: TypeExpr → Doc
  | TypeName name comments => token comments name
  | TypeBracketed open inner close => Doc.concat [token open "(", inner.layout, closer close ")"]

--| P3: a body after `=` goes on the `=` line if it fits there, else on one
--| line below at +2, else below and broken. A list opens on the `=` line
--| whenever its first line fits there (P5). A block always goes below, and
--| so does any body after a trailing comment on `=`.
def Body.afterEquals (body: Body) (equals: Comments): Doc := match body with
  | { statements = [{ line = Bare value, .. }] } if equals.after.isNone =>
    let doc := value.layout
    match value with
      | ListLiteral _ _ _ => Choice [Doc.concat [Doc.text " ", Flatten doc], Doc.concat [Doc.text " ", doc]]
      | _ => Choice [Doc.concat [Doc.text " ", Flatten doc], OneLineBelow doc, below doc]
  | { statements = [{ line = Bare value, .. }] } => below value.layout
  | _ => below body.block

--| On the lines below, at +2.
def below (doc: Doc): Doc := Nest 2 (Doc.concat [HardLine, doc])

--| The body's statements, one a line, from where it starts.
def Body.block: Body → Doc
  | { statements } => Doc.concat (statementLines 0 statements)

def statementLines (index: Nat): List (Spaced Statement) → List Doc
  | [] => []
  | [{ blankBefore, line }, ..rest] => [lineStart index blankBefore, line.layout, ..statementLines (index + 1) rest]

def Statement.layout: Statement → Doc
  | Let letComments name nameComments equals body => binding letComments name nameComments equals body
  | Bare value => value.layout
  | StatementNote comment => Doc.text comment.text

def Expr.layout: Expr → Doc
  | Var name comments => token comments name
  | NumberLiteral digits comments => token comments digits
  | StringLiteral written comments => token comments written
  | Bracketed open inner close => Doc.concat [token open "(", inner.layout, closeAfter inner (closer close ")")]
  | ListLiteral open items close => listLayout open items close
  | Call callee open arguments close => Doc.concat [callee.layout, argumentsLayout open arguments close]
  | Field target dot name nameComments => Doc.concat [target.layout, token dot ".", token nameComments name]
  | Negate minus operand =>
    Doc.concat [token minus "-", Doc.text (if operand.startsWithMinus then " " else ""), operand.layout]
  | Binary operator sign left right =>
    match chainParts operator.level left ++ [link operator sign right.layout] with
      | [first, ..links] => Doc.group (Doc.concat [first, Nest 2 (Doc.concat links)])
      | [] => Empty
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    ifLayout ifComments condition thenComments whenTrue elseComments whenFalse

--| Whether the expression's text starts with `-`. A `-` right before it
--| would make `--`, which starts a comment, so `Negate` spaces them apart.
def Expr.startsWithMinus: Expr → Bool
  | Negate _ _ => True
  | Binary _ _ left _ => left.startsWithMinus
  | Call callee _ _ _ => callee.startsWithMinus
  | Field target _ _ _ => target.startsWithMinus
  | _ => False

--| `closer` (a `,` or closing bracket) after `expr`: on the line below if
--| `expr` ends in a trailing comment, at the indentation in force, rather
--| than where a comment break would put it.
def closeAfter (expr: Expr) (closer: Doc): Doc := if expr.endsWithComment then Doc.concat [HardLine, closer] else closer

--| P6: an operator chain of one level, from its left-nested tree: `a - b +
--| c` is `a`, then `- b` and `+ c` each after a line break. Operands of
--| tighter levels are left whole, as groups of their own.
def chainParts (level: Nat): Expr → List Doc
  | Binary operator sign left right if operator.level == level =>
    chainParts level left ++ [link operator sign right.layout]
  | operand => [operand.layout]

def link (operator: Operator) (sign: Comments) (operand: Doc): Doc :=
  Doc.concat [Line, token sign operator.spelling, Doc.text " ", operand]

--| P7: `if c then a else b` on one line if it fits, else `else` starts a
--| line at the `if`'s indentation.
def ifLayout (ifComments: Comments) (condition: Expr) (thenComments: Comments) (whenTrue: Body)
    (elseComments: Comments) (whenFalse: Body):
    Doc :=
  Doc.group
    (Doc.concat [
      token ifComments "if",
      Doc.text " ",
      condition.layout,
      Doc.text " ",
      token thenComments "then",
      branch thenComments whenTrue,
      Line,
      token elseComments "else",
      elseBranch elseComments whenFalse
    ])

--| A branch of an `if` goes after its keyword (`then` or `else`, whose
--| comments are `keyword`) if it fits there, else below at +2. A block
--| always goes below, and so does any branch after a trailing comment on
--| the keyword.
def branch (keyword: Comments) (body: Body): Doc := match body with
  | { statements = [{ line = Bare value, .. }] } if keyword.after.isNone =>
    let doc := value.layout
    Choice [Doc.concat [Doc.text " ", Flatten doc], below doc]
  | { statements = [{ line = Bare value, .. }] } => below value.layout
  | _ => below body.block

--| An `else` whose branch is another `if` keeps it on its line, so a chain
--| of `else if`s lines up at the first `if`'s column; not after a comment
--| on `else` or above that `if`, where the `if` starts a line and so a
--| block.
def elseBranch (elseComments: Comments) (body: Body): Doc := match body with
  | {
      statements = [{ line = Bare (If ifComments condition thenComments whenTrue innerElse whenFalse), .. }]
    } if elseComments.after.isNone && ifComments.above.isEmpty =>
    Doc.concat [Doc.text " ", ifLayout ifComments condition thenComments whenTrue innerElse whenFalse]
  | _ => branch elseComments body

--| P4: the arguments on the call's line, else one a line at +2 with `)` at
--| the call's line.
def argumentsLayout (open: Comments) (arguments: List Expr) (close: Comments): Doc := match arguments with
  | [] => Doc.concat [token open "(", closer close ")"]
  | _ =>
    Doc.group
      (Doc.concat [
        token open "(",
        Nest 2 (Doc.concat [SoftLine, itemDocs arguments |> joined Line]),
        SoftLine,
        closer close ")"
      ])

--| P5: list items fill their lines, the `]` after the last. A trailing
--| comment on the last item puts the `]` on the line below, at the list's
--| indentation: after the `]`, the comment would belong to it.
def listLayout (open: Comments) (items: List Expr) (close: Comments): Doc := match items.last with
  | None => Doc.concat [token open "[", closer close "]"]
  | Some last =>
    Doc.group (Doc.concat [token open "[", Nest 2 (Fill (itemDocs items)), closeAfter last (closer close "]")])

--| Each item, and its comma but the last's: after the item's own line if
--| the item ends in a trailing comment.
def itemDocs: List Expr → List Doc
  | [] => []
  | [value] => [value.layout]
  | [value, ..rest] => [Doc.concat [value.layout, closeAfter value (token Comments.none ",")], ..itemDocs rest]
