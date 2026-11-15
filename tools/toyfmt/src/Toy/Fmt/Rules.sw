--| Sprig's printing rules, P1 to P10 (toy-formatter.md §1): each construct
--| of the tree as a layout document. The rules read only the tree, so the
--| output can't depend on the author's layout.
--|
--| P1 (every construct is a group) and P10 (strings and names never split,
--| width in characters) are the engine's; the rest are below, each where
--| its construct is laid out.
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

--| A file printed: its text, and how many declarations were left as
--| written because a comment was where no rule places one (P8).
type Printed = { text: Text, asWritten: Nat }

def SourceFile.print (file: SourceFile) (width: Nat): Printed := {
  text = Toy.Doc.print file.layout width,
  asWritten = file.declarations.count (spaced => spaced.line |> matches | AsWritten _)
}

--| P9: declarations one a line at column 0, with the kept blank lines.
def SourceFile.layout (file: SourceFile): Doc := match file.declarations with
  | [] => Empty
  | declarations =>
    let lines := declarations.withIndex.map (((index, spaced)) =>
      Doc.concat [lineStart index spaced.blankBefore, spaced.line.layout])
    Doc.concat [Doc.concat lines, HardLine]

--| What starts a line of a vertical list: nothing for the first, which
--| starts where the list does; a line break, and the kept blank line, for
--| the others (P9).
def lineStart (index: Nat) (blankBefore: Bool): Doc :=
  if index == 0 then Empty else Doc.concat [HardLine, if blankBefore then Blank else Empty]

def Declaration.layout: Declaration → Doc
  | Function name parameters body => Doc.concat [header name parameters, body.afterEquals]
  | Value name body => Doc.concat [Doc.text "let ${name} =", body.afterEquals]
  | DeclarationNote comment => Doc.text comment.text
  | AsWritten text => text.lines.map Doc.text |> joined HardLine

--| P2: the parameters on the header's line, else one a line at +4, with
--| `) =` back at the header's column.
def header (name: Text) (parameters: List Text): Doc := match parameters with
  | [] => Doc.text "fn ${name}() ="
  | _ =>
    let listed := parameters.map Doc.text |> joined (Doc.concat [Doc.text ",", Line])
    Doc.group (Doc.concat [Doc.text "fn ${name}(", Nest 4 (Doc.concat [SoftLine, listed]), SoftLine, Doc.text ") ="])

--| P3: a body after `=` goes on the `=` line if it fits there, else on one
--| line below at +2, else below and broken. A list opens on the `=` line
--| whenever its first line fits there (P5). A block always goes below.
def Body.afterEquals: Body → Doc
  | { statements = [{ line = Bare value trailing, .. }] } =>
    let doc := Doc.concat [value.layout, trailingComment trailing]
    match value with
      | ListLiteral _ => Choice [Doc.concat [Doc.text " ", Flatten doc], Doc.concat [Doc.text " ", doc]]
      | _ => Choice [Doc.concat [Doc.text " ", Flatten doc], OneLineBelow doc, below doc]
  | body => below body.block

--| On the lines below, at +2.
def below (doc: Doc): Doc := Nest 2 (Doc.concat [HardLine, doc])

--| The body's statements, one a line, from where it starts.
def Body.block: Body → Doc
  | { statements } => Doc.concat (statementLines 0 statements)

def statementLines (index: Nat): List (Spaced Statement) → List Doc
  | [] => []
  | [{ blankBefore, line }, ..rest] => [lineStart index blankBefore, line.layout, ..statementLines (index + 1) rest]

def Statement.layout: Statement → Doc
  | Let name body => Doc.concat [Doc.text "let ${name} =", body.afterEquals]
  | Bare value trailing => Doc.concat [value.layout, trailingComment trailing]
  | StatementNote comment => Doc.text comment.text

--| P8: a trailing comment stays at the end of its line after one space, so
--| the group around it breaks if anything but closing brackets and commas
--| would follow it there.
def trailingComment: Option Comment → Doc
  | None => Empty
  | Some comment => LineSuffix comment.text

def Expr.layout: Expr → Doc
  | Var name => Doc.text name
  | NumberLiteral digits => Doc.text digits
  | StringLiteral written => Doc.text written
  | Bracketed inner => Doc.concat [Doc.text "(", inner.layout, closeAfter inner (Doc.text ")")]
  | ListLiteral items => listLayout items
  | Call callee arguments => Doc.concat [callee.layout, argumentsLayout arguments]
  | Field target name => Doc.concat [target.layout, Doc.text ".${name}"]
  | Negate operand => Doc.concat [Doc.text (if operand.startsWithMinus then "- " else "-"), operand.layout]
  | Binary operator left right =>
    match chainParts operator.level left ++ [link operator right.layout] with
      | [first, ..links] => Doc.group (Doc.concat [first, Nest 2 (Doc.concat links)])
      | [] => Empty
  | If condition whenTrue whenFalse => ifLayout condition whenTrue whenFalse

--| Whether the expression's text starts with `-`. A `-` right before it
--| would make `--`, which starts a comment, so `Negate` spaces them apart.
def Expr.startsWithMinus: Expr → Bool
  | Negate _ => True
  | Binary _ left _ => left.startsWithMinus
  | Call callee _ => callee.startsWithMinus
  | Field target _ => target.startsWithMinus
  | _ => False

--| Whether the expression's text ends in a trailing comment: an `if` whose
--| last branch is one expression with a comment after it (the comment is
--| that branch's, Tree.sw).
def Expr.endsWithComment: Expr → Bool
  | If _ _ whenFalse => whenFalse.endsWithComment
  | _ => False

def Body.endsWithComment: Body → Bool
  | { statements } => statementsEndWithComment statements

--| Whether the last of the statements ends in a trailing comment.
def statementsEndWithComment: List (Spaced Statement) → Bool
  | [] => False
  | [{ line, .. }] => line.endsWithComment
  | [_, ..rest] => statementsEndWithComment rest

def Statement.endsWithComment: Statement → Bool
  | Bare _ (Some _) => True
  | Bare value None => value.endsWithComment
  | Let _ body => body.endsWithComment
  | StatementNote _ => False

--| `closer` (a `,` or closing bracket) after `expr`: on the line below if
--| `expr` ends in a trailing comment, which would otherwise end up after the
--| closer and so belong to whatever ends there.
def closeAfter (expr: Expr) (closer: Doc): Doc := if expr.endsWithComment then Doc.concat [HardLine, closer] else closer

--| P6: an operator chain of one level, from its left-nested tree: `a - b +
--| c` is `a`, then `- b` and `+ c` each after a line break. Operands of
--| tighter levels are left whole, as groups of their own.
def chainParts (level: Nat): Expr → List Doc
  | Binary operator left right if operator.level == level => chainParts level left ++ [link operator right.layout]
  | operand => [operand.layout]

def link (operator: Operator) (operand: Doc): Doc := Doc.concat [Line, Doc.text "${operator.spelling} ", operand]

--| P7: `if c then a else b` on one line if it fits, else `else` starts a
--| line at the `if`'s indentation.
def ifLayout (condition: Expr) (whenTrue whenFalse: Body): Doc :=
  Doc.group
    (Doc.concat [
      Doc.text "if ",
      condition.layout,
      Doc.text " then",
      branch whenTrue,
      Line,
      Doc.text "else",
      elseBranch whenFalse
    ])

--| A branch of an `if` goes after its keyword if it fits there, else below
--| at +2; a block always goes below.
def branch: Body → Doc
  | { statements = [{ line = Bare value trailing, .. }] } =>
    let doc := Doc.concat [value.layout, trailingComment trailing]
    Choice [Doc.concat [Doc.text " ", Flatten doc], below doc]
  | body => below body.block

--| An `else` whose branch is another `if` keeps it on its line, so a chain
--| of `else if`s lines up at the first `if`'s column.
def elseBranch: Body → Doc
  | { statements = [{ line = Bare (If condition whenTrue whenFalse) None, .. }] } =>
    Doc.concat [Doc.text " ", ifLayout condition whenTrue whenFalse]
  | body => branch body

--| P4: the arguments on the call's line, else one a line at +2 with `)` at
--| the call's line.
def argumentsLayout: List Item → Doc
  | [] => Doc.text "()"
  | arguments =>
    Doc.group
      (Doc.concat [
        Doc.text "(",
        Nest 2 (Doc.concat [SoftLine, itemDocs arguments |> joined Line]),
        SoftLine,
        Doc.text ")"
      ])

--| P5: list items fill their lines, the `]` after the last. An own-line
--| comment above the first item needs a line of its own, and a trailing
--| comment on the last puts the `]` on the line below, at the list's
--| indentation: after the `]`, the comment would belong to what ends there.
def listLayout: List Item → Doc
  | [] => Doc.text "[]"
  | items =>
    let opening := match items with
      | [{ comments = [_, .._], .. }, .._] => HardLine
      | _ => Empty
    let closing := match items.last with
      | Some { trailing = Some _, .. } => Doc.concat [HardLine, Doc.text "]"]
      | Some { value, .. } => closeAfter value (Doc.text "]")
      | None => Doc.text "]"
    Doc.group (Doc.concat [Doc.text "[", Nest 2 (Fill (itemDocs items |> withFirst opening)), closing])

def withFirst (docs: List Doc) (opening: Doc): List Doc := match docs with
  | [] => []
  | [first, ..rest] => [Doc.concat [opening, first], ..rest]

--| Each item with its comments: those above it each on a line of their own
--| at its indentation, the trailing one after its comma (P8).
def itemDocs: List Item → List Doc
  | [] => []
  | [{ comments, value, trailing }] => [itemDoc comments value.layout Empty trailing]
  | [{ comments, value, trailing }, ..rest] =>
    [itemDoc comments value.layout (closeAfter value (Doc.text ",")) trailing, ..itemDocs rest]

def itemDoc (comments: List Comment) (value comma: Doc) (trailing: Option Comment): Doc :=
  let above := comments.map (comment => Doc.concat [Doc.text comment.text, HardLine])
  Doc.concat [..above, value, comma, trailingComment trailing]
