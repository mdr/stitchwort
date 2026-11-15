--| The tree as text, one declaration a line, in brackets: for tests to
--| compare trees and to show where they differ. `==` isn't derived for
--| the tree, whose types refer to each other (an `Expr` holds `Body`s,
--| which hold `Statement`s, which hold `Expr`s), so this stands in for it.
--| Distinct trees dump differently: every node is bracketed with its kind.

namespace Toy.Syntax
import Std (List, Option, Text)

def SourceFile.dump (file: SourceFile): Text :=
  file.declarations.map (spaced => "${blankMark spaced.blankBefore}${spaced.line.dump}\n") |> .joinWith ""

def blankMark (blankBefore: Bool): Text := if blankBefore then "blank " else ""

def Declaration.dump: Declaration → Text
  | Function name parameters body => "(fn ${name} (${parameters.joinWith " "}) ${body.dump})"
  | Value name body => "(let ${name} ${body.dump})"
  | DeclarationNote comment => "(note ${comment.text})"
  | AsWritten text => "(as-written ${text.lines.joinWith "\\n"})"

def Body.dump: Body → Text
  | { statements } => "(body${dumpStatements statements})"

def dumpStatements: List (Spaced Statement) → Text
  | [] => ""
  | [{ blankBefore, line }, ..rest] => " ${blankMark blankBefore}${line.dump}${dumpStatements rest}"

def Statement.dump: Statement → Text
  | Let name body => "(let ${name} ${body.dump})"
  | Bare value trailing => "(bare ${value.dump}${dumpTrailing trailing})"
  | StatementNote comment => "(note ${comment.text})"

def dumpTrailing: Option Comment → Text
  | None => ""
  | Some comment => " (trailing ${comment.text})"

def Expr.dump: Expr → Text
  | Var name => "(var ${name})"
  | NumberLiteral digits => "(number ${digits})"
  | StringLiteral written => "(string ${written})"
  | Bracketed inner => "(bracketed ${inner.dump})"
  | ListLiteral items => "(list${dumpItems items})"
  | Call callee arguments => "(call ${callee.dump}${dumpItems arguments})"
  | Field target name => "(field ${target.dump} ${name})"
  | Negate operand => "(negate ${operand.dump})"
  | Binary operator left right => "(${operator.spelling} ${left.dump} ${right.dump})"
  | If condition whenTrue whenFalse => "(if ${condition.dump} ${whenTrue.dump} ${whenFalse.dump})"

def dumpItems: List Item → Text
  | [] => ""
  | [{ comments, value, trailing }, ..rest] =>
    let above := comments.map (comment => "(comment ${comment.text}) ") |> .joinWith ""
    " (item ${above}${value.dump}${dumpTrailing trailing})${dumpItems rest}"
