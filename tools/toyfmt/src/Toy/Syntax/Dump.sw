--| The tree as text, one declaration a line, in brackets: for tests to
--| compare trees and to show where they differ. `==` isn't derived for
--| the tree, whose types refer to each other (an `Expr` holds `Body`s,
--| which hold `Statement`s, which hold `Expr`s), so this stands in for it.
--| Distinct trees dump differently: every node is bracketed with its kind,
--| and a token's comments follow it as `{…}`.

namespace Toy.Syntax
import Std (List, Option, Text)

def SourceFile.dump (file: SourceFile): Text :=
  file.declarations.map (spaced => "${blankMark spaced.blankBefore}${spaced.line.dump}\n") |> .joinWith ""

def blankMark (blankBefore: Bool): Text := if blankBefore then "blank " else ""

--| Nothing for a token without comments, else `{above … after …}`.
def Comments.dump (comments: Comments): Text :=
  let above := comments.above.map (comment => " above ${comment.text}") |> .joinWith ""
  let after := comments.after.map (comment => " after ${comment.text}") |> .getOrElse ""
  if comments.above.isEmpty && comments.after.isNone then "" else "{${above}${after} }"

def Declaration.dump: Declaration → Text
  | Function fnComments name nameComments takes open parameters close equals body =>
    let listed := parameters.map (parameter => parameter.dump)
    let taken := takes.map (comments => " (takes${comments.dump})") |> .getOrElse ""
    "(fn${fnComments.dump} ${name}${nameComments.dump}${taken} ${open.dump}(${listed.joinWith " "})${close.dump}${equals.dump} ${body.dump})"
  | Value letComments name nameComments equals body =>
    "(let${letComments.dump} ${name}${nameComments.dump}${equals.dump} ${body.dump})"
  | DeclarationNote comment => "(note ${comment.text})"

--| An untyped parameter is its name; a group is `(group names : type)`.
def ParameterGroup.dump: ParameterGroup → Text
  | Untyped parameter => parameter.dump
  | Typed names colon annotation =>
    let listed := [names.head, ..names.tail].map (named => named.dump) |> .joinWith " "
    "(group ${listed} :${colon.dump} ${annotation.dump})"

def Named.dump (named: Named): Text := "${named.name}${named.comments.dump}"

def TypeExpr.dump: TypeExpr → Text
  | TypeName name comments => "${name}${comments.dump}"
  | TypeBracketed open inner close => "(bracketed${open.dump} ${inner.dump}${close.dump})"

def Body.dump: Body → Text
  | { statements } => "(body${dumpStatements statements})"

def dumpStatements: List (Spaced Statement) → Text
  | [] => ""
  | [{ blankBefore, line }, ..rest] => " ${blankMark blankBefore}${line.dump}${dumpStatements rest}"

def Statement.dump: Statement → Text
  | Let letComments name nameComments equals body =>
    "(let${letComments.dump} ${name}${nameComments.dump}${equals.dump} ${body.dump})"
  | Bare value => "(bare ${value.dump})"
  | StatementNote comment => "(note ${comment.text})"

def Expr.dump: Expr → Text
  | Var name comments => "(var ${name}${comments.dump})"
  | NumberLiteral digits comments => "(number ${digits}${comments.dump})"
  | StringLiteral written comments => "(string ${written}${comments.dump})"
  | Bracketed open inner close => "(bracketed${open.dump} ${inner.dump}${close.dump})"
  | ListLiteral open items close => "(list${open.dump}${dumpItems items}${close.dump})"
  | Call callee open arguments close => "(call ${callee.dump}${open.dump}${dumpItems arguments}${close.dump})"
  | Field target dot name nameComments => "(field ${target.dump}${dot.dump} ${name}${nameComments.dump})"
  | Negate minus operand => "(negate${minus.dump} ${operand.dump})"
  | Binary operator sign left right => "(${operator.spelling}${sign.dump} ${left.dump} ${right.dump})"
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    "(if${ifComments.dump} ${condition.dump}${thenComments.dump} ${whenTrue.dump}${elseComments.dump} ${whenFalse.dump})"

def dumpItems: List Expr → Text
  | [] => ""
  | [value, ..rest] => " (item ${value.dump})${dumpItems rest}"
