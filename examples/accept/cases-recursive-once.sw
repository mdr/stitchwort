-- When nothing else is left, `cases` takes apart a value of a recursive
-- type that the goal is stuck on, once (SW-3734, SW-3748, from the toy
-- formatter's passes): each case then computes. A part of that value is
-- never taken apart again, so `cases` doesn't do induction.
import Std (List, Nat)

type Expr =
  | Var (name: Text)
  | Number (digits: Text)
  | Bracketed (inner: Expr)
  | Items (items: List Expr) (trailingComma: Bool)
  | Call (callee: Expr) (arguments: List Expr) (trailingComma: Bool)
  | Field (target: Expr) (name: Text)
  | Negate (operand: Expr)
  | Plus (left: Expr) (right: Expr)
  | Times (left: Expr) (right: Expr)
  | If (condition: Expr) (whenTrue: Expr) (whenFalse: Expr)

def Expr.isPostfix: Expr → Bool
  | Var _ => True
  | Number _ => True
  | Bracketed _ => True
  | Items _ _ => True
  | Call _ _ _ => True
  | Field _ _ => True
  | _ => False

def Expr.isOperand: Expr → Bool
  | Negate _ => True
  | expr => expr.isPostfix

-- A pass that changes a flag nothing above reads.
def dropComma (expr: Expr): Expr := match expr with
  | Items items _ => Items items False
  | Call callee arguments _ => Call callee arguments False
  | other => other

-- What the tree means: the commas forgotten, all the way down.
def Expr.plain: Expr → Expr
  | Bracketed inner => Bracketed inner.plain
  | Items items _ => Items (plainItems items) False
  | Call callee arguments _ => Call callee.plain (plainItems arguments) False
  | Field target name => Field target.plain name
  | Negate operand => Negate operand.plain
  | Plus left right => Plus left.plain right.plain
  | Times left right => Times left.plain right.plain
  | If condition whenTrue whenFalse => If condition.plain whenTrue.plain whenFalse.plain
  | leaf => leaf

def plainItems: List Expr → List Expr
  | [] => []
  | [item, ..rest] => [item.plain, ..plainItems rest]

-- Both sides wait for `expr`, of a ten-constructor type, and neither is
-- stuck on anything else: ten cases, each by computing (a hand-written
-- `match` had ten arms).
theorem dropPlain ∀ (expr: Expr): (dropComma expr).plain = expr.plain := cases

-- A pass's result, tested: the same, through `isPostfix`.
theorem dropPostfix ∀ (expr: Expr) (postfix: expr.isPostfix = True): (dropComma expr).isOperand = True := cases

type Group =
  | Untyped (name: Text)
  | Typed (names: List Text) (colon: Bool) (annotation: Text)

def Group.mergesInto (group next: Group): Bool := match group, next with
  | Typed _ colon name, Typed _ _ annotation => !colon && annotation == name
  | _, _ => False

def Group.size: Group → Nat
  | Untyped _ => 1
  | Typed names _ _ => names.length

def mergeOnto (group: Group) (rest: List Group): List Group := match rest with
  | [] => [group]
  | [next, ..others] =>
    match group, next with
      | Typed names _ _, Typed more colon annotation if group.mergesInto next =>
        [Typed (names ++ more) colon annotation, ..others]
      | _, _ => [group, ..rest]

def total: List Group → Nat
  | [] => 0
  | [group, ..rest] => group.size + total rest

-- The arm that merges is written; every other arm computes, and the
-- wildcard's `cases` takes `rest` apart to see it.
theorem mergeOntoTotal ∀ (group: Group) (rest: List Group): total (mergeOnto group rest) = total [group, ..rest] :=
  match group, rest with
    | Typed names colon name, [Typed more colon2 annotation, ..others] =>
      match merges: (Typed names colon name).mergesInto (Typed more colon2 annotation) with
        | False => byComputing
        | True => arithmetic [List.lengthAppend names more]
    | _, _ => cases
