--| Where a list may start with an `auto` call (SW-4128; docs/reviews/SW-4166-carried-walk-plan.md §2.1). The parser
--| tests for an implicit binder, `[auto Ord …` (`namelessAutoAt`), only where a full expression starts (`exprPlain`):
--| a declaration's type and value, a paren's inside, a tuple's or a list's item, and an arrow's right side. There such a
--| list reads as a binder, so a parsed tree has none; anywhere else, as an argument or an operand, it is a list
--| (`f [auto Ord]`, `x + [auto Ord]`). `Expr.autoPlaced` says so of a tree, and read-back takes it.
--|
--| It also says no name is `byWalking` (SW-4427): at a full expression's start, `byWalking [` reads as a walk, a form
--| outside slice 1, and the slice keeps the word out everywhere (`Fmt.Expr.within1`, `Fmt.Expr.grammar1`).

namespace Syntax.AutoPlaced
import Std (Bool, List, Text)
import Syntax (..)

--| A call of `auto` on a type's name, `auto Ord …`: first in a list that starts a full expression, `[auto Ord]` reads
--| as an implicit binder (`namelessAutoAt`), not as a list.
def Expr.autoCall: Expr → Bool
  | App (Atom headKind word) [Atom argumentKind _, .._] =>
    headKind == Lower && word.text == "auto" && argumentKind == Upper
  | Infix _ left _ _ => left.autoCall
  | _ => False

--| A list's first item, where `full` says the list starts a full expression: then it is no `auto` call.
def autoLead (full: Bool) (one: Expr): Bool := !full || !one.autoCall

--| An operator whose right side is a full expression: the arrow.
def arrowKind1: InfixKind → Bool
  | InfixArrow => True
  | _ => False

--| No list that starts a full expression starts with an `auto` call, and no name is `byWalking`. `full` says whether
--| `expr` starts one; it passes down the leftmost spine (a call's head, an operator's left side), which starts where
--| `expr` does, and every bracket's inside and an arrow's right side start one of their own.
def Expr.autoPlaced (expr: Expr) (full: Bool): Bool := match expr with
  | Atom _ word => word.text != "byWalking"
  | Paren _ inner _ => inner.autoPlaced True
  | Tuple _ items _ _ => autoPlacedAll True items
  | ListOf _ [] _ _ => True
  | ListOf _ [one, ..others] _ _ => autoLead full one && one.autoPlaced True && autoPlacedAll True others
  | App head arguments => head.autoPlaced full && autoPlacedAll False arguments
  | Prefix _ operand => operand.autoPlaced False
  | Infix kind left _ right => left.autoPlaced full && right.autoPlaced (arrowKind1 kind)
  | _ => True

def autoPlacedAll (full: Bool): List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.autoPlaced full && autoPlacedAll full rest

--| A declaration's type and value are full expressions.
def Decl.autoPlaced: Decl → Bool
  | Definition _ header (Assigned _ value) => header.result.autoPlaced True && value.autoPlaced True
  | _ => True

def SourceFile.autoPlaced (file: SourceFile): Bool := file.decls.all Decl.autoPlaced

--| Placed as a full expression, an expression is placed anywhere: only the start's list is tested more.
theorem autoPlacedInner ∀ (expr: Expr) (placed: expr.autoPlaced True = True): expr.autoPlaced False = True :=
  match expr, placed with
    | ListOf _ [one, ..others] _ _, placed => Bool.andIntro byComputing (Bool.andRight placed)
    | App head _ | Infix _ head _ _, placed =>
      Bool.andIntro (autoPlacedInner head (Bool.andLeft placed)) (Bool.andRight placed)
    | Atom _ _ | Paren _ _ _ | Tuple _ _ _ _ | Prefix _ _, placed => placed
    | ListOf _ [] _ _, _ => byComputing
    | other, _ => cases

--| A list's first item, placed as a full expression's, is no `auto` call.
theorem autoLeadFull ∀ (one: Expr) (lead: autoLead True one = True): one.autoCall = False :=
  match call: one.autoCall with | False => byComputing

--| A list's first item that isn't placed as a full expression's is an `auto` call.
theorem autoLeadCall ∀ (one: Expr) (lead: autoLead True one = False): one.autoCall = True :=
  match call: one.autoCall with | True => byComputing
