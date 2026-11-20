-- A continuation fixed by abstracting what the first parser read, where the
-- goal writes the mark's field through its accessor (`here.left`) and the
-- parser, once run, holds it as the state's own projection
-- (`state.at.left`). `Parse.followsThen`'s `j` has to be found by comparing
-- the two, so they are compared with accessors written as projections
-- (SW-4356): `j := here => pick (ahead (here.left + 1) items)`. Before, `j`
-- and `k` had to be spelled with `[j := …][k := …]`.
import Std (Parse)

def SameNat (x y: Nat): Prop := x = y

def ahead (fuel: Nat) (items: List Nat): Bool := match fuel, items with
  | Zero, _ => False
  | _, [] => False
  | Succ more, [item, .._] => item == more

def pick (typed: Bool): {Parse Nat} Nat := if typed then Parse.mark().left else 0

def isTyped (items: List Nat): Bool := match items with
  | [] => False
  | [item, .._] => item == 0

def lookup (items: List Nat): {Parse Nat} Nat :=
  if isTyped items then 7
  else
    let here := Parse.mark()
    pick (ahead (here.left + 1) items)

theorem followsPick ∀ (typed: Bool): Parse.Follows SameNat SameNat (() => pick typed) (() => pick typed) :=
  match typed with
    | True =>
      Parse.followsMap [alike := SameNat] (m => m.left) (m => m.left) Parse.followsMark (m n alike => alike.right.right)
    | False => Parse.followsDone byComputing

theorem followsLookup ∀ (items others: List Nat)
    (same: items = others):
    Parse.Follows SameNat SameNat (() => lookup items) (() => lookup others) :=
  rewrite same then
    match isTyped others with
      | True => Parse.followsDone byComputing
      | False => Parse.followsThen Parse.followsMark (here hereTwin marks =>
        rewrite <- marks.right.right then followsPick (ahead (here.left + 1) others))
