-- The goal after a `rewrite` whose left side is inside a call: only that
-- call is opened. `Parse.Follows` stays folded, and so does the right-hand
-- `line others`, which doesn't mention `items`. (examples/accept/
-- rewrite-partial-unfold.sw; docs/proposals/partial-unfold.md.)
import Std (List, Parse)

def SameNat (x y: Nat): Prop := x = y

def here (): {Parse Nat} Nat := Parse.mark().offset

def size (items: List Nat): Nat := items.length

def line (items: List Nat): {Parse Nat} Nat := here() + size items

theorem followsLine ∀ (items others: List Nat)
    (same: size items = size others):
    Parse.Follows SameNat SameNat (() => line items) (() => line others) :=
  rewrite same then ?
