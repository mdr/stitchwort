-- A bind whose bound computation isn't one call (docs/syntax.md,
-- "byWalking"): `let y := size (look()); k y` runs `look()`, then
-- `size` of its value, then `k`. The walk reads it as `let x := look();
-- let y := size x; k y`: the bound computation is walked as the first
-- premise of the family's bind lemma, and where it ends, in a call or a
-- value, the walk goes on in the code after it. One run and two.

import Std (Parse, Option, Nat, Bool, List)

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

@[walk]
theorem givesLook: Parse.Gives Parse.Invariant.any (() => look()) ((v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)

def size (found: Option Nat): {Parse Nat} Nat := match found with
  | Some n => n
  | None => 0

@[walk]
theorem givesSize ∀ (found: Option Nat): Parse.Gives Parse.Invariant.any (() => size found) (n => n = n) := byWalking []

-- The bound computation ends in a call: `y` and its fact are `size`'s.
def sizeOfLook(): {Parse Nat} Nat :=
  let y := size (look())
  y + 1

theorem givesSizeOfLook: Parse.Gives Parse.Invariant.any (() => sizeOfLook()) (n => 1 <= n) := byWalking []

-- It ends in a value, `found` computed from `look()`'s, and the split
-- after it is on that.
def present(): {Parse Nat} Bool :=
  let found := (look()).isSome
  if found then True else False

theorem givesPresent: Parse.Gives Parse.Invariant.any (() => present()) (b => True) := byWalking []

-- Two in one expression, neither named; and one whose bound computation
-- splits, a call in one branch and a value in the other.
def total(): {Parse Nat} Nat := size (look()) + size (look())

theorem givesTotal: Parse.Gives Parse.Invariant.any (() => total()) (n => n = n) := byWalking []

def sizeIfPresent(): {Parse Nat} Nat :=
  let y := size (if (look()).isSome then Some (size (look())) else None)
  y + 1

theorem givesSizeIfPresent: Parse.Gives Parse.Invariant.any (() => sizeIfPresent()) (n => 1 <= n) := byWalking []

-- Two runs: the pair of bound computations walked in lockstep, with the
-- values' equality rewritten as for any bind.
def SameNat (x y: Nat): Prop := x = y

def here(): {Parse Nat} Nat := Parse.mark().offset

@[walk]
theorem followsHere: Parse.Follows SameNat SameNat (() => here()) (() => here()) :=
  Parse.followsMap [alike := SameNat] (m => m.offset) (m => m.offset) Parse.followsMark (m n alike => alike.right.left)

def double (n: Nat): {Parse Nat} Nat :=
  let at := here()
  n + n + at

@[walk]
theorem followsDouble ∀ (n nTwin: Nat)
    (same: n = nTwin):
    Parse.Follows SameNat SameNat (() => double n) (() => double nTwin) :=
  byWalking [] then arithmetic [same]

def doubleHere(): {Parse Nat} Nat :=
  let d := double (here())
  d + 1

theorem followsDoubleHere: Parse.Follows SameNat SameNat (() => doubleHere()) (() => doubleHere()) := byWalking []
