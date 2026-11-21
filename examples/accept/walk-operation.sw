-- An operation performed directly in the code walked (docs/syntax.md,
-- "byWalking"): `Parse.mark()` is a call of the operation `mark`, whose
-- lemma is found as a function's is (std's `Parse.givesMark` is
-- `@[walk]`), and code after it is read as a bind of the operation. A
-- fuel taken from the mark (`Parse.mark().left + 1`) gives a call that
-- computes at once, `down (Succ m.left)`; it is still the call, and its
-- lemma fits it by its arguments, as it fits `downFrom 5 3`.

import Std (Parse, Option, Nat, Bool, List)

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

@[walk]
theorem givesLook: Parse.Gives Parse.Invariant.any (() => look()) ((v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)

-- The mark bound, then used.
def marked(): {Parse Nat} Nat :=
  let here := Parse.mark()
  let found := look()
  here.left

theorem givesMarked: Parse.Gives Parse.Invariant.any (() => marked()) (n => n = n) := byWalking []

-- The mark inside a bound computation.
def nested(): {Parse Nat} Nat :=
  let y := Parse.mark().left + 1
  let found := look()
  y

theorem givesNested: Parse.Gives Parse.Invariant.any (() => nested()) (n => 1 <= n) := byWalking []

def down (fuel: Nat): {Parse Nat} Nat := match fuel with
  | Zero => 0
  | Succ more =>
    let x := look()
    down more

theorem givesDown ∀ (fuel: Nat): Parse.Gives Parse.Invariant.any (() => down fuel) (n => True) := byWalking []

-- A fuel from the mark, in tail position and bound.
def fromMark(): {Parse Nat} Nat := down (Parse.mark().left + 1)

theorem givesFromMark: Parse.Gives Parse.Invariant.any (() => fromMark()) (n => True) := byWalking [givesDown]

def bound(): {Parse Nat} Nat :=
  let n := down (Parse.mark().left + 1)
  n

theorem givesBound: Parse.Gives Parse.Invariant.any (() => bound()) (n => True) := byWalking [givesDown]

-- A call whose arguments make it compute at once, with no operation in
-- sight: the lemma's call, stuck on its unknowns, is matched by arguments.
def downFrom (fuel extra: Nat): {Parse Nat} Nat := downStep fuel (look())

def downStep (fuel: Nat) (seen: Option Nat): {Parse Nat} Nat := down fuel

theorem givesDownFrom ∀ (fuel extra: Nat): Parse.Gives Parse.Invariant.any (() => downFrom fuel extra) (n => True) :=
  Parse.givesThen givesLook (seen _ => givesDown fuel)

def five(): {Parse Nat} Nat := downFrom 5 3

theorem givesFive: Parse.Gives Parse.Invariant.any (() => five()) (n => True) := byWalking [givesDownFrom]
