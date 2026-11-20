-- The two-run walk (docs/syntax.md, "byWalking"): a statement relating
-- two runs, `Parse.Follows same alike first second`, is walked in
-- lockstep, both runs' code at once. Binds in both take one lemma for the
-- pair of calls; where the lemma says the two values are equal, the second
-- run's is rewritten to the first's, so that a split on it is made once; a
-- pair is split in each run alone; the recursive call uses the theorem
-- itself, a parameter's call its hypothesis, and a premise about a
-- function the call passes on is walked too.

import Std (Parse, Option, Nat, Bool, List)

def SameNat (x y: Nat): Prop := x = y

def here(): {Parse Nat} Nat := Parse.mark().offset

--| Registered: every pair of calls of `here` uses it.
@[walk]
theorem followsHere: Parse.Follows SameNat SameNat (() => here()) (() => here()) :=
  Parse.followsMap [alike := SameNat] (m => m.offset) (m => m.offset) Parse.followsMark (m n alike => alike.right.left)

-- Two binds, their values equal; the value's leaf by computation.
def hereTwice(): {Parse Nat} Nat :=
  let first := here()
  let second := here()
  first + second

theorem followsHereTwice: Parse.Follows SameNat SameNat (() => hereTwice()) (() => hereTwice()) := byWalking []

-- A loop: a split on the fuel and on an `if` the equal values share, made
-- once; a parameter's call by its hypothesis; the recursive call by the
-- theorem itself.
def collect (fuel: Nat) (next: () → {Parse Nat} a) (found: List a): {Parse Nat} List a := match fuel with
  | Zero => found
  | Succ more =>
    let at := here()
    if at == 0 then found
    else
      let value := next()
      collect more next [value, ..found]

theorem followsCollect ∀ [alike: a → b → Prop] (next: () → {Parse Nat} a) (nextTwin: () → {Parse Nat} b)
    (nexts: Parse.Follows SameNat alike next nextTwin)
    (fuel: Nat) (found: List a) (foundTwin: List b)
    (founds: List.All2 alike found foundTwin):
    Parse.Follows SameNat (List.All2 alike) (() => collect fuel next found) (() => collect fuel nextTwin foundTwin) :=
  byWalking []

-- A pair split in each run alone; the leaf by `then`.
def sumWith (pair: (Nat, Nat)): {Parse Nat} Nat :=
  let at := here()
  match pair with | (x, y) => x + y + at

theorem followsSumWith ∀ (pair pairTwin: (Nat, Nat))
    (pairs: pair.fst + pair.snd = pairTwin.fst + pairTwin.snd):
    Parse.Follows SameNat SameNat (() => sumWith pair) (() => sumWith pairTwin) :=
  byWalking [] then arithmetic [pairs]

-- A premise about a function the call passes on, walked: `collect`'s
-- lemma needs `nexts` for `() => here()`, which the registered lemma
-- gives.
def collectHeres (fuel: Nat): {Parse Nat} List Nat := collect fuel (() => here()) []

theorem followsCollectHeres ∀ (fuel: Nat):
    Parse.Follows SameNat (List.All2 SameNat) (() => collectHeres fuel) (() => collectHeres fuel) :=
  byWalking [followsCollect]
