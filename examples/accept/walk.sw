-- The walk step (docs/proposals/proof-walk-step.md, docs/syntax.md
-- "byWalking"): `byWalking [lemmas] then t` proves a statement about
-- effectful code by following the code, with a lemma at each call. One
-- theorem for each thing the walk does: a call, then a value; a split, on
-- a `match` and an `if`; a loop, through the theorem's own recursive
-- call; a parameter's call, by a hypothesis; a function unfolded on
-- request; and a leaf `then` proves.

import Std (Parse, Option, Nat, Bool, List)

def look(): {Parse Nat} Option Nat := Parse.next (n => True)

--| Registered: every call of `look` uses it.
@[walk]
theorem givesLook: Parse.Gives Parse.Invariant.any (() => look()) ((v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)

-- A call, then a value.
def lookTwice(): {Parse Nat} (Option Nat, Option Nat) :=
  let first := look()
  let second := look()
  (first, second)

theorem givesLookTwice: Parse.Gives Parse.Invariant.any (() => lookTwice()) (pair => True) := byWalking []

-- A split on a `match` and on an `if`; the leaves by arithmetic, with the
-- `if`'s condition as a hypothesis.
def capped (limit: Nat): {Parse Nat} Nat := match look() with
  | Some n => if n <= limit then n else limit
  | None => 0

theorem givesCapped ∀ (limit: Nat): Parse.Gives Parse.Invariant.any (() => capped limit) (n => n <= limit) :=
  byWalking []

-- A loop: the recursive call by the theorem itself, weakened to the goal.
def countZeros (fuel count: Nat): {Parse Nat} Nat := match fuel with
  | Zero => count
  | Succ more =>
    match look() with
      | Some n => if n == 0 then countZeros more (count + 1) else count
      | None => count

theorem givesCountZeros ∀ (fuel count: Nat):
    Parse.Gives Parse.Invariant.any (() => countZeros fuel count) (n => count <= n) :=
  byWalking []

-- A parameter's call, by the hypothesis about it; a leaf by `then`.
def both (next: () → {Parse Nat} a): {Parse Nat} List a :=
  let first := next()
  let second := next()
  [first, second]

theorem givesBoth ∀ (next: () → {Parse Nat} a) (holds: a → Prop)
    (nextGives: Parse.Gives Parse.Invariant.any next holds):
    Parse.Gives Parse.Invariant.any (() => both next) (List.All holds) :=
  byWalking [] then (firstFacts, secondFacts, ())

-- `unfold f`: a function without a lemma of its own, walked through.
def lookOnce(): {Parse Nat} Option Nat := look()

def lookOnceTwice(): {Parse Nat} Nat :=
  let first := lookOnce()
  let second := lookOnce()
  0

theorem givesLookOnceTwice: Parse.Gives Parse.Invariant.any (() => lookOnceTwice()) (n => n = 0) :=
  byWalking [unfold lookOnce]

-- A function with a lemma in two families: a `Gives` walk takes its
-- `Gives` lemma, the family it walks in first, not its `ReadsIn` one.
def peek(): {Parse Nat} Option Nat := Parse.next (n => True)

@[walk]
theorem readsPeek: Parse.ReadsIn Parse.Invariant.any (() => peek()) ((read: List Nat) (v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)

@[walk]
theorem givesPeek: Parse.Gives Parse.Invariant.any (() => peek()) ((v: Option Nat) => True) :=
  Parse.readsWeaken (Parse.readsNext (n => True)) (read value proved => byComputing)

def peekTwice(): {Parse Nat} Nat :=
  let first := peek()
  let second := peek()
  0

theorem givesPeekTwice: Parse.Gives Parse.Invariant.any (() => peekTwice()) (n => n = 0) := byWalking []
