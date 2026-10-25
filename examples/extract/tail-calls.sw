-- More tail calls that become loops in the generated JS (see loops.sw for
-- the plain ones): a call in a branch of `if h:`, a call in a `match` that
-- isn't the whole right-hand side (it's lifted into its own definition,
-- which the loop inlines), and calls between the members of a group.
-- `crates/cli/tests/extract.rs` runs each a million times deep, and has the
-- recursive calls of a definition by `decreasing` (which the reference
-- evaluator doesn't run, so they can't be `run:` lines here).
--
-- run: countDown 100000
-- run: firstOver 10 [1, 5, 20, 3]
-- run: firstOver 10 [1, 5]
-- run: lookup 3 [(1, "a"), (3, "c"), (3, "d")]
-- run: lookup 4 [(1, "a")]
-- run: steps 100000
-- run: closures 5
-- run: isEven 100001
-- run: isOdd 7
-- run: rounds 3 10

import Std (List, Nat, Option, Text)

-- A call in a branch of `if h:` (a `Decidable.elim`).
def countFrom (acc: Nat): Nat → Nat
  | 0 => acc
  | Succ n => if h: n = 7000000000 then acc else countFrom (acc + 1) n

export def countDown (n: Nat): Nat := countFrom 0 n

-- A call in a `match` in an arm: the `match` is lifted into
-- `firstAbove.%match1`, which calls `firstAbove`.
def firstAbove (limit: Nat): List Nat → Option Nat
  | Nil => None
  | Cons x xs => match Nat.leq x limit with
    | True => firstAbove limit xs
    | False => Some x

export def firstOver (limit: Nat) (xs: List Nat): Option Nat := firstAbove limit xs

-- A lookup by `Ord.compare`, as the library's maps do on their lists.
def lookupIn (key: Nat): List (Nat, Text) → Option Text
  | Nil => None
  | Cons (k, v) rest => match Ord.compare key k with
    | Equal => Some v
    | _ => lookupIn key rest

export def lookup (key: Nat) (entries: List (Nat, Text)): Option Text := lookupIn key entries

-- A `match` after an `if`, lifted: the definition isn't a case tree.
def stepsFrom (acc: Nat) (n: Nat): Nat :=
  if acc == 7000000000 then acc else match n with
    | Zero => acc
    | Succ k => stepsFrom (acc + 1) k

export def steps (n: Nat): Nat := stepsFrom 0 n

-- Each turn makes a closure in the inlined `match`, which must keep that
-- turn's `k`.
def adders (acc: List (Nat → Nat)) (n: Nat): List (Nat → Nat) :=
  if n == 7000000000 then acc else match n with
    | Zero => acc
    | Succ k => adders (Cons (x => x + k) acc) k

def applyAll: List (Nat → Nat) → List Nat
  | Nil => Nil
  | Cons f fs => Cons (f 100) (applyAll fs)

export def closures (n: Nat): List Nat := applyAll (adders Nil n)

-- Two members of a group: each loop inlines the other.
export def isEven: Nat → Bool
  | 0 => True
  | Succ n => isOdd n

export def isOdd: Nat → Bool
  | 0 => False
  | Succ n => isEven n

-- Members with an accumulator and a second parameter.
def evenRounds (acc: Nat): Nat → Nat
  | 0 => acc
  | Succ n => oddRounds (acc + 2) n

def oddRounds (acc: Nat): Nat → Nat
  | 0 => acc
  | Succ n => evenRounds (acc + 1) n

export def rounds (start: Nat) (n: Nat): Nat := evenRounds start n

-- For the long run in extract.rs.
export def lookupLast (n: Nat): Option Text :=
  lookupIn n (List.map (List.range (n + 1)) (k => (k, "x")))
