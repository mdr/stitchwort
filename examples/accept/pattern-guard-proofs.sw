-- Proofs see a guard as the `if` it is (docs/proposals/pattern-guards.md §3).
import Std (Option, List, Void, Exists)

def clamp (limit: Nat): Nat → Nat
  | n if n <= limit => n
  | _ => limit

theorem clampLe (limit n: Nat): clamp limit n <= limit := match e: n <= limit with
  | True => e
  | False => omega

-- A guarded `match some` and what `filterMap` keeps.
def keepBig: Nat → Option Nat := match some
  | x if x > 2 => x

theorem keepBigGt (x y: Nat) (h: keepBig x = Some y): y > 2 := match e: x > 2 with
  | True => omega [Option.someInjective h]
  | False => Void.exfalso (Option.noneNotSome y h)

def bigOnes (xs: List Nat): List Nat :=
  xs.filterMap keepBig

theorem bigOnesBig (xs: List Nat) (y: Nat) (h: y ∈ bigOnes xs): y > 2 :=
  Exists.elim ((List.memFilterMap keepBig y xs).forward h) (x both => keepBigGt x y (And.right both))

-- A guarded arm in a theorem: its goal is a proposition.
theorem lessOrAtLeast: ∀ (n: Nat) => n < 3 ∨ 3 <= n
  | n if n < 3 => Inl omega
  | n => Inr omega
