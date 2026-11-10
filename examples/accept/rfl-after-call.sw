-- `rfl` as an argument is checked after the rest of its call (stage 7,
-- rule 1, in docs/proposals/postponement.md), against its goal read
-- afresh. AoC 2021 day 10's `firstIllegalOfScan _ Curly rfl` (SW-963):
-- the `_` is fixed only by the expected type, on which the result type
-- depends. Checked in place, `rfl` failed and was checked again after the
-- expected type, but against its goal as computed before the `_` was
-- solved, so `firstOf [3, 4]` stayed stuck on it (SW-1007).
import Std (Eq, List, Nat, Option, Void)

def firstOf (xs: List Nat): Option Nat := List.head xs

type Starts: List Nat → Nat → Prop =
  | Here (n: Nat) (rest: List Nat): Starts [n, ..rest] n

theorem startsOf: ∀ (xs: List Nat) (n: Nat) => firstOf xs = Some n → Starts xs n
  | [], n, h => Void.exfalso (Option.noneNotSome n h)
  | [m, ..rest], n, h => rewrite <- Option.someInjective h in Here m rest

theorem rflUnderHole: Starts [3, 4] 3 := startsOf _ 3 rfl
