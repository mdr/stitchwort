-- `byComputing` as an argument is checked after the rest of its call (stage 7,
-- rule 1, in docs/proposals/postponement.md), against its goal read
-- afresh. AoC 2021 day 10's `firstIllegalOfScan _ Curly byComputing` (SW-963):
-- the `_` is fixed only by the expected type, on which the result type
-- depends. Checked in place, `byComputing` failed and was checked again after the
-- expected type, but against its goal as computed before the `_` was
-- solved, so `firstOf [3, 4]` stayed stuck on it (SW-1007).
import Std (Eq, List, Nat, Option)

def firstOf (xs: List Nat): Option Nat := List.head xs

type Starts: List Nat → Nat → Prop =
  | Here (n: Nat) (rest: List Nat): Starts [n, ..rest] n

theorem startsOf ∀ (xs: List Nat) (n: Nat) (h: firstOf xs = Some n): Starts xs n := match xs with
  | [m, ..rest] => rewrite <- Option.someInjective h then Here m rest

theorem rflUnderHole: Starts [3, 4] 3 := startsOf _ 3 byComputing
