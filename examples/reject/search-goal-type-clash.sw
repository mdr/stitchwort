-- expect-error: E-TYPE-MISMATCH
-- A call whose result type clashes with the goal in a type (`Nat` against
-- `Bool`) is reported as that mismatch, not by its proof argument checked
-- against a goal built from a solution of the wrong type (SW-3306).
import Std (Nat, Bool)

type P (a: Type) (x: a): Prop = { holds: x = x }

theorem lem ∀ [x: Nat] (h: x + 1 = 3): P Nat x := { holds = rfl }

theorem use: P Bool True := lem rfl
