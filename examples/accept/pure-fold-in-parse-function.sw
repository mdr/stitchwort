-- A fold with a pure callback inside a `{Parse}` function is a plain call, not
-- a Parse step, so `Parse.readsDone` can take it (SW-1564). It once became a
-- `Std.Effect.foldComp`, and the theorem's last step was a type mismatch.
import Std (Char, List, Nat, Parse)

def total (steps: List Nat): {Parse} Nat := steps.foldLeft 0 (a b => a + b)

theorem totalReads ∀ (steps: List Nat): Parse.Reads (() => total steps) (read value => read = []) :=
  Parse.readsDone (steps.foldLeft 0 (a b => a + b)) (read value => read = []) rfl
