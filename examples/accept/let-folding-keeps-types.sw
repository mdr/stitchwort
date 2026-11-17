-- A solution written inside a `let` has the `let`'s value folded back to
-- its variable, but only a value whose form fixes its type: `byComputing`
-- (`Refl`), `[]`, `None` and a lambda each have many types, so folding
-- one back could put the variable where another type is expected.
-- `rb.left` solves `And.left`'s implicit statement from the goal, and each
-- goal holds such a form: the `Float` literal's validity proof, `[]` at
-- `List Bool`, `None` at `Option Bool`, a lambda on `Bool` (SW-3887).
import Std (Float)

theorem floatLiteralBesideAnEquation ∀ (x: Float) (rb: Float.leq 1.0 x = True ∧ True): Float.leq 1.0 x = True :=
  let two: 2 = 2 := byComputing
  rb.left

theorem nilBesideAnotherNil ∀ (rb: ([]: List Bool) = [] ∧ True): ([]: List Bool) = [] :=
  let xs: List Nat := []
  rb.left

theorem noneBesideAnotherNone ∀ (rb: (None: Option Bool) = None ∧ True): (None: Option Bool) = None :=
  let o: Option Nat := None
  rb.left

theorem lambdaBesideAnotherLambda ∀ (f: (Bool → Bool) → Prop) (rb: f (x => True) ∧ True): f (x => True) :=
  let g: Nat → Bool := x => True
  rb.left

--| Folding back still happens where the form fixes the type: `[n]` is a
--| `List Nat` whatever it's compared with.
theorem singletonBesideItself ∀ (n: Nat) (rb: [n] = [n] ∧ True): [n] = [n] :=
  let xs: List Nat := [n]
  rb.left
