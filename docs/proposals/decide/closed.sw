-- Lean's `decide` for a closed goal, today: an `auto` argument finds the
-- goal's decision procedure, runs it, and the kernel runs it again
-- (`Decidable.fromYes d Trivial`). One line of library would name it.
import Std (Bool, List)

type Key =
  | Digit0
  | Digit1
  | Digit2
  | Enter

def keys: List Key := [Digit0, Digit1, Digit2, Enter]

def byDecision [p: Prop] [auto h: p]: p := h

theorem enterIn: Enter ∈ keys := byDecision

theorem twoBelow: 2 + 2 < 5 := byDecision

-- A false one is refused with `E-AUTO-FALSE`:
--   theorem enterNot: Enter ∈ [Digit0, Digit1] := byDecision
--   [E-AUTO-FALSE] Error: `Digit0 = Enter ∨ Digit1 = Enter ∨ Void` is false
