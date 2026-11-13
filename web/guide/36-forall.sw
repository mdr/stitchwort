import Std (Exists, Nat)
import Std.Exists (Witness)

-- `∀ (n: Nat) => P` says `P` for every `n`. It's another way to write the
-- function type `(n: Nat) -> P`. `forall` is the same, spelled in ASCII.
-- A theorem's own variables go before the colon, as here.
theorem zeroPlus ∀ (n: Nat): 0 + n = n := rfl

-- A hypothesis about every value: `all 1` is a proof of `p 1`.
theorem atOneAndTwo ∀ (p: Nat -> Prop) (all: ∀ (n: Nat) => p n): p 1 ∧ p 2 :=
  Both (all 1) (all 2)

-- Several parameters go together.
theorem swap: ∀ (a b: Nat) => a + b = b + a := a => b => omega

-- The statement runs to the end, so the `->` here is "if" inside the
-- "for all": every positive number is at least one.
theorem atLeastOne: ∀ (n: Nat) => n > 0 -> n >= 1 := n => positive => omega

-- `∀` and `∃` together: every number has a successor.
theorem successor ∀ (n: Nat): ∃ (m: Nat) => m = n + 1 := Witness (n + 1) rfl

-- Goals and messages show these statements with `∀`, whichever way they
-- were written: put `?` in place of a proof to see one.
