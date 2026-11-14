-- SW-2812: `rewrite` of a decision's test tries the usual motive first, and
-- carries the decision's proofs along the equation only when that motive
-- fails (crates/elab/src/carry.rs). Here the test, `g f`, is an occurrence of
-- the left side `g (x => f x)` only by computation, so the decision's
-- proposition, `g f = True`, doesn't show the left side, yet its `g f` is
-- replaced too. The usual motive replaces the test and the proposition
-- together; carrying the proofs would have left them typed by `g f`.
import Std (Bool, Decidable, Eq, Nat)

theorem trueSound ∀ (b: Bool): b = True → b = True := h => h

-- A decision whose `sound` is a call, so its type can be worked out.
def decTrue (b: Bool): Decidable (b = True) := { holds = b, sound = trueSound b, complete = trueSound b }

def pick (b: Bool): Nat := Decidable.elim (decTrue b) (_ => 1) (_ => 0)

def pickWith (g: (Nat → Bool) → Bool) (f: Nat → Bool): Nat := pick (g f)

theorem pickWithTrue ∀ (g: (Nat → Bool) → Bool) (f: Nat → Bool) (h: g (x => f x) = True): pickWith g f = 1 :=
  rewrite h in rfl
