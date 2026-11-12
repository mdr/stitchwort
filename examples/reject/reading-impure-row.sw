-- expect-error: E-NO-READING
-- A reading stated with a pure callback fits only tests whose callback is
-- pure: `ignoring p b` with a `p` that may perform isn't its test.
import Std (Bool, Nat)
import Std.Effect (Effects)

-- A `Bool` whatever its callback's row, since it never calls it.
def ignoring [e: Effects] (p: Nat → {e} Bool) (b: Bool): Bool := b

@[reading]
theorem ignoringReads (p: Nat → Bool) (b: Bool): ignoring p b ↔ b = True := { forward = h => h, backward = h => h }

theorem pure (b: Bool) (h: ignoring (x => x > 2) b): b = True := h.read

theorem performing [e: Effects] (p: Nat → {e} Bool) (b: Bool) (h: ignoring p b): b = True := h.read
