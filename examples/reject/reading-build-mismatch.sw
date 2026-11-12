-- expect-error: E-NO-READING
-- `Both` builds an `∧`, but `a || b` reads as `a ∨ b`.
import Std (Bool)

theorem both (a b: Bool) (ha: a) (hb: b): (a || b) = True := Both ha hb
