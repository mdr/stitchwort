-- expect-error: E-NO-READING
-- A variable has no reading, so its fact `a = True` has no parts to read.
import Std (Bool)

theorem whole (a: Bool) (h: a = True): a := h.read
