-- expect-error: E-ATTRIBUTE
-- Attributes attach to the next declaration, whatever it is.
@[js.name "zero"]
theorem zeroAdd (n: Nat): 0 + n = n := rfl
