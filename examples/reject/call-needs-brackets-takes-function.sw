-- expect-error: E-NOT-A-FUNCTION
-- `twice start ()` (with a space) passes `start` itself to `twice`, which
-- takes a function, and then applies the number it returns to `()`; the
-- error suggests the brackets.
import Std (Nat)

def start (): Nat := 5

def twice (make: () → Nat): Nat := make () + make ()

def go (): Nat := twice start ()
