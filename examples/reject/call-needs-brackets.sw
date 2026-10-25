-- expect-error: E-TYPE-MISMATCH
-- `play start ()` (with a space) passes `start` itself to `play` and then applies the result to `()`; the error suggests the brackets. (`play start()`, with no space, is a call and one argument.)
import Std (Nat)

def start (): Nat := 5

def play (n: Nat): Nat := n + 1

def go (): Nat := play start ()
