-- expect-error: E-TYPE-MISMATCH
-- `play start ()` (with a space), where `play` performs an operation:
-- `start` itself is passed to `play`; the error suggests the brackets.
import Std (Nat)

def start (): {IO} Nat := 5

def play (n: Nat): {IO} Nat := n + 1

def go (): {IO} Nat := play start ()
