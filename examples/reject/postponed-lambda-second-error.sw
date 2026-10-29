-- expect-error: E-UNKNOWN-FIELD
-- A lambda that fails in place (`c`'s type is unknown) and is checked again
-- after `z` fails for the real reason, which is the error given: `List` has
-- no `size`, not "can't tell what `c` is".
import Std (List, Nat)

def Counts: Type := List Nat

def Counts.size (counts: Counts): Nat := counts.length

def Counts.of (n: Nat): Counts := [n]

def twice (f: b → Nat) (g: b → Nat) (z: b): Nat := f z + g z

def a: Nat := twice (c => c.size) (c => List.length c) (Counts.of 1)
