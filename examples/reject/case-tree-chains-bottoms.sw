-- expect-error: E-REFL
-- Two chains of helpers, each calling the next one down in both its
-- branches, compared by their case trees (SW-386, SW-395): equal all the
-- way down but for the bottoms, which differ in their `False` branch.

import Std (Nat, Bool)

def a0 (x: Bool): Nat := match x with | True => 1 | False => 0
def a1 (x: Bool): Nat := match x with | True => a0 x | False => a0 x
def a2 (x: Bool): Nat := match x with | True => a1 x | False => a1 x
def a3 (x: Bool): Nat := match x with | True => a2 x | False => a2 x
def a4 (x: Bool): Nat := match x with | True => a3 x | False => a3 x
def a5 (x: Bool): Nat := match x with | True => a4 x | False => a4 x
def a6 (x: Bool): Nat := match x with | True => a5 x | False => a5 x
def a7 (x: Bool): Nat := match x with | True => a6 x | False => a6 x
def a8 (x: Bool): Nat := match x with | True => a7 x | False => a7 x
def a9 (x: Bool): Nat := match x with | True => a8 x | False => a8 x
def a10 (x: Bool): Nat := match x with | True => a9 x | False => a9 x
def a11 (x: Bool): Nat := match x with | True => a10 x | False => a10 x
def a12 (x: Bool): Nat := match x with | True => a11 x | False => a11 x
def a13 (x: Bool): Nat := match x with | True => a12 x | False => a12 x
def a14 (x: Bool): Nat := match x with | True => a13 x | False => a13 x
def a15 (x: Bool): Nat := match x with | True => a14 x | False => a14 x
def a16 (x: Bool): Nat := match x with | True => a15 x | False => a15 x

def c0 (x: Bool): Nat := match x with | True => 1 | False => 2
def c1 (x: Bool): Nat := match x with | True => c0 x | False => c0 x
def c2 (x: Bool): Nat := match x with | True => c1 x | False => c1 x
def c3 (x: Bool): Nat := match x with | True => c2 x | False => c2 x
def c4 (x: Bool): Nat := match x with | True => c3 x | False => c3 x
def c5 (x: Bool): Nat := match x with | True => c4 x | False => c4 x
def c6 (x: Bool): Nat := match x with | True => c5 x | False => c5 x
def c7 (x: Bool): Nat := match x with | True => c6 x | False => c6 x
def c8 (x: Bool): Nat := match x with | True => c7 x | False => c7 x
def c9 (x: Bool): Nat := match x with | True => c8 x | False => c8 x
def c10 (x: Bool): Nat := match x with | True => c9 x | False => c9 x
def c11 (x: Bool): Nat := match x with | True => c10 x | False => c10 x
def c12 (x: Bool): Nat := match x with | True => c11 x | False => c11 x
def c13 (x: Bool): Nat := match x with | True => c12 x | False => c12 x
def c14 (x: Bool): Nat := match x with | True => c13 x | False => c13 x
def c15 (x: Bool): Nat := match x with | True => c14 x | False => c14 x
def c16 (x: Bool): Nat := match x with | True => c15 x | False => c15 x

theorem different (x: Bool): a16 x = c16 x := rfl
