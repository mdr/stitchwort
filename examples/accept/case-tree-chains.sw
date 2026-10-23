-- Two different definitions stuck on a `match` are compared by their case
-- trees (SW-386, D1091). Here each helper calls the next one down in both
-- its branches, so comparing `a30 x` with `b30 x` meets the pair `a29 x`,
-- `b29 x` twice, `a28 x`, `b28 x` four times, and so on: 2^30 paths. A pair
-- already found equal is answered at once (SW-395), so this takes a step
-- per level. The bottoms differ in text (`1` against `0 + 1`), so the two
-- chains don't have the same content hash: they're equal in value.

import Std (Nat, Bool)

def a0 (x: Bool): Nat := match x with | True => 1 | False => 0
def b0 (x: Bool): Nat := match x with | True => 0 + 1 | False => 0
def a1 (x: Bool): Nat := match x with | True => a0 x | False => a0 x
def b1 (x: Bool): Nat := match x with | True => b0 x | False => b0 x
def a2 (x: Bool): Nat := match x with | True => a1 x | False => a1 x
def b2 (x: Bool): Nat := match x with | True => b1 x | False => b1 x
def a3 (x: Bool): Nat := match x with | True => a2 x | False => a2 x
def b3 (x: Bool): Nat := match x with | True => b2 x | False => b2 x
def a4 (x: Bool): Nat := match x with | True => a3 x | False => a3 x
def b4 (x: Bool): Nat := match x with | True => b3 x | False => b3 x
def a5 (x: Bool): Nat := match x with | True => a4 x | False => a4 x
def b5 (x: Bool): Nat := match x with | True => b4 x | False => b4 x
def a6 (x: Bool): Nat := match x with | True => a5 x | False => a5 x
def b6 (x: Bool): Nat := match x with | True => b5 x | False => b5 x
def a7 (x: Bool): Nat := match x with | True => a6 x | False => a6 x
def b7 (x: Bool): Nat := match x with | True => b6 x | False => b6 x
def a8 (x: Bool): Nat := match x with | True => a7 x | False => a7 x
def b8 (x: Bool): Nat := match x with | True => b7 x | False => b7 x
def a9 (x: Bool): Nat := match x with | True => a8 x | False => a8 x
def b9 (x: Bool): Nat := match x with | True => b8 x | False => b8 x
def a10 (x: Bool): Nat := match x with | True => a9 x | False => a9 x
def b10 (x: Bool): Nat := match x with | True => b9 x | False => b9 x
def a11 (x: Bool): Nat := match x with | True => a10 x | False => a10 x
def b11 (x: Bool): Nat := match x with | True => b10 x | False => b10 x
def a12 (x: Bool): Nat := match x with | True => a11 x | False => a11 x
def b12 (x: Bool): Nat := match x with | True => b11 x | False => b11 x
def a13 (x: Bool): Nat := match x with | True => a12 x | False => a12 x
def b13 (x: Bool): Nat := match x with | True => b12 x | False => b12 x
def a14 (x: Bool): Nat := match x with | True => a13 x | False => a13 x
def b14 (x: Bool): Nat := match x with | True => b13 x | False => b13 x
def a15 (x: Bool): Nat := match x with | True => a14 x | False => a14 x
def b15 (x: Bool): Nat := match x with | True => b14 x | False => b14 x
def a16 (x: Bool): Nat := match x with | True => a15 x | False => a15 x
def b16 (x: Bool): Nat := match x with | True => b15 x | False => b15 x
def a17 (x: Bool): Nat := match x with | True => a16 x | False => a16 x
def b17 (x: Bool): Nat := match x with | True => b16 x | False => b16 x
def a18 (x: Bool): Nat := match x with | True => a17 x | False => a17 x
def b18 (x: Bool): Nat := match x with | True => b17 x | False => b17 x
def a19 (x: Bool): Nat := match x with | True => a18 x | False => a18 x
def b19 (x: Bool): Nat := match x with | True => b18 x | False => b18 x
def a20 (x: Bool): Nat := match x with | True => a19 x | False => a19 x
def b20 (x: Bool): Nat := match x with | True => b19 x | False => b19 x
def a21 (x: Bool): Nat := match x with | True => a20 x | False => a20 x
def b21 (x: Bool): Nat := match x with | True => b20 x | False => b20 x
def a22 (x: Bool): Nat := match x with | True => a21 x | False => a21 x
def b22 (x: Bool): Nat := match x with | True => b21 x | False => b21 x
def a23 (x: Bool): Nat := match x with | True => a22 x | False => a22 x
def b23 (x: Bool): Nat := match x with | True => b22 x | False => b22 x
def a24 (x: Bool): Nat := match x with | True => a23 x | False => a23 x
def b24 (x: Bool): Nat := match x with | True => b23 x | False => b23 x
def a25 (x: Bool): Nat := match x with | True => a24 x | False => a24 x
def b25 (x: Bool): Nat := match x with | True => b24 x | False => b24 x
def a26 (x: Bool): Nat := match x with | True => a25 x | False => a25 x
def b26 (x: Bool): Nat := match x with | True => b25 x | False => b25 x
def a27 (x: Bool): Nat := match x with | True => a26 x | False => a26 x
def b27 (x: Bool): Nat := match x with | True => b26 x | False => b26 x
def a28 (x: Bool): Nat := match x with | True => a27 x | False => a27 x
def b28 (x: Bool): Nat := match x with | True => b27 x | False => b27 x
def a29 (x: Bool): Nat := match x with | True => a28 x | False => a28 x
def b29 (x: Bool): Nat := match x with | True => b28 x | False => b28 x
def a30 (x: Bool): Nat := match x with | True => a29 x | False => a29 x
def b30 (x: Bool): Nat := match x with | True => b29 x | False => b29 x

theorem sameChains (x: Bool): a30 x = b30 x := rfl
