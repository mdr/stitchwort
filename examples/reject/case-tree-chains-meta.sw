-- expect-error: E-REFL
-- The chains below are equal, and comparing them solves the `_` (as 3)
-- through all 16 levels, each pair met many times and answered from the
-- record of pairs already found equal (SW-395). The tops then differ in
-- their other branch, so `rfl` is rejected, and what was solved is
-- taken back.

import Std (Nat, Bool)

def same [t: Type] (a: t) (b: t) (p: a = b): Nat := 0

def a0 (x: Bool) (n: Nat): Nat := match x with | True => n | False => n
def a1 (x: Bool) (n: Nat): Nat := match x with | True => a0 x n | False => a0 x n
def a2 (x: Bool) (n: Nat): Nat := match x with | True => a1 x n | False => a1 x n
def a3 (x: Bool) (n: Nat): Nat := match x with | True => a2 x n | False => a2 x n
def a4 (x: Bool) (n: Nat): Nat := match x with | True => a3 x n | False => a3 x n
def a5 (x: Bool) (n: Nat): Nat := match x with | True => a4 x n | False => a4 x n
def a6 (x: Bool) (n: Nat): Nat := match x with | True => a5 x n | False => a5 x n
def a7 (x: Bool) (n: Nat): Nat := match x with | True => a6 x n | False => a6 x n
def a8 (x: Bool) (n: Nat): Nat := match x with | True => a7 x n | False => a7 x n
def a9 (x: Bool) (n: Nat): Nat := match x with | True => a8 x n | False => a8 x n
def a10 (x: Bool) (n: Nat): Nat := match x with | True => a9 x n | False => a9 x n
def a11 (x: Bool) (n: Nat): Nat := match x with | True => a10 x n | False => a10 x n
def a12 (x: Bool) (n: Nat): Nat := match x with | True => a11 x n | False => a11 x n
def a13 (x: Bool) (n: Nat): Nat := match x with | True => a12 x n | False => a12 x n
def a14 (x: Bool) (n: Nat): Nat := match x with | True => a13 x n | False => a13 x n
def a15 (x: Bool) (n: Nat): Nat := match x with | True => a14 x n | False => a14 x n
def a16 (x: Bool) (n: Nat): Nat := match x with | True => a15 x n | False => a15 x n

def b0 (x: Bool) (n: Nat): Nat := match x with | True => n | False => n
def b1 (x: Bool) (n: Nat): Nat := match x with | True => b0 x n | False => b0 x n
def b2 (x: Bool) (n: Nat): Nat := match x with | True => b1 x n | False => b1 x n
def b3 (x: Bool) (n: Nat): Nat := match x with | True => b2 x n | False => b2 x n
def b4 (x: Bool) (n: Nat): Nat := match x with | True => b3 x n | False => b3 x n
def b5 (x: Bool) (n: Nat): Nat := match x with | True => b4 x n | False => b4 x n
def b6 (x: Bool) (n: Nat): Nat := match x with | True => b5 x n | False => b5 x n
def b7 (x: Bool) (n: Nat): Nat := match x with | True => b6 x n | False => b6 x n
def b8 (x: Bool) (n: Nat): Nat := match x with | True => b7 x n | False => b7 x n
def b9 (x: Bool) (n: Nat): Nat := match x with | True => b8 x n | False => b8 x n
def b10 (x: Bool) (n: Nat): Nat := match x with | True => b9 x n | False => b9 x n
def b11 (x: Bool) (n: Nat): Nat := match x with | True => b10 x n | False => b10 x n
def b12 (x: Bool) (n: Nat): Nat := match x with | True => b11 x n | False => b11 x n
def b13 (x: Bool) (n: Nat): Nat := match x with | True => b12 x n | False => b12 x n
def b14 (x: Bool) (n: Nat): Nat := match x with | True => b13 x n | False => b13 x n
def b15 (x: Bool) (n: Nat): Nat := match x with | True => b14 x n | False => b14 x n
def b16 (x: Bool) (n: Nat): Nat := match x with | True => b15 x n | False => b15 x n

def aTop (x: Bool) (y: Bool) (n: Nat): Nat := match y with | True => a16 x n | False => 0
def bTop (x: Bool) (y: Bool) (n: Nat): Nat := match y with | True => b16 x n | False => 1

def different (x: Bool) (y: Bool): Nat := same (aTop x y 3) (bTop x y _) rfl
