import Std (List, Nat)

def a (n: Nat): List Nat := 0..<n
def b (n: Nat): List Nat := 1  ..=n
def c (xs: List Nat): List Nat := 0 ..<   xs.length |> .map (i => i * 2)
def d (n: Nat): Bool := 3 in 0..<n && 5 in 0 ..= n
def e (n: Nat): List Nat := [0, ..2..<n, 99]
def f (n: Nat): List (List Nat) := [(0..<n)]
def g (n: Nat): List Nat := 0 ..< n + 1
