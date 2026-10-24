def clampTo (low: Nat) (high: Nat) (value: Nat): Nat := value
def pick [count: Nat] [label: Text] (x: Nat): Nat := x
def a: Nat := clampTo (high := 9) (low := 3) 5
def b: Nat := pick [label := "a"] [count := 3] 1
def c: Nat := clampTo (high := 10) (low := 0)
  (value := 55)
def d: Nat := clampTo
  (high := 10)
  (low := 0)
  (value := 55)
def e: Nat := clampTo (low := 2) (high := (clampTo (low := 1) (high := 3) 2)) 5
def f: Nat := 5 |> clampTo (high := 3) (low := 0)
def g: Nat := clampTo (low := 0) (high := [
  1,
  2
].length) 5
def h: Nat := clampTo (low := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20].length) (high := 100) 5
