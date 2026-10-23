-- D1012, D1017: a comma bracket that spans lines puts one element per line,
-- a comma at the end of each, no trailing comma, the opener at the end of the
-- line before and the closer on a line of its own.
type Sized (a: Type) = {
  items: List a,
  size: Nat
}

def leading: List Text := [
  "a",
  "b",
  "c",
  "d",
  "e"
]

def grid: List Nat := [
  1,
  2,
  3,
  4
]

def example: List Text := [
  "a",
  "b"
]

def pair: (Nat, Nat) := (
  1,
  2
)

def alice: Person := {
  name = "Alice",
  age = 30
}

def call (n: Nat): Nat :=
  f (
    n,
    1,
    2
  )
