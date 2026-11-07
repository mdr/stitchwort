-- Default values of record and constructor fields.
type RangeOptions = {
    start: Nat:=0,
  stop: Nat,
      step: Nat :=  1
}

type Small = {a: Nat:=1, b: Nat}

type Hooks = {
  onDone: Nat -> Nat := n =>
      n + 1,
  label: Text := "hooks"
}

type Shape =
  | Circle (radius: Nat) (id: Text:="anonymous")
  | Square (side: Nat)
