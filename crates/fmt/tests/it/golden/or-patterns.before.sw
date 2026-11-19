-- S22: an or-pattern that fits stays on one line; one that doesn't ends
-- each line with its `|`, the alternatives continuing at +4 from the arm's `|`.
type Colour =
  | Red
  | Green
  | Blue

def warm: Colour -> Bool
  | Red | Green => True
  | Blue => False

def nested: Nat -> Bool
  | Inl (Inl same | Inr same) => True
  | Inr (Inl firstVeryLongBindingName | Inr firstVeryLongBindingName | Inr (Inr firstVeryLongBindingName) | Inr (Inl firstVeryLongBindingName)) => False

def longer (n: Nat): Bool :=
  match n with
    | 100000 | 200000 | 300000 | 400000 | 500000 | 600000 | 700000 | 800000 | 900000 | 1000000 | 2000000 | 3000000 | 4000000 | 5000000 => True
    | 1 | 2 => False
    | _ => True

def guarded (n: Nat): Bool :=
  match n with
    | 1000000000 | 2000000000 | 3000000000 | 4000000000 | 5000000000 | 6000000000 | 7000000000 | 8000000000 | 9000000000 if n > 5 => True
    | _ => False

def commented (n: Nat): Bool :=
  match n with
    | 1000000000 | -- the first group
      2000000000 | 3000000000 | 4000000000 | 5000000000 | 6000000000 | 7000000000 | 8000000000 => True
    | _ => False
