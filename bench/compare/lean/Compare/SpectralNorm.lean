def entry (i j : Nat) : Float :=
  1.0 / (((i + j) * (i + j + 1) / 2 + i + 1).toFloat)

/-- A applied to `vector`, or Aᵀ when `transposed`. -/
def apply (size : Nat) (transposed : Bool) (vector : Array Float) : Array Float :=
  (Array.range size).map fun i =>
    (List.range size).foldl (fun sum j =>
      let weight := if transposed then entry j i else entry i j
      sum + weight * vector[j]!) 0.0

def normal (size : Nat) (vector : Array Float) : Array Float :=
  apply size true (apply size false vector)

def dotProduct (xs ys : Array Float) : Float :=
  (List.range xs.size).foldl (fun sum i => sum + xs[i]! * ys[i]!) 0.0

/-- `x` to nine decimals, by scaling and rounding as the Stitchwort port does. -/
def nineDecimals (x : Float) : String :=
  let units := (x * 1000000000.0).round.toUInt64.toNat
  let fraction := toString (units % 1000000000)
  s!"{units / 1000000000}.{"".pushn '0' (9 - fraction.length)}{fraction}"

def main (args : List String) : IO Unit := do
  let size := match args with
    | [text] => text.toNat!
    | _ => 1000
  let mut u := Array.replicate size 1.0
  let mut v := u
  for _ in [0:10] do
    v := normal size u
    u := normal size v
  IO.println (nineDecimals (Float.sqrt (dotProduct u v / dotProduct v v)))
