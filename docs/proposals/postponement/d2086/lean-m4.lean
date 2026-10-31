-- D2086: does Lean's `match` apply default instances to numerals made
-- before it (Match.lean's synthesizeSyntheticMVarsUsingDefault)?

-- Without a match: `m` is an `Int` (D2084's check).
def f (i : Int) : Bool :=
  let m := 3 - 5
  m + i == 0

-- With a `match` between the `let` and the use.
def g (i : Int) : Bool :=
  let m := 3 - 5
  let k : Int := match i with
    | _ => (0 : Int)
  m + i == k

set_option pp.numericTypes true
#print f
#print g
#eval f 2
#eval g 2
