structure Spigot where
  numer : Int
  accum : Int
  denom : Int

/-- The digits found so far, newest first, given `fuel` more terms of the series
to try and `wanted` more digits to find; `k` terms are taken. -/
def digitsFrom : Nat → Nat → Nat → Spigot → List Nat → List Nat
  | 0, _, _, _, found => found
  | fuel + 1, k, wanted, s, found =>
    if wanted == 0 then found else
    let next := k + 1
    let step : Int := 2 * next + 1
    let accum := (s.accum + s.numer * 2) * step
    let numer := s.numer * next
    let denom := s.denom * step
    if numer > accum then digitsFrom fuel next wanted ⟨numer, accum, denom⟩ found
    else
      let digit := (numer * 3 + accum) / denom
      if digit != (numer * 4 + accum) / denom then
        digitsFrom fuel next wanted ⟨numer, accum, denom⟩ found
      else
        digitsFrom fuel next (wanted - 1) ⟨numer * 10, (accum - denom * digit) * 10, denom⟩
          (digit.toNat :: found)

def main (args : List String) : IO Unit := do
  let count := match args with
    | [text] => text.toNat!
    | _ => 10000
  let digits := (digitsFrom (6 * count + 100) 0 count ⟨1, 0, 1⟩ []).reverse
  let mut rest := digits
  let mut shown := 0
  while !rest.isEmpty do
    let row := rest.take 10
    rest := rest.drop 10
    shown := shown + row.length
    IO.println s!"{String.join (row.map toString)}\t:{shown}"
