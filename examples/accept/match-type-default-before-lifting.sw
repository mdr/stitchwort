-- A `match` whose type only its alternatives' record literals say, by their
-- field names (docs/proposals/postponement.md, invariant 7 restated,
-- D2087). The literals wait for their type; the `match`'s helper is lifted
-- at the end of the declaration, and a part about to be lifted is settled
-- as its end is, defaults included, so the helper is made with its type
-- known: `Pos`.
import Std (Nat)

type Pos = { row: Nat, column: Nat }

def pick (n: Nat): Nat :=
  let p := match n with
    | Zero => { row = 1, column = 2 }
    | Succ _ => { row = 3, column = 4 }
  p.row

-- With the type written, nothing waits.
def annotated (n: Nat): Nat :=
  let p: Pos := match n with
    | Zero => { row = 1, column = 2 }
    | Succ _ => { row = 3, column = 4 }
  p.row

test "picked" := pick 0 == 1 && pick 5 == 3 && annotated 5 == 3
