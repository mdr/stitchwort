-- `split` on data: variants, records and results of effectful code
-- (docs/proposals/simp.md, stage 1).
import Std (Abort, Nat, Option, Text)
import Std.Abort (ensure, toOption)

-- An update of a field every variant shares: `split` takes `s` apart, and
-- each variant computes.
type Shape =
  | Dot (ref: Nat) (id: Text)
  | Circle (ref: Nat) (id: Text) (radius: Nat)
  | Square (ref: Nat) (id: Text) (side: Nat)

theorem refAfterId (s: Shape) (t: Text): ({ s | id = t }).ref = s.ref := split

-- A record is taken apart into its fields.
type Pos = { row: Nat, column: Nat }

theorem posEta (p: Pos): p = { row = p.row, column = p.column } := split

-- A chain of `.orAbort`s: `h` says the run gave `Some v`, so `split` follows
-- each step it is stuck on; the aborting cases contradict `h`, and in the
-- last one `v` is `a + b`, which `ensure` bounded.
def parseSmall (s: Text) (t: Text): {Abort} Nat :=
  let a := s.toNat.orAbort
  let b := t.toNat.orAbort
  ensure (a + b <= 10)
  a + b

def parseSmallOption (s: Text) (t: Text): Option Nat := toOption (() => parseSmall s t)

theorem parseSmallSome (s: Text) (t: Text) (v: Nat) (h: parseSmallOption s t = Some v): v <= 10 := split
