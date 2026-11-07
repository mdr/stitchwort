-- `cases` falls back on splitting a variable the goal mentions when nothing
-- the goal is stuck on can be split (`aim` in `probeVar`). A field of a
-- record variable (`start.aim`) isn't a candidate. Before record eta,
-- `start.aim` was an accessor call stuck on `start`, so the fallback split
-- `start` and then its field `aim`; with eta it is a projection, and
-- `probe` fails.
type Sub = { depth: Int, aim: Int }

def scale (aim: Int): (n: Nat) → Nat
  | Zero => 0
  | Succ k => scale aim k

theorem probeVar (aim: Int) (n: Nat): scale aim n = scale (aim + 0) n := cases

theorem probe (start: Sub) (n: Nat): scale start.aim n = scale (start.aim + 0) n := cases
