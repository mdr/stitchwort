-- `match h: e` replaces `e` where the goal holds it, as computed. A field of
-- a call (`cave.tiled.level`) whose call is stuck on `e` is kept as the
-- field call (SW-1829), so the `Nat.decEq` inside isn't replaced and the
-- `No` branch's `rfl` fails. It checked before record eta.
import Std (Nat)

type Cave = { rows: List Nat }
type Map = { size: Nat, level: Nat → Nat }

def Cave.height (cave: Cave): Nat := cave.rows.length

def Cave.tiled (cave: Cave): Map :=
  if tall: cave.height != 0 then { size = 5, level = n => n + 1 } else { size = 0, level = n => n }

theorem probe (cave: Cave) (n: Nat): cave.tiled.level n = (if cave.height != 0 then n + 1 else n) :=
  match h: Nat.decEq cave.height 0 with
    | Yes zero => rfl
    | No _ => rfl
