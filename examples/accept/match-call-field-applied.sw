-- `match h: e` replaces `e` where the goal holds it, as computed, and that
-- includes inside a function field of a call that is stuck on `e`, once the
-- field is applied: `cave.tiled.level n` computes to the field of what
-- `cave.tiled` unfolds to, applied, so the `Nat.decEq` test inside is
-- replaced and both arms are `rfl` (docs/proposals/match-call-field.md
-- §2.1; AoC 2021 day 15, `tiledLevelsAgree`).
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
