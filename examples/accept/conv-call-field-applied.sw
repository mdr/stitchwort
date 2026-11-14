-- A function field of a call that is stuck, applied, is equal by `rfl` to
-- the same field of the call's unfolding, applied: both compute to the
-- field of the stuck `if`, applied (docs/proposals/match-call-field.md
-- §2.1, "Conversion").
import Std (Nat)

type Cave = { rows: List Nat }
type Map = { size: Nat, level: Nat → Nat }

def Cave.height (cave: Cave): Nat := cave.rows.length

def Cave.tiled (cave: Cave): Map :=
  if tall: cave.height != 0 then { size = 5, level = n => n + 1 } else { size = 0, level = n => n }

theorem twoWays ∀ (cave: Cave) (n: Nat):
    cave.tiled.level n
      = (if tall: cave.height != 0 then { size = 5, level = m => m + 1 } else { size = 0, level = m => m }).level n :=
  rfl

def Cave.levelAt (cave: Cave) (n: Nat): Nat := cave.tiled.level n

-- The field is applied inside another definition, as a goal reaches it.
theorem throughACall ∀ (cave: Cave) (n: Nat):
    cave.levelAt n
      = (if tall: cave.height != 0 then { size = 5, level = m => m + 1 } else { size = 0, level = m => m }).level n :=
  rfl
