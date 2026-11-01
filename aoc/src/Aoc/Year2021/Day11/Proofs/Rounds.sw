-- What one round of the program does, in the spec's terms: an octopus
-- flashes after the round exactly when it is on the grid and its energy,
-- counting the flashes before the round, is above 9. And facts about the
-- spec's counts.

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Std (Bool, DecEq, Eq, Exists, Iff, List, Nat, Option, Void)

-- The positions on the grid.
def positions (levels: List (List Nat)): List (Nat, Nat) := levels.gridCells.map Pair.fst

-- Only octopuses on the grid have flashed.
def OnGrid (levels: List (List Nat)) (flashed: (Nat, Nat) → Bool): Prop := (q: (Nat, Nat)) → flashed q = True → q ∈ positions levels

-- A grid the shape of `levels` has `True`s only on its positions.
theorem onGridMapCells (levels: List (List Nat)) (h: (Nat, Nat) → Nat → Bool): OnGrid levels (flashedAt (mapCells levels h))
  | (a, b), flashes =>
    match e: cellAt levels (a, b) with
      | None => Void.exfalso (Bool.falseNotTrue (rewrite cellAtMapCells levels h a b, e at flashes in flashes))
      | Some level => List.memMap levels.gridCells ((a, b), level) ((memGridCellsAt levels a b level).backward e) Pair.fst

-- Whether (a, b) has flashed in a grid made by `mapCells`.
theorem flashedAtMapCells (levels: List (List Nat)) (h: (Nat, Nat) → Nat → Bool) (a: Nat) (b: Nat):
    flashedAt (mapCells levels h) (a, b) = Option.getOrElse (Option.map (cellAt levels (a, b)) (h (a, b))) False :=
  Eq.cong (found => Option.getOrElse found False) (cellAtMapCells levels h a b)

-- The program's energy is the spec's, for flashers on the grid.
theorem energyAgrees (levels: List (List Nat)) (flashed: List (List Bool)) (onGrid: OnGrid levels (flashedAt flashed)) (a: Nat) (b: Nat)
    (level: Nat): energy flashed (a, b) level = energyIn levels (flashedAt flashed) (a, b) level :=
  rewrite countAround levels (flashedAt flashed) onGrid a b in rfl

-- After a round, an octopus with energy above 9 has flashed...
theorem roundIntro (levels: List (List Nat)) (flashed: List (List Bool)) (onGrid: OnGrid levels (flashedAt flashed)) (a: Nat) (b: Nat)
    (level: Nat) (member: ((a, b), level) ∈ levels.gridCells) (above: 9 < energyIn levels (flashedAt flashed) (a, b) level):
    flashedAt (flashRound levels flashed) (a, b) = True :=
  Eq.trans (flashedAtMapCells levels (at level => 9 < energy flashed at level) a b)
    (rewrite (memGridCellsAt levels a b level).forward member in Eq.trans (Eq.cong (Nat.leq 10) (energyAgrees levels flashed onGrid a b level)) above)

-- ...and an octopus that has flashed is on the grid, with energy above 9.
theorem roundElim (levels: List (List Nat)) (flashed: List (List Bool)) (onGrid: OnGrid levels (flashedAt flashed)) (a: Nat) (b: Nat)
    (flashes: flashedAt (flashRound levels flashed) (a, b) = True):
    ∃ (level: Nat) => ((a, b), level) ∈ levels.gridCells ∧ 9 < energyIn levels (flashedAt flashed) (a, b) level :=
  let opened := Eq.trans (Eq.sym (flashedAtMapCells levels (at level => 9 < energy flashed at level) a b)) flashes
  match e: cellAt levels (a, b) with
    | None => Void.exfalso (Bool.falseNotTrue opened)
    | Some level =>
      Witness level (Both ((memGridCellsAt levels a b level).backward e) (Eq.trans (Eq.sym (Eq.cong (Nat.leq 10) (energyAgrees levels flashed onGrid a b level))) opened))

-- More flashers, more flashing neighbours.
theorem neighboursMono (levels: List (List Nat)) (f: (Nat, Nat) → Bool) (g: (Nat, Nat) → Bool) (fg: (q: (Nat, Nat)) → f q = True → g q = True)
    (at: (Nat, Nat)): flashingNeighbours levels f at ≤ flashingNeighbours levels g at :=
  List.countLeMem levels.gridCells (cell => adjacent at cell.fst && f cell.fst) (cell => adjacent at cell.fst && g cell.fst)
    (cell member both => Bool.andIntro _ _ (Bool.andLeft _ _ both) (fg cell.fst (Bool.andRight _ _ both)))
