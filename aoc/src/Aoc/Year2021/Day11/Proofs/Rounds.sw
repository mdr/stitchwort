--| What one round of the program does, in the spec's terms: an octopus
--| flashes after the round exactly when it is on the grid and its energy,
--| counting the flashes before the round, is above 9. And facts about the
--| spec's counts.

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Aoc.Common (Position, touching)
import Aoc.Common.Proofs (cellAtMapCells, memCells)
import Std (Bool, DecEq, Eq, Exists, Iff, List, Nat, Option, Void)

--| The positions on the grid.
def positions (cavern: Cavern): List Position := cavern.grid.cells.map Pair.fst

--| Only octopuses on the grid have flashed.
def OnGrid (cavern: Cavern) (flashed: Position → Bool): Prop := (q: Position) → flashed q = True → q ∈ positions cavern

--| Flashers made for the cavern's octopuses have `True`s only on its positions.
theorem onGridFlash (cavern: Cavern) (h: Position → Nat → Bool): OnGrid cavern (cavern.flash h).has
  | q, flashes =>
    match e: cavern.grid.at q with
      | None => Void.exfalso (Bool.falseNotTrue (rewrite cellAtMapCells cavern.grid.rows h q, e at flashes in flashes))
      | Some level => List.memMap cavern.grid.cells (q, level) ((memCells cavern.grid.rows q level).backward e) Pair.fst

--| Whether `q` has flashed in the flashers `cavern.flash h` made.
theorem hasFlash (cavern: Cavern) (h: Position → Nat → Bool) (q: Position):
    (cavern.flash h).has q = Option.getOrElse (Option.map (cavern.grid.at q) (h q)) False :=
  Eq.cong (found => Option.getOrElse found False) (cellAtMapCells cavern.grid.rows h q)

--| The program's energy is the spec's, for flashers on the grid.
theorem energyAgrees (cavern: Cavern) (flashed: Flashed) (onGrid: OnGrid cavern flashed.has) (q: Position) (level: Nat):
    flashed.energy q level = energyIn cavern flashed.has q level :=
  rewrite countAround cavern flashed.has onGrid q in rfl

--| After a round, an octopus with energy above 9 has flashed...
theorem roundIntro (cavern: Cavern) (flashed: Flashed) (onGrid: OnGrid cavern flashed.has) (q: Position) (level: Nat)
    (member: (q, level) ∈ cavern.grid.cells) (above: 9 < energyIn cavern flashed.has q level): (cavern.flashRound flashed).has q = True :=
  Eq.trans (hasFlash cavern (at level => 9 < flashed.energy at level) q)
    (rewrite (memCells cavern.grid.rows q level).forward member in Eq.trans (Eq.cong (Nat.leq 10) (energyAgrees cavern flashed onGrid q level)) above)

--| ...and an octopus that has flashed is on the grid, with energy above 9.
theorem roundElim (cavern: Cavern) (flashed: Flashed) (onGrid: OnGrid cavern flashed.has) (q: Position)
    (flashes: (cavern.flashRound flashed).has q = True): ∃ (level: Nat) => (q, level) ∈ cavern.grid.cells ∧ 9 < energyIn cavern flashed.has q level :=
  let opened := Eq.trans (Eq.sym (hasFlash cavern (at level => 9 < flashed.energy at level) q)) flashes
  match e: cavern.grid.at q with
    | None => Void.exfalso (Bool.falseNotTrue opened)
    | Some level =>
      Witness level
        (Both ((memCells cavern.grid.rows q level).backward e) (Eq.trans (Eq.sym (Eq.cong (Nat.leq 10) (energyAgrees cavern flashed onGrid q level))) opened))

--| More flashers, more flashing neighbours.
theorem neighboursMono (cavern: Cavern) (f: Position → Bool) (g: Position → Bool) (fg: (q: Position) → f q = True → g q = True)
    (at: Position): flashingNeighbours cavern f at ≤ flashingNeighbours cavern g at :=
  List.countLeMem cavern.grid.cells (cell => touching at cell.fst && f cell.fst) (cell => touching at cell.fst && g cell.fst)
    (cell member both => Bool.andIntro _ _ (Bool.andLeft _ _ both) (fg cell.fst (Bool.andRight _ _ both)))
