--| What one round of the program does, in the spec's terms: an octopus
--| flashes after the round exactly when it is on the grid and its energy,
--| counting the flashes before the round, is above 9. And facts about the
--| spec's counts.

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Aoc.Common (Position, cellAt, cells, mapCells, touching)
import Aoc.Common.Proofs (cellAtMapCells, memCells)
import Std (Bool, DecEq, Eq, Exists, Iff, List, Nat, Option, Void)

--| The positions on the grid.
def positions (levels: List (List Nat)): List Position := (cells levels).map Pair.fst

--| Only octopuses on the grid have flashed.
def OnGrid (levels: List (List Nat)) (flashed: Position → Bool): Prop := (q: Position) → flashed q = True → q ∈ positions levels

--| A grid the shape of `levels` has `True`s only on its positions.
theorem onGridMapCells (levels: List (List Nat)) (h: Position → Nat → Bool): OnGrid levels (flashedAt (mapCells levels h))
  | q, flashes =>
    match e: cellAt levels q with
      | None => Void.exfalso (Bool.falseNotTrue (rewrite cellAtMapCells levels h q, e at flashes in flashes))
      | Some level => List.memMap (cells levels) (q, level) ((memCells levels q level).backward e) Pair.fst

--| Whether `q` has flashed in a grid made by `mapCells`.
theorem flashedAtMapCells (levels: List (List Nat)) (h: Position → Nat → Bool) (q: Position):
    flashedAt (mapCells levels h) q = Option.getOrElse (Option.map (cellAt levels q) (h q)) False :=
  Eq.cong (found => Option.getOrElse found False) (cellAtMapCells levels h q)

--| The program's energy is the spec's, for flashers on the grid.
theorem energyAgrees (levels: List (List Nat)) (flashed: List (List Bool)) (onGrid: OnGrid levels (flashedAt flashed)) (q: Position) (level: Nat):
    energy flashed q level = energyIn levels (flashedAt flashed) q level :=
  rewrite countAround levels (flashedAt flashed) onGrid q in rfl

--| After a round, an octopus with energy above 9 has flashed...
theorem roundIntro (levels: List (List Nat)) (flashed: List (List Bool)) (onGrid: OnGrid levels (flashedAt flashed)) (q: Position) (level: Nat)
    (member: (q, level) ∈ cells levels) (above: 9 < energyIn levels (flashedAt flashed) q level): flashedAt (flashRound levels flashed) q = True :=
  Eq.trans (flashedAtMapCells levels (at level => 9 < energy flashed at level) q)
    (rewrite (memCells levels q level).forward member in Eq.trans (Eq.cong (Nat.leq 10) (energyAgrees levels flashed onGrid q level)) above)

--| ...and an octopus that has flashed is on the grid, with energy above 9.
theorem roundElim (levels: List (List Nat)) (flashed: List (List Bool)) (onGrid: OnGrid levels (flashedAt flashed)) (q: Position)
    (flashes: flashedAt (flashRound levels flashed) q = True): ∃ (level: Nat) => (q, level) ∈ cells levels ∧ 9 < energyIn levels (flashedAt flashed) q level :=
  let opened := Eq.trans (Eq.sym (flashedAtMapCells levels (at level => 9 < energy flashed at level) q)) flashes
  match e: cellAt levels q with
    | None => Void.exfalso (Bool.falseNotTrue opened)
    | Some level =>
      Witness level
        (Both ((memCells levels q level).backward e) (Eq.trans (Eq.sym (Eq.cong (Nat.leq 10) (energyAgrees levels flashed onGrid q level))) opened))

--| More flashers, more flashing neighbours.
theorem neighboursMono (levels: List (List Nat)) (f: Position → Bool) (g: Position → Bool) (fg: (q: Position) → f q = True → g q = True)
    (at: Position): flashingNeighbours levels f at ≤ flashingNeighbours levels g at :=
  List.countLeMem (cells levels) (cell => touching at cell.fst && f cell.fst) (cell => touching at cell.fst && g cell.fst)
    (cell member both => Bool.andIntro _ _ (Bool.andLeft _ _ both) (fg cell.fst (Bool.andRight _ _ both)))
