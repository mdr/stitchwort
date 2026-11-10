--| Plots joined by a chain of touching plots: every plot is joined to itself,
--| a chain can be extended by one more touching plot, reversed, or followed
--| by another, and every plot joined to one growing a plant grows it too.

namespace Aoc.Year2024.Day12.Proofs
import Aoc.Year2024.Day12 (..)
import Aoc.Common (Direction, Position, directions)
import Aoc.Year2024.Day12.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, List, Option)

theorem joinedRefl (garden: Garden) (plot: Position): Joined garden plot plot := Witness [] (DecEq.refl plot)

--| A chain extended by one more touching plot.
theorem chainSnoc (garden: Garden) (from: Position) (chain: List Position) (to next: Position)
    (same: isChain garden from chain to = True) (touching: touches garden to next = True): isChain garden from (chain ++ [next]) next = True :=
  match chain, same with
    | [], same => rewrite DecEq.sound same in Bool.andIntro touching (DecEq.refl next)
    | [middle, ..rest], chained =>
      Bool.andIntro (Bool.andLeft chained) (chainSnoc garden middle rest to next (Bool.andRight chained) touching)

theorem joinedStep (garden: Garden) (plot: Position) (other: Position) (next: Position) (joined: Joined garden plot other)
    (touching: touches garden other next = True): Joined garden plot next :=
  Exists.elim joined (chain chained => Witness (chain ++ [next]) (chainSnoc garden plot chain other next chained touching))

theorem chainSymmetric (garden: Garden) (from: Position) (chain: List Position) (to: Position) (same: isChain garden from chain to = True):
    Joined garden to from :=
  match chain, same with
    | [], same => rewrite DecEq.sound same in joinedRefl garden to
    | [next, ..rest], chained =>
      joinedStep garden to next from (chainSymmetric garden next rest to (Bool.andRight chained))
        (touchesSymmetric garden from next (Bool.andLeft chained))

theorem joinedSymmetric (garden: Garden) (plot: Position) (other: Position) (joined: Joined garden plot other): Joined garden other plot :=
  Exists.elim joined (chain chained => chainSymmetric garden plot chain other chained)

theorem chainTrans (garden: Garden) (plot: Position) (from: Position) (chain: List Position) (to: Position) (joined: Joined garden plot from)
    (same: isChain garden from chain to = True): Joined garden plot to :=
  match chain, same with
    | [], same => rewrite <- DecEq.sound same in joined
    | [next, ..rest], chained =>
      chainTrans garden plot next rest to (joinedStep garden plot from next joined (Bool.andLeft chained)) (Bool.andRight chained)

theorem joinedTrans (garden: Garden) (plot: Position) (middle: Position) (other: Position) (first: Joined garden plot middle)
    (second: Joined garden middle other): Joined garden plot other :=
  Exists.elim second (chain chained => chainTrans garden plot middle chain other first chained)

--| Every plot of a chain grows the plant the first one does.
theorem chainPlant (garden: Garden) (plant: Char) (from: Position) (chain: List Position) (to: Position)
    (grows: garden.plantAt from = Some plant) (h: isChain garden from chain to = True): garden.plantAt to = Some plant :=
  match chain, h with
    | [], same => rewrite <- DecEq.sound same in grows
    | [next, ..rest], chained =>
      Exists.elim (growSameElim garden from next (Bool.andRight (Bool.andLeft chained))) (same both =>
        let plantSame: same = plant := Option.someInjective (Eq.trans (Eq.sym (And.left both)) grows)
        chainPlant garden plant next rest to (rewrite <- plantSame in And.right both) (Bool.andRight chained))

theorem joinedPlant (garden: Garden) (plant: Char) (plot: Position) (other: Position) (grows: garden.plantAt plot = Some plant)
    (joined: Joined garden plot other): garden.plantAt other = Some plant :=
  Exists.elim joined (chain chained => chainPlant garden plant plot chain other grows chained)
