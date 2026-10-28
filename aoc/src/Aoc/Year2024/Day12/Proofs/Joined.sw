-- Plots joined by a chain of touching plots: every plot is joined to itself,
-- a chain can be extended by one more touching plot, reversed, or followed
-- by another, and every plot joined to one growing a plant grows it too.

namespace Aoc.Year2024.Day12.Proofs
import Aoc.Year2024.Day12 (..)
import Aoc.Year2024.Day12.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, List, Option)

theorem joinedRefl (garden: Garden) (plot: Position): Joined garden plot plot := Witness Nil (DecEq.refl plot)

-- A chain extended by one more touching plot.
theorem chainSnoc (garden: Garden): (from: Position) → (chain: List Position) → (to: Position) → (next: Position) →
    isChain garden from chain to = True → touches garden to next = True → isChain garden from (chain ++ [next]) next = True
  | from, Nil, to, next, same, touching => rewrite DecEq.sound from to same in Bool.andIntro _ _ touching (DecEq.refl next)
  | from, Cons middle rest, to, next, chained, touching =>
    Bool.andIntro _ _ (Bool.andLeft _ _ chained) (chainSnoc garden middle rest to next (Bool.andRight _ _ chained) touching)

theorem joinedStep (garden: Garden) (plot: Position) (other: Position) (next: Position) (joined: Joined garden plot other)
    (touching: touches garden other next = True): Joined garden plot next :=
  Exists.elim joined (chain chained => Witness (chain ++ [next]) (chainSnoc garden plot chain other next chained touching))

theorem chainSymmetric (garden: Garden): (from: Position) → (chain: List Position) → (to: Position) → isChain garden from chain to = True →
    Joined garden to from
  | from, Nil, to, same => rewrite DecEq.sound from to same in joinedRefl garden to
  | from, Cons next rest, to, chained =>
    joinedStep garden to next from (chainSymmetric garden next rest to (Bool.andRight _ _ chained))
      (touchesSymmetric garden from next (Bool.andLeft _ _ chained))

theorem joinedSymmetric (garden: Garden) (plot: Position) (other: Position) (joined: Joined garden plot other): Joined garden other plot :=
  Exists.elim joined (chain chained => chainSymmetric garden plot chain other chained)

theorem chainTrans (garden: Garden) (plot: Position): (from: Position) → (chain: List Position) → (to: Position) → Joined garden plot from →
    isChain garden from chain to = True → Joined garden plot to
  | from, Nil, to, joined, same => rewrite <- DecEq.sound from to same in joined
  | from, Cons next rest, to, joined, chained =>
    chainTrans garden plot next rest to (joinedStep garden plot from next joined (Bool.andLeft _ _ chained)) (Bool.andRight _ _ chained)

theorem joinedTrans (garden: Garden) (plot: Position) (middle: Position) (other: Position) (first: Joined garden plot middle)
    (second: Joined garden middle other): Joined garden plot other :=
  Exists.elim second (chain chained => chainTrans garden plot middle chain other first chained)

-- Every plot of a chain grows the plant the first one does.
theorem chainPlant (garden: Garden) (plant: Char): (from: Position) → (chain: List Position) → (to: Position) →
    garden.plantAt from = Some plant → isChain garden from chain to = True → garden.plantAt to = Some plant
  | from, Nil, to, grows, same => rewrite <- DecEq.sound from to same in grows
  | from, Cons next rest, to, grows, chained =>
    Exists.elim (growSameElim garden from next (Bool.andRight _ _ (Bool.andLeft _ _ chained))) (same both =>
      let plantSame: same = plant := Option.someInjective _ _ (Eq.trans (Eq.sym (And.left both)) grows)
      chainPlant garden plant next rest to (rewrite <- plantSame in And.right both) (Bool.andRight _ _ chained))

theorem joinedPlant (garden: Garden) (plant: Char) (plot: Position) (other: Position) (grows: garden.plantAt plot = Some plant)
    (joined: Joined garden plot other): garden.plantAt other = Some plant :=
  Exists.elim joined (chain chained => chainPlant garden plant plot chain other grows chained)
