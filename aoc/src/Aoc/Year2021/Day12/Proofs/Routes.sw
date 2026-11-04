--| The routes the search lists, described one step at a time (`Follows`),
--| and listed each once.

namespace Aoc.Year2021.Day12.Proofs
import Aoc.Year2021.Day12 (..)
import Std (Bool, Eq, Exists, List, Nat, Void)

--| A route on from `cave`: its first cave is a neighbour, and the step to it
--| ends the route there, or goes on along a route from it.
def Follows (next: Text → List Text) (unvisited: List Text) (spare: Bool) (cave: Text): List Text → Prop
  | [] => Void
  | [other, ..rest] =>
    other ∈ next cave
      ∧ (match step unvisited spare cave other with
        | Finish => rest = []
        | Blocked => Void
        | Continue left stillSpare => Follows next left stillSpare other rest)

--| Every route listed follows the steps...
theorem routesFollow (next: Text → List Text) (unvisited: List Text) (spare: Bool) (cave: Text):
    (steps: Nat) → (rest: List Text) → rest ∈ routesFrom next unvisited spare cave steps → Follows next unvisited spare cave rest
  | Zero, rest, found => Void.exfalso found
  | Succ more, rest, found =>
    List.anyElim _ _ (next cave) (List.memFlatMapElim _ rest (next cave) found) (other member inOther =>
      Exists.elim (List.memMapElim (Cons other) rest _ inOther) (tail both =>
        let (Both inTail same) := both
        rewrite <- same in
          match e: step unvisited spare cave other with
            | Finish =>
              match inTail with
                | Inl empty => rewrite <- empty in Both member rfl
                | Inr nothing => Void.exfalso nothing
            | Blocked => Void.exfalso inTail
            | Continue left stillSpare => Both member (routesFollow next left stillSpare other more tail inTail)))

--| ...and every route that follows them is listed, if the search goes deep
--| enough.
theorem followRoutes (next: Text → List Text) (unvisited: List Text) (spare: Bool) (cave: Text):
    (steps: Nat) → (rest: List Text) → reach unvisited spare cave < steps → Follows next unvisited spare cave rest → rest ∈ routesFrom next unvisited spare cave steps
  | Zero, rest, enough, follows => Void.exfalso (omega)
  | Succ more, [], enough, follows => Void.exfalso follows
  | Succ more, [other, ..tail], enough, Both member after =>
    List.memFlatMapIntro _ other [other, ..tail] (next cave) member
      (match e: step unvisited spare cave other with
        | Finish => rewrite after in Inl rfl
        | Blocked => Void.exfalso after
        | Continue left stillSpare =>
          List.memMap _ tail (followRoutes next left stillSpare other more tail (omega [stepDecreases unvisited spare cave other left stillSpare e]) after) (Cons other))

--| Routes on from `other` start with it...
theorem viaFirst (other: Text) (after: List (List Text)) (route: List Text) (found: route ∈ routesVia other after): route.headOr "" = other :=
  Exists.elim (List.memMapElim (Cons other) route after found) (tail both => rewrite <- And.right both in rfl)

--| ...and are as many as the routes they continue.
theorem viaDistinct (other: Text) (after: List (List Text)) (distinct: List.Distinct after): List.Distinct (routesVia other after) :=
  List.distinctMap after distinct (Cons other) (a b same => Eq.cong (route => route.drop 1) same)

--| The search lists each route once, if each cave's neighbours are listed
--| once.
theorem routesDistinct (next: Text → List Text) (distinctNext: (cave: Text) → List.Distinct (next cave)) (unvisited: List Text) (spare: Bool) (cave: Text):
    (steps: Nat) → List.Distinct (routesFrom next unvisited spare cave steps)
  | Zero => Trivial
  | Succ more =>
    List.distinctFlatMap _ (route => route.headOr "") (next cave) (distinctNext cave)
      (other member =>
        viaDistinct other _
          (match e: step unvisited spare cave other with
            | Finish => Both (nothing => nothing) Trivial
            | Blocked => Trivial
            | Continue left stillSpare => routesDistinct next distinctNext left stillSpare other more))
      (other member route found => viaFirst other _ route found)
