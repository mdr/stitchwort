--| The program's regions are the map's regions, each once: every list in
--| `regions` is the region of one of its plots (`regionsAreRegions`), and
--| every plot is in exactly one of them (`inOneRegion`).

namespace Aoc.Year2024.Day12.Proofs
import Aoc.Year2024.Day12 (..)
import Aoc.Common (Direction, Position, directions)
import Aoc.Year2024.Day12.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Iff, List, Map, Nat, Option, Or, Set, Void)

--| Every position on the list grows a plant.
theorem positionsGrow ∀ (garden: Garden) (position: Position)
    (member: position ∈ garden.positions):
    Exists Char (plant => garden.plantAt position = Some plant) :=
  let contains := (Map.memKeys garden.plots position).forward member
  match grows: garden.plantAt position with | Some plant => Witness plant rfl

--| After inserting a list of plots, `seen` has what it had and the plots.
theorem containsInsertAll ∀ (seen: Set Position) (plots: List Position) (position: Position):
    ((plots.foldLeft seen Set.insert).contains position = True)
      ↔ ((seen.contains position = True) ∨ (position ∈ plots)) :=
  rewrite Set.containsFoldInsert seen position plots,
      List.anyCong plots (member => Map.Spec.sameKey position member) (member => member == position) (member =>
        Map.Spec.sameKeyDecide position member) in
    {
      forward = either =>
        match before: seen.contains position with
          | True => Inl rfl
          | False => Inr ((List.memContains plots position).forward either),
      backward = either =>
        match either with
          | Inl before => rewrite before in rfl
          | Inr isIn => rewrite (List.memContains plots position).backward isIn in Bool.orTrue _
    }

--| A set of positions that has every plot joined to one it has.
def Closed (garden: Garden) (seen: Set Position): Prop :=
  ∀ (plot other: Position) => seen.contains plot = True → Joined garden plot other → seen.contains other = True

--| The region of a plot has every plot joined to one it has.
theorem regionClosed ∀ (garden: Garden) (start: Position) (plant: Char)
    (grows: garden.plantAt start = Some plant) (plot other: Position)
    (member: plot ∈ (garden.regionOf start).plots)
    (joined: Joined garden plot other):
    other ∈ (garden.regionOf start).plots :=
  let region := regionOfIsRegion garden start plant grows
  (region other).backward (joinedTrans garden start plot other ((region plot).forward member) joined)

--| A region's plots are joined to its start, and its start to itself.
theorem startInRegion ∀ (garden: Garden) (start: Position) (plant: Char)
    (grows: garden.plantAt start = Some plant):
    start ∈ (garden.regionOf start).plots :=
  (regionOfIsRegion garden start plant grows start).backward (joinedRefl garden start)

--| The regions containing `position`.
def regionsWith (regions: List Region) (position: Position): Nat := regions.count (region => region.contains position)

--| From a closed `seen`, the regions found are disjoint from `seen` and
--| from each other.
theorem atMostOnce ∀ (garden: Garden) (position: Position) (starts: List Position) (seen: Set Position)
    (closed: Closed garden seen)
    (plots: ∀ (start: Position) => start ∈ starts → Exists Char (plant => garden.plantAt start = Some plant)):
    (regionsWith (garden.regionsFrom starts seen) position ≤ 1)
      ∧ (seen.contains position = True → regionsWith (garden.regionsFrom starts seen) position = 0) :=
  match starts with
    | [] => Both (omega) (has => rfl)
    | [start, ..rest] =>
      match taken: seen.contains start with
        | True => atMostOnce garden position rest seen closed (other member => plots other (Inr member))
        | False => Exists.elim (plots start (Inl rfl)) (plant grows =>
          let region := garden.regionOf start
          let after := region.plots.foldLeft seen Set.insert
          let closedAfter: Closed garden after := from other has joined =>
            (containsInsertAll seen region.plots other).backward
              (match (containsInsertAll seen region.plots from).forward has with
                | Inl before => Inl (closed from other before joined)
                | Inr isIn => Inr (regionClosed garden start plant grows from other isIn joined))
          let later := atMostOnce garden position rest after closedAfter (other member => plots other (Inr member))
          rewrite List.countCons (garden.regionsFrom rest after) region (region => region.contains position) in
            match here: region.contains position with
              | True =>
                let isIn := here.read
                Both
                  (omega [And.right later ((containsInsertAll seen region.plots position).backward (Inr isIn))])
                  (has =>
                    Void.exfalso
                      (Bool.falseNotTrue
                        (Eq.trans
                          (Eq.sym taken)
                          (closed position start has
                            (joinedSymmetric garden start position
                              ((regionOfIsRegion garden start plant grows position).forward isIn))))))
              | False => Both (omega [And.left later]) (has =>
                omega [And.right later ((containsInsertAll seen region.plots position).backward (Inl has))]))

--| Each start is in `seen` or in a region found.
theorem covered ∀ (garden: Garden) (position: Position) (starts: List Position) (seen: Set Position)
    (plots: ∀ (start: Position) => start ∈ starts → Exists Char (plant => garden.plantAt start = Some plant))
    (none: position ∈ starts):
    (seen.contains position = True) ∨ (1 ≤ regionsWith (garden.regionsFrom starts seen) position) :=
  match starts, none with
    | [], none => Void.exfalso none
    | [start, ..rest], member =>
      match taken: seen.contains start with
        | True =>
          match member with
            | Inl same => Inl (rewrite <- same in taken)
            | Inr later => covered garden position rest seen (other isIn => plots other (Inr isIn)) later
        | False => Exists.elim (plots start (Inl rfl)) (plant grows =>
          let region := garden.regionOf start
          let after := region.plots.foldLeft seen Set.insert
          rewrite List.countCons (garden.regionsFrom rest after) region (region => region.contains position) in
            let inRegion: position ∈ region.plots
              → (seen.contains position = True)
                ∨ (1 ≤ Bool.toNat (region.contains position) + regionsWith (garden.regionsFrom rest after) position) :=
              isIn => Inr (rewrite (List.memContains region.plots position).backward isIn in omega)
            match member with
              | Inl same => inRegion (rewrite <- same in startInRegion garden start plant grows)
              | Inr later =>
                match covered garden position rest after (other isIn => plots other (Inr isIn)) later with
                  | Inl has =>
                    match (containsInsertAll seen region.plots position).forward has with
                      | Inl before => Inl before
                      | Inr isIn => inRegion isIn
                  | Inr found => Inr (omega [found]))

--| "Each garden plot" is in exactly one of the program's regions.
theorem inOneRegion ∀ (garden: Garden) (position: Position) (plant: Char)
    (grows: garden.plantAt position = Some plant):
    regionsWith garden.regions position = 1 :=
  let plots := (start: Position) (member: start ∈ garden.positions) => positionsGrow garden start member
  let once := atMostOnce garden position garden.positions Set.empty (from other has joined => cases) plots
  match covered garden position garden.positions Set.empty plots (garden.positionsComplete position plant grows) with
    | Inl has => cases
    | Inr found => omega [found, And.left once]

--| Each region found is the region of one of the starts.
theorem fromStarts ∀ (garden: Garden) (region: Region) (starts: List Position) (seen: Set Position)
    (none: region ∈ garden.regionsFrom starts seen):
    Exists Position (start => (start ∈ starts) ∧ (region = garden.regionOf start)) :=
  match starts, none with
    | [], none => Void.exfalso none
    | [start, ..rest], member =>
      match taken: seen.contains start with
        | True => Exists.elim (fromStarts garden region rest seen member) (other both =>
          Witness other (Both (Inr (And.left both)) (And.right both)))
        | False =>
          match member with
            | Inl same => Witness start (Both (Inl rfl) (Eq.sym same))
            | Inr later =>
              Exists.elim
                (fromStarts garden region rest ((garden.regionOf start).plots.foldLeft seen Set.insert) later)
                (other both => Witness other (Both (Inr (And.left both)) (And.right both)))

--| Each of the program's regions is a region of the map, its plots listed
--| once, and holds a plot.
theorem regionsAreRegions ∀ (garden: Garden) (region: Region)
    (member: region ∈ garden.regions):
    Exists Position (start =>
      (Exists Char (plant => garden.plantAt start = Some plant))
        ∧ ((IsRegion garden start region) ∧ (List.Distinct region.plots))) :=
  Exists.elim (fromStarts garden region garden.positions Set.empty member) (start both =>
    Exists.elim (positionsGrow garden start (And.left both)) (plant grows =>
      Witness start
        (Both
          (Witness plant grows)
          (rewrite And.right both in
            Both (regionOfIsRegion garden start plant grows) (regionOfDistinct garden start)))))
