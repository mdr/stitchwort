--| `FreeSpace`, the free spans by length, against the set of spans it holds:
--| adding and removing a span, building it from a list, and which span
--| `leftmostFit` finds.

namespace Aoc.Year2024.Day09.Proofs
import Aoc.Year2024.Day09 (..)
import Std (Bool, Eq, List, Map, Nat, Option, Set, Void)

--| Whether the free spans hold `span`.
def FreeSpace.has (free: FreeSpace) (span: Span): Bool := free.containsIn span.length span.start

--| Adding a span of length 0 changes nothing.
theorem hasAdd (free: FreeSpace) (span: Span) (other: Span):
    ((free.add span).has other = True) ↔ ((0 < span.length ∧ other = span) ∨ free.has other = True) :=
  match empty: span.length == 0 with
    | True => {
      forward = held => Inr held,
      backward = either =>
        match either with
          | Inl pair => Void.exfalso (omega [pair.left])
          | Inr held => held
    }
    | False => {
      forward = held =>
        match (Map.containsInInsertInIff free span.length span.start other.length other.start).forward held with
          | Inl pair => Inl (Both (omega) (Span.ext other span pair.right pair.left))
          | Inr old => Inr old,
      backward = either =>
        match either with
          | Inl pair =>
            (Map.containsInInsertInIff free span.length span.start other.length other.start).backward
              (Inl (Both (rewrite pair.right in rfl) (rewrite pair.right in rfl)))
          | Inr old => (Map.containsInInsertInIff free span.length span.start other.length other.start).backward (Inr old)
    }

theorem hasRemove (free: FreeSpace) (span: Span) (other: Span):
    ((free.remove span).has other = True) ↔ (other ≠ span ∧ free.has other = True) := {
  forward = held =>
    let (Both differs old) := (Map.containsInRemoveInIff free span.length span.start other.length other.start).forward held
    Both (same => differs (Both (rewrite same in rfl) (rewrite same in rfl))) old,
  backward = both =>
    (Map.containsInRemoveInIff free span.length span.start other.length other.start).backward
      (Both (pair => both.left (Span.ext other span pair.right pair.left)) both.right)
}

-- Stated for any starting map, since the fold's recursive call starts from the map after the first add.
theorem hasFoldAdd (span: Span) (spans: List Span) (free: FreeSpace):
    FreeSpace.has (spans.foldLeft free FreeSpace.add) span = True ↔ ((0 < span.length ∧ span ∈ spans) ∨ free.has span = True) :=
  match spans with
    | [] => {
      forward = held => Inr held,
      backward = either =>
        match either with
          | Inl pair => Void.exfalso pair.right
          | Inr held => held
    }
    | [x, ..rest] => {
      forward = held =>
        match (hasFoldAdd span rest (free.add x)).forward held with
          | Inl pair => Inl (Both pair.left (Inr pair.right))
          | Inr added =>
            match (hasAdd free x span).forward added with
              | Inl pair => Inl (Both (rewrite pair.right in pair.left) (Inl (Eq.sym pair.right)))
              | Inr old => Inr old,
      backward = either =>
        (hasFoldAdd span rest (free.add x)).backward
          (match either with
            | Inl pair =>
              match pair.right with
                | Inl same => Inr ((hasAdd free x span).backward (Inl (Both (rewrite same in pair.left) (Eq.sym same))))
                | Inr later => Inl (Both pair.left later)
            | Inr old => Inr ((hasAdd free x span).backward (Inr old)))
    }

--| The spans of length 0 aren't kept.
theorem hasOf (spans: List Span) (span: Span): (FreeSpace.of spans).has span = True ↔ (0 < span.length ∧ span ∈ spans) := {
  forward = held =>
    match (hasFoldAdd span spans Map.empty).forward held with
      | Inl pair => pair
      | Inr empty => cases,
  backward = pair => (hasFoldAdd span spans Map.empty).backward (Inl pair)
}

--| What `leftmostFit` makes of one entry of the map: the span at the entry's smallest start, if the entry is long enough.
def fitIn (length: Nat) (entry: (Nat, Set Nat)): Option Span :=
  if length <= entry.fst then entry.snd.min |> .map (start => ({ start, length = entry.fst }: Span)) else None

theorem fitInSome (length: Nat) (key: Nat) (items: Set Nat) (span: Span) (found: fitIn length (key, items) = Some span):
    length ≤ key ∧ span.length = key ∧ items.min = Some span.start := match fits: length <= key with
      | True =>
        match least: items.min with
          | Some start =>
            let same: { start, length = key } = span := Option.someInjective found
            rewrite <- same in Both (omega) (Both rfl rfl)

theorem fitInIntro (length: Nat) (key: Nat) (items: Set Nat) (start: Nat) (fits: length ≤ key) (least: items.min = Some start):
    fitIn length (key, items) = Some { start, length = key } := match enough: length <= key with
      | True => rewrite least in rfl

--| A span the map holds, long enough, is not before the span `fitIn` makes of its entry.
theorem fitMember (free: FreeSpace) (length: Nat) (other: Span) (held: free.has other = True) (fits: length ≤ other.length):
    ∃ (start: Nat) => (({ start, length = other.length }: Span) ∈ free.toList.filterMap (fitIn length)) ∧ start ≤ other.start :=
  let (Witness items (Both inList there)) := (Map.containsInToList free other.length other.start).forward held
  let (Witness least isLeast) := Set.minOfContains items other.start there
  Witness least (Both
    (List.memFilterMapIntro (fitIn length) (other.length, items) _ free.toList inList (fitInIntro length other.length items least fits isLeast))
    (Set.minLeast items least isLeast other.start there))

theorem leftmostFitSome (free: FreeSpace) (length: Nat) (before: Nat) (span: Span) (found: free.leftmostFit length before = Some span):
    free.has span = True ∧ length ≤ span.length ∧ span.start < before ∧
      (∀ (other: Span) => free.has other = True → length ≤ other.length → span.start ≤ other.start) :=
  let (Both minimal early) := Option.filterEqSome _ ((s: Span) => s.start < before) found
  let (Both mem least) := List.minBySome (free.toList.filterMap (fitIn length)) (.start) span minimal
  let (Witness entry (Both inList fit)) := (List.memFilterMap (fitIn length) span free.toList).forward mem
  match entry with
    | (key, items) =>
      let (Both enough (Both sameLength isLeast)) := fitInSome length key items span fit
      Both
        ((Map.containsInToList free span.length span.start).backward
          (Witness items (Both (rewrite sameLength in inList) (Set.containsMin items span.start isLeast))))
        (Both (rewrite sameLength in enough) (Both early
          (other held fits =>
            let (Witness start (Both member below)) := fitMember free length other held fits
            omega [least _ member, below])))

theorem leftmostFitNone (free: FreeSpace) (length: Nat) (before: Nat) (none: free.leftmostFit length before = None)
    (other: Span) (held: free.has other = True) (fits: length ≤ other.length): before ≤ other.start :=
  let (Witness start (Both member below)) := fitMember free length other held fits
  match Option.filterEqNone _ ((s: Span) => s.start < before) none with
    | Inl empty =>
      let nothing := List.minByNone _ _ empty
      Void.exfalso (rewrite nothing at member in member)
    | Inr (Witness least (Both minimal late)) =>
      let (Both memberLeast bound) := List.minBySome (free.toList.filterMap (fitIn length)) (.start) least minimal
      omega [bound _ member]
