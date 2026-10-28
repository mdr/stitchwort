-- Facts the proofs need: steps along a line never revisit a position, what
-- the set operations the moves use do to membership, and that a set holding
-- `count` different positions has at least `count` elements.

namespace Aoc.Year2024.Day15.Proofs
import Aoc.Year2024.Day15 (..)
import Aoc.Year2024.Day15.Spec (ahead)
import Std (And, Bool, DecEq, Decidable, Eq, Exists, Iff, Int, List, Map, Nat, Not, Or, Pair, Set, Void)

-- How far along `direction` a position is.
def progress (direction: Direction) (position: Position): Int :=
  match direction with
    | Up => 0 - position.row
    | Down => position.row
    | Left => 0 - position.column
    | Right => position.column

theorem progressStep (position: Position): (direction: Direction) → progress direction (position.step direction) = progress direction position + 1
  | Up => omega
  | Down => rfl
  | Left => omega
  | Right => rfl

theorem progressAhead (position: Position) (direction: Direction): (count: Nat) → progress direction (ahead position direction count) = progress direction position + count.toInt
  | Zero => omega
  | Succ count => omega [progressStep (ahead position direction count) direction, progressAhead position direction count]

-- Steps along a line never come back.
theorem aheadInjective (position: Position) (direction: Direction) (i: Nat) (j: Nat) (same: ahead position direction i = ahead position direction j): i = j :=
  omega [Eq.cong (progress direction) same, progressAhead position direction i, progressAhead position direction j]

-- Counting from the next position.
theorem aheadFrom (position: Position) (direction: Direction): (count: Nat) → ahead (position.step direction) direction count = ahead position direction (Succ count)
  | Zero => rfl
  | Succ count => Eq.cong (here => here.step direction) (aheadFrom position direction count)

theorem aheadAddOne (position: Position) (direction: Direction) (count: Nat):
    ahead position direction (count + 1) = (ahead position direction count).step direction :=
  rewrite Nat.addOne count in rfl

-- Whether `position` is one of the `count` positions after `start`.
theorem decideAhead (start: Position) (direction: Direction) (count: Nat) (position: Position):
    Or (∃ (j: Nat) => j < count ∧ position = ahead start direction (j + 1))
      ((i: Nat) → i < count → Not (position = ahead start direction (i + 1))) :=
  match found: (List.range count).any (i => position == ahead start direction (i + 1)) with
    | True =>
      List.anyTrueElim (List.range count) _ _ found
        (j member same => Inl (Witness j (Both (omega [List.memRangeFrom j count 0 member]) (DecEq.sound _ _ same))))
    | False =>
      Inr (i below same =>
        Bool.trueNotFalse
          (Eq.trans
            (Eq.sym
              (List.anyOfMem (List.range count) _ i (rewrite same in DecEq.refl (ahead start direction (i + 1)))
                (List.memRangeFromIntro i count 0 (omega) (omega))))
            found))

-- A `Bool` that can't be `True` is `False`.
theorem falseOf (value: Bool) (refute: value = True → Void): value = False :=
  match held: value with
    | True => Void.exfalso (refute rfl)
    | False => rfl

-- Positions with the same row and column are equal.
theorem positionEq: (position: Position) → (other: Position) → position.row = other.row → position.column = other.column → position = other
  | { row, column }, { row = otherRow, column = otherColumn }, rows, columns => rewrite rows, columns in rfl

theorem stepInjective (position: Position) (other: Position): (direction: Direction) → position.step direction = other.step direction → position = other
  | Up, same => positionEq position other (omega [Eq.cong (here => here.row) same]) (Eq.cong (here => here.column) same)
  | Down, same => positionEq position other (omega [Eq.cong (here => here.row) same]) (Eq.cong (here => here.column) same)
  | Left, same => positionEq position other (Eq.cong (here => here.row) same) (omega [Eq.cong (here => here.column) same])
  | Right, same => positionEq position other (Eq.cong (here => here.row) same) (omega [Eq.cong (here => here.column) same])

theorem stepRightLeft (position: Position): (position.step Right).step Left = position := positionEq ((position.step Right).step Left) position rfl (omega)

theorem stepLeftRight (position: Position): (position.step Left).step Right = position := positionEq ((position.step Left).step Right) position rfl (omega)

-- Steps in two directions can be taken in either order.
theorem stepRightComm (position: Position): (direction: Direction) → (position.step direction).step Right = (position.step Right).step direction
  | Up => rfl
  | Down => rfl
  | Left => positionEq ((position.step Left).step Right) ((position.step Right).step Left) rfl (omega)
  | Right => rfl

-- Sets.

-- A set holding something isn't empty.
theorem sizePositive (set: Set Position) (key: Position) (member: set.contains key = True): 1 ≤ set.size :=
  match c: set.toList with
    | Nil => Void.exfalso (rewrite c at (Map.memKeysOfContains set.items key member: List.Mem key (Set.toList set)))
    | Cons first rest => rewrite Set.sizeToList set, c in omega

-- A set holding `count` different positions, `at 0` to `at (count - 1)`,
-- has at least `count` elements.
theorem countAtMostSize (at: Nat → Position): (count: Nat) → (set: Set Position) →
    ((i: Nat) → i < count → set.contains (at i) = True) → ((i: Nat) → (j: Nat) → i < count → j < count → at i = at j → i = j) → count ≤ set.size
  | Zero, set, members, different => omega
  | Succ count, set, members, different =>
    let rest := set.remove (at count)
    let restMembers: (i: Nat) → i < count → rest.contains (at i) = True := i below =>
      rewrite Set.containsRemoveOther set (at count) (at i) (same => omega [different i count (omega) (omega) same]) in members i (omega)
    let smaller := countAtMostSize at count rest restMembers (i j below belowJ same => different i j (omega) (omega) same)
    let removed: rest.size = set.size - 1 := rewrite Map.sizeRemove set.items (at count), members count (omega) in rfl
    omega [sizePositive set (at count) (members count (omega))]

-- A fold over a map's entries that ignores the values is a fold over its keys.
theorem foldEntriesIsFoldKeys (f: b → Position → b): (entries: List (Position, ())) → (initial: b) →
    Map.Spec.foldLeft (acc key unit => f acc key) initial entries = List.foldLeft (entries.map Pair.fst) initial f
  | Nil, initial => rfl
  | Cons (key, unit) rest, initial => foldEntriesIsFoldKeys f rest (f initial key)

-- A fold over a set is a fold over its elements in order.
theorem setFoldLeftIsList (set: Set Position) (initial: b) (f: b → Position → b): set.foldLeft initial f = set.toList.foldLeft initial f :=
  rewrite Map.foldLeftToList (acc key unit => f acc key) initial set.items in foldEntriesIsFoldKeys f (Map.toList set.items) initial

-- A set holds what its list of elements holds.
theorem memToList (set: Set Position) (key: Position): Iff (key ∈ set.toList) (set.contains key = True) := Map.memKeys set.items key

-- Removing each of `keys` from `set` leaves what `set` holds and `keys`
-- doesn't.
theorem containsFoldRemove: (keys: List Position) → (set: Set Position) → (key: Position) →
    Iff ((keys.foldLeft set Set.remove).contains key = True) (And (set.contains key = True) (Not (key ∈ keys)))
  | Nil, set, key => { forward = held => Both held (none => none), backward = held => And.left held }
  | Cons first rest, set, key =>
    let later := containsFoldRemove rest (set.remove first) key
    {
      forward = held =>
        match Iff.forward later held with
          | Both inRemoved notRest =>
            match DecEq.decide key first with
              | Yes same => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym inRemoved) (rewrite same in Set.containsRemove set first)))
              | No different =>
                Both (rewrite Set.containsRemoveOther set first key different at inRemoved)
                  (member =>
                    match member with
                      | Inl same => different (Eq.sym same)
                      | Inr inRest => notRest inRest),
      backward = held =>
        let different: Not (key = first) := same => And.right held (Inl (Eq.sym same))
        Iff.backward later (Both (rewrite Set.containsRemoveOther set first key different in And.left held) (inRest => And.right held (Inr inRest)))
    }

-- Inserting `f` of each of `keys` into `set` gives what `set` holds and
-- `f` of each key.
theorem containsFoldInsertMap (f: Position → Position): (keys: List Position) → (set: Set Position) → (key: Position) →
    Iff ((keys.foldLeft set (acc x => acc.insert (f x))).contains key = True) (Or (set.contains key = True) (∃ (x: Position) => x ∈ keys ∧ f x = key))
  | Nil, set, key => { forward = held => Inl held, backward = held => match held with
    | Inl inSet => inSet
    | Inr (Witness x (Both none same)) => Void.exfalso none }
  | Cons first rest, set, key =>
    let later := containsFoldInsertMap f rest (set.insert (f first)) key
    {
      forward = held =>
        match Iff.forward later held with
          | Inl inInserted =>
            match DecEq.decide key (f first) with
              | Yes same => Inr (Witness first (Both (Inl rfl) (Eq.sym same)))
              | No different => Inl (rewrite Set.containsInsertOther set (f first) key different at inInserted)
          | Inr (Witness x (Both inRest same)) => Inr (Witness x (Both (Inr inRest) same)),
      backward = held =>
        match held with
          | Inl inSet => Iff.backward later (Inl (Set.containsInsertMono set (f first) key inSet))
          | Inr (Witness x (Both (Inl isFirst) same)) => Iff.backward later (Inl (rewrite <- same, <- isFirst in Set.containsInsert (f first) set))
          | Inr (Witness x (Both (Inr inRest) same)) => Iff.backward later (Inr (Witness x (Both inRest same)))
    }

-- `set.map f` holds `f` of each element of `set`, and nothing else.
theorem containsMap (set: Set Position) (f: Position → Position) (key: Position):
    Iff ((set.map f).contains key = True) (∃ (x: Position) => set.contains x = True ∧ f x = key) :=
  let folded := containsFoldInsertMap f set.toList Set.empty key
  {
    forward = held =>
      match Iff.forward folded (rewrite <- setFoldLeftIsList set Set.empty (acc x => acc.insert (f x)) in held) with
        | Inl none => Void.exfalso (Bool.falseNotTrue none)
        | Inr (Witness x (Both member same)) => Witness x (Both (Iff.forward (memToList set x) member) same),
    backward = held =>
      match held with
        | Witness x (Both inSet same) =>
          rewrite setFoldLeftIsList set Set.empty (acc x => acc.insert (f x)) in
            Iff.backward folded (Inr (Witness x (Both (Iff.backward (memToList set x) inSet) same)))
  }
