-- The step budget is enough: a guard who starts on the map and is still on
-- it after `stateCount` steps loops forever (`budgetEnough`). There are only
-- `stateCount` states on the map, so two of the first `stateCount + 1` are the
-- same (`pigeonhole`), and from then on the walk repeats.

namespace Aoc.Year2024.Day06.Proofs
import Aoc.Year2024.Day06 (..)
import Aoc.Year2024.Day06.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Nat, Not, Option, Void)

-- Once off the map, she stays off.
theorem walkNone (lab: Lab): (steps: Nat) → walk lab None steps = None
  | Zero => rfl
  | Succ steps => walkNone lab steps

-- The last of `steps + 1` steps.
theorem walkSucc (lab: Lab): (steps: Nat) → (guard: Option Guard) → walk lab guard (Succ steps) = (walk lab guard steps).flatMap lab.step
  | Zero, guard => rfl
  | Succ steps, guard => walkSucc lab steps (guard.flatMap lab.step)

-- Walking `first + second` steps is walking `first`, then `second`.
theorem walkAdd (lab: Lab): (first: Nat) → (guard: Option Guard) → (second: Nat) → walk lab guard (first + second) = walk lab (walk lab guard first) second
  | Zero, guard, second => rfl
  | Succ first, guard, second => walkAdd lab first (guard.flatMap lab.step) second

-- Gone after `steps`, she is gone after any more.
theorem walkLater (lab: Lab) (guard: Option Guard) (steps: Nat) (later: Nat) (gone: walk lab guard steps = None) (le: steps ≤ later):
    walk lab guard later = None :=
  let split: later = steps + (later - steps) := omega
  rewrite split, walkAdd lab steps guard (later - steps), gone in walkNone lab (later - steps)

-- Still on the map after `later` steps, she was after any fewer.
theorem walkEarlier (lab: Lab) (guard: Option Guard) (steps: Nat) (later: Nat) (still: Not (walk lab guard later = None)) (le: steps ≤ later):
    Not (walk lab guard steps = None) :=
  gone => still (walkLater lab guard steps later gone le)

-- The first `i ≤ last` (counting down from `last`) with `f i = value`.
def lastHit (f: Nat → Nat) (value: Nat): (last: Nat) → Option Nat
  | Zero => if f 0 == value then Some 0 else None
  | Succ last => if f (Succ last) == value then Some (Succ last) else lastHit f value last

theorem lastHitSome (f: Nat → Nat) (value: Nat): (last: Nat) → (i: Nat) → lastHit f value last = Some i → And (i ≤ last) (f i = value)
  | Zero, i, found =>
    match e: f 0 == value with
      | True => rewrite <- Option.someInjective 0 i found in Both rfl (DecEq.sound (f 0) value e)
      | False => Void.exfalso (Option.noneNotSome i found)
  | Succ last, i, found =>
    match e: f (Succ last) == value with
      | True => rewrite <- Option.someInjective (Succ last) i found in Both (Nat.leRefl (Succ last)) (DecEq.sound (f (Succ last)) value e)
      | False =>
        let earlier := lastHitSome f value last i found
        Both (omega [And.left earlier]) (And.right earlier)

theorem lastHitNone (f: Nat → Nat) (value: Nat): (last: Nat) → lastHit f value last = None → (i: Nat) → i ≤ last → Not (f i = value)
  | Zero, none, i, le, same =>
    match e: f 0 == value with
      | True => Option.someNotNone 0 none
      | False => DecEq.soundFalse (f 0) value e (rewrite (omega: i = 0) at same)
  | Succ last, none, i, le, same =>
    match e: f (Succ last) == value with
      | True => Option.someNotNone (Succ last) none
      | False =>
        match atLast: i == Succ last with
          | True => DecEq.soundFalse (f (Succ last)) value e (rewrite DecEq.sound i (Succ last) atLast at same)
          | False => lastHitNone f value last none i (omega [DecEq.soundFalse i (Succ last) atLast]) same

-- Two of `i` and `j` at most `last`, `i` first, where `f` agrees.
def Repeats (f: Nat → Nat) (last: Nat): Prop := Exists Nat (i => Exists Nat (j => And (i < j) (And (j ≤ last) (f i = f j))))

-- `f` takes `last + 1` values below `last` at `0, …, last`, so two are the
-- same. If none of the first `last` hits `f last`'s value, swap the values
-- `last - 1` and `f last` in them: they are then all below `last - 1`.
theorem pigeonhole: (last: Nat) → (f: Nat → Nat) → ((i: Nat) → i ≤ last → f i < last) → Repeats f last
  | Zero, f, small => Void.exfalso (omega [small 0 rfl])
  | Succ last, f, small =>
    match found: lastHit f (f (Succ last)) last with
      | Some i =>
        let hit := lastHitSome f (f (Succ last)) last i found
        Witness i (Witness (Succ last) (Both (omega [And.left hit]) (Both (Nat.leRefl (Succ last)) (And.right hit))))
      | None =>
        let missed := lastHitNone f (f (Succ last)) last found
        let swapped := (i: Nat) => if f i == last then f (Succ last) else f i
        let swappedSmall: (i: Nat) → i ≤ last → swapped i < last :=
          i le =>
            match atLast: f i == last with
              | True =>
                let notLast: Not (f (Succ last) = last) := same => missed i le (Eq.trans (DecEq.sound (f i) last atLast) (Eq.sym same))
                omega [small (Succ last) (Nat.leRefl (Succ last)), notLast]
              | False => omega [small i (omega [le]), DecEq.soundFalse (f i) last atLast]
        Exists.elim (pigeonhole last swapped swappedSmall) (i rest =>
          Exists.elim rest (j both =>
            let ij := And.left both
            let jLast := And.left (And.right both)
            let same := And.right (And.right both)
            let agree: f i = f j :=
              match atI: f i == last, atJ: f j == last with
                | True, True => Eq.trans (DecEq.sound (f i) last atI) (Eq.sym (DecEq.sound (f j) last atJ))
                | True, False => Void.exfalso (missed j jLast (Eq.sym same))
                | False, True => Void.exfalso (missed i (omega [ij, jLast]) same)
                | False, False => same
            Witness i (Witness j (Both ij (Both (omega [jLast]) agree)))))

-- A step from the map that stays on it lands on the map.
-- On the map, if there is a position.
def onMapIfAny (lab: Lab): Option Position → Bool
  | None => True
  | Some position => onMap lab position

theorem aheadOnMapIfAny (lab: Lab) (guard: Guard) (inside: onMap lab guard.position = True): onMapIfAny lab (lab.ahead guard) = True := cases

theorem aheadOnMap (lab: Lab) (guard: Guard) (inside: onMap lab guard.position = True) (position: Position) (ahead: lab.ahead guard = Some position):
    onMap lab position = True :=
  rewrite ahead at aheadOnMapIfAny lab guard inside

theorem stepOnMap (lab: Lab) (guard: Guard) (inside: onMap lab guard.position = True) (next: Guard) (stepped: lab.step guard = Some next):
    onMap lab next.position = True :=
  match ahead: lab.ahead guard with
    | None => Void.exfalso (Option.noneNotSome next stepped)
    | Some position =>
      match blocked: lab.obstructions.contains position with
        | True => rewrite <- Option.someInjective _ next stepped in inside
        | False => rewrite <- Option.someInjective _ next stepped in aheadOnMap lab guard inside position ahead

-- She stays on the map until she leaves it.
theorem afterOnMap (lab: Lab) (inside: onMap lab lab.start = True): (steps: Nat) → (guard: Guard) → after lab steps = Some guard → onMap lab guard.position = True
  | Zero, guard, reached => rewrite <- Option.someInjective lab.startGuard guard reached in inside
  | Succ steps, guard, reached =>
    let reachedStep: (after lab steps).flatMap lab.step = Some guard := rewrite <- walkSucc lab steps (Some lab.startGuard) in reached
    match before: after lab steps with
      | None => Void.exfalso (Option.noneNotSome guard reachedStep)
      | Some earlier => stepOnMap lab earlier (afterOnMap lab inside steps earlier before) guard reachedStep

-- Each state on the map as a number below `stateCount`.
def directionIndex: Direction → Nat
  | Up => 0
  | Right => 1
  | Down => 2
  | Left => 3

def stateCode (lab: Lab) (guard: Guard): Nat :=
  (guard.position.row * lab.width + guard.position.column) * 4 + directionIndex guard.facing

theorem directionIndexSmall (direction: Direction): directionIndex direction < 4 := cases

theorem stateCodeSmall (lab: Lab) (guard: Guard) (inside: onMap lab guard.position = True): stateCode lab guard < lab.stateCount :=
  let rowFits := Nat.nextMultipleLe guard.position.row lab.height lab.width (omega [inside])
  omega [directionIndexSmall guard.facing, rowFits, inside]

def directionOfIndex: Nat → Direction
  | 0 => Up
  | 1 => Right
  | 2 => Down
  | _ => Left

theorem directionOfIndexOf (direction: Direction): directionOfIndex (directionIndex direction) = direction := cases

theorem directionIndexInjective (one: Direction) (other: Direction) (same: directionIndex one = directionIndex other): one = other :=
  calc one
    _ = directionOfIndex (directionIndex one) := Eq.sym (directionOfIndexOf one)
    _ = directionOfIndex (directionIndex other) := rewrite same in rfl
    _ = other := directionOfIndexOf other

-- Guards with the same row, column and facing are the same.
theorem guardExt: (one: Guard) → (other: Guard) → one.position.row = other.position.row → one.position.column = other.position.column →
    one.facing = other.facing → one = other
  | { position = { row, column }, facing }, { position = { row = otherRow, column = otherColumn }, facing = otherFacing }, rows, columns, facings =>
    rewrite rows, columns, facings in rfl

-- A cell's row: `row * width + column` with `column < width` determines
-- `row`.
theorem rowOfCell (width: Nat) (positive: width ≠ 0) (row: Nat) (column: Nat) (small: column < width): (row * width + column) / width = row :=
  rewrite (omega: row * width + column = column + row * width), Nat.divAddMul column row width [ok := positive], Nat.divSmall column width [ok := positive] small in rfl

-- Different states on the map have different numbers.
theorem stateCodeInjective (lab: Lab) (one: Guard) (other: Guard) (oneInside: onMap lab one.position = True) (otherInside: onMap lab other.position = True)
    (same: stateCode lab one = stateCode lab other): one = other :=
  let indexes: directionIndex one.facing = directionIndex other.facing :=
    omega [same, directionIndexSmall one.facing, directionIndexSmall other.facing]
  let cells: one.position.row * lab.width + one.position.column = other.position.row * lab.width + other.position.column :=
    omega [same, directionIndexSmall one.facing, directionIndexSmall other.facing]
  let positive: lab.width ≠ 0 := omega [oneInside]
  let rows: one.position.row = other.position.row :=
    calc one.position.row
      _ = (one.position.row * lab.width + one.position.column) / lab.width := Eq.sym (rowOfCell lab.width positive one.position.row one.position.column (omega [oneInside]))
      _ = (other.position.row * lab.width + other.position.column) / lab.width := rewrite cells in rfl
      _ = other.position.row := rowOfCell lab.width positive other.position.row other.position.column (omega [otherInside])
  let columns: one.position.column = other.position.column := omega [rewrite rows at cells]
  guardExt one other rows columns (directionIndexInjective one.facing other.facing indexes)

-- After a repeat, every step is one taken before: by induction on a bound
-- for the step count.
theorem repeatFrom (lab: Lab) (first: Nat) (second: Nat) (earlier: first < second) (same: after lab first = after lab second)
    (still: Not (after lab second = None)): (bound: Nat) → (steps: Nat) → steps < bound → Not (after lab steps = None)
  | Zero, steps, small, gone => omega
  | Succ bound, steps, small, gone =>
    match early: Nat.leq steps second with
      | True => walkEarlier lab (Some lab.startGuard) steps second still early gone
      | False =>
        let back := first + (steps - second)
        let shifted: after lab steps = after lab back :=
          calc after lab steps
            _ = walk lab (Some lab.startGuard) (second + (steps - second)) := rewrite (omega: second + (steps - second) = steps) in rfl
            _ = walk lab (after lab second) (steps - second) := walkAdd lab second (Some lab.startGuard) (steps - second)
            _ = walk lab (after lab first) (steps - second) := rewrite same in rfl
            _ = after lab back := Eq.sym (walkAdd lab first (Some lab.startGuard) (steps - second))
        repeatFrom lab first second earlier same still bound back omega (rewrite shifted at gone)

-- The same state at two step counts, still on the map at the later: she
-- loops.
theorem repeatLoops (lab: Lab) (first: Nat) (second: Nat) (earlier: first < second) (same: after lab first = after lab second)
    (still: Not (after lab second = None)): Loops lab :=
  steps => repeatFrom lab first second earlier same still (Succ steps) steps (Nat.leRefl (Succ steps))

-- The state's number, or 0 once she has left.
def codeOf (lab: Lab): Option Guard → Nat
  | None => 0
  | Some guard => stateCode lab guard

-- The budget is enough: still on the map after `stateCount` steps, she
-- loops.
theorem budgetEnough (lab: Lab) (inside: onMap lab lab.start = True) (still: Not (after lab lab.stateCount = None)): Loops lab :=
  let small: (steps: Nat) → steps ≤ lab.stateCount → codeOf lab (after lab steps) < lab.stateCount :=
    steps le =>
      match reached: after lab steps with
        | None => Void.exfalso (walkEarlier lab (Some lab.startGuard) steps lab.stateCount still le reached)
        | Some guard => stateCodeSmall lab guard (afterOnMap lab inside steps guard reached)
  Exists.elim (pigeonhole lab.stateCount (steps => codeOf lab (after lab steps)) small) (first rest =>
    Exists.elim rest (second both =>
      let earlier := And.left both
      let inBudget := And.left (And.right both)
      let codes := And.right (And.right both)
      let secondStill := walkEarlier lab (Some lab.startGuard) second lab.stateCount still inBudget
      let firstStill := walkEarlier lab (Some lab.startGuard) first lab.stateCount still (omega [earlier, inBudget])
      let same: after lab first = after lab second :=
        match atFirst: after lab first, atSecond: after lab second with
          | Some one, Some other =>
            Eq.cong Some
              (stateCodeInjective lab one other (afterOnMap lab inside first one atFirst) (afterOnMap lab inside second other atSecond) codes)
          | None, _ => Void.exfalso (firstStill rfl)
          | Some one, None => Void.exfalso (secondStill rfl)
      repeatLoops lab first second earlier same secondStill))
