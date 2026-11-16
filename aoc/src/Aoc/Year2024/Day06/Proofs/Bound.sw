--| The step budget is enough: a guard who starts on the map and is still on
--| it after `stateCount` steps loops forever (`budgetEnough`).
--
-- There are only `stateCount` states on the map, so two of the first
-- `stateCount + 1` are the same (`Nat.pigeonhole`), and from then on the walk
-- repeats (`Nat.iterateRepeatNeverNone`).

namespace Aoc.Year2024.Day06.Proofs
import Aoc.Year2024.Day06 (..)
import Aoc.Common (Direction, Position)
import Aoc.Year2024.Day06.Spec (..)
import Std (And, Bool, DecEq, Eq, Exists, Nat, Not, Option, Void)

theorem walkIterate ∀ (lab: Lab) (steps: Nat) (guard: Option Guard):
    walk lab guard steps = Nat.iterate steps (state => state.flatMap lab.step) guard :=
  match steps with
    | Zero => byComputing
    | Succ steps => walkIterate lab steps (guard.flatMap lab.step)

--| Once off the map, she stays off.
theorem walkNone ∀ (lab: Lab) (steps: Nat): walk lab None steps = None := match steps with
  | Zero => byComputing
  | Succ steps => walkNone lab steps

theorem walkSucc ∀ (lab: Lab) (steps: Nat) (guard: Option Guard):
    walk lab guard (Succ steps) = (walk lab guard steps).flatMap lab.step :=
  match steps with
    | Zero => byComputing
    | Succ steps => walkSucc lab steps (guard.flatMap lab.step)

theorem walkAdd ∀ (lab: Lab) (first: Nat) (guard: Option Guard) (second: Nat):
    walk lab guard (first + second) = walk lab (walk lab guard first) second :=
  match first with
    | Zero => byComputing
    | Succ first => walkAdd lab first (guard.flatMap lab.step) second

--| Gone after `steps`, she is gone after any more.
theorem walkLater ∀ (lab: Lab) (guard: Option Guard) (steps later: Nat)
    (gone: walk lab guard steps = None)
    (le: steps ≤ later):
    walk lab guard later = None :=
  rewrite walkIterate lab later guard then
    Nat.iterateFixedLater
      (state => Option.flatMap state lab.step)
      guard
      None
      byComputing
      steps
      later
      (rewrite walkIterate lab steps guard at gone)
      le

--| Still on the map after `later` steps, she was after any fewer.
theorem walkEarlier ∀ (lab: Lab) (guard: Option Guard) (steps later: Nat)
    (still: walk lab guard later ≠ None)
    (le: steps ≤ later):
    walk lab guard steps ≠ None :=
  gone => still (walkLater lab guard steps later gone le)

--| On the map, if there is a position.
def onMapIfAny (lab: Lab): Option Position → Bool
  | None => True
  | Some position => onMap lab position

theorem aheadOnMapIfAny ∀ (lab: Lab) (guard: Guard)
    (inside: onMap lab guard.position = True):
    onMapIfAny lab (lab.ahead guard) = True :=
  cases

theorem aheadOnMap ∀ (lab: Lab) (guard: Guard)
    (inside: onMap lab guard.position = True) (position: Position)
    (ahead: lab.ahead guard = Some position):
    onMap lab position = True :=
  rewrite ahead at aheadOnMapIfAny lab guard inside

theorem stepOnMap ∀ (lab: Lab) (guard: Guard)
    (inside: onMap lab guard.position = True) (next: Guard)
    (stepped: lab.step guard = Some next):
    onMap lab next.position = True :=
  match ahead: lab.ahead guard with
    | Some position =>
      match blocked: lab.obstructions.contains position with
        | True => rewrite <- Option.someInjective stepped then inside
        | False => rewrite <- Option.someInjective stepped then aheadOnMap lab guard inside position ahead

--| She stays on the map until she leaves it.
theorem afterOnMap ∀ (lab: Lab)
    (inside: onMap lab lab.start = True)
    (steps: Nat) (guard: Guard)
    (reached: after lab steps = Some guard):
    onMap lab guard.position = True :=
  match steps with
    | Zero => rewrite <- Option.someInjective reached then inside
    | Succ steps =>
      let reachedStep: (after lab steps).flatMap lab.step = Some guard :=
        rewrite <- walkSucc lab steps (Some lab.startGuard) then reached
      match before: after lab steps with
        | Some earlier => stepOnMap lab earlier (afterOnMap lab inside steps earlier before) guard reachedStep

--| A direction as 0 to 3, so `stateCode` keeps a state below `stateCount`.
def directionIndex: Direction → Nat
  | Up => 0
  | Right => 1
  | Down => 2
  | Left => 3

def stateCode (lab: Lab) (guard: Guard): Nat :=
  (guard.position.row * lab.width + guard.position.column) * 4 + directionIndex guard.facing

theorem directionIndexSmall ∀ (direction: Direction): directionIndex direction < 4 := cases

theorem stateCodeSmall ∀ (lab: Lab) (guard: Guard)
    (inside: onMap lab guard.position = True):
    stateCode lab guard < lab.stateCount :=
  let rowFits := Nat.nextMultipleLe guard.position.row lab.height lab.width (arithmetic [inside])
  arithmetic [directionIndexSmall guard.facing, rowFits, inside]

def directionOfIndex: Nat → Direction
  | 0 => Up
  | 1 => Right
  | 2 => Down
  | _ => Left

theorem directionOfIndexOf ∀ (direction: Direction): directionOfIndex (directionIndex direction) = direction := cases

theorem directionIndexInjective ∀ (one other: Direction)
    (same: directionIndex one = directionIndex other):
    one = other :=
  calc one
    _ = directionOfIndex (directionIndex one) := (directionOfIndexOf one).flipped
    _ = directionOfIndex (directionIndex other) := rewrite same
    _ = other := directionOfIndexOf other

theorem guardExt ∀ (one other: Guard)
    (rows: one.position.row = other.position.row)
    (columns: one.position.column = other.position.column)
    (facings: one.facing = other.facing):
    one = other :=
  match one, other with
    | { position = { row, column }, facing }, {
        position = { row = otherRow, column = otherColumn },
        facing = otherFacing
      } => rewrite rows, columns, facings

--| Different states on the map have different numbers.
theorem stateCodeInjective ∀ (lab: Lab) (one other: Guard)
    (oneInside: onMap lab one.position = True)
    (otherInside: onMap lab other.position = True)
    (same: stateCode lab one = stateCode lab other):
    one = other :=
  let indexes: directionIndex one.facing = directionIndex other.facing :=
    arithmetic [same, directionIndexSmall one.facing, directionIndexSmall other.facing]
  let cells: one.position.row * lab.width + one.position.column
    = other.position.row * lab.width + other.position.column :=
    arithmetic [same, directionIndexSmall one.facing, directionIndexSmall other.facing]
  let positive: lab.width ≠ 0 := arithmetic [oneInside]
  let rows: one.position.row = other.position.row := calc one.position.row
    _ = (one.position.row * lab.width + one.position.column) / lab.width :=
      Eq.flipped (Nat.mulAddDivSmall one.position.row lab.width one.position.column (arithmetic [oneInside]))
    _ = (other.position.row * lab.width + other.position.column) / lab.width := rewrite cells
    _ = other.position.row :=
      Nat.mulAddDivSmall other.position.row lab.width other.position.column (arithmetic [otherInside])
  let columns: one.position.column = other.position.column := arithmetic [rewrite rows at cells]
  guardExt one other rows columns (directionIndexInjective one.facing other.facing indexes)

--| The same state at two step counts, still on the map at the later: she
--| loops.
theorem repeatLoops ∀ (lab: Lab) (first second: Nat)
    (earlier: first < second)
    (same: after lab first = after lab second)
    (still: after lab second ≠ None):
    Loops lab :=
  steps gone =>
    Nat.iterateRepeatNeverNone lab.step
      (Some lab.startGuard)
      first
      second
      earlier
      (calc Nat.iterate first (state => state.flatMap lab.step) (Some lab.startGuard)
        _ = after lab first := Eq.flipped (walkIterate lab first (Some lab.startGuard))
        _ = after lab second := same
        _ = Nat.iterate second (state => state.flatMap lab.step) (Some lab.startGuard) :=
          walkIterate lab second (Some lab.startGuard))
      (stopped => still (Eq.trans (walkIterate lab second (Some lab.startGuard)) stopped))
      steps
      (Eq.trans (Eq.flipped (walkIterate lab steps (Some lab.startGuard))) gone)

--| The state's number, or 0 once she has left.
def codeOf (lab: Lab): Option Guard → Nat
  | None => 0
  | Some guard => stateCode lab guard

--| The budget is enough: still on the map after `stateCount` steps, she
--| loops.
theorem budgetEnough ∀ (lab: Lab)
    (inside: onMap lab lab.start = True)
    (still: after lab lab.stateCount ≠ None):
    Loops lab :=
  let small: ∀ (steps: Nat) => steps ≤ lab.stateCount → codeOf lab (after lab steps) < lab.stateCount := steps le =>
    match reached: after lab steps with
      | None => Void.impossible (walkEarlier lab (Some lab.startGuard) steps lab.stateCount still le reached)
      | Some guard => stateCodeSmall lab guard (afterOnMap lab inside steps guard reached)
  Exists.elim (Nat.pigeonhole lab.stateCount (steps => codeOf lab (after lab steps)) small) (first rest =>
    Exists.elim rest (second both =>
      let earlier := both.left
      let inBudget := both.right.left
      let codes := both.right.right
      let secondStill := walkEarlier lab (Some lab.startGuard) second lab.stateCount still inBudget
      let firstStill :=
        walkEarlier lab (Some lab.startGuard) first lab.stateCount still (arithmetic [earlier, inBudget])
      let same: after lab first = after lab second := match atFirst: after lab first, atSecond: after lab second with
        | Some one, Some other =>
          Eq.cong Some
            (stateCodeInjective lab one other
              (afterOnMap lab inside first one atFirst)
              (afterOnMap lab inside second other atSecond)
              codes)
        | None, _ => (firstStill byComputing).impossible
        | Some one, None => (secondStill byComputing).impossible
      repeatLoops lab first second earlier same secondStill))
