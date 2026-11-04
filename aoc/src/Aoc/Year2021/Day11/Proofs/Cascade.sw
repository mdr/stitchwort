--| The cascade reaches exactly the spec's flashers. The rounds from nobody
--| are the Kleene iteration of "above 9 flashes": each round's flashers
--| include the last round's (`grows`), and are inside every closed set
--| (`belowClosed`). Once a round adds nobody, no later round does
--| (`staysStable`) and the flashers are closed (`closedOfStable`). A round
--| that adds someone adds an octopus on the grid, so after as many rounds
--| as there are octopuses one adds nobody (`stableAtSize`). The program
--| stops at the first round that adds nobody, or after one round more than
--| there are octopuses (`cascadeAfter`), so it stops at a stable round.

namespace Aoc.Year2021.Day11.Proofs
import Aoc.Year2021.Day11 (..)
import Aoc.Year2021.Day11.Spec (..)
import Aoc.Common (Position, cellAt, cells, mapCells)
import Std (Bool, DecEq, Eq, Exists, List, Nat, Option, Void)

--| The flashers after k rounds, from nobody.
def flashedAfter (levels: List (List Nat)): Nat → List (List Bool)
  | Zero => mapCells levels (_ _ => False)
  | Succ k => flashRound levels (flashedAfter levels k)

--| Only octopuses on the grid flash in any round.
theorem onGridAfter (levels: List (List Nat)): (k: Nat) → OnGrid levels (flashedAt (flashedAfter levels k))
  | Zero, q, flashes => onGridMapCells levels (_ _ => False) q flashes
  | Succ k, q, flashes => onGridMapCells levels (at level => 9 < energy (flashedAfter levels k) at level) q flashes

--| Before the first round nobody has flashed.
theorem noneAtStart (levels: List (List Nat)): (q: Position) → flashedAt (flashedAfter levels 0) q = False
  | q =>
    Eq.trans (flashedAtMapCells levels (_ _ => False) q)
      (match cellAt levels q with
        | None => rfl
        | Some level => rfl)

--| A spec energy grows with the flashers.
theorem energyMono (levels: List (List Nat)) (f: Position → Bool) (g: Position → Bool) (fg: (q: Position) → f q = True → g q = True)
    (at: Position) (level: Nat): energyIn levels f at level ≤ energyIn levels g at level :=
  let more := neighboursMono levels f g fg at
  omega

--| Each round's flashers include the last round's.
theorem grows (levels: List (List Nat)): (k: Nat) → (q: Position) →
    flashedAt (flashedAfter levels k) q = True → flashedAt (flashedAfter levels (Succ k)) q = True
  | Zero, q, flashes => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (noneAtStart levels q)) flashes))
  | Succ k, q, flashes =>
    Exists.elim (roundElim levels (flashedAfter levels k) (onGridAfter levels k) q flashes) (level both =>
      let more := energyMono levels (flashedAt (flashedAfter levels k)) (flashedAt (flashedAfter levels (Succ k))) (grows levels k) q level
      let above := And.right both
      roundIntro levels (flashedAfter levels (Succ k)) (onGridAfter levels (Succ k)) q level (And.left both) (omega))

--| Every round's flashers are inside every closed set.
theorem belowClosed (levels: List (List Nat)) (other: Position → Bool) (closed: Closed levels other): (k: Nat) → (q: Position) →
    flashedAt (flashedAfter levels k) q = True → other q = True
  | Zero, q, flashes => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (noneAtStart levels q)) flashes))
  | Succ k, q, flashes =>
    Exists.elim (roundElim levels (flashedAfter levels k) (onGridAfter levels k) q flashes) (level both =>
      let more := energyMono levels (flashedAt (flashedAfter levels k)) other (belowClosed levels other closed k) q level
      let above := And.right both
      closed q level (And.left both) (omega))

--| Round k + 1 adds nobody.
def Stable (levels: List (List Nat)) (k: Nat): Prop :=
  (q: Position) → flashedAt (flashedAfter levels (Succ k)) q = True → flashedAt (flashedAfter levels k) q = True

--| A round after one that adds nobody adds nobody.
theorem staysStable (levels: List (List Nat)) (k: Nat) (stable: Stable levels k): Stable levels (Succ k)
  | q, flashes =>
    Exists.elim (roundElim levels (flashedAfter levels (Succ k)) (onGridAfter levels (Succ k)) q flashes) (level both =>
      let more := energyMono levels (flashedAt (flashedAfter levels (Succ k))) (flashedAt (flashedAfter levels k)) stable q level
      let above := And.right both
      roundIntro levels (flashedAfter levels k) (onGridAfter levels k) q level (And.left both) (omega))

--| The flashers of a round that the next adds nobody to are closed.
theorem closedOfStable (levels: List (List Nat)) (k: Nat) (stable: Stable levels k): Closed levels (flashedAt (flashedAfter levels k))
  | q, level, member, above => stable q (roundIntro levels (flashedAfter levels k) (onGridAfter levels k) q level member above)

--| How many octopuses have flashed after k rounds.
def flashedCount (levels: List (List Nat)) (k: Nat): Nat := (positions levels).count (flashedAt (flashedAfter levels k))

--| A round that adds somebody adds to the count.
theorem stableOfCount (levels: List (List Nat)) (k: Nat) (same: flashedCount levels (Succ k) ≤ flashedCount levels k): Stable levels k
  | q, flashes =>
    match e: flashedAt (flashedAfter levels k) q with
      | True => rfl
      | False =>
        let more := List.countLtMem (positions levels) (flashedAt (flashedAfter levels k)) (flashedAt (flashedAfter levels (Succ k)))
          (x member => grows levels k x) q (onGridAfter levels (Succ k) q flashes) flashes e
        Void.exfalso (omega)

--| After k rounds, k have flashed, or a round has added nobody.
theorem stableOrCount (levels: List (List Nat)): (k: Nat) → (Stable levels k) ∨ (k + 1 ≤ flashedCount levels (Succ k))
  | Zero =>
    match Nat.decLessEq (flashedCount levels 1) (flashedCount levels 0) with
      | Yes same => Inl (stableOfCount levels 0 same)
      | No more => Inr (omega)
  | Succ k =>
    match stableOrCount levels k with
      | Inl stable => Inl (staysStable levels k stable)
      | Inr enough =>
        match Nat.decLessEq (flashedCount levels (Succ (Succ k))) (flashedCount levels (Succ k)) with
          | Yes same => Inl (stableOfCount levels (Succ k) same)
          | No more => Inr (omega)

--| So the round after as many rounds as there are octopuses adds nobody...
theorem stableAtSize (levels: List (List Nat)): Stable levels (positions levels).length :=
  match stableOrCount levels (positions levels).length with
    | Inl stable => stable
    | Inr tooMany =>
      let bound := List.countLeLength (positions levels) (flashedAt (flashedAfter levels (Succ (positions levels).length)))
      Void.exfalso (omega)

--| ...nor any later one.
theorem stableAbove (levels: List (List Nat)) (n: Nat) (stable: Stable levels n): (k: Nat) → n ≤ k → Stable levels k
  | Zero, below, q, flashes => (rewrite (omega: n = 0) at stable in stable) q flashes
  | Succ k, below, q, flashes =>
    match Nat.decLessEq n k with
      | Yes late => staysStable levels k (stableAbove levels n stable k late) q flashes
      | No early => (rewrite (omega: n = Succ k) at stable in stable) q flashes

--| One step of `cascade`.
theorem cascadeStep (levels: List (List Nat)) (flashed: List (List Bool)) (m: Nat):
    cascade levels flashed (Succ m) = (if flashRound levels flashed == flashed then flashed else cascade levels (flashRound levels flashed) m) :=
  rfl

--| `cascade` from round k with `m` rounds to go stops at a round that adds
--| nobody, or after all `m`.
theorem cascadeAfter (levels: List (List Nat)): (m: Nat) → (k: Nat) →
    ∃ (j: Nat) => cascade levels (flashedAfter levels k) m = flashedAfter levels j ∧ ((Stable levels j) ∨ (j = k + m))
  | Zero, k => Witness k (Both rfl (Inr (omega)))
  | Succ m, k =>
    rewrite cascadeStep levels (flashedAfter levels k) m in
      match e: flashRound levels (flashedAfter levels k) == flashedAfter levels k with
        | True =>
          let same: flashedAfter levels (Succ k) = flashedAfter levels k := DecEq.sound _ _ e
          Witness k (Both rfl (Inl (q flashes => rewrite same at flashes in flashes)))
        | False =>
          Exists.elim (cascadeAfter levels m (Succ k)) (j both =>
            let (Both found stops) := both
            Witness j (Both found (match stops with
              | Inl stable => Inl stable
              | Inr after => Inr (omega))))

--| The program's flashers are the flashers of a round that adds nobody.
theorem flashersStable (levels: List (List Nat)): ∃ (j: Nat) => flashers levels = flashedAfter levels j ∧ Stable levels j :=
  Exists.elim (cascadeAfter levels (cells levels).length 0) (j both =>
    let (Both found stops) := both
    Witness j (Both found (match stops with
      | Inl stable => stable
      | Inr after =>
        let sameLength: (positions levels).length = (cells levels).length := List.lengthMap (cells levels) Pair.fst
        stableAbove levels (positions levels).length (stableAtSize levels) j (omega))))

--| The program's flashers are the spec's: the least closed set.
theorem flashersCorrect (levels: List (List Nat)): Flashers levels (flashedAt (flashers levels)) :=
  Exists.elim (flashersStable levels) (j both =>
    let (Both found stable) := both
    rewrite found in Both (closedOfStable levels j stable) (other closed q flashes => belowClosed levels other closed j q flashes))
