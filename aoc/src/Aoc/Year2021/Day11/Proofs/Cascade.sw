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
import Aoc.Common (Position)
import Std (Bool, DecEq, Eq, Exists, List, Nat, Option, Void)

--| The flashers after k rounds, from nobody.
def flashedAfter (cavern: Cavern): Nat → Flashed
  | Zero => cavern.noFlashers
  | Succ k => cavern.flashRound (flashedAfter cavern k)

--| Only octopuses on the grid flash in any round.
theorem onGridAfter (cavern: Cavern) (k: Nat): OnGrid cavern ((flashedAfter cavern k).has) := match k with
  | Zero => q flashes => onGridFlash cavern (_ _ => False) q flashes
  | Succ k => q flashes => onGridFlash cavern (at level => 9 < energyWith (flashedAfter cavern k).lookup at level) q flashes

--| Before the first round nobody has flashed.
theorem noneAtStart (cavern: Cavern) (q: Position): (flashedAfter cavern 0).has q = False :=
  Eq.trans (hasFlash cavern (_ _ => False) q)
    (match cavern.grid.at q with
      | None => rfl
      | Some level => rfl)

--| A spec energy grows with the flashers.
theorem energyMono (cavern: Cavern) (f: Position → Bool) (g: Position → Bool) (fg: ∀ (q: Position) => f q = True → g q = True)
    (at: Position) (level: Nat): energyIn cavern f at level ≤ energyIn cavern g at level :=
  let more := neighboursMono cavern f g fg at
  omega

--| Each round's flashers include the last round's.
theorem grows (cavern: Cavern) (k: Nat) (q: Position)
    (flashes: (flashedAfter cavern k).has q = True): (flashedAfter cavern (Succ k)).has q = True := match k with
      | Zero => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (noneAtStart cavern q)) flashes))
      | Succ k =>
        Exists.elim (roundElim cavern (flashedAfter cavern k) (onGridAfter cavern k) q flashes) (level both =>
          let more := energyMono cavern ((flashedAfter cavern k).has) ((flashedAfter cavern (Succ k)).has) (grows cavern k) q level
          let above := And.right both
          roundIntro cavern (flashedAfter cavern (Succ k)) (onGridAfter cavern (Succ k)) q level (And.left both) (omega))

--| Every round's flashers are inside every closed set.
theorem belowClosed (cavern: Cavern) (other: Position → Bool) (closed: Closed cavern other) (k: Nat) (q: Position)
    (flashes: (flashedAfter cavern k).has q = True): other q = True := match k with
      | Zero => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym (noneAtStart cavern q)) flashes))
      | Succ k =>
        Exists.elim (roundElim cavern (flashedAfter cavern k) (onGridAfter cavern k) q flashes) (level both =>
          let more := energyMono cavern ((flashedAfter cavern k).has) other (belowClosed cavern other closed k) q level
          let above := And.right both
          closed q level (And.left both) (omega))

--| Round k + 1 adds nobody.
def Stable (cavern: Cavern) (k: Nat): Prop :=
  ∀ (q: Position) => (flashedAfter cavern (Succ k)).has q = True → (flashedAfter cavern k).has q = True

--| A round after one that adds nobody adds nobody.
theorem staysStable (cavern: Cavern) (k: Nat) (stable: Stable cavern k): Stable cavern (Succ k)
  | q, flashes =>
    Exists.elim (roundElim cavern (flashedAfter cavern (Succ k)) (onGridAfter cavern (Succ k)) q flashes) (level both =>
      let more := energyMono cavern ((flashedAfter cavern (Succ k)).has) ((flashedAfter cavern k).has) stable q level
      let above := And.right both
      roundIntro cavern (flashedAfter cavern k) (onGridAfter cavern k) q level (And.left both) (omega))

--| The flashers of a round that the next adds nobody to are closed.
theorem closedOfStable (cavern: Cavern) (k: Nat) (stable: Stable cavern k): Closed cavern ((flashedAfter cavern k).has)
  | q, level, member, above => stable q (roundIntro cavern (flashedAfter cavern k) (onGridAfter cavern k) q level member above)

--| How many octopuses have flashed after k rounds.
def flashedCount (cavern: Cavern) (k: Nat): Nat := (positions cavern).count ((flashedAfter cavern k).has)

--| A round that adds somebody adds to the count.
theorem stableOfCount (cavern: Cavern) (k: Nat) (same: flashedCount cavern (Succ k) ≤ flashedCount cavern k): Stable cavern k
  | q, flashes =>
    match e: (flashedAfter cavern k).has q with
      | True => rfl
      | False =>
        let more := List.countLtMem (positions cavern) ((flashedAfter cavern k).has) ((flashedAfter cavern (Succ k)).has)
          (x member => grows cavern k x) q (onGridAfter cavern (Succ k) q flashes) flashes e
        Void.exfalso (omega)

--| After k rounds, k have flashed, or a round has added nobody.
theorem stableOrCount (cavern: Cavern) (k: Nat): (Stable cavern k) ∨ (k + 1 ≤ flashedCount cavern (Succ k)) :=
  match k with
    | Zero =>
      if same: flashedCount cavern 1 ≤ flashedCount cavern 0 then Inl (stableOfCount cavern 0 same)
      else Inr (omega)
    | Succ k =>
      match stableOrCount cavern k with
        | Inl stable => Inl (staysStable cavern k stable)
        | Inr enough =>
          if same: flashedCount cavern (Succ (Succ k)) ≤ flashedCount cavern (Succ k) then Inl (stableOfCount cavern (Succ k) same)
          else Inr (omega)

--| So the round after as many rounds as there are octopuses adds nobody...
theorem stableAtSize (cavern: Cavern): Stable cavern (positions cavern).length :=
  match stableOrCount cavern (positions cavern).length with
    | Inl stable => stable
    | Inr tooMany =>
      let bound := List.countLeLength (positions cavern) ((flashedAfter cavern (Succ (positions cavern).length)).has)
      Void.exfalso (omega)

--| ...nor any later one.
theorem stableAbove (cavern: Cavern) (n: Nat) (stable: Stable cavern n) (k: Nat) (below: n ≤ k): Stable cavern k :=
  match k with
    | Zero => q flashes => (rewrite (omega: n = 0) at stable in stable) q flashes
    | Succ k => q flashes =>
      if late: n ≤ k then staysStable cavern k (stableAbove cavern n stable k late) q flashes
      else (rewrite (omega: n = Succ k) at stable in stable) q flashes

--| One step of `cascade`.
theorem cascadeStep (cavern: Cavern) (flashed: Flashed) (m: Nat):
    cavern.cascade flashed (Succ m) = (if cavern.flashRound flashed == flashed then flashed else cavern.cascade (cavern.flashRound flashed) m) :=
  rfl

--| `cascade` from round k with `m` rounds to go stops at a round that adds
--| nobody, or after all `m`.
theorem cascadeAfter (cavern: Cavern) (m k: Nat):
    ∃ (j: Nat) => cavern.cascade (flashedAfter cavern k) m = flashedAfter cavern j ∧ ((Stable cavern j) ∨ (j = k + m)) :=
  match m with
    | Zero => Witness k (Both rfl (Inr (omega)))
    | Succ m =>
      rewrite cascadeStep cavern (flashedAfter cavern k) m in
        match e: cavern.flashRound (flashedAfter cavern k) == flashedAfter cavern k with
          | True =>
            let same: flashedAfter cavern (Succ k) = flashedAfter cavern k := e.read
            Witness k (Both rfl (Inl (q flashes => Eq.trans (Eq.sym (Eq.cong (round => round.has q) same)) flashes)))
          | False =>
            Exists.elim (cascadeAfter cavern m (Succ k)) (j both =>
              let (Both found stops) := both
              Witness j (Both found (match stops with
                | Inl stable => Inl stable
                | Inr after => Inr (omega))))

--| The program's flashers are the flashers of a round that adds nobody.
theorem flashersStable (cavern: Cavern): ∃ (j: Nat) => cavern.flashers = flashedAfter cavern j ∧ Stable cavern j :=
  Exists.elim (cascadeAfter cavern cavern.grid.cells.length 0) (j both =>
    let (Both found stops) := both
    Witness j (Both found (match stops with
      | Inl stable => stable
      | Inr after =>
        let sameLength: (positions cavern).length = cavern.grid.cells.length := List.lengthMap cavern.grid.cells Pair.fst
        stableAbove cavern (positions cavern).length (stableAtSize cavern) j (omega))))

--| The program's flashers are the spec's: the least closed set.
theorem flashersCorrect (cavern: Cavern): Flashers cavern (cavern.flashers.has) :=
  Exists.elim (flashersStable cavern) (j both =>
    let (Both found stable) := both
    rewrite found in Both (closedOfStable cavern j stable) (other closed q flashes => belowClosed cavern other closed j q flashes))
