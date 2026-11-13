--| The parser keeps the promise the answers' theorems need: no
--| passage of a successful parse joins two big caves.
-- (D2108)

namespace Aoc.Year2021.Day12.Proofs
import Aoc.Year2021.Day12 (..)
import Aoc.Year2021.Day12.Spec (..)
import Std (Bool, DecEq, Eq, Fail, List, Option, Result, Void)

--| `checkPassages` gives the passages back, and only if none joins two big
--| caves...
theorem checkPassagesOk (passages: List Passage) (result: List Passage) (h: Fail.toResult (() => checkPassages passages) = Ok result):
    result = passages ∧ passages.all (passage => not passage.joinsBig) = True := match e: firstBigPair passages with
      | Some (index, passage) => Void.exfalso (Result.errNotOk h)
      | None => Both (Eq.sym (Result.okInjective h)) (List.findNoneAll passages Passage.joinsBig (List.findWithIndexFromNone Passage.joinsBig 0 passages e))

--| ...whatever reads them.
theorem parsedChecked (read: () → {Fail} List Passage) (passages: List Passage)
    (parsed: Fail.toResult (() => checkPassages (read ())) = Ok passages): passages.all (passage => not passage.joinsBig) = True :=
  let split := rewrite Fail.toResultThen read checkPassages at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkPassages x)) passages split
    (readPassages _ checked =>
      let (Both same none) := checkPassagesOk readPassages passages checked
      rewrite same in none)

--| Of a passage that doesn't join two big caves, if one end is big the
--| other isn't.
theorem otherSmall (from: Cave) (to: Cave) (fine: not (from.isBig && to.isBig) = True): from.isBig = True → to.isBig = False :=
  cases

theorem otherSmallBack (from: Cave) (to: Cave) (fine: not (from.isBig && to.isBig) = True): to.isBig = True → from.isBig = False :=
  cases

--| If `parsePassages` reads `input` as `passages`, no two big caves are
--| connected.
theorem parseNoBigNeighbours (input: Text) (passages: List Passage) (parsed: Fail.toResult (() => parsePassages input) = Ok passages):
    NoBigNeighbours passages :=
  let checked := parsedChecked _ passages parsed
  a b joined bigA =>
    let Witness edge (Both member joins) := joined
    match edge with
      | { from, to } =>
        let fine := checked.read { from, to } member
        match joins with
          | Inl (Both fromA toB) =>
            rewrite <- toB.read in otherSmall from to fine (rewrite fromA.read in bigA)
          | Inr (Both fromB toA) =>
            rewrite <- fromB.read in otherSmallBack from to fine (rewrite toA.read in bigA)
