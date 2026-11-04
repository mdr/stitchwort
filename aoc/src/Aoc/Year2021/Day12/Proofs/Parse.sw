--| The parser keeps the promise the answers' theorems need: no
--| passage of a successful parse joins two big caves.
-- (D2108)

namespace Aoc.Year2021.Day12.Proofs
import Aoc.Year2021.Day12 (..)
import Aoc.Year2021.Day12.Spec (NoBigNeighbours, connected)
import Std (Bool, DecEq, Eq, Fail, List, Option, Result, Void)

--| `checkPassages` gives the passages back, and only if none joins two big
--| caves...
theorem checkPassagesOk (passages: List (Text, Text)) (result: List (Text, Text)) (h: Fail.toResult (() => checkPassages passages) = Ok result):
    result = passages ∧ passages.all (passage => not (joinsBig passage)) = True :=
  match e: firstBigPair passages with
    | Some (index, (from, to)) => Void.exfalso (Result.errNotOk _ result h)
    | None => Both (Eq.sym (Result.okInjective _ result h)) (List.findNoneAll passages joinsBig (List.findWithIndexFromNone joinsBig 0 passages e))

--| ...whatever reads them.
theorem parsedChecked (read: () → {Fail} List (Text, Text)) (passages: List (Text, Text))
    (parsed: Fail.toResult (() => checkPassages (read ())) = Ok passages): passages.all (passage => not (joinsBig passage)) = True :=
  let split := rewrite Fail.toResultThen read checkPassages at parsed
  Result.flatMapEqOk (Fail.toResult read) (x => Fail.toResult (() => checkPassages x)) passages split
    (readPassages _ checked =>
      let (Both same none) := checkPassagesOk readPassages passages checked
      rewrite same in none)

--| Of a passage that doesn't join two big caves, if one end is big the
--| other isn't.
theorem otherSmall (from: Text) (to: Text) (fine: not (isBig from && isBig to) = True): isBig from = True → isBig to = False :=
  cases

theorem otherSmallBack (from: Text) (to: Text) (fine: not (isBig from && isBig to) = True): isBig to = True → isBig from = False :=
  cases

--| If `parsePassages` reads `input` as `passages`, no two big caves are
--| connected.
theorem parseNoBigNeighbours (input: Text) (passages: List (Text, Text)) (parsed: Fail.toResult (() => parsePassages input) = Ok passages):
    NoBigNeighbours passages :=
  let none := List.allToAll _ passages (parsedChecked _ passages parsed)
  a b joined bigA =>
    List.anyTrueElim passages (((from, to)) => (from == a && to == b) || (from == b && to == a)) _ joined (edge member joins =>
      match edge with
        | (from, to) =>
          let fine := List.allMem (passage => not (joinsBig passage) = True) (from, to) passages none member
          Bool.orElim (from == a && to == b) (from == b && to == a) _ joins
            (forward =>
              rewrite <- DecEq.sound to b (Bool.andRight _ _ forward) in
                otherSmall from to fine (rewrite DecEq.sound from a (Bool.andLeft _ _ forward) in bigA))
            (backward =>
              rewrite <- DecEq.sound from b (Bool.andLeft _ _ backward) in
                otherSmallBack from to fine (rewrite DecEq.sound to a (Bool.andRight _ _ backward) in bigA)))
