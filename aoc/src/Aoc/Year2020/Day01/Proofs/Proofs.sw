--| Day 1 proved, for every list of entries: what the program finds are
--| entries summing to 2020, and it finds some whenever there are any. So its
--| answer is one of the puzzle's (Spec/), and the puzzle's when that is unique.

namespace Aoc.Year2020.Day01.Proofs
import Aoc.Year2020.Day01 (..)
import Aoc.Year2020.Day01.Spec (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Pair, Set, Void)

--| A pair still possible partway through `findPairAfter`: `a` was passed (it
--| is in `before`) and `b` is still to come, or both are still to come, `a`
--| first.
def PairAhead (before rest: List Nat) (a b: Nat): Prop := ((a ∈ before) ∧ (b ∈ rest)) ∨ ((a, b) ∈ rest.pairs)

--| One step on: a pair ahead of `x` (`x` still to come) is ahead after `x`
--| is passed, or has `x` second.
theorem pairAheadStep ∀ (before: List Nat) (x: Nat) (rest: List Nat) (a b: Nat)
    (ahead: PairAhead before [x, ..rest] a b):
    ((a ∈ before) ∧ (b = x)) ∨ (PairAhead [x, ..before] rest a b) :=
  match ahead with
    | Inl (Both aBefore bIn) =>
      match bIn with
        | Inl xIs => Inl (Both aBefore (Eq.sym xIs))
        | Inr bRest => Inr (Inl (Both (Inr aBefore) bRest))
    | Inr inPairs =>
      match (List.memPairsCons a b x rest).forward inPairs with
        | Inl (Both aIs bIn) => Inr (Inl (Both (Inl (Eq.sym aIs)) bIn))
        | Inr inRest => Inr (Inr inRest)

--| And back: a pair ahead after `x` is passed was ahead before it.
theorem pairAheadBack ∀ (before: List Nat) (x: Nat) (rest: List Nat) (a b: Nat)
    (ahead: PairAhead [x, ..before] rest a b):
    PairAhead before [x, ..rest] a b :=
  match ahead with
    | Inl (Both (Inl xIs) bRest) => Inr ((List.memPairsCons a b x rest).backward (Inl (Both (Eq.sym xIs) bRest)))
    | Inl (Both (Inr aBefore) bRest) => Inl (Both aBefore (Inr bRest))
    | Inr inRest => Inr ((List.memPairsCons a b x rest).backward (Inr inRest))

--| What `findPairAfter` finds is a pair ahead summing to the target, when
--| everything in `seen` was passed.
theorem findPairAfterSound ∀ (target: Nat) (seen: Set Nat) (before: List Nat)
    (passed: ∀ (y: Nat) => seen.contains y = True → y ∈ before)
    (rest: List Nat) (a b: Nat)
    (found: findPairAfter target seen rest = Some (a, b)):
    (PairAhead before rest a b) ∧ (a + b = target) :=
  match rest with
    | [x, ..rest] =>
      match c: (x <= target && Set.contains seen (target - x)) with
        | True =>
          let same := Option.someInjective found
          let aIs: target - x = a := Pair.mkInjectiveFst same
          let bIs: x = b := Pair.mkInjectiveSnd same
          let Both fits partner := c
          Both (Inl (Both (rewrite <- aIs in passed (target - x) partner) (Inl bIs))) omega
        | False =>
          let passedNow: ∀ (y: Nat) => Set.contains (Set.insert seen x) y = True → y ∈ [x, ..before] := y contained =>
            if h: y = x then Inl (Eq.sym h)
            else Inr (passed y (rewrite Set.containsInsertOther seen x y h at contained in contained))
          let after := findPairAfterSound target (Set.insert seen x) [x, ..before] passedNow rest a b found
          Both (pairAheadBack before x rest a b after.left) after.right

--| And it finds one if there is a pair ahead summing to the target, when
--| everything passed is in `seen`.
theorem findPairAfterComplete ∀ (target: Nat) (seen: Set Nat) (before: List Nat)
    (remembered: ∀ (y: Nat) => y ∈ before → seen.contains y = True)
    (rest: List Nat) (a b: Nat)
    (ahead: PairAhead before rest a b)
    (sum: a + b = target):
    findPairAfter target seen rest ≠ None :=
  match rest, ahead with
    | [], Inl (Both aIn bIn) => isNone => bIn
    | [], Inr inPairs => isNone => inPairs
    | [x, ..rest], ahead => isNone =>
      match c: (x <= target && Set.contains seen (target - x)) with
        | False =>
          match pairAheadStep before x rest a b ahead with
            | Inl (Both aBefore bIs) =>
              let fits: x <= target := omega
              let aIs: target - x = a := omega
              let partner: Set.contains seen (target - x) = True := rewrite aIs in remembered a aBefore
              let holds: (x <= target && Set.contains seen (target - x)) = True := Both fits partner
              Bool.trueNotFalse (Eq.trans (Eq.sym holds) c)
            | Inr aheadNow =>
              let rememberedNow: ∀ (y: Nat) => y ∈ [x, ..before] → Set.contains (Set.insert seen x) y = True :=
                y member =>
                  match member with
                    | Inl xIs => rewrite <- xIs in Set.containsInsert x seen
                    | Inr earlier => Set.containsInsertMono seen x y (remembered y earlier)
              findPairAfterComplete target (Set.insert seen x) [x, ..before] rememberedNow rest a b aheadNow sum isNone

--| What `findPair` finds are two entries, the earlier first, summing to the
--| target.
theorem findPairSound ∀ (target: Nat) (entries: List Nat) (a b: Nat)
    (found: findPair target entries = Some (a, b)):
    ((a, b) ∈ entries.pairs) ∧ (a + b = target) :=
  let nothingSeen: ∀ (y: Nat) => Set.contains Set.empty y = True → y ∈ [] := y contained => cases
  match findPairAfterSound target Set.empty [] nothingSeen entries a b found with
    | Both (Inl (Both aNowhere bIn)) sum => Void.exfalso aNowhere
    | Both (Inr inPairs) sum => Both inPairs sum

--| And it finds two whenever there are two.
theorem findPairComplete ∀ (target: Nat) (entries: List Nat) (a b: Nat)
    (inPairs: (a, b) ∈ entries.pairs)
    (sum: a + b = target):
    findPair target entries ≠ None :=
  findPairAfterComplete target Set.empty [] (y nowhere => Void.exfalso nowhere) entries a b (Inr inPairs) sum

--| When `findTriple` finds nothing, it finds nothing after the first entry,
--| nor a pair after it making up the rest.
theorem findTripleNoneCons ∀ (target x: Nat) (rest: List Nat)
    (none: findTriple target [x, ..rest] = None):
    (findTriple target rest = None) ∧ ((fits: x <= target) → findPair (target - x) rest = None) :=
  match c: x <= target with
    | True =>
      match pair: findPair (target - x) rest with
        | Some (p, q) => Void.exfalso (Option.someNotNone _ none)
        | None => Both none (fits => rfl)
    | False => Both none (fits => cases)

--| Three entries add up as a list's sum and product do.
theorem sum3 ∀ (a b c: Nat): [a, b, c].sum = a + b + c := ring

theorem product3 ∀ (a b c: Nat): [a, b, c].product = a * b * c := ring

--| What `findTriple` finds are three entries, in order, summing to the target.
theorem findTripleSound ∀ (target: Nat) (entries: List Nat) (a b c: Nat)
    (found: findTriple target entries = Some (a, b, c)):
    ([a, b, c] ∈ entries.combinations 3) ∧ (a + b + c = target) :=
  match entries with
    | [x, ..rest] =>
      let later: findTriple target rest = Some (a, b, c)
        → ([a, b, c] ∈ [x, ..rest].combinations 3) ∧ (a + b + c = target) :=
        laterFound =>
          let after := findTripleSound target rest a b c laterFound
          Both ((List.memCombinationsCons a [b, c] x rest 2).backward (Inr after.left)) after.right
      match fits: x <= target with
        | True =>
          match pair: findPair (target - x) rest with
            | Some (p, q) =>
              let same := Option.someInjective found
              let xIs: x = a := Pair.mkInjectiveFst same
              let pq := Pair.mkInjectiveSnd same
              let pIs: p = b := Pair.mkInjectiveFst pq
              let qIs: q = c := Pair.mkInjectiveSnd pq
              let sound := findPairSound (target - x) rest p q pair
              Both
                (rewrite <- xIs, <- pIs, <- qIs in
                  (List.memCombinationsCons x [p, q] x rest 2).backward
                    (Inl (Both rfl ((List.memCombinationsTwo p q rest).backward sound.left))))
                omega
            | None => later found
        | False => later found

--| And it finds three whenever there are three.
theorem findTripleComplete ∀ (target: Nat) (entries: List Nat) (a b c: Nat)
    (inTriples: [a, b, c] ∈ entries.combinations 3)
    (sum: a + b + c = target):
    findTriple target entries ≠ None :=
  match entries with
    | [x, ..rest] => none =>
      let nothing := findTripleNoneCons target x rest none
      match (List.memCombinationsCons a [b, c] x rest 2).forward inTriples with
        | Inl (Both xIs inPairs) =>
          findPairComplete
            (target - x)
            rest
            b
            c
            ((List.memCombinationsTwo b c rest).forward inPairs)
            omega
            (nothing.right omega)
        | Inr later => findTripleComplete target rest a b c later sum nothing.left

--| An answer that is sound and complete is the only answer, when there is
--| exactly one.
theorem onlyAnswer ∀ (answers: List Nat) (found: Option Nat)
    (sound: ∀ (x: Nat) => found = Some x → x ∈ answers)
    (complete: ∀ (x: Nat) => x ∈ answers → found ≠ None) (answer: Nat)
    (isAnswer: answer ∈ answers)
    (only: ∀ (other: Nat) => other ∈ answers → other = answer):
    found = Some answer :=
  match found with
    | Some x => rewrite only x (sound x rfl) in rfl
    | None => Void.exfalso (complete answer isAnswer rfl)

--| Part 1's answer is one of the puzzle's.
theorem part1Sound ∀ (entries: List Nat) (answer: Nat)
    (found: solvePart1 entries = Some answer):
    answer ∈ part1Answers entries :=
  match pair: findPair 2020 entries with
    | Some (a, b) =>
      let sound := findPairSound 2020 entries a b pair
      rewrite <- Option.someInjective found in
        List.memMap _ (a, b) (List.memFilterIntro _ _ sound.left (rewrite sound.right in rfl)) (((a, b)) => a * b)

--| Part 1 has an answer whenever the puzzle has one.
theorem part1Complete ∀ (entries: List Nat) (answer: Nat)
    (isAnswer: answer ∈ part1Answers entries):
    solvePart1 entries ≠ None :=
  match List.memMapElim (((a, b)) => a * b) answer _ isAnswer with
    | Witness (a, b) (Both chosen made) =>
      let kept := List.memFilter _ _ chosen
      none =>
        match pair: findPair 2020 entries with
          | None => findPairComplete 2020 entries a b kept.left (kept.right.read) pair

--| So part 1 is the puzzle's answer, when there is exactly one.
theorem part1Correct ∀ (entries: List Nat) (answer: Nat)
    (isAnswer: answer ∈ part1Answers entries)
    (only: ∀ (other: Nat) => other ∈ part1Answers entries → other = answer):
    solvePart1 entries = Some answer :=
  onlyAnswer
    (part1Answers entries)
    (solvePart1 entries)
    (part1Sound entries)
    (part1Complete entries)
    answer
    isAnswer
    only

--| Part 2's answer is one of the puzzle's.
theorem part2Sound ∀ (entries: List Nat) (answer: Nat)
    (found: solvePart2 entries = Some answer):
    answer ∈ part2Answers entries :=
  match triple: findTriple 2020 entries with
    | Some (a, b, c) =>
      let sound := findTripleSound 2020 entries a b c triple
      rewrite <- Option.someInjective found in
        rewrite <- product3 a b c in
          List.memMap _
            [a, b, c]
            (List.memFilterIntro _ _ sound.left (rewrite sum3 a b c, sound.right in rfl))
            (choice => choice.product)

--| Part 2 has an answer whenever the puzzle has one.
theorem part2Complete ∀ (entries: List Nat) (answer: Nat)
    (isAnswer: answer ∈ part2Answers entries):
    solvePart2 entries ≠ None :=
  match List.memMapElim (choice => choice.product) answer _ isAnswer with
    | Witness choice (Both chosen made) =>
      let kept := List.memFilter _ _ chosen
      let length := (List.memCombinations entries 3 choice kept.left).left
      match choice, length with
        | [a, b, c], threeLong => none =>
          match triple: findTriple 2020 entries with
            | None => findTripleComplete 2020 entries a b c kept.left (rewrite <- sum3 a b c in kept.right.read) triple
        | [], tooShort => Void.exfalso (omega [tooShort])
        | [x], tooShort => Void.exfalso (omega [tooShort])
        | [x, y], tooShort => Void.exfalso (omega [tooShort])
        | [x, y, z, w, ..rest], tooLong => Void.exfalso (omega [tooLong])

--| So part 2 is the puzzle's answer, when there is exactly one.
theorem part2Correct ∀ (entries: List Nat) (answer: Nat)
    (isAnswer: answer ∈ part2Answers entries)
    (only: ∀ (other: Nat) => other ∈ part2Answers entries → other = answer):
    solvePart2 entries = Some answer :=
  onlyAnswer
    (part2Answers entries)
    (solvePart2 entries)
    (part2Sound entries)
    (part2Complete entries)
    answer
    isAnswer
    only
