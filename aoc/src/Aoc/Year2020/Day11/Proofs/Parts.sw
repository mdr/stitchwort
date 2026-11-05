--| Both answers are the spec's: the program's rounds are the spec's
--| (Rounds.sw, Sight.sw), so what `settle` stops at is the layout the spec's
--| rounds settle on (Settle.sw), and its occupied seats are the answer.
--| Each part answers exactly when the spec's rounds settle within the
--| round limit.

namespace Aoc.Year2020.Day11.Proofs
import Aoc.Year2020.Day11 (..)
import Aoc.Year2020.Day11 (Spec)
import Std (Eq, Exists, Iff, Nat, Option, Void)

--| Layouts as tall plus as wide as `start`: the ones the rounds reach.
def SameShape (start: Layout) (layout: Layout): Prop := start.grid.height + start.grid.width = layout.grid.height + layout.grid.width

theorem adjacentAgrees (start: Layout) (layout: Layout) (shape: SameShape start layout): layout.round adjacentRule = Spec.adjacentRound layout :=
  adjacentRound layout

theorem sightAgrees (start: Layout) (layout: Layout) (shape: SameShape start layout): layout.round start.sightRule = Spec.sightRound layout :=
  sightRound start layout shape

theorem adjacentKeeps (start: Layout) (layout: Layout) (shape: SameShape start layout): SameShape start (Spec.adjacentRound layout) :=
  Eq.trans shape (Eq.sym (roundShape layout (Spec.occupiedAdjacent layout) 4))

theorem sightKeeps (start: Layout) (layout: Layout) (shape: SameShape start layout): SameShape start (Spec.sightRound layout) :=
  Eq.trans shape (Eq.sym (roundShape layout (Spec.occupiedSeen layout) 5))

--| An answer from layouts the spec's rounds settle on within the limit.
def AnswerWithin (specRound: Layout → Layout) (start: Layout) (limit: Nat) (answer: Nat): Prop :=
  ∃ (final: Layout) => SettlesWithin specRound start final limit ∧ answer = Spec.occupiedSeats final

--| A rule whose rounds are the spec's gives the occupied seats of a
--| layout the spec's rounds settle on, exactly when they settle within
--| the limit.
theorem settledExactly (start: Layout) (rule: Rule) (specRound: Layout → Layout)
    (agree: (layout: Layout) → SameShape start layout → layout.round rule = specRound layout)
    (keeps: (layout: Layout) → SameShape start layout → SameShape start (specRound layout))
    (limit: Nat) (answer: Nat): (start.settle rule limit |> .map (.occupied)) = Some answer ↔ AnswerWithin specRound start limit answer := {
  forward = solved =>
    match found: start.settle rule limit with
      | None => Void.exfalso (Option.noneNotSome answer solved)
      | Some final =>
        Witness final (Both (settleSound rule specRound (SameShape start) agree keeps final limit start rfl found) (Eq.sym (Option.someInjective solved))),
  backward = spec =>
    Exists.elim spec (final both =>
      let (Both within same) := both
      Exists.elim within (reached parts =>
        let (Both early (Both there fixed)) := parts
        rewrite settleComplete rule specRound (SameShape start) agree keeps final fixed limit start rfl reached early there, same in rfl))
}

--| Part 1's answer is the occupied seats of the layout part 1's rounds
--| settle on, exactly when they settle within the round limit.
theorem part1Exactly (start: Layout) (answer: Nat): start.settledOccupied adjacentRule = Some answer ↔ AnswerWithin Spec.adjacentRound start roundLimit answer :=
  settledExactly start adjacentRule Spec.adjacentRound (adjacentAgrees start) (adjacentKeeps start) roundLimit answer

--| Part 2 likewise, with part 2's rounds.
theorem part2Exactly (start: Layout) (answer: Nat): start.settledOccupied start.sightRule = Some answer ↔ AnswerWithin Spec.sightRound start roundLimit answer :=
  settledExactly start start.sightRule Spec.sightRound (sightAgrees start) (sightKeeps start) roundLimit answer

--| An answer within the limit is the spec's.
theorem answerOfWithin (specRound: Layout → Layout) (start: Layout) (answer: Nat) (limit: Nat) (within: AnswerWithin specRound start limit answer):
    ∃ (final: Layout) => Spec.Settles specRound start final ∧ answer = Spec.occupiedSeats final :=
  Exists.elim within (final both => Witness final (Both (settlesOfWithin specRound start final limit (And.left both)) (And.right both)))

theorem part1Rules (start: Layout) (answer: Nat) (solved: start.settledOccupied adjacentRule = Some answer): Spec.Part1 start answer :=
  answerOfWithin Spec.adjacentRound start answer roundLimit ((part1Exactly start answer).forward solved)

theorem part2Rules (start: Layout) (answer: Nat) (solved: start.settledOccupied start.sightRule = Some answer): Spec.Part2 start answer :=
  answerOfWithin Spec.sightRound start answer roundLimit ((part2Exactly start answer).forward solved)

--| "How many seats end up occupied" names one number: the rounds settle on
--| one layout.
theorem answerUnique (specRound: Layout → Layout) (start: Layout) (one: Nat) (other: Nat)
    (first: ∃ (final: Layout) => Spec.Settles specRound start final ∧ one = Spec.occupiedSeats final)
    (second: ∃ (final: Layout) => Spec.Settles specRound start final ∧ other = Spec.occupiedSeats final): one = other :=
  Exists.elim first (a bothA =>
    Exists.elim second (b bothB =>
      rewrite And.right bothA, And.right bothB, settledUnique specRound start a b (And.left bothA) (And.left bothB) in rfl))

theorem part1Unique (start: Layout) (one: Nat) (other: Nat) (first: Spec.Part1 start one) (second: Spec.Part1 start other): one = other :=
  answerUnique Spec.adjacentRound start one other first second

theorem part2Unique (start: Layout) (one: Nat) (other: Nat) (first: Spec.Part2 start one) (second: Spec.Part2 start other): one = other :=
  answerUnique Spec.sightRound start one other first second
