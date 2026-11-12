--| Both answers are the spec's. The rounds keep the start's floor plan
--| (Plan.sw), and on such layouts the program's rounds, with the seats in
--| view planned on the start, are the spec's (Rounds.sw, Sight.sw); so
--| what `settle` stops at is the layout the spec's rounds settle on
--| (Settle.sw), and its occupied seats are the answer.
--| Each part answers exactly when the spec's rounds settle within the
--| round limit.

namespace Aoc.Year2020.Day11.Proofs
import Aoc.Year2020.Day11 (..)
import Aoc.Year2020.Day11 (Spec)
import Aoc.Common (Position)
import Aoc.Common.Proofs (lookupAt)
import Std (Eq, Exists, Iff, List, Nat, Option, Void)

--| Layouts as tall plus as wide as `start`.
def SameShape (start: Layout) (layout: Layout): Prop := start.grid.height + start.grid.width = layout.grid.height + layout.grid.width

--| What the rounds from `start` keep: its floor plan, and so its shape.
def Kept (start: Layout) (layout: Layout): Prop := SamePlan start layout ∧ SameShape start layout

--| Part 2 looks at the same positions on any layout with the start's
--| floor plan.
theorem sameSight (start: Layout) (layout: Layout) (same: SamePlan start layout) (position: Position):
    start.sightRule.inView start.grid.lookup position = start.sightRule.inView layout.grid.lookup position :=
  let reach := start.grid.height + start.grid.width
  List.filterMapCong compass (direction => firstSeat start.grid.lookup position direction 1 reach)
    (direction => firstSeat layout.grid.lookup position direction 1 reach)
    (direction =>
      firstSeatPlan start.grid.lookup layout.grid.lookup (near => rewrite lookupAt start.grid near, lookupAt layout.grid near in Eq.sym (same near))
        position direction 1 reach)

theorem adjacentAgrees (start: Layout) (layout: Layout) (kept: Kept start layout):
    layout.round (adjacentRule.planFor start) = Spec.adjacentRound layout :=
  roundSpec layout (adjacentRule.planFor start) (Spec.occupiedAdjacent layout)
    (position here found seat => rewrite planCount adjacentRule start layout (And.left kept) position here found seat rfl in aroundOccupied layout position)

theorem sightAgrees (start: Layout) (layout: Layout) (kept: Kept start layout):
    layout.round (start.sightRule.planFor start) = Spec.sightRound layout :=
  roundSpec layout (start.sightRule.planFor start) (Spec.occupiedSeen layout)
    (position here found seat =>
      rewrite planCount start.sightRule start layout (And.left kept) position here found seat (sameSight start layout (And.left kept) position) in
      sightOccupied layout (start.grid.height + start.grid.width) (And.right kept) position)

theorem adjacentKeeps (start: Layout) (layout: Layout) (kept: Kept start layout): Kept start (Spec.adjacentRound layout) :=
  Both (roundPlan start layout (Spec.occupiedAdjacent layout) 4 (And.left kept))
    (Eq.trans (And.right kept) (Eq.sym (roundShape layout (Spec.occupiedAdjacent layout) 4)))

theorem sightKeeps (start: Layout) (layout: Layout) (kept: Kept start layout): Kept start (Spec.sightRound layout) :=
  Both (roundPlan start layout (Spec.occupiedSeen layout) 5 (And.left kept))
    (Eq.trans (And.right kept) (Eq.sym (roundShape layout (Spec.occupiedSeen layout) 5)))

--| The start has its own floor plan and shape.
theorem keptStart (start: Layout): Kept start start := Both (position => rfl) rfl

--| An answer from layouts the spec's rounds settle on within the limit.
def AnswerWithin (specRound: Layout → Layout) (start: Layout) (limit: Nat) (answer: Nat): Prop :=
  ∃ (final: Layout) => SettlesWithin specRound start final limit ∧ answer = Spec.occupiedSeats final

--| A plan whose rounds are the spec's gives the occupied seats of a
--| layout the spec's rounds settle on, exactly when they settle within
--| the limit.
theorem settledExactly (start: Layout) (plan: Plan) (specRound: Layout → Layout)
    (agree: ∀ (layout: Layout) => Kept start layout → layout.round plan = specRound layout)
    (keeps: ∀ (layout: Layout) => Kept start layout → Kept start (specRound layout))
    (limit: Nat) (answer: Nat): (start.settle plan limit |> .map (.occupied)) = Some answer ↔ AnswerWithin specRound start limit answer := {
  forward = solved =>
    match found: start.settle plan limit with
      | Some final =>
        Witness final (Both (settleSound plan specRound (Kept start) agree keeps final limit start (keptStart start) found) (Eq.sym (Option.someInjective solved))),
  backward = spec =>
    Exists.elim spec (final both =>
      let (Both within same) := both
      Exists.elim within (reached parts =>
        let (Both early (Both there fixed)) := parts
        rewrite settleComplete plan specRound (Kept start) agree keeps final fixed limit start (keptStart start) reached early there, same in rfl))
}

--| Part 1's answer is the occupied seats of the layout part 1's rounds
--| settle on, exactly when they settle within the round limit.
theorem part1Exactly (start: Layout) (answer: Nat): start.settledOccupied adjacentRule = Some answer ↔ AnswerWithin Spec.adjacentRound start roundLimit answer :=
  settledExactly start (adjacentRule.planFor start) Spec.adjacentRound (adjacentAgrees start) (adjacentKeeps start) roundLimit answer

--| Part 2 likewise, with part 2's rounds.
theorem part2Exactly (start: Layout) (answer: Nat): start.settledOccupied start.sightRule = Some answer ↔ AnswerWithin Spec.sightRound start roundLimit answer :=
  settledExactly start (start.sightRule.planFor start) Spec.sightRound (sightAgrees start) (sightKeeps start) roundLimit answer

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
