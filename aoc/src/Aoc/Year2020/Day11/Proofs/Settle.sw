--| Running rounds until one changes nothing finds the spec's settled
--| layout, for any plan whose round is a spec round `specRound` on the
--| layouts the rounds reach (those `keep` holds of): what `settle` stops at
--| is reached by rounds and a round leaves it alone, and if the spec's
--| rounds settle within the round limit, `settle` stops there. Nothing
--| bounds the rounds in general; these say what happens when they stop.

namespace Aoc.Year2020.Day11.Proofs
import Aoc.Year2020.Day11 (..)
import Aoc.Year2020.Day11.Spec (Settles)
import Std (DecEq, Eq, Exists, Nat, Option, Void)

--| The rounds from `start` reach `final` in fewer than `limit` rounds, and
--| a round changes nothing there.
def SettlesWithin (specRound: Layout → Layout) (start final: Layout) (limit: Nat): Prop :=
  ∃ (reached: Nat) => reached < limit ∧ Nat.iterate reached specRound start = final ∧ specRound final = final

--| What `settle` stops at is settled: reached by the spec's rounds, fewer
--| than it was given, which leave it alone.
theorem settleSound ∀ (plan: Plan) (specRound: Layout → Layout) (keep: Layout → Prop)
    (agree: ∀ (layout: Layout) => keep layout → layout.round plan = specRound layout)
    (keeps: ∀ (layout: Layout) => keep layout → keep (specRound layout)) (final: Layout) (rounds: Nat)
    (start: Layout) (kept: keep start)
    (stopped: start.settle plan rounds = Some final):
    SettlesWithin specRound start final rounds :=
  match rounds with
    | Succ more =>
      let same := agree start kept
      match e: start.round plan == start with
        | True =>
          let here: start = final := Option.someInjective stopped
          Witness 0 (Both (arithmetic) (Both here (rewrite <- here, <- same then e.read)))
        | False =>
          let later :=
            settleSound plan specRound keep agree keeps final more
              (specRound start)
              (keeps start kept)
              (rewrite <- same then stopped)
          Exists.elim later (reached both => Witness (Succ reached) (Both (arithmetic [both.left]) both.right))

--| Settled within a limit is settled.
theorem settlesOfWithin ∀ (specRound: Layout → Layout) (start final: Layout) (limit: Nat)
    (within: SettlesWithin specRound start final limit):
    Settles specRound start final :=
  Exists.elim within (reached both => Witness reached both.right)

--| The rounds settle on one layout: once a round changes nothing, no later
--| round does.
theorem settledUnique ∀ (specRound: Layout → Layout) (start one other: Layout)
    (first: Settles specRound start one)
    (second: Settles specRound start other):
    one = other :=
  Exists.elim first (m firstBoth =>
    Exists.elim second (n secondBoth =>
      let (Both reachedOne fixedOne) := firstBoth
      let (Both reachedOther fixedOther) := secondBoth
      match order: Nat.leq m n with
        | True =>
          Eq.trans
            (Eq.flipped (Nat.iterateFixedLater specRound start one fixedOne m n reachedOne (arithmetic)))
            reachedOther
        | False =>
          Eq.trans reachedOne.flipped
            (Nat.iterateFixedLater specRound start other fixedOther n m reachedOther (arithmetic))))

--| If the spec's rounds reach a layout a round leaves alone, `settle` with
--| more rounds than that to spare stops there.
theorem settleComplete ∀ (plan: Plan) (specRound: Layout → Layout) (keep: Layout → Prop)
    (agree: ∀ (layout: Layout) => keep layout → layout.round plan = specRound layout)
    (keeps: ∀ (layout: Layout) => keep layout → keep (specRound layout)) (final: Layout)
    (fixed: specRound final = final):
    ∀ (rounds: Nat) (start: Layout) => keep start
      → ∀ (reached: Nat) => reached < rounds
        → Nat.iterate reached specRound start = final
        → start.settle plan rounds = Some final
  | Zero, start, kept, reached, within, there => Void.impossible arithmetic
  | Succ more, start, kept, reached, within, there =>
    let same := agree start kept
    match e: start.round plan == start with
      | True =>
        let still: specRound start = start := rewrite <- same then e.read
        rewrite <- Nat.iterateFixed specRound start still reached, there then byComputing
      | False =>
        match reached with
          | Zero => Void.impossible (e.read (rewrite same, there, fixed then byComputing))
          | Succ earlier =>
            rewrite same then
              settleComplete plan specRound keep agree keeps final fixed more
                (specRound start)
                (keeps start kept)
                earlier
                (arithmetic)
                there
