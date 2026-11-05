--| Running rounds until one changes nothing finds the spec's settled
--| layout, for any rule whose round is a spec round `specRound` on the
--| layouts the rounds reach (those `keep` holds of): what `settle` stops at
--| is reached by rounds and a round leaves it alone, and if the spec's
--| rounds settle within the round limit, `settle` stops there. Nothing
--| bounds the rounds in general; these say what happens when they stop.

namespace Aoc.Year2020.Day11.Proofs
import Aoc.Year2020.Day11 (..)
import Aoc.Year2020.Day11.Spec (Settles)
import Std (DecEq, Eq, Exists, Nat, Option, Void)

--| What `settle` stops at is settled: reached by the spec's rounds, which
--| leave it alone.
theorem settleSound (rule: Rule) (specRound: Layout → Layout) (keep: Layout → Prop)
    (agree: (layout: Layout) → keep layout → layout.round rule = specRound layout)
    (keeps: (layout: Layout) → keep layout → keep (specRound layout)) (final: Layout):
    (rounds: Nat) → (start: Layout) → keep start → start.settle rule rounds = Some final → Settles specRound start final
  | Zero, start, kept, stopped => Void.exfalso (Option.noneNotSome final stopped)
  | Succ more, start, kept, stopped =>
    let same := agree start kept
    match e: start.round rule == start with
      | True =>
        let here: start = final := Option.someInjective stopped
        Witness 0 (Both here (rewrite <- here, <- same in DecEq.sound e))
      | False =>
        let later := settleSound rule specRound keep agree keeps final more (specRound start) (keeps start kept) (rewrite <- same in stopped)
        Exists.elim later (rounds both => Witness (Succ rounds) both)

--| If the spec's rounds reach a layout a round leaves alone, `settle` with
--| more rounds than that to spare stops there.
theorem settleComplete (rule: Rule) (specRound: Layout → Layout) (keep: Layout → Prop)
    (agree: (layout: Layout) → keep layout → layout.round rule = specRound layout)
    (keeps: (layout: Layout) → keep layout → keep (specRound layout)) (final: Layout) (fixed: specRound final = final):
    (rounds: Nat) → (start: Layout) → keep start → (reached: Nat) → reached < rounds → Nat.iterate reached specRound start = final →
      start.settle rule rounds = Some final
  | Zero, start, kept, reached, within, there => Void.exfalso (omega)
  | Succ more, start, kept, reached, within, there =>
    let same := agree start kept
    match e: start.round rule == start with
      | True =>
        let still: specRound start = start := rewrite <- same in DecEq.sound e
        rewrite <- Nat.iterateFixed specRound start still reached, there in rfl
      | False =>
        match reached with
          | Zero => Void.exfalso (DecEq.soundFalse (start.round rule) start e (rewrite same, there, fixed in rfl))
          | Succ earlier =>
            rewrite same in settleComplete rule specRound keep agree keeps final fixed more (specRound start) (keeps start kept) earlier (omega) there
