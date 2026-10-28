-- Counting stones by number: a map of counts stands for a line of stones
-- when, for every way of weighing a stone, the entries' weights (count times
-- weight) add up to the line's (`Represents`). Every blink keeps that, so the
-- counts add up to the line's length after any number of blinks.

namespace Aoc.Year2024.Day11.Proofs
import Aoc.Year2024.Day11 (..)
import Aoc.Year2024.Day11.Spec (..)
import Std (Eq, List, Map, Nat, Ord)

-- The entries' total weight: each count times its number's weight.
def weigh (weight: Nat → Nat): List (Nat, Nat) → Nat
  | Nil => 0
  | Cons (stone, count) rest => count * weight stone + weigh weight rest

theorem weighCong (first: Nat → Nat) (second: Nat → Nat) (same: (stone: Nat) → first stone = second stone):
    (entries: List (Nat, Nat)) → weigh first entries = weigh second entries
  | Nil => rfl
  | Cons (stone, count) rest => rewrite same stone, weighCong first second same rest in rfl

-- Adding `count` stones of one number adds their weight, whether the number
-- is new or already there.
theorem weighInsertWith (weight: Nat → Nat) (key: Nat) (count: Nat):
    (entries: List (Nat, Nat)) → weigh weight (Map.Spec.insertWith Nat.add key count entries) = count * weight key + weigh weight entries
  | Nil => rfl
  | Cons (stone, other) rest =>
    match order: Ord.compare key stone with
      | Less => rfl
      | Equal => rewrite Nat.instOrd.equal key stone order in ring
      | Greater => rewrite weighInsertWith weight key count rest in ring

theorem weighAddStones (weight: Nat → Nat): (counts: Map Nat Nat) → (stones: List Nat) → (count: Nat) →
    weigh weight (addStones counts stones count).toList = count * stones.sumBy weight + weigh weight counts.toList
  | counts, Nil, count => ring
  | counts, Cons stone rest, count =>
    rewrite weighAddStones weight (counts.insertWith stone count Nat.add) rest count, Map.toListInsertWith counts stone count Nat.add,
      weighInsertWith weight stone count counts.toList, List.sumByCons rest stone weight
      in ring

-- A blink on the counts weighs each number by what it changes into.
theorem weighFold (weight: Nat → Nat): (after: Map Nat Nat) → (entries: List (Nat, Nat)) →
    weigh weight (Map.Spec.foldLeft (blinked stone count => addStones blinked (changeStone stone) count) after entries).toList
      = weigh (stone => (changeStone stone).sumBy weight) entries + weigh weight after.toList
  | after, Nil => ring
  | after, Cons (stone, count) rest =>
    rewrite weighFold weight (addStones after (changeStone stone) count) rest, weighAddStones weight after (changeStone stone) count in ring

theorem weighBlinkCounts (weight: Nat → Nat) (counts: Map Nat Nat):
    weigh weight (blinkCounts counts).toList = weigh (stone => (changeStone stone).sumBy weight) counts.toList :=
  rewrite Map.foldLeftToList (blinked stone count => addStones blinked (changeStone stone) count) Map.empty counts,
    weighFold weight Map.empty counts.toList
    in ring

-- `counts` stands for the line `stones`: weighed any way, they agree.
def Represents (counts: Map Nat Nat) (stones: List Nat): Prop := (weight: Nat → Nat) → weigh weight counts.toList = stones.sumBy weight

theorem representsCounts (stones: List Nat): Represents (Map.counts stones) stones := weight =>
  rewrite weighAddStones weight Map.empty stones 1 in ring

-- A blink on the counts stands for a blink on the line.
theorem representsBlink (counts: Map Nat Nat) (stones: List Nat) (represents: Represents counts stones):
    Represents (blinkCounts counts) (blink stones) := weight =>
  rewrite weighBlinkCounts weight counts, weighCong (stone => (changeStone stone).sumBy weight) (stone => (change stone).sumBy weight)
      (stone => rewrite changeAgrees stone in rfl) counts.toList,
    represents (stone => (change stone).sumBy weight), List.sumByFlatMap stones weight change
    in rfl

theorem representsAfter: (blinks: Nat) → (counts: Map Nat Nat) → (stones: List Nat) → Represents counts stones →
    Represents (blinks.iterate blinkCounts counts) (blinkTimes blinks stones)
  | Zero, counts, stones, represents, weight => represents weight
  | Succ blinks, counts, stones, represents, weight =>
    representsAfter blinks (blinkCounts counts) (blink stones) (representsBlink counts stones represents) weight

-- The counts add up to their entries' weight when every stone weighs 1.
theorem sumCounts: (entries: List (Nat, Nat)) → (entries.map Pair.snd).sum = weigh (stone => 1) entries
  | Nil => rfl
  | Cons (stone, count) rest => rewrite List.sumCons count (rest.map Pair.snd), sumCounts rest in ring

theorem sumByOne: (stones: List Nat) → stones.sumBy (stone => 1) = stones.length
  | Nil => rfl
  | Cons stone rest => rewrite List.sumByCons rest stone (stone => 1), sumByOne rest in ring

-- The program's count is the length of the puzzle's line, after any number
-- of blinks.
theorem countCorrect (blinks: Nat) (stones: List Nat): countAfter blinks stones = (blinkTimes blinks stones).length :=
  rewrite sumCounts (blinks.iterate blinkCounts (Map.counts stones)).toList,
    representsAfter blinks (Map.counts stones) stones (representsCounts stones) (stone => 1), sumByOne (blinkTimes blinks stones)
    in rfl
