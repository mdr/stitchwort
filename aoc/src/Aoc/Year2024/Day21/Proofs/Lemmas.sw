--| General facts the proofs use: adding up a cost over each key and the
--| next, the last key of a list, `List.all` on a member, `Option.flatMap`
--| after a `Some`, and that `List.minBy` returns one of the list.

namespace Aoc.Year2024.Day21.Proofs
import Std (Bool, Eq, List, Nat, Option, Ord, Void)

--| The cost of pressing `keys` in turn from `from`: each key's cost from the
--| one before.
def costFrom (cost: k → k → Nat) (from: k): List k → Nat
  | [] => 0
  | [to, ..rest] => cost from to + costFrom cost to rest

--| The last of `keys`, or `from` if there are none.
def lastFrom (from: k): List k → k
  | [] => from
  | [key, ..rest] => lastFrom key rest

--| Adding up over each key and the next is `costFrom`.
theorem sumByPairs (cost: k → k → Nat) (from: k) (keys: List k):
    [from, ..keys].zipWithNext.sumBy (((before, after)) => cost before after) = costFrom cost from keys :=
  match keys with
    | [] => rfl
    | [to, ..rest] =>
      rewrite List.sumByCons [to, ..rest].zipWithNext (MkPair from to) (((before, after)) => cost before after), sumByPairs cost to rest in rfl

--| Pressing one list then another: the second starts from the first's last key.
theorem costFromAppend (cost: k → k → Nat) (from: k) (first second: List k):
    costFrom cost from (first.append second) = costFrom cost from first + costFrom cost (lastFrom from first) second :=
  match first with
    | [] => rfl
    | [key, ..rest] => rewrite costFromAppend cost key rest second in omega

--| Equal costs give equal totals.
theorem costFromCong (cost: k → k → Nat) (same: k → k → Nat) (equal: ∀ (from to: k) => cost from to = same from to) (from: k) (keys: List k):
    costFrom cost from keys = costFrom same from keys := match keys with
      | [] => rfl
      | [to, ..rest] => rewrite equal from to, costFromCong cost same equal to rest in rfl

--| When every press costs one, the total is the number of keys.
theorem costFromOnes (from: k) (keys: List k): costFrom (before after => 1) from keys = keys.length := match keys with
  | [] => rfl
  | [to, ..rest] => rewrite costFromOnes to rest in omega

theorem lastFromAppendOne (from: k) (keys: List k) (key: k): lastFrom from (keys.append [key]) = key := match keys with
  | [] => rfl
  | [first, ..rest] => lastFromAppendOne first rest key

theorem flatMapSome (f: a → Option b) (x: Option a) (value: a) (same: x = Some value): x.flatMap f = f value :=
  match x with
    | Some found => rewrite Option.someInjective same in rfl

theorem flatMapIntoSome (x: Option a): x.flatMap (value => Some value) = x := match x with
  | None => rfl
  | Some value => rfl

--| Folding with `List.minByStep` keeps a value that passes, if all do.
theorem minByStepPasses [auto ord: Ord b] (key: a → b) (passes: a → Bool): ∀ (best: a) => passes best = True → ∀ (rest: List a) => rest.all passes = True →
    passes (rest.foldLeft best (List.minByStep key)) = True
  | best, good, [], all => good
  | best, good, [next, ..others], all =>
    let nextGood := Bool.andLeft all
    let othersGood := Bool.andRight all
    match compared: Ord.compare (key best) (key next) with
      | Greater => minByStepPasses key passes next nextGood others othersGood
      | Less => minByStepPasses key passes best good others othersGood
      | Equal => minByStepPasses key passes best good others othersGood
