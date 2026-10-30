-- General facts the proofs use: adding up a cost over each key and the
-- next, the last key of a list, `List.all` on a member, `Option.flatMap`
-- after a `Some`, and that `List.minBy` returns one of the list.

namespace Aoc.Year2024.Day21.Proofs
import Std (Bool, Eq, List, Nat, Option, Ord, Void)

-- The cost of pressing `keys` in turn from `from`: each key's cost from the
-- one before.
def costFrom (cost: k → k → Nat) (from: k): List k → Nat
  | Nil => 0
  | Cons to rest => cost from to + costFrom cost to rest

-- The last of `keys`, or `from` if there are none.
def lastFrom (from: k): List k → k
  | Nil => from
  | Cons key rest => lastFrom key rest

-- Adding up over each key and the next is `costFrom`.
theorem sumByPairs (cost: k → k → Nat): (from: k) → (keys: List k) →
    (Cons from keys).zipWithNext.sumBy (((before, after)) => cost before after) = costFrom cost from keys
  | from, Nil => rfl
  | from, Cons to rest =>
    rewrite List.sumByCons (Cons to rest).zipWithNext (MkPair from to) (((before, after)) => cost before after), sumByPairs cost to rest in rfl

-- Pressing one list then another: the second starts from the first's last key.
theorem costFromAppend (cost: k → k → Nat): (from: k) → (first: List k) → (second: List k) →
    costFrom cost from (List.append first second) = costFrom cost from first + costFrom cost (lastFrom from first) second
  | from, Nil, second => rfl
  | from, Cons key rest, second => rewrite costFromAppend cost key rest second in omega

-- Equal costs give equal totals.
theorem costFromCong (cost: k → k → Nat) (same: k → k → Nat) (equal: (from: k) → (to: k) → cost from to = same from to): (from: k) → (keys: List k) →
    costFrom cost from keys = costFrom same from keys
  | from, Nil => rfl
  | from, Cons to rest => rewrite equal from to, costFromCong cost same equal to rest in rfl

-- When every press costs one, the total is the number of keys.
theorem costFromOnes: (from: k) → (keys: List k) → costFrom (before after => 1) from keys = keys.length
  | from, Nil => rfl
  | from, Cons to rest => rewrite costFromOnes to rest in omega

theorem lastFromAppendOne: (from: k) → (keys: List k) → (key: k) → lastFrom from (List.append keys [key]) = key
  | from, Nil, key => rfl
  | from, Cons first rest, key => lastFromAppendOne first rest key

theorem flatMapSome (f: a → Option b): (x: Option a) → (value: a) → x = Some value → x.flatMap f = f value
  | None, value, same => Void.exfalso (Option.noneNotSome value same)
  | Some found, value, same => rewrite Option.someInjective found value same in rfl

theorem flatMapIntoSome: (x: Option a) → x.flatMap (value => Some value) = x
  | None => rfl
  | Some value => rfl

-- Folding with `List.minByStep` keeps a value that passes, if all do.
theorem minByStepPasses [auto ord: Ord b] (key: a → b) (passes: a → Bool): (best: a) → passes best = True → (rest: List a) → List.all rest passes = True →
    passes (List.foldLeft rest best (List.minByStep key)) = True
  | best, good, Nil, all => good
  | best, good, Cons next others, all =>
    let nextGood := Bool.andLeft _ _ all
    let othersGood := Bool.andRight _ _ all
    match compared: Ord.compare (key best) (key next) with
      | Greater => minByStepPasses key passes next nextGood others othersGood
      | Less => minByStepPasses key passes best good others othersGood
      | Equal => minByStepPasses key passes best good others othersGood
