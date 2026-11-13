--| `valueAt` reads the values `assign` finds as a function on the
--| positions: mapping it over the (distinct) keys gives the values back, it
--| relates each key to its value as the lists are related, its values are
--| in the list, and it is injective on the keys when the values are
--| distinct.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Bool, DecEq, Eq, List, Nat, Void)

--| A member that is not the head is in the rest.
theorem memRestOfNe ∀ [auto eq: DecEq k] (key: k) (first: k) (rest: List k) (member: key ∈ [first, ..rest]) (other: (key == first) = False): key ∈ rest :=
  match member with
    | Inl equal => Void.exfalso (other.read (Eq.sym equal))
    | Inr later => later

--| A key other than the first reads from the rest.
theorem valueAtLater ∀ [auto eq: DecEq k] (fallback: v) (first: k) (rest: List k) (value: v) (values: List v) (key: k) (other: key ≠ first):
    valueAt fallback [first, ..rest] [value, ..values] key = valueAt fallback rest values key :=
  match same: key == first with
    | True => Void.exfalso (other same.read)
    | False => rfl

--| Reading each of distinct keys gives the values, in order.
theorem mapValueAt ∀ [auto eq: DecEq k] (fallback: v) (keys: List k) (values: List v) (lengths: keys.length = values.length) (h: keys.Distinct):
    keys.map (valueAt fallback keys values) = values := match keys, values, h with
      | [], [], distinct => rfl
      | [first, ..rest], [value, ..values], Both fresh distinct =>
        rewrite DecEq.refl first in
          rewrite List.mapCongMem rest (valueAt fallback [first, ..rest] [value, ..values]) (valueAt fallback rest values)
              (key member => valueAtLater fallback first rest value values key (same => fresh (rewrite <- same in member))),
            mapValueAt fallback rest values (Nat.succInjective lengths) distinct in rfl
      | [], [value, ..values], distinct => Void.exfalso (Nat.zeroNotSucc _ lengths)
      | [first, ..rest], [], distinct => Void.exfalso (Nat.succNotZero _ lengths)

--| A key's value is related to it as the values are to the keys.
theorem valueAtRelated ∀ [auto eq: DecEq k] (fallback: v) (related: v → k → Prop): ∀ (keys: List k) (values: List v) =>
    List.All2 related values keys → ∀ (key: k) => key ∈ keys → related (valueAt fallback keys values key) key
  | [first, ..rest], [value, ..values], Both here later, key, member =>
    match same: key == first with
      | True => rewrite same.read in here
      | False => valueAtRelated fallback related rest values later key (memRestOfNe key first rest member same)
  | [], values, related2, key, member => Void.exfalso member
  | [first, ..rest], [], related2, key, member => Void.exfalso related2

--| A key's value is one of the values.
theorem valueAtMember ∀ [auto eq: DecEq k] (fallback: v): ∀ (keys: List k) (values: List v) => keys.length = values.length →
    ∀ (key: k) => key ∈ keys → valueAt fallback keys values key ∈ values
  | [], values, lengths, key, member => Void.exfalso member
  | [first, ..rest], [], lengths, key, member => Void.exfalso (Nat.succNotZero _ lengths)
  | [first, ..rest], [value, ..values], lengths, key, member =>
    match here: key == first with
      | True => Inl rfl
      | False => Inr (valueAtMember fallback rest values (Nat.succInjective lengths) key (memRestOfNe key first rest member here))

--| Distinct values mean distinct keys have distinct values.
theorem valueAtInjective ∀ [auto eq: DecEq k] (fallback: v): ∀ (keys: List k) (values: List v) => keys.length = values.length → values.Distinct →
    ∀ (first second: k) => first ∈ keys → second ∈ keys → valueAt fallback keys values first = valueAt fallback keys values second → first = second
  | [], values, lengths, distinct, first, second, inFirst, inSecond, same => Void.exfalso inFirst
  | [head, ..rest], [], lengths, distinct, first, second, inFirst, inSecond, same => Void.exfalso (Nat.succNotZero _ lengths)
  | [head, ..rest], [value, ..values], lengths, Both fresh distinct, first, second, inFirst, inSecond, same =>
    match firstHere: first == head with
      | True =>
        match secondHere: second == head with
          | True => Eq.trans firstHere.read (Eq.sym secondHere.read)
          | False =>
            Void.exfalso (fresh (rewrite same in valueAtMember fallback rest values (Nat.succInjective lengths) second (memRestOfNe second head rest inSecond secondHere)))
      | False =>
        match secondHere: second == head with
          | True =>
            Void.exfalso (fresh (rewrite <- same in valueAtMember fallback rest values (Nat.succInjective lengths) first (memRestOfNe first head rest inFirst firstHere)))
          | False =>
            valueAtInjective fallback rest values (Nat.succInjective lengths) distinct first second (memRestOfNe first head rest inFirst firstHere)
              (memRestOfNe second head rest inSecond secondHere) same
