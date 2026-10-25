-- Chapter 11: exporting functions to JavaScript and TypeScript.
import Std (List, Option, SafeNat, Text)

type Item = { name: Text, pence: Nat, note: Option Text }

type Discount =
  | NoDiscount
  | PercentOff (percent: Nat)

-- A `Nat` is a `bigint`, a record a plain object, an `Option` a value or
-- `undefined`, and a variant an object with a `$tag`.
export def total (items: List Item) (discount: Discount): Nat :=
  let full := items.map (.pence) |> .sum
  match discount with
    | NoDiscount => full
    | PercentOff percent => full - full * percent / 100

-- `SafeNat` is a whole number that fits a JS `number`.
export def count (items: List Item): Option SafeNat := SafeNat.ofNat items.length

-- A proof the caller can't give becomes a check when the function is called.
export def share (pence: Nat) (people: Nat): [auto someone: people ≠ 0] → Nat := pence / people

test "total" := total [{ name = "tea", pence = 250, note = None }] (PercentOff 10) == 225
