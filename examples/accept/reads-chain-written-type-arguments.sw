-- A `readsThen` chain checks with any of its type arguments written, as it
-- does with none: each step's continuation meets the parser's next step, a
-- solved unknown standing for an `Effect.bind` call, as a call compared by
-- its arguments (SW-3304). Compared by unfolding both, `?p ()` would meet
-- what `Parse.nat` computes to, which it can't be solved from.
import Std (Char, List, Parse)

def p(): {Parse Char} List Nat :=
  let x0 := Parse.nat()
  let x1 := Parse.nat()
  let x2 := Parse.nat()
  [x0, x1, x2]

def Spec (read: List Char) (made: List Nat): Prop := made = made

theorem readsNone: Parse.Reads p Spec := Parse.readsThen Parse.readsNat (r0 x0 h0 =>
  Parse.readsThen Parse.readsNat (r1 x1 h1 =>
    Parse.readsThen Parse.readsNat (r2 x2 h2 => Parse.readsDone [x0, x1, x2] _ rfl)))

theorem readsT: Parse.Reads p Spec := Parse.readsThen [t := Char] Parse.readsNat (r0 x0 h0 =>
  Parse.readsThen [t := Char] Parse.readsNat (r1 x1 h1 =>
    Parse.readsThen [t := Char] Parse.readsNat (r2 x2 h2 => Parse.readsDone [x0, x1, x2] _ rfl)))

theorem readsA: Parse.Reads p Spec := Parse.readsThen [a := Nat] Parse.readsNat (r0 x0 h0 =>
  Parse.readsThen [a := Nat] Parse.readsNat (r1 x1 h1 =>
    Parse.readsThen [a := Nat] Parse.readsNat (r2 x2 h2 => Parse.readsDone [x0, x1, x2] _ rfl)))

theorem readsB: Parse.Reads p Spec := Parse.readsThen [b := List Nat] Parse.readsNat (r0 x0 h0 =>
  Parse.readsThen [b := List Nat] Parse.readsNat (r1 x1 h1 =>
    Parse.readsThen [b := List Nat] Parse.readsNat (r2 x2 h2 => Parse.readsDone [x0, x1, x2] _ rfl)))

theorem readsTA: Parse.Reads p Spec := Parse.readsThen [t := Char] [a := Nat] Parse.readsNat (r0 x0 h0 =>
  Parse.readsThen [t := Char] [a := Nat] Parse.readsNat (r1 x1 h1 =>
    Parse.readsThen [t := Char] [a := Nat] Parse.readsNat (r2 x2 h2 => Parse.readsDone [x0, x1, x2] _ rfl)))

theorem readsTB: Parse.Reads p Spec := Parse.readsThen [t := Char] [b := List Nat] Parse.readsNat (r0 x0 h0 =>
  Parse.readsThen [t := Char] [b := List Nat] Parse.readsNat (r1 x1 h1 =>
    Parse.readsThen [t := Char] [b := List Nat] Parse.readsNat (r2 x2 h2 => Parse.readsDone [x0, x1, x2] _ rfl)))

theorem readsAB: Parse.Reads p Spec := Parse.readsThen [a := Nat] [b := List Nat] Parse.readsNat (r0 x0 h0 =>
  Parse.readsThen [a := Nat] [b := List Nat] Parse.readsNat (r1 x1 h1 =>
    Parse.readsThen [a := Nat] [b := List Nat] Parse.readsNat (r2 x2 h2 => Parse.readsDone [x0, x1, x2] _ rfl)))

theorem readsTAB: Parse.Reads p Spec :=
  Parse.readsThen [t := Char] [a := Nat] [b := List Nat] Parse.readsNat (r0 x0 h0 =>
    Parse.readsThen [t := Char] [a := Nat] [b := List Nat] Parse.readsNat (r1 x1 h1 =>
      Parse.readsThen [t := Char] [a := Nat] [b := List Nat] Parse.readsNat (r2 x2 h2 =>
        Parse.readsDone [x0, x1, x2] _ rfl)))
