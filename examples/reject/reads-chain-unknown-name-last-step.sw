-- expect-error: E-UNKNOWN-NAME
-- A slip in the last step of a `readsThen` chain is reported where it is,
-- not at the chain's first lemma (SW-3281). The spec is true of the list the
-- chain builds, so the unknown name is the only error.
import Std (Char, List, Parse)

def p(): {Parse Char} List Nat :=
  let x0 := Parse.nat()
  let x1 := Parse.nat()
  let x2 := Parse.nat()
  [x0, x1, x2]

def Spec (read: List Char) (made: List Nat): Prop := made.length = 3

theorem readsP: Parse.Reads p Spec := Parse.readsThen Parse.readsNat (r0 x0 h0 =>
  Parse.readsThen Parse.readsNat (r1 x1 h1 =>
    Parse.readsThen Parse.readsNat (r2 x2 h2 => Parse.readsDone [x0, x1, xBad] _ rfl)))
