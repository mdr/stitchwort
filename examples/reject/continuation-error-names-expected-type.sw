-- expect-error: E-TYPE-MISMATCH
-- When the rest lambda of `Parse.followsThen` fails in place and the call's
-- own type then fails to match the goal too, the error keeps the lambda's
-- message and adds a note giving the call's type and the expected one, so
-- the failure is not read as the order the lambda was checked in. Here the
-- goal's parser reads `m.left` as well as `m.offset`, so no `j` fits.
import Std (Parse)

def SameNat (x y: Nat): Prop := x = y

def SameBool (x y: Bool): Prop := x = y

def both (a b: Bool): Bool := a && b

def here (): {Parse Nat} Nat := Parse.mark().offset

theorem followsHere: Parse.Follows SameNat SameNat (() => here()) (() => here()) :=
  Parse.followsMap [alike := SameNat] (m => m.offset) (m => m.offset) Parse.followsMark (m n alike => alike.right.left)

theorem followsBoth: Parse.Follows SameNat SameBool
      (() => (let m := Parse.mark(); both (m.offset == 0) (m.left == 0)))
      (() => (let m := Parse.mark(); both (m.offset == 0) (m.left == 0))) :=
  Parse.followsThen followsHere (x y same => Parse.followsDone (rewrite same))
