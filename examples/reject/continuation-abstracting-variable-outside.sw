-- expect-error: E-TYPE-MISMATCH
-- A continuation is solved by abstracting what the first parser read only
-- when nothing else in the goal mentions where it was read
-- (`examples/accept/continuation-solved-by-abstracting.sw`). Here `here`
-- reads `m.offset`, and the goal's parser also uses `m.left` of the same
-- mark: no `j` gives `j m.offset` without `m`, so `Parse.followsThen` with
-- `p` as `here` doesn't fit this goal, and nothing is solved.
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
