-- A continuation fixed by abstracting what the first parser read:
-- `Parse.followsThen` proves `Parse.Follows same alike (() => j (p()))
-- (() => k (q()))`, and here `j` is never spelled. Once `p` is `here`, the
-- goal's parser `both (here() == 0) (Parse.mark().left == 0)` and `j
-- (here())` both run `Parse.mark` first; after it, `j` meets `m.offset`,
-- the value `here` read, inside the rest of the goal, where no pattern can
-- solve it. `m` is bound inside the goal, so no solution can mention
-- `m.offset`: each occurrence becomes the parameter, `j := x => both (x ==
-- 0) (Parse.mark().left == 0)`, as Lean's `kabstract` makes a motive
-- (SW-4330). Before, `j` and `k` had to be given with `[j := …][k := …]`.
import Std (Parse)

def SameNat (x y: Nat): Prop := x = y

def SameBool (x y: Bool): Prop := x = y

def both (a b: Bool): Bool := a && b

def here (): {Parse Nat} Nat := Parse.mark().offset

theorem followsHere: Parse.Follows SameNat SameNat (() => here()) (() => here()) :=
  Parse.followsMap [alike := SameNat] (m => m.offset) (m => m.offset) Parse.followsMark (m n alike => alike.right.left)

theorem followsTwice: Parse.Follows SameNat SameBool (() => both (here() == 0) (Parse.mark().left == 0)) (() =>
      both (here() == 0) (Parse.mark().left == 0)) :=
  Parse.followsThen followsHere (x y same =>
    Parse.followsThen Parse.followsMark (m n alike => Parse.followsDone (rewrite same, alike.right.right)))
