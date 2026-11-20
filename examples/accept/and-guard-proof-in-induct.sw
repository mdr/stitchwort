-- `f.induct` is made when an `&&` guard's proof reaches the case only at
-- a position conversion skips: the case states the guard as its `Bool`
-- and holds the proof as read from it, where the definition's tree has
-- the proof itself (SW-4360). A proof field, a condition over a
-- constructor holding the proof, and a `decreasing` proof each convert.
import Std (Bool, Eq, List, Nat)

type Gap = | MkGap (lo: Nat) (hi: Nat) (ok: lo < hi ∧ 0 < lo)

def mkGap (x y: Nat) [auto ok: x < y ∧ 0 < x]: Gap := MkGap x y ok

-- The recursive call's argument holds the proof in a field.
def collect: List Nat → List Gap → List Gap
  | [x, y, ..rest], acc if x < y && 0 < x => collect rest [mkGap x y, ..acc]
  | [_, ..rest], acc => collect rest acc
  | [], acc => acc

theorem grows ∀ (ns: List Nat) (gs: List Gap): gs.length ≤ (collect ns gs).length := match induct (collect ns gs) with
  | eq1 x y rest acc guard ih => arithmetic
  | eq2 head rest acc notArm1 ih => ih
  | eq3 acc => arithmetic

-- An `if` below the guard tests a constructor holding the proof.
def wide (g: Gap): Bool := match g with | MkGap lo hi _ => lo + 3 < hi

def keep: List Nat → List Gap
  | [x, y, ..rest] if x < y && 0 < x => if wide (mkGap x y) then [mkGap x y, ..keep rest] else keep rest
  | [_, ..rest] => keep rest
  | [] => []

theorem keepShorter ∀ (xs: List Nat): (keep xs).length ≤ xs.length := match induct (keep xs) with
  | eq1IfTrue x y rest guard h1 ih => arithmetic
  | eq1IfFalse x y rest guard h1 ih => arithmetic
  | eq2 head rest notArm1 ih => arithmetic
  | eq3 => arithmetic

-- The decrease proof comes from the guard's proof.
theorem stepDown ∀ (k n: Nat) [auto h: k < n ∧ 0 < k]: n - (k + 1) < n - k := arithmetic

def climb (k n: Nat): Nat
    decreasing n - k
:=
  match k with
    | j if j < n && 0 < j => 1 + climb (j + 1) n [decreasing := stepDown j n]
    | _ => 0

theorem climbBounded ∀ (k n: Nat): climb k n ≤ n - k := match induct (climb k n) with
  | eq1 n j guard ih =>
    let below: j < n := guard.read.left
    arithmetic
  | eq2 k n notArm1 => arithmetic
