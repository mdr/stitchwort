-- A guard in a proof's `match` refines the goal and the hypotheses as `match`
-- on its condition does (D3701, docs/proposals/guard-refinement.md): in the
-- guarded arm the condition is `True`, in the arms below it `False`, so a
-- program's `if` on the same condition computes, and a proof can follow a
-- guarded program arm for arm. The facts are D3699's: a `Bool` guard `c`
-- gives `c = True` to its arm and `c = False` to the arms below, a decided
-- proposition `p` gives `p` and `¬p`.
import Std (List, Void)

def weight (c: Char): Nat := if c == '(' then 1 else 2

-- Each arm's `if` computes: `1 <= 1`, then `1 <= 2`.
theorem weightOpen ∀ (c: Char): 1 <= weight c := match c with
  | c if c == '(' => byComputing
  | c => byComputing

-- A hypothesis is refined too: in the guarded arm `h` is `1 = 2`.
theorem weightTwo ∀ (c: Char) (h: weight c = 2): c ≠ '(' := match c with
  | c if c == '(' => Void.impossible arithmetic
  | c => Std.byDecision

-- A guard on a list pattern's variable, mirroring the program's arms; the
-- arms below see `x > 3` as `False` where `pick` tests it.
def pick (xs: List Nat): Nat := match xs with
  | [x, .._] if x > 3 => x
  | _ => 4

theorem pickAtLeast ∀ (xs: List Nat): 4 <= pick xs := match xs with
  | [x, .._] if x > 3 => arithmetic
  | _ => byComputing

-- A proposition guard: the arm gets `n ≤ limit`, the arm below `¬(n ≤ limit)`,
-- and `clamp`'s `if` computes in both.
def clamp (limit n: Nat): Nat := if n <= limit then n else limit

theorem clampAtMost ∀ (limit n: Nat): clamp limit n <= limit := match n with
  | n if n <= limit => arithmetic
  | n => arithmetic

-- The arm below the guard has `(n == 0) = False`, so `weight n` is `2`.
def weightOf (n: Nat): Nat := if n == 0 then 1 else 2

theorem weightOfOther ∀ (n: Nat) (h: n ≠ 0): weightOf n = 2 := match n with
  | n if n == 0 => arithmetic
  | n => byComputing

-- An `&&` guard is one `Bool`, replaced where the goal has it whole.
def inRange (lo hi n: Nat): Nat := if lo <= n && n <= hi then 1 else 0

theorem inRangeAtMostOne ∀ (lo hi n: Nat): inRange lo hi n <= 1 := match n with
  | n if lo <= n && n <= hi => byComputing
  | n => byComputing
