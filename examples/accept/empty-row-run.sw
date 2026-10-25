-- A computation that may perform nothing, used where a plain value is
-- expected, is run there (SW-124; docs/proposals/let.md §8, item 6). It's
-- the direct-style rule for any computation (naming or calling one
-- performs it) with nothing to handle, so the elaborator wraps it in
-- `Effect.runPure` and the kernel checks that. The types themselves stay
-- different: see reject/empty-row-function.sw.

import Std.Effect (Comp, NoOp, NoRes)

-- A computation that isn't a function, named in a pure definition.
def f: Comp NoOp NoRes Nat := 3
def g: Nat := f
theorem gIsThree: g = 3 := rfl

-- As an operand of `=`, `f` is the computation itself, passed as written
-- (D1140 (a)), and the `3` on the other side is `Done 3`.
theorem fIsThree: f = 3 := rfl

-- A parameter of that type, and a function returning one, called.
def runIt (c: Comp NoOp NoRes Nat): Nat := c
def next (n: Nat): Comp NoOp NoRes Nat := n + 1
def two: Nat := next 1
theorem twoIsTwo: two = 2 := rfl

-- A function over any row, used at the empty row.
def twice (k: () → {e} Nat): {e} Nat := k () + k ()
def eight: Nat := twice (() => 4)
theorem eightIsEight: eight = 8 := rfl

-- A plain value where the computation is expected becomes `Done`.
def lifted: Comp NoOp NoRes Nat := g

-- A row written `{}` is no row: `{} Nat` is `Nat`, so this is a
-- `Nat -> Nat` (unlike `next`).
def nextPlain (n: Nat): {} Nat := n + 1
def apply (k: Nat → Nat) (n: Nat): Nat := k n
theorem applyNextPlain: apply nextPlain 1 = 2 := rfl
