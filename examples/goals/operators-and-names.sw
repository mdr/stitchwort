-- Goals show `&&`, `||`, `<` and `<=` as written, on `Nat`, `Int` and
-- through an `Ord` dictionary (`a > b` is `b < a`), and name declarations
-- by the shortest name that means them here: `gentle`, not
-- `Demo.Ops.gentle`; `Demo.Ops.count` where a variable `count` hides it.
namespace Demo.Ops

def gentle (a: Nat) (b: Nat): Bool := a < b && b <= a + 3

def count: Nat := 3

theorem onNat (a: Nat) (b: Nat): (a < b && b <= a + 3 || a > b) = (gentle a b || b < a) := ?

theorem onInt (a: Int) (b: Int) (h: a < b) (k: a <= b): (a < b && a <= b) = True := ?

theorem throughOrd [t: Type] [auto ord: Ord t] (a: t) (b: t) (h: a < b): (a <= b || a < b) = True := ?

theorem hidden (count: Nat): count + Demo.Ops.count = Demo.Ops.count + count := ?
