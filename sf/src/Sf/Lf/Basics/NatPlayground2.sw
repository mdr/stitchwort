-- Software Foundations, Volume 1: Logical Foundations, Basics.v, module
-- `NatPlayground2` (in the section "Numbers"), ported to Stitchwort.
-- Copyright and licence: sf/LICENSE-SF.

-- The book's own addition, multiplication and subtraction on the
-- library's numbers, in a namespace of their own as in the book. The
-- library's `+`, `*` and `-` (`Nat.add`, `Nat.mul`, `Nat.sub`,
-- std/core/Data.sw) have the same definitions, and are what the rest of
-- the book uses. Induction.sw uses this `plus` to show why proofs about
-- numbers need induction: the library's `+` is special in one way that
-- hides it (see there).

namespace Sf.Lf.Basics.NatPlayground2

-- Multi-argument functions can be defined by recursion too.

def plus (n: Nat) (m: Nat): Nat := match n with
  | Zero => m
  | Succ n' => Succ (plus n' m)

-- Adding three to two gives us five (whew!):

test "plus 3 2" := plus 3 2 == 5

-- The steps of simplification that compute this can be visualised as
-- follows:
--
--         plus 3 2
--    i.e. plus (Succ (Succ (Succ Zero))) (Succ (Succ Zero))
--     ==> Succ (plus (Succ (Succ Zero)) (Succ (Succ Zero)))
--           by the second arm of the match
--     ==> Succ (Succ (plus (Succ Zero) (Succ (Succ Zero))))
--           by the second arm of the match
--     ==> Succ (Succ (Succ (plus Zero (Succ (Succ Zero)))))
--           by the second arm of the match
--     ==> Succ (Succ (Succ (Succ (Succ Zero))))
--           by the first arm of the match
--    i.e. 5
--
-- Rocq lets parameters of the same type share brackets, `(n m : nat)`.
-- Stitchwort does too: `(n m: Nat)` is `(n: Nat) (m: Nat)`.

def mult (n m: Nat): Nat := match n with
  | Zero => Zero
  | Succ n' => plus m (mult n' m)

theorem testMult1: mult 3 3 = 9 := rfl

-- Two expressions can be matched at once by putting a comma between them:

def minus (n m: Nat): Nat := match n, m with
  | Zero, _ => Zero
  | Succ _, Zero => n
  | Succ n', Succ m' => minus n' m'
