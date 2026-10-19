||| Division by a dial's size, `S h`, kept folded: `export` (not `public
||| export`) hides the definitions from other modules, so the type checker
||| doesn't unfold `modS h x` into the library's `mod'` with fuel. Only the
||| four facts below are visible outside.
module DialArith

import Data.Nat
import Data.Nat.Division

%default total

export
modS : (h : Nat) -> Nat -> Nat
modS h x = modNatNZ x (S h) ItIsSucc

export
divS : (h : Nat) -> Nat -> Nat
divS h x = divNatNZ x (S h) ItIsSucc

-- Quotient and remainder are unique (contrib's `DivisionTheoremUniqueness`).
export
modUniq : (h, x, q, r : Nat) -> LT r (S h) -> x = q * S h + r -> modS h x = r
modUniq h x q r lt e = snd (DivisionTheoremUniqueness x (S h) ItIsSucc q r lt e)

export
divUniq : (h, x, q, r : Nat) -> LT r (S h) -> x = q * S h + r -> divS h x = q
divUniq h x q r lt e = fst (DivisionTheoremUniqueness x (S h) ItIsSucc q r lt e)

export
modBound : (h, x : Nat) -> LT (modS h x) (S h)
modBound h x = boundModNatNZ x (S h) ItIsSucc

-- x = q * s + r
export
divThm : (h, x : Nat) -> x = divS h x * S h + modS h x
divThm h x = trans (DivisionTheorem x (S h) ItIsSucc ItIsSucc) (plusCommutative _ _)
