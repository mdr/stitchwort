-- The order of `Float`s, as the merge uses it: the total order's `Float.leq`
-- and `Float.less`, as `Bool`s. Std proves its laws (`Ord`'s, `Float.leTotal`,
-- `Float.leOfNotLess`, `Float.notLessOfLe`) and `Float.addMonotoneRight`.
namespace Trip.Proofs

import Std (Float, Int, List, Nat, Option, Ord, DecEq, Eq, Void)
import Trip.Model (..)
import Trip.Merge (..)

theorem floatLeTrans ∀ (x: Float) (y: Float) (z: Float) (h1: Float.leq x y = True) (h2: Float.leq y z = True):
    Float.leq x z = True :=
  Ord.leTrans x y z h1 h2

theorem floatLeRefl ∀ (x: Float): Float.leq x x = True := Ord.leRefl x

theorem floatLessLe ∀ (x: Float) (y: Float) (h: Float.less x y = True): Float.leq x y = True := Ord.lessLe x y h

-- A leg ends no earlier than it starts, if its duration isn't negative.
theorem startLeEnd ∀ (leg: Leg) (ok: 0.0 <= leg.duration): Float.leq leg.start leg.end = True :=
  Float.addMonotoneRight leg.start leg.duration ok

-- Clamping

theorem clampLow ∀ (lo: Float) (hi: Float) (t: Float) (ok: Float.leq lo hi = True): Float.leq lo (clamp lo hi t) = True :=
  match c: Float.less t lo with
    | True => floatLeRefl lo
    | False =>
      match d: Float.less hi t with
        | True => ok
        | False => Float.leOfNotLess t lo c

theorem clampHigh ∀ (lo: Float) (hi: Float) (t: Float) (ok: Float.leq lo hi = True): Float.leq (clamp lo hi t) hi = True :=
  match c: Float.less t lo with
    | True => ok
    | False =>
      match d: Float.less hi t with
        | True => floatLeRefl hi
        | False => Float.leOfNotLess hi t d

-- A time already inside is left as it is.
theorem clampInside ∀ (lo: Float) (hi: Float) (t: Float) (low: Float.leq lo t = True) (high: Float.leq t hi = True):
    clamp lo hi t = t :=
  rewrite Float.notLessOfLe lo t low, Float.notLessOfLe t hi high in rfl
