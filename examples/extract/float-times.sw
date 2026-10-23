-- Millisecond times as a ported TypeScript app has them (docs/proposals/
-- float.md §6.4, §7.4 item 6): fractional, added, subtracted and compared
-- as JS does. JS's `<` and `<=` are `Float.ieeeLt` and `Float.ieeeLe`, and
-- `a > b` is `Float.ieeeLt b a`; `+` and `-` keep the original order. The
-- same functions, written in TS, are compared with these by canonical bits
-- (crates/cli/tests/float.rs).
--
-- run: inWindow 1000.0 2000.0 [999.5, 1000.0, 1500.25, 2000.0, -0.0, Float.nan]
-- run: shiftAll (-1000) [80281.87, 0.1, -0.0]
-- run: gaps [80281.87, 80300.0, 80299.5]
-- run: snap 16.666666666666668 80281.87
-- run: snap 10.0 (-4.0)
-- run: latest [3.5, Float.nan, 7.25, -0.0]
-- run: latest []
-- run: total [0.1, 0.2, 0.3]
-- run: wholeMs 80281.0
-- run: wholeMs 80281.87
-- run: wholeMs (-0.0)
-- run: fromCount 9007199254740993
-- run: clamped 0.0 100.0 (-0.0)
-- run: clamped 0.0 100.0 Float.nan

import Std (Float, List, Option)

-- The times in `[start, end)`: `start <= t && t < end` in the TS.
export def inWindow (start: Float) (end: Float) (times: List Float): List Float :=
  List.filter (t => Float.ieeeLe start t && Float.ieeeLt t end) times

export def shiftAll (by: Float) (times: List Float): List Float := List.map (t => t + by) times

-- Each time minus the one before it.
export def gaps: List Float -> List Float
  | Cons a (Cons b rest) => Cons (b - a) (gaps (Cons b rest))
  | _ => Nil

-- `Math.round(t / grid) * grid`.
export def snap (grid: Float) (t: Float): Float := Float.round (t / grid) * grid

-- `times.reduce((best, t) => (t > best ? t : best))`, `undefined` for none.
export def latest: List Float -> Option Float
  | Nil => None
  | Cons t ts => Some (List.foldLeft (best t => if Float.ieeeLt best t then t else best) t ts)

-- `times.reduce((sum, t) => sum + t, 0)`.
export def total (times: List Float): Float := List.foldLeft (sum t => sum + t) 0.0 times

-- `Number.isInteger(t) ? BigInt(t) : undefined`.
export def wholeMs (t: Float): Option Int := Float.toInt t

-- `Number(n)` of a `bigint`.
export def fromCount (n: Int): Float := Float.ofInt n

-- `t < low ? low : t > high ? high : t`.
export def clamped (low: Float) (high: Float) (t: Float): Float :=
  if Float.ieeeLt t low then low else if Float.ieeeLt high t then high else t
