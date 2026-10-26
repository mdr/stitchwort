-- `<`, `<=` and sorting on `Float` are IEEE 754's total order
-- (`Float.compare`): `-0.0 < 0.0`, and the NaN is above `+Infinity`, equal to
-- itself. In JS, `x <= y` and `x < y` are one call each of the natives
-- `Float.leq` and `Float.less`, as cheap as `Float.ieeeLe` (JS's `<=`) on
-- ordinary numbers, and `Float.instOrd` passes `Float.compare`'s native to
-- `sortOn` and `Map` (the `extract` test `float_order_is_native` checks the
-- generated calls).
--
-- run: atMost 1.5 2.5
-- run: atMost 2.5 1.5
-- run: atMost (-0.0) 0.0
-- run: atMost 0.0 (-0.0)
-- run: atMost Float.nan Float.nan
-- run: atMost Float.infinity Float.nan
-- run: atMost Float.nan Float.infinity
-- run: below (-0.0) 0.0
-- run: below 0.0 (-0.0)
-- run: below Float.nan Float.nan
-- run: below 5e-324 (-5e-324)
-- run: belowTen 9.999999999999998
-- run: belowTen Float.nan
-- run: order (-0.0) 0.0
-- run: order Float.nan Float.nan
-- run: order Float.nan (-Float.infinity)
-- run: upTo 1000.0 [999.5, 1000.0, 1500.25, -0.0, Float.nan, 0.0]
-- run: byStart [{ startTime = 3.5, id = 1 }, { startTime = Float.nan, id = 2 }, { startTime = -0.0, id = 3 }, { startTime = 0.0, id = 4 }, { startTime = -1.0, id = 5 }]
-- run: sorted [0.0, -0.0, Float.nan, 1e308, -1e308, 5e-324]
-- run: firstAt [{ startTime = 0.0, id = 1 }, { startTime = -0.0, id = 2 }] (-0.0)

import Std (Float, List, Map, Nat, Option, Ord, Ordering)

type Event = { startTime: Float, id: Nat }

export def atMost (x: Float) (y: Float): Bool := x <= y

export def below (x: Float) (y: Float): Bool := x < y

export def belowTen (x: Float): Bool := x < 10.0

export def order (x: Float) (y: Float): Ordering := Ord.compare x y

export def upTo (limit: Float) (times: List Float): List Float := times.filter (t => t <= limit)

export def byStart (events: List Event): List Event := List.sortOn events .startTime

export def sorted (times: List Float): List Float := List.sort times

export def firstAt (events: List Event) (t: Float): Option Nat :=
  Map.indexBy events .startTime |> .get t |> .map (e => e.id)
