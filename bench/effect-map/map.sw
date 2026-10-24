-- Benchmark: `List.map` against `List.mapIn` with a pure callback, and
-- `List.mapIn` with an effectful one (docs/proposals/effect-polymorphism.md,
-- stage 2). Reads `mode n rounds` from standard input, where `mode` is `map`,
-- `mapIn`, `fail`, or `sum` (the sum alone, which the others include);
-- prints a checksum. Run with
--   echo "mapIn 1000000 10" | stitchwort run bench/effect-map/map.sw [--js]
import Std (List, Fail, Text, Option, Nat)

def step (n: Nat): Nat := n + 1

-- A callback that may fail but doesn't.
def checked (n: Nat): {Fail} Nat := if n > 1000000000 then Fail.fail "too big" else n + 1

def viaMap (xs: List Nat): Nat := List.sum (List.map step xs)

def viaMapIn (xs: List Nat): Nat := List.sum (List.mapIn step xs)

def viaFail (xs: List Nat): Nat :=
  match Fail.toResult (() => List.mapIn checked xs) with
    | Ok ys => List.sum ys
    | Err _ => 0

def once (mode: Text) (xs: List Nat): Nat :=
  if mode == "map" then viaMap xs
  else if mode == "mapIn" then viaMapIn xs
  else if mode == "sum" then List.sum xs
  else viaFail xs

def repeat (mode: Text) (xs: List Nat): Nat -> Nat -> Nat
  | 0, total => total
  | Succ k, total => repeat mode xs k (total + once mode xs)

def main(): {IO} () :=
  match Text.words (IO.readAll ()) with
    | [mode, n, rounds] =>
      let xs := List.range (Option.getOrElse 0 n.toNat)
      IO.print (Nat.toText (repeat mode xs (Option.getOrElse 1 rounds.toNat) 0))
    | _ => IO.print "usage: mode n rounds"
