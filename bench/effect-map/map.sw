-- Benchmark: `List.map` with a pure callback and with an effectful one
-- (docs/proposals/effect-polymorphism.md, stages 2 and 3; before stage 3 the
-- effect-polymorphic map was `List.mapIn`, measured here as mode `mapIn`).
-- Reads `mode n rounds` from standard input, where `mode` is `map`, `fail`,
-- `sum` (the sum alone, which the others include), or one of the other
-- effect-polymorphic list functions with a pure callback (effect-polymorphic-list.md):
-- `filter` (then the sum), `fold` (a `foldLeft`) or `any` (which never
-- finds one, so it visits every element); prints a checksum. Run
-- with
--   echo "map 1000000 10" | stitchwort run bench/effect-map/map.sw [--js]
import Std (List, Fail, Text, Option, Nat)

def step (n: Nat): Nat := n + 1

-- A callback that may fail but doesn't.
def checked (n: Nat): {Fail} Nat := if n > 1000000000 then Fail.fail "too big" else n + 1

def viaMap (xs: List Nat): Nat := List.sum (List.map xs step)

def isEven (n: Nat): Bool := n % 2 == 0

def addTwice (total: Nat) (n: Nat): Nat := total + n + n

def isHuge (n: Nat): Bool := n > 1000000000

def viaFilter (xs: List Nat): Nat := List.sum (List.filter xs isEven)

def viaFold (xs: List Nat): Nat := List.foldLeft xs 0 addTwice

def viaAny (xs: List Nat): Nat := if List.any xs isHuge then 1 else 2

def viaFail (xs: List Nat): Nat :=
  match Fail.toResult (() => List.map xs checked) with
    | Ok ys => List.sum ys
    | Err _ => 0

def once (mode: Text) (xs: List Nat): Nat :=
  if mode == "map" then viaMap xs
  else if mode == "sum" then List.sum xs
  else if mode == "filter" then viaFilter xs
  else if mode == "fold" then viaFold xs
  else if mode == "any" then viaAny xs
  else viaFail xs

def repeat (mode: Text) (xs: List Nat): Nat -> Nat -> Nat
  | 0, total => total
  | Succ k, total => repeat mode xs k (total + once mode xs)

def main(): {IO} () :=
  match Text.words (IO.readAll ()) with
    | [mode, n, rounds] =>
      let xs := List.range (Option.getOrElse n.toNat 0)
      IO.print (Nat.toText (repeat mode xs (Option.getOrElse rounds.toNat 1) 0))
    | _ => IO.print "usage: mode n rounds"
