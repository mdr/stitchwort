namespace Day

import Lib (..)
import Twin (..)
import Other (count)

def size(): Nat := 100

def pick: Option -> Nat
  | Nope => 0
  | Yep n => n

-- Own beats a wildcard, with no clash.
test "own" := size() == 100
-- A named import beats a wildcard.
test "named" := count() == 20
-- From Lib's other file.
test "other file" := only() == 5
-- A wildcard name beats the default `not`.
test "default" := not 1 == 11
-- The wildcard `Option` and its constructors beat the default `Option`.
test "type" := pick (Yep 3) == 3
-- `shared` is in both `(..)` imports, which is fine until it is used bare.
test "both" := Lib.shared() + Twin.shared() == 33
