-- Effect-polymorphic functions used purely and effectfully
-- (docs/proposals/effect-polymorphism.md, design E). A pure use passes the
-- empty row, and the generated JS calls the function's empty-row variant:
-- `List.mapIn` at the empty row is the same loop as `List.map`, with no row
-- passed and no test of one, so it handles 100,000 elements without running
-- out of Node's default stack. An effectful use calls the generic code.
--
-- run: doubled [1, 2, 3]
-- run: doubled []
-- run: mappedSum 100000
-- run: mapInSum 100000
-- run: doubledEach [[1, 2], [], [3]]
-- run: twiceDoubled 5
-- run: parsed ["1", "22", "333"]
-- run: parsed ["1", "x", "333"]
-- run: parsed []
-- run: counted [4, 5, 6]
import Std (List, Nat, Fail, Result, Text)

def double (n: Nat): Nat := n + n

def sum (xs: List Nat): Nat := List.foldLeft (a x => a + x) 0 xs

-- Pure uses of `List.mapIn`: directly, and as a value with its row given.
export def doubled (xs: List Nat): List Nat := List.mapIn double xs

export def mappedSum (n: Nat): Nat := sum (List.map (x => x + 1) (List.range n))

export def mapInSum (n: Nat): Nat := sum (List.mapIn (x => x + 1) (List.range n))

export def doubledEach (xss: List (List Nat)): List (List Nat) := List.map (List.mapIn double) xss

-- A program's own effect-polymorphic function, used purely.
def twice (f: a -> {e} a) (x: a): {e} a := f (f x)

export def twiceDoubled (n: Nat): Nat := twice double n

-- An effectful use: the callback may fail, and the handler's remaining row
-- is empty.
def parse (text: Text): {Fail} Nat := Fail.need text.toNat "not a number: ${text}"

export def parsed (texts: List Text): Result (List Nat) Text :=
  Fail.toResult (() => List.mapIn parse texts)

-- A handler with an open row, used at the empty row.
ability Count where
  count: () -> {Count} ()

def countAll (prog: () -> {Count | e} a): {e} Pair a Nat :=
  let run: Nat -> {e} Pair a Nat :=
    handle prog() with
      | return x => n => MkPair x n
      | count u, k => n => k () (n + 1)
  run 0

def tally (x: Nat): {Count} Nat :=
  count ()
  x

export def counted (xs: List Nat): Pair (List Nat) Nat := countAll (() => List.mapIn tally xs)
