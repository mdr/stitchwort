-- Effect-polymorphic functions used purely and effectfully
-- (docs/proposals/effect-polymorphism.md, design E). A pure use passes the
-- empty row, and the generated JS calls the function's empty-row variant:
-- `List.map` at the empty row is the tail-recursion-modulo-cons loop, with no
-- row passed and no test of one, so it handles 100,000 elements without
-- running out of Node's default stack. An effectful use calls the generic
-- code.
--
-- run: doubled [1, 2, 3]
-- run: doubled []
-- run: mappedSum 100000
-- run: pureDoubled [1, 2, 3]
-- run: doubledEach [[1, 2], [], [3]]
-- run: twiceDoubled 5
-- run: parsed ["1", "22", "333"]
-- run: parsed ["1", "x", "333"]
-- run: parsed []
-- run: counted [4, 5, 6]
import Std (List, Nat, Fail, Result, Text)

def double (n: Nat): Nat := n + n

def sum (xs: List Nat): Nat := List.foldLeft xs 0 (a x => a + x)

-- Pure uses of `List.map`: directly, and partially applied as a callback.
export def doubled (xs: List Nat): List Nat := List.map xs double

export def mappedSum (n: Nat): Nat := sum (List.map (List.range n) (x => x + 1))

-- A map with a pure callback type, as `List.map` was before it took effects:
-- `List.map`'s empty-row variant is the same loop.
def pureMap: List a -> (a -> b) -> List b
  | Nil, f => Nil
  | Cons x xs, f => Cons (f x) (pureMap xs f)

export def pureDoubled (xs: List Nat): List Nat := pureMap xs double

export def doubledEach (xss: List (List Nat)): List (List Nat) := List.map xss (.map double)

-- A program's own effect-polymorphic function, used purely.
def twice (f: a -> {e} a) (x: a): {e} a := f (f x)

export def twiceDoubled (n: Nat): Nat := twice double n

-- An effectful use: the callback may fail, and the handler's remaining row
-- is empty.
def parse (text: Text): {Fail} Nat := Fail.need text.toNat "not a number: ${text}"

export def parsed (texts: List Text): Result (List Nat) Text :=
  Fail.toResult (() => List.map texts parse)

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

export def counted (xs: List Nat): Pair (List Nat) Nat := countAll (() => List.map xs tally)
