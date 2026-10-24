-- A lambda may bind implicit and `auto` parameters, written as a header
-- writes them: `[a: Type] => …`, `[auto h: P] => …`
-- (docs/proposals/lambda-syntax.md §4.3, D91). Checked against a function
-- type, each takes the parameter of its own kind, by its own name.

import Std (List, Ord)

-- The body names the implicit parameter the lambda binds.
def idf: [a: Type] -> a -> a := [a: Type] => (x: a) => x

-- Several, side by side or grouped, mixed with explicit parameters.
def first: [a: Type] -> [b: Type] -> a -> b -> a := [a: Type] [b: Type] (x: a) (y: b) => x

def firstGrouped: [a b: Type] -> a -> b -> a := [a b: Type] (x: a) (y: b) => x

-- An `auto` parameter, named or not.
def larger: [a: Type] -> [auto order: Ord a] -> a -> a -> a :=
  [a: Type] [auto order: Ord a] (x: a) (y: a) => if x <= y then y else x

def atMost: [a: Type] -> [auto Ord a] -> a -> a -> Bool :=
  [a: Type] [auto Ord a] (x: a) (y: a) => x <= y

-- Without `[…]`, the implicit parameter is introduced for the lambda, as
-- before: in a definition by its signature, which puts `a` in scope ...
def silent: [a: Type] -> a -> a := (x: a) => x

-- After an explicit parameter.
def constant: Nat -> [a: Type] -> a -> Nat := n => [a: Type] (x: a) => n

test "checked" :=
  idf 3 == 3
    && first 1 True == 1
    && firstGrouped "x" 2 == "x"
    && larger 3 7 == 7
    && atMost 9 2 == False
    && silent 4 == 4
    && constant 5 "five" == 5

-- No expected type: the lambda's type is inferred, with an implicit
-- parameter, and each use fills it in.
test "inferred" :=
  let pick := [a: Type] (x: a) (y: a) => x
  pick 1 2 == 1 && pick "a" "b" == "a"

-- Applied on the spot: the implicit argument is filled in.
test "applied" := ([a: Type] (x: a) => x) 4 == 4

-- Passed where a polymorphic function is expected.
def twice (f: [a: Type] -> a -> a): (Nat, Text) := (f 1, f "one")

test "passed" := twice ([a: Type] (x: a) => x) == (1, "one")

-- ... and elsewhere under a name the lambda can't use.
test "passed without the parameter" := twice (x => x) == (1, "one")
