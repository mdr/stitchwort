-- The checker binds an argument to a variable instead of computing it, when
-- the type it's working out doesn't depend on it
-- (docs/proposals/checker-evaluation.md, option (a)). These are the cases
-- where it can't, and falls back to computing the value as before.

-- An operation whose result type depends on its argument.
def Payload: Nat -> Type
  | 0 => Nat
  | _ => Text

ability Fetch where
  fetch: (n: Nat) -> {Fetch} Payload n

def width (xs: List Nat): Nat := List.length xs

def fetchText(): {Fetch} Text := fetch (width [1, 2, 3])

def fetchNat(): {Fetch} Nat := fetch (width [])

-- A decision procedure that only applies to particular values: it decides
-- `f = f`, so with the two sides as separate variables it doesn't fit, and
-- the search is made again with their values.
type Fun = | MkFun (apply: Nat -> Nat)

def decSelf (f: Fun): Decidable (f = f) := Yes rfl

def adder (n: Nat): Fun := MkFun (x => x + n)

def same: Bool := adder 1 == adder 1

def sameIf: Nat := if adder 2 == adder 2 then 1 else 0

test "found with the values" := same && sameIf == 1
