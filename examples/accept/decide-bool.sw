-- A proposition with a decision procedure can be used where a `Bool` is
-- expected: it's decided (`Decidable.toBool` of its decision), as Lean's
-- `decide` coercion does.

def small (k: Nat) (size: Nat) (xs: List Nat): List Nat :=
  xs.filter (n => k * n <= size)

theorem smallExample: small 2 10 [1, 5, 6, 2] = [1, 5, 2] := rfl

def allSmall (xs: List Nat): Bool := xs.all (< 10)

theorem allSmallYes: allSmall [1, 2, 9] = True := rfl
theorem allSmallNo: allSmall [1, 20] = False := rfl

-- An `Int` comparison, and an equation.
def negatives (xs: List Int): List Int := xs.filter (< 0)

theorem negativesExample: negatives [3, -1, 0, -7] = [-1, -7] := rfl

def threes (xs: List Nat): List Nat := xs.filter (n => n = 3)

theorem threesExample: threes [3, 4, 3] = [3, 3] := rfl

-- A definition whose type is a proposition, applied.
def IsSmall (n: Nat): Prop := n < 10

def keepSmall (xs: List Nat): List Nat := xs.filter (n => IsSmall n)

theorem keepSmallExample: keepSmall [3, 30] = [3] := rfl

-- A body, a branch and an argument, each expecting a `Bool`.
def le (a: Nat) (b: Nat): Bool := a <= b

theorem leExample: le 2 3 = True := rfl

def pick (b: Bool) (n: Nat): Bool := if b then n < 5 else n = 0

theorem pickExample: pick True 3 = True := rfl

def both (a: Bool) (b: Bool): Bool := a && b

theorem bothExample: both (1 < 2) (3 = 3) = True := rfl

-- `if` and `&&` still take a proposition as they did.
def clamp (n: Nat): Nat := if n < 10 && n != 3 then n else 0

theorem clampExample: clamp 3 = 0 := rfl
