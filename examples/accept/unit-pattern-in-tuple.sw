-- `()` inside a pattern, where what it matches is `()`, is the unit
-- pattern, as `let () := e` on its own is: in a `let`, a `match` arm, an
-- equation, a lambda's parameter, and nested (SW-886). At a type with no
-- values it is still the absurd pattern.
import Std (List, Parse)
import Std.Parse (char, natDigits)

def second (p: ((), Nat)): Nat :=
  let ((), n) := p
  n

def first (p: (Nat, ())): Nat :=
  let (n, ()) := p
  n

def nested (p: (Nat, ((), Nat))): Nat :=
  let (a, ((), b)) := p
  a + b

def arms (p: (Bool, ())): Nat := match p with
  | (True, ()) => 1
  | (False, ()) => 0

def equations: (Nat, ()) → Nat
  | (n, ()) => n

def viaLambda (ps: List ((), Nat)): List Nat := ps.map (((), n) => n)

theorem secondIs: second ((), 3) = 3 := rfl

theorem nestedIs: nested (1, ((), 2)) = 3 := rfl

theorem armsIs: arms (True, ()) = 1 := rfl

theorem equationsIs: equations (4, ()) = 4 := rfl

-- An effectful tuple whose first part is a parser that gives `()`.
def afterComma(): {Parse} Nat :=
  let ((), n) := (char ',', natDigits 1 3)
  n

-- The absurd pattern is unchanged.
type Empty: Type

def noValues: (Nat, Empty) → Nat
  | (_, ())
