-- An unknown lowercase name used as the whole argument of a type, for a
-- parameter that's a value, is bound automatically as an implicit (Idris's
-- way), its type taken from the parameter's: `Dial highest` binds
-- `[highest: Nat]`.

type Dial (highest: Nat) = { position: Nat, inRange: position <= highest }

def Dial.top (d: Dial highest): Nat := highest

def small: Dial 9 := { position = 3, inRange = rfl }

theorem topExample: Dial.top small = 9 := rfl

-- In a header parameter and the result alike, and in a function type.
def Dial.reset (d: Dial highest): Dial highest := { position = 0, inRange = rfl }

def Dial.apply (d: Dial highest) (f: Dial highest -> Dial highest): Nat := (f d).position

theorem applyExample: Dial.apply small Dial.reset = 0 := rfl

-- Two value parameters, of different types, bound in order of first use.
type Grid (width: Nat) (wrap: Bool) = { cells: List Nat }

def Grid.size (g: Grid w b): Nat := if b then w + 1 else w

def grid: Grid 4 True := { cells = [] }

theorem sizeExample: Grid.size grid = 5 := rfl

-- Named explicitly, in the bound order.
theorem sizeNamed: Grid.size [w := 4] [b := False] { cells = [] } = 4 := rfl

-- A dependent use: the value's type is another auto-bound name.
type Tagged (a: Type) (tag: a) = { payload: Nat }

def Tagged.tag (t: Tagged a x): a := x

def tagged: Tagged Bool True := { payload = 1 }

theorem tagExample: Tagged.tag tagged = True := rfl

-- A definition whose result is a type takes a value argument the same way.
def Below (n: Nat): Type := Dial n

def Below.top (d: Below n): Nat := n

theorem belowExample: Below.top small = 9 := rfl

-- In a local definition's signature.
def twice (d: Dial highest): Nat :=
  def double (e: Dial h): Nat := h + h
  double d

theorem twiceExample: twice small = 18 := rfl
