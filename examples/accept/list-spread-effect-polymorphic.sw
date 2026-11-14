import Std (Vec)

-- `[f x, ..rest]` and `Cons (f x) rest` are the same term, also where the
-- elements run a callback's abilities, so both compile to the same loop.

def mapCons: List a → (f: a → {e} b) → {e} List b
  | [], f => []
  | [x, ..xs], f => Cons (f x) (mapCons xs f)

def mapSpread: List a → (f: a → {e} b) → {e} List b
  | [], f => []
  | [x, ..xs], f => [f x, ..mapSpread xs f]

def takeCons (xs: List a) (p: a → {e} Bool): {e} List a := match xs with
  | [] => []
  | [x, ..ys] => if p x then Cons x (takeCons ys p) else []

def takeSpread (xs: List a) (p: a → {e} Bool): {e} List a := match xs with
  | [] => []
  | [x, ..ys] => if p x then [x, ..takeSpread ys p] else []

def mapPure: List a → (f: a → b) → List b
  | [], f => []
  | [x, ..xs], f => [f x, ..mapPure xs f]

test "same results" := mapSpread [1, 2, 3] (x => x + 1) = mapCons [1, 2, 3] (x => x + 1)

-- A comparison that performs, in a Bool field, is decided (SW-573).
def orNone: Option Text → Text
  | None => "none"
  | Some t => t

def len(): {IO} Nat := (orNone IO.readLine()).length

type Flag = | MkFlag (b: Bool)
type Flags = | MkFlags (n: Nat) (b: Bool)

def flag(): {IO} Flag := MkFlag (len() < 3)
def flags(): {IO} Flags := MkFlags 1 (len() < 3)

-- Likewise where the field's type is a parameter fixed to `Bool` by the
-- expected type.
def someB(): {IO} Option Bool := Some (len() < 3)
def listB(): {IO} List Bool := [len() < 3]
def consB(): {IO} List Bool := Cons (len() < 3) Nil
def vecB(): {IO} Vec Bool 1 := VCons (len() < 3) VNil
