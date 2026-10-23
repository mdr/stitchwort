-- Named construction (docs/proposals/variant-fields.md §4.5):
-- `C { f = e, g }` builds a `C` by field name. It is the positional
-- application `C e …` with the fields in declaration order: the same term.

import Std (Eq, Int, IO, List, Nat, Option, Pair)

type Shape =
  | Dot (ref: Nat) (id: Text)
  | Circle (ref: Nat) (id: Text) (text: Text)

type Item = { name: Text, price: Nat }

type Vec (a: Type): Nat -> Type =
  | VNil: Vec a 0
  | VCons [n: Nat] (x: a) (xs: Vec a n): Vec a (Succ n)

type Pos = | MkPos (n: Nat) (ok: 0 < n)

type Box (a: Type) = | MkBox (inner: a) (label: Text)

-- Fields come in any order; a bare field is punned (`id` is `id = id`).
def circle (id: Text): Shape := Circle { text = "t", id, ref = 1 }

def idOf: Shape -> Text
  | Dot { id, .. } => id
  | Circle { id, .. } => id

test "any order is the positional form" :=
  Circle { text = "t", id = "a", ref = 1 } == Circle 1 "a" "t"

theorem sameTerm: Circle { id = "a", text = "t", ref = 1 } = Circle 1 "a" "t" := rfl

test "punning" := idOf (circle "z") == "z"

-- An implicit field is filled by unification, as in `VCons 1 VNil`.
def one: Vec Int 1 := VCons { x = 1, xs = VNil }

-- A proof field is an explicit field: it is given.
def three: Pos := MkPos { n = 3, ok = omega }

-- A parameterised type; fields nest.
def boxed: Box (Option Shape) :=
  MkBox { label = "b", inner = Some { value = Dot { id = "d", ref = 0 } } }

test "nesting" :=
  (match boxed.inner with
    | Some s => idOf s
    | None => "") == "d"

-- A record argument: in brackets, or by the constructor's field name.
def tea: Option Item := Some ({ name = "tea", price = 3 })
def coffee: Option Item := Some { value = { name = "coffee", price = 4 } }

test "a record argument both ways" :=
  (tea == Some ({ name = "tea", price = 3 }))
    && (coffee == Some { value = { name = "coffee", price = 4 } })

-- A field access on the result.
test "field access" := (Circle { ref = 1, id = "a", text = "t" }).id == "a"

-- Field expressions run in the order written.
def orNone: Option Text -> Text
  | None => "none"
  | Some t => t

def next(): {IO} Text := orNone IO.readLine()

def read(): {IO} Shape := Circle { text = next(), ref = 1, id = next() }

test "effects run in the order written" :=
  idOf (Pair.snd (IO.simulate ["1", "2"] read)) == "2"
