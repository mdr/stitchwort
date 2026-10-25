-- Shared-field access (docs/proposals/variant-fields.md §5): a field name
-- every constructor has, at the same type, is a field of the whole type.
-- The compiler generates `T.f` (one `case`, a branch per constructor), so
-- `a.f`, `.f` sections, pipes, `T.f a` and proofs all work.

import Std (List, Nat, Vec)

type Shape =
  | Dot (ref: Nat) (id: Text) (start: Nat)
  | Circle (ref: Nat) (id: Text) (start: Nat) (text: Text)

def s: Shape := Circle 1 "a" 0 "t"

-- `id` is in both constructors, so `Shape.id: Shape -> Text` exists.
test "dot" := s.id == "a"

-- A `.f` section, handy with `map`.
test "section" := [Dot 1 "p" 0, s].map .id == ["p", "a"]

-- A pipe.
test "pipe" := (s |> .start) == 0

-- The generated function, written in full.
test "full" := Shape.id s == "a"

-- `text` is only `Circle`'s: no `s.text`; match instead (see
-- examples/reject/shared-field-not-in-every-ctor.sw).
def textOf: Shape → Text
  | Circle { text, .. } => text
  | _ => ""

-- The type of a shared field may mention the type's parameters.
type Labelled (a: Type) =
  | One (label: a)
  | Two (x: Nat) (label: a)

test "parameter" := (Two 3 "x").label == "x"

-- Dependent shared fields, declared in different orders in each constructor.
type Sized =
  | A (n: Nat) (xs: Vec Nat n) (tag: Text)
  | B (tag: Text) (n: Nat) (xs: Vec Nat n)

def xsOf (t: Sized): Vec Nat t.n := t.xs

test "dependent" := (A 2 (VCons 1 (VCons 2 VNil)) "q").n == 2
test "dependent, other order" := (B "q" 0 VNil).tag == "q"

-- Proofs: by `rfl` on a constructor...
theorem idCircle: (Circle 1 "a" 0 "t").id = "a" := rfl

-- ...and by cases, against a hand-written function.
def idOf: Shape → Text
  | Dot { id, .. } => id
  | Circle { id, .. } => id

theorem idIsIdOf (a: Shape): a.id = idOf a := match a with
  | Dot { .. } => rfl
  | Circle { .. } => rfl

theorem idFull (a: Shape): a.id = Shape.id a := rfl

-- A proposition's shared field: both constructors hold a proof of `q`.
type Evidence (q: Prop): Prop =
  | EA (witness: q)
  | EB (witness: q)

def ev (e: Evidence (1 = 1)): 1 = 1 := e.witness

-- An indexed family gets accessors by the same rule.
type Fam: Nat → Type =
  | FA (tag: Text): Fam 0
  | FB [n: Nat] (tag: Text) (xs: Fam n): Fam (Succ n)

def tagOf (f: Fam m): Text := f.tag

test "indexed" := tagOf (FB "b" (FA "a")) == "b"

theorem tagFB: (FB "b" (FA "a")).tag = "b" := rfl

-- One-constructor types have them too: `Pair.fst`, `And.left`.
test "pair" := (1, "x").fst == 1

-- When `id` is not shared (different types), a written `V.id` is allowed,
-- and dot notation finds it.
type V =
  | VA (id: Nat)
  | VB (id: Text)

def V.id: V → Text
  | VA _ => "a"
  | VB t => t

def vid (v: V): Text := v.id

test "written" := vid (VB "x") == "x"
