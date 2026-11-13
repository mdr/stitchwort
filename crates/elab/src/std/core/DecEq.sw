--| The `DecEq` interface, its instances for the core types, and
--| the uniqueness of equality proofs it gives.
-- Loaded with the core: `==`, `!=`, `if h: x = y` and `auto` deciding an
-- equation all use `DecEq` instances, found by full key
-- (docs/proposals/prelude-slim.md §2.1).

-- Decidable equality (docs/proposals/interfaces.md §6.1): `a == b`,
-- `a != b`, `if h: a = b` and `auto` deciding an equation all use the
-- `DecEq` instance for the type. A data type or record declared in a
-- program gets one derived, when it can (`T.%instDecEq`).

--| Types whose values can be compared for equality, with a proof: what `==`,
--| `!=` and `if h: a = b` use.
interface DecEq (a: Type) =
  { decide: (x: a) → (y: a) → Decidable (x = y) }

instance Nat.instDecEq: DecEq Nat := { decide = Nat.decEq }

instance Int.instDecEq: DecEq Int := { decide = Int.decEq }

instance Bool.instDecEq: DecEq Bool := { decide = Bool.decEq }

instance Char.instDecEq: DecEq Char := { decide = Char.decEq }

instance Text.instDecEq: DecEq Text := { decide = Text.decEq }

instance Ordering.instDecEq: DecEq Ordering := { decide = Ordering.decEq }

--| `()` has one value, so any two are equal.
def Builtin.UnitType.decEq: (x: Builtin.UnitType) → (y: Builtin.UnitType) → Decidable (x = y)
  | Builtin.UnitType.UnitValue, Builtin.UnitType.UnitValue => Decidable.yes rfl

instance Builtin.UnitType.instDecEq: DecEq Builtin.UnitType := { decide = Builtin.UnitType.decEq }

instance List.instDecEq [auto decEq: DecEq a]: DecEq (List a) :=
  { decide = List.decEq (x y => DecEq.decide x y) }

instance Pair.instDecEq [auto decEqA: DecEq a] [auto decEqB: DecEq b]: DecEq (Pair a b) :=
  { decide = Pair.decEq (x y => DecEq.decide x y) (x y => DecEq.decide x y) }

instance Option.instDecEq [auto decEq: DecEq a]: DecEq (Option a) :=
  { decide = Option.decEq (x y => DecEq.decide x y) }

instance Result.instDecEq [auto decEqA: DecEq a] [auto decEqE: DecEq e]: DecEq (Result a e) :=
  { decide = Result.decEq (x y => DecEq.decide x y) (x y => DecEq.decide x y) }

--| Proofs of an equation in a type with decidable equality are unique
--| ([`Decidable.uniqueEq`], Hedberg's argument).
theorem DecEq.uniqueEq ∀ [auto decEq: DecEq a] [x y: a] (p: x = y) (q: x = y): p = q :=
  Decidable.uniqueEq (DecEq.decide [decEq := decEq]) x y p q
