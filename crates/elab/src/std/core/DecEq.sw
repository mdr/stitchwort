-- core/DecEq.sw. The `DecEq` interface, its instances for the core types, and
-- the uniqueness of equality proofs it gives. Loaded with the core: `==`,
-- `!=`, `if h: x = y` and `auto` deciding an equation all use `DecEq`
-- instances, found by full key (docs/proposals/prelude-slim.md §2.1).

-- Decidable equality (docs/proposals/interfaces.md §6.1): `a == b`,
-- `a != b`, `if h: a = b` and `auto` deciding an equation all use the
-- `DecEq` instance for the type. A data type or record declared in a
-- program gets one derived, when it can (`T.%instDecEq`).

interface DecEq (a: Type) =
  { decide: (x: a) -> (y: a) -> Decidable (x = y) }

instance Nat.instDecEq: DecEq Nat := { decide = Nat.decEq }

instance Int.instDecEq: DecEq Int := { decide = Int.decEq }

instance Bool.instDecEq: DecEq Bool := { decide = Bool.decEq }

instance Char.instDecEq: DecEq Char := { decide = Char.decEq }

instance Text.instDecEq: DecEq Text := { decide = Text.decEq }

instance Ordering.instDecEq: DecEq Ordering := { decide = Ordering.decEq }

instance List.instDecEq [auto decEq: DecEq a]: DecEq (List a) :=
  { decide = List.decEq (x y => DecEq.decide x y) }

instance Pair.instDecEq [auto decEqA: DecEq a] [auto decEqB: DecEq b]: DecEq (Pair a b) :=
  { decide = Pair.decEq (x y => DecEq.decide x y) (x y => DecEq.decide x y) }

instance Option.instDecEq [auto decEq: DecEq a]: DecEq (Option a) :=
  { decide = Option.decEq (x y => DecEq.decide x y) }

instance Result.instDecEq [auto decEqA: DecEq a] [auto decEqE: DecEq e]: DecEq (Result a e) :=
  { decide = Result.decEq (x y => DecEq.decide x y) (x y => DecEq.decide x y) }

-- Proofs of an equation in a type with decidable equality are unique:
-- Hedberg's argument, as for `Bool` above. `DecEq.canon` turns any proof of
-- `x = y` into the one the decision gives, ignoring which proof it was
-- given, and every proof can be recovered from its canonical one.
def DecEq.canon: [x y: a] -> Decidable (x = y) -> x = y -> x = y
  | Yes e, p => e
  | No r, p => Void.exfalso (r p)

theorem DecEq.canonConst: [x y: a] -> (d: Decidable (x = y)) -> (p: x = y) -> (q: x = y) ->
    DecEq.canon d p = DecEq.canon d q
  | Yes e, p, q => rfl
  | No r, p, q => Void.exfalso (r p)

theorem DecEq.symThenSelf [x y: a] (q: x = y): rfl = Eq.trans (Eq.sym q) q := J (y' q' => rfl = Eq.trans (Eq.sym q') q') rfl q

theorem DecEq.fromCanon [auto decEq: DecEq a] (x: a) (y: a) (p: x = y):
    p = Eq.trans (Eq.sym (DecEq.canon (DecEq.decide [decEq := decEq] x x) rfl)) (DecEq.canon (DecEq.decide [decEq := decEq] x y) p) :=
  J (y' p' => p' = Eq.trans (Eq.sym (DecEq.canon (DecEq.decide [decEq := decEq] x x) rfl)) (DecEq.canon (DecEq.decide [decEq := decEq] x y') p'))
    (DecEq.symThenSelf (DecEq.canon (DecEq.decide [decEq := decEq] x x) rfl)) p

theorem DecEq.uniqueEq [auto decEq: DecEq a] [x y: a] (p: x = y) (q: x = y): p = q :=
  J (z e => p = z)
    (J (r e => p = Eq.trans (Eq.sym (DecEq.canon (DecEq.decide [decEq := decEq] x x) rfl)) r)
      (DecEq.fromCanon x y p) (DecEq.canonConst (DecEq.decide [decEq := decEq] x y) p q))
    (J (z e => z = q) rfl (DecEq.fromCanon x y q))
