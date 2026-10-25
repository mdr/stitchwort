-- core/AddMul.sw. The `Add` and `Mul` interfaces and their instances for
-- `Nat` and `Int`. Loaded with the core: `+` and `*` go through `Add` and
-- `Mul` dictionaries, so they are checked before any program that adds two
-- numbers (docs/proposals/prelude-slim.md §2.1).

-- Things you can add, starting from zero, in any order (a commutative
-- monoid): what `+` means, for every type (docs/proposals/interfaces.md
-- §6.3, §5.13).
interface Add (a: Type) = {
  zero: a,
  add: a → a → a,
  zeroAdd: (x: a) → add zero x = x,
  assoc: (x: a) → (y: a) → (z: a) → add (add x y) z = add x (add y z),
  comm: (x: a) → (y: a) → add x y = add y x
}

-- Things you can multiply, starting from one (a monoid; not commutative):
-- what `*` means.
interface Mul (a: Type) = {
  one: a,
  mul: a → a → a,
  oneMul: (x: a) → mul one x = x,
  mulOne: (x: a) → mul x one = x,
  assoc: (x: a) → (y: a) → (z: a) → mul (mul x y) z = mul x (mul y z)
}

-- The bootstrap phase ends here (D187): from now on `+`, `*`, `<` and `<=`
-- on `Nat` and `Int` mean these dictionaries' fields, which are the
-- operations above, so the terms are the same.
instance Nat.instAdd: Add Nat :=
  { zero = 0, add = Nat.add, zeroAdd = x => rfl, assoc = Nat.addAssoc, comm = Nat.addComm }

instance Nat.instMul: Mul Nat :=
  { one = 1, mul = Nat.mul, oneMul = Nat.oneMul, mulOne = Nat.mulOne, assoc = Nat.mulAssoc }

instance Int.instAdd: Add Int :=
  { zero = OfNat 0, add = Int.add, zeroAdd = Int.zeroAdd, assoc = Int.addAssoc, comm = Int.addComm }

instance Int.instMul: Mul Int :=
  { one = OfNat 1, mul = Int.mul, oneMul = Int.oneMul, mulOne = Int.mulOne, assoc = Int.mulAssoc }
