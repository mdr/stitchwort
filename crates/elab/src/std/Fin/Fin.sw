-- `Fin n`: the numbers below n, as an indexed data type (Agda's and Idris's
-- `Fin`). A value of `Fin n` is a position in a `Vec a n`, so `Vec.get` needs
-- no bound proof: the type of the index is the proof. `Fin.ofNatLt` and
-- `Fin.toNat` convert to and from a `Nat` with its bound.

type Fin: Nat -> Type =
  | FZero: Fin (Succ n)
  | FSucc (i: Fin n): Fin (Succ n)

-- The number itself: `FSucc FZero` is 1.
def Fin.toNat: Fin n -> Nat
  | FZero   => 0
  | FSucc i => Succ (Fin.toNat i)

theorem Fin.toNatLt: (i: Fin n) -> Fin.toNat i < n
  | FZero   => rfl
  | FSucc i => Fin.toNatLt i

-- `i` as a position below n, from a proof that it is one.
def Fin.ofNatLt: (n: Nat) -> (i: Nat) -> i < n -> Fin n
  | Zero,   i,      h => Void.absurd (Bool.falseNotTrue h)
  | Succ n, Zero,   h => FZero
  | Succ n, Succ i, h => FSucc (Fin.ofNatLt n i h)

-- `Fin.ofNat i` when `i < n` is decided for closed numbers: `(Fin.ofNat 2: Fin 5)`.
def Fin.ofNat (i: Nat) [auto ok: i < n]: Fin n := Fin.ofNatLt n i ok

theorem Fin.toNatOfNatLt: (n: Nat) -> (i: Nat) -> (h: i < n) -> Fin.toNat (Fin.ofNatLt n i h) = i
  | Zero,   i,      h => Void.exfalso (Bool.falseNotTrue h)
  | Succ n, Zero,   h => rfl
  | Succ n, Succ i, h => Eq.cong Succ (Fin.toNatOfNatLt n i h)

theorem Fin.ofNatExample: Fin.toNat (Fin.ofNat 3: Fin 5) = 3 := rfl

test "toNat" := Fin.toNat (FSucc (FSucc FZero): Fin 4) == 2
test "ofNat" := Fin.toNat (Fin.ofNat 4: Fin 5) == 4
