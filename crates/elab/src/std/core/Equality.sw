-- core/Equality.sw. Equality lemmas (`Eq.cong`, `Eq.sym`, `Eq.trans`) and the
-- facts that different constructors are different. Loaded with the core:
-- `calc` and `deriving` write `Eq.sym` and `Eq.trans` in full, and every
-- decision procedure after this uses them (docs/proposals/prelude-slim.md
-- §2.1).

-- Equality lemmas, all built from `J`.

theorem Eq.cong (f: a -> b) [x y: a] (p: x = y): f x = f y := J (y' p' => f x = f y') rfl p

theorem Eq.sym [x y: a] (p: x = y): y = x := J (y' p' => y' = x) rfl p

theorem Eq.trans [x y z: a] (p: x = y) (q: y = z): x = z := J (z' q' => x = z') p q

-- Different constructors are different. Each proof transports along the
-- equation into a family that's `Unit` at one constructor and `Void` at the other.

def Nat.IsZero: Nat -> Prop
  | Zero => Unit
  | Succ n => Void

theorem Nat.zeroNotSucc (n: Nat): Not (0 = Succ n)
  | p => J (y q => Nat.IsZero y) Trivial p

theorem Nat.succNotZero (n: Nat): Not (Succ n = 0)
  | p => Nat.zeroNotSucc n (Eq.sym p)

theorem Nat.succInjective (m: Nat) (n: Nat) (p: Succ m = Succ n): m = n := Eq.cong Nat.pred p

def Bool.IsFalse: Bool -> Prop
  | False => Unit
  | True => Void

theorem Bool.falseNotTrue: Not (False = True)
  | p => J (y q => Bool.IsFalse y) Trivial p

-- Whether two numbers are equal, as a `Bool`.
def Nat.equal: Nat -> Nat -> Bool
  | Zero, Zero => True
  | Zero, Succ n => False
  | Succ m, Zero => False
  | Succ m, Succ n => Nat.equal m n

theorem Nat.equalRefl: (n: Nat) -> Nat.equal n n = True
  | Zero => rfl
  | Succ n => Nat.equalRefl n

-- Numbers that `Nat.equal` says are equal are equal.
theorem Nat.equalSound: (m: Nat) -> (n: Nat) -> Nat.equal m n = True -> m = n
  | Zero, Zero, h => rfl
  | Zero, Succ n, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ m, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ m, Succ n, h => Eq.cong Succ (Nat.equalSound m n h)

-- Numbers that `Nat.equal` says differ are different.
theorem Nat.equalFalse (m: Nat) (n: Nat) (h: Nat.equal m n = False): Not (m = n)
  | p => Bool.falseNotTrue (Eq.trans (Eq.sym h) (J (y q => Nat.equal m y = True) (Nat.equalRefl m) p))
