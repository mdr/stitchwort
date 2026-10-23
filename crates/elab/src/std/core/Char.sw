-- core/Char.sw. `Char`: scalar values, conversion to and from `Nat`,
-- extensionality and decidable equality. Loaded with the core: `Char` is
-- pinned by content hash for compact text and the JS backend, and `Text` is a
-- list of them (docs/proposals/prelude-slim.md §2.1).

-- Characters

-- Whether a number is a Unicode scalar value: at most 0x10FFFF, and not a
-- surrogate (0xD800 to 0xDFFF).
def Char.isScalar (n: Nat): Bool := if Nat.leq 55296 n then (if Nat.leq n 57343 then False else Nat.leq n 1114111) else True

-- A Unicode scalar value. `'a'` is a `Char`; the compiler proves `valid` for
-- a literal by computation, and the kernel checks it.
type Char: Type =
  | MkChar (code: Nat) (valid: Char.isScalar code = True)

def Char.toNat: Char -> Nat
  | MkChar n v => n

def Char.fromNat (n: Nat): Option Char := if h: Char.isScalar n = True then Some (MkChar n h) else None

-- Characters with the same code are equal: their proofs of `valid` are too.
theorem Char.mkExt (a: Nat) (b: Nat) (p: Char.isScalar a = True) (e: a = b):
    (q: Char.isScalar b = True) -> MkChar a p = MkChar b q :=
  J (b' e' => (q': Char.isScalar b' = True) -> MkChar a p = MkChar b' q')
    (q' => J (r e'' => MkChar a p = MkChar a r) rfl (Bool.uniqueEq (Char.isScalar a) True p q'))
    e

theorem Char.ext: (x: Char) -> (y: Char) -> Char.toNat x = Char.toNat y -> x = y
  | MkChar a p, MkChar b q, e => Char.mkExt a b p e q

def Char.decEqFrom (x: Char) (y: Char): Decidable (Char.toNat x = Char.toNat y) -> Decidable (x = y)
  | Yes e => Yes (Char.ext x y e)
  | No r => No (p => r (Eq.cong Char.toNat p))

def Char.decEq (x: Char) (y: Char): Decidable (x = y) := Char.decEqFrom x y (Nat.decEq (Char.toNat x) (Char.toNat y))
