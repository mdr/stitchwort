--| `Char`: scalar values, conversion to and from `Nat`,
--| extensionality and decidable equality.
-- Loaded with the core: `Char` is pinned by content hash for compact text and
-- the JS backend, and `Text` is a list of them (docs/proposals/prelude-slim.md
-- §2.1).

-- Characters

--| Whether a number is a Unicode scalar value: at most 0x10FFFF, and not a
--| surrogate (0xD800 to 0xDFFF).
def Char.isScalar (n: Nat): Bool := if Nat.leq 55296 n then (if Nat.leq n 57343 then False else Nat.leq n 1114111) else True

--| A Unicode scalar value. `'a'` is a `Char`; the compiler proves `valid` for
--| a literal by computation, and the kernel checks it.
type Char: Type =
  | MkChar (code: Nat) (valid: Char.isScalar code = True)

--| The character's code, its scalar value: `'a'.toNat` is 97.
def Char.toNat: (char: Char) → Nat
  | MkChar n v => n

--| The character with this code, if it is a Unicode scalar value: `Char.fromNat 97` is `Some 'a'`.
def Char.fromNat (n: Nat): Option Char := if h: Char.isScalar n = True then Some (MkChar n h) else None

--| Characters with the same code are equal; the proof of `valid` doesn't matter.
theorem Char.mkExt (a: Nat) (b: Nat) (p: Char.isScalar a = True) (e: a = b):
    (q: Char.isScalar b = True) → MkChar a p = MkChar b q :=
  J (b' e' => (q': Char.isScalar b' = True) → MkChar a p = MkChar b' q') (q' => rfl) e

theorem Char.ext: (x: Char) → (y: Char) → Char.toNat x = Char.toNat y → x = y
  | MkChar a p, MkChar b q, e => Char.mkExt a b p e q

--| A decision whether two characters are equal, from one on their codes.
def Char.decEqFrom (x: Char) (y: Char): (natEq: Decidable (Char.toNat x = Char.toNat y)) → Decidable (x = y)
  | Yes e => Yes (Char.ext x y e)
  | No r => No (p => r (Eq.cong Char.toNat p))

--| Decides whether two characters are equal, by their codes.
def Char.decEq (x: Char) (y: Char): Decidable (x = y) := Char.decEqFrom x y (Nat.decEq (Char.toNat x) (Char.toNat y))
