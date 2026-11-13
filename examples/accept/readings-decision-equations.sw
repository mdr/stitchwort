-- `==` on a list, a `Text`, a tuple or an `Option` reads as `=` (and `!=`
-- or `= False` as `≠`), whether or not the two sides are constructors:
-- the reader takes the equation the decision decides, not the test it
-- computes to one step in (`&&` of the heads and the tails for two
-- non-empty lists, the equation of the characters for a `Text`)
-- (docs/proposals/bool-as-proposition.md §5.4).
import Std (Bool, Char, DecEq, Decidable, Eq, Nat, Option, Text, Witness)

theorem lists ∀ (xs ys: List Char) (h: (xs == ys) = True): xs = ys := h.read

theorem listsApart ∀ (xs ys: List Nat) (h: (xs == ys) = False): xs ≠ ys := h.read

theorem listsApartApplied ∀ (xs ys: List Nat) (h: (xs == ys) = False) (e: xs = ys): Void := h.read e

theorem listTail ∀ (chars: List Char) (h: (chars.drop 2 == ['c', 'm']) = True): chars.drop 2 = ['c', 'm'] := h.read

theorem conses ∀ (x y: Nat) (xs ys: List Nat) (h: ([x, ..xs] == [y, ..ys]) = True): [x, ..xs] = [y, ..ys] := h.read

theorem consesApart ∀ (x y: Nat) (xs ys: List Nat) (h: ([x, ..xs] == [y, ..ys]) = False): [x, ..xs] ≠ [y, ..ys] := h.read

theorem consesSwap ∀ (x y: Nat) (xs ys: List Nat) (h: ([x, ..xs] == [y, ..ys]) = True): [y, ..ys] = [x, ..xs] :=
  Eq.sym h.read

theorem texts ∀ (p q: Text) (h: (p == q) = True): p = q := h.read

theorem textsApart ∀ (p q: Text) (h: (p == q) = False): p ≠ q := h.read

theorem textOfChars ∀ (chars: List Char) (q: Text) (h: (Text.fromList chars == q) = True): Text.fromList chars = q := h.read

theorem pairs ∀ (x y: Nat) (p q: (Nat, Nat)) (h: ((x, p) == (y, q)) = True): (x, p) = (y, q) := h.read

theorem options ∀ (a b: Option Nat) (h: (a == b) = True): a = b := h.read

type Pos = { row: Nat, col: Nat }

-- The decision of the whole `Option`, not of the `Pos` inside it (which is
-- what `Some a == Some b` computes to), and not a field at a time.
theorem optionOfRecord ∀ (a b: Pos) (h: (Some a == Some b) = True): Some a = Some b := h.read

theorem inALambda ∀ (xs: List Pos) (t: Pos) (found: xs.any (p => Some p == Some t) = True): ∃ (p: Pos) => Some p = Some t :=
  let Witness p (Both _ same) := found
  Witness p same.read

theorem natInALambda ∀ (xs: List Nat) (t: Nat) (found: xs.any (x => x == t) = True): ∃ (x: Nat) => x = t :=
  let Witness x (Both _ same) := found
  Witness x same.read

theorem optionOfList ∀ (xs ys: List Nat) (h: (Some xs == Some ys) = True): Some xs = Some ys := h.read

theorem optionOfListsOfTexts ∀ (xs ys: List Text) (h: (Some xs == Some ys) = False): Some xs ≠ Some ys := h.read

theorem character ∀ (c: Char) (h: (c == 'a') = True): c = 'a' := h.read

theorem characterApart ∀ (c: Char) (h: (c == 'a') = False): c ≠ 'a' := h.read

theorem swapped ∀ (xs ys: List Nat) (h: (ys == xs) = True): ys = xs := h.read

-- A hand-written instance, by cases: its `==` reads as the equation too.
type Light = | Red | Green

def Light.isRed: Light → Bool
  | Red => True
  | Green => False

def Light.decEq: (a: Light) → (b: Light) → Decidable (a = b)
  | Red, Red => Decidable.yes rfl
  | Green, Green => Decidable.yes rfl
  | Red, Green => Decidable.no (e => Bool.trueNotFalse (Eq.cong Light.isRed e))
  | Green, Red => Decidable.no (e => Bool.falseNotTrue (Eq.cong Light.isRed e))

instance Light.instDecEq: DecEq Light := { decide = Light.decEq }

theorem lights ∀ (a b: Light) (h: (a == b) = True): a = b := h.read

theorem lightsApart ∀ (a b: Light) (h: (a == b) = False): a ≠ b := h.read

-- And one built with `Decidable.map` from a decision about a part: it
-- reads as the equation of the whole, not of the part.
type Code = { n: Nat }

def Code.decEq (a b: Code): Decidable (a = b) :=
  Decidable.map (Nat.decEq a.n b.n) (e => match a, b with | { n }, { n = m } => rewrite e in rfl) (e => rewrite e in rfl)

instance Code.instDecEq: DecEq Code := { decide = Code.decEq }

theorem codes ∀ (a b: Code) (h: (a == b) = True): a = b := h.read
