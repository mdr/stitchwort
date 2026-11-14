-- Proofs by char patterns: in an arm for `'a'`, the matched character *is*
-- `'a'`, so `rfl` proves it equal to the literal. (A char pattern is
-- `MkChar 97 _`; the arm takes the proof field to be the literal's.)
import Std (Eq)

theorem firstIsA ∀ (c: Char) (h: c = 'a'): c = 'a' := match c with
  | 'a' => rfl
  | _ => h

-- Several characters, and a default arm that uses the equation.
def next: Char → Char
  | 'a' => 'b'
  | 'b' => 'c'
  | c => c

theorem nextOfA ∀ (c: Char) (h: c = 'a'): next c = 'b' := match c with
  | 'a' => rfl
  | 'b' => J (y e => next y = 'b') rfl (Eq.sym h)
  | _ => J (y e => next y = 'b') rfl (Eq.sym h)

-- The matched character by name in a `match`.
theorem isItself ∀ (c: Char): (c = 'x') ∨ (c = c) := match c with
  | 'x' => Inl (rfl: c = 'x')
  | _ => Inr rfl

-- Proof by cases over a function that classifies characters: on each digit
-- the goal mentions the character itself.
def isBit: Char → Bool
  | '0' => True
  | '1' => True
  | _ => False

def bitValue: Char → Nat
  | '1' => 1
  | _ => 0

def bitChar: Nat → Char
  | 0 => '0'
  | _ => '1'

theorem bitRoundTrip ∀ (c: Char) (o: (c = '0') ∨ (c = '1')): bitChar (bitValue c) = c := match c, o with
  | '0', o => rfl
  | '1', o => rfl
  | _, Inl h => J (y e => bitChar (bitValue y) = y) rfl (Eq.sym h)
  | _, Inr h => J (y e => bitChar (bitValue y) = y) rfl (Eq.sym h)

theorem bitIsBit ∀ (c: Char) (o: (c = '0') ∨ (c = '1')): isBit c = True := match c, o with
  | '0', o => rfl
  | '1', o => rfl
  | _, Inl h => Eq.cong isBit h
  | _, Inr h => Eq.cong isBit h

-- A hypothesis about the character, refined in the arm.
theorem hypothesisRefined ∀ (c: Char) (h: next c = 'b'): (c = 'a') ∨ (next c = 'b') := match c with
  | 'a' => Inl rfl
  | _ => Inr h

-- Two characters at once, nested in a pair.
theorem pairOfChars ∀ (p: Pair Char Char): (p = ('a', 'b')) ∨ (p = p) := match p with
  | ('a', 'b') => Inl rfl
  | q => Inr rfl

-- Running code with char arms is unchanged.
test "next" := next 'a' == 'b' ∧ next 'z' == 'z'
test "bits" := bitChar (bitValue '1') == '1' ∧ isBit '0' ∧ not (isBit '2')
-- The transport computes away on a literal.
theorem firstIsAComputes: firstIsA 'a' rfl = rfl := rfl
theorem nextOfAComputes: nextOfA 'a' rfl = rfl := rfl

-- A `match` nested inside a char arm, on another char or on the same one,
-- gets the same treatment: in its arms the matched characters are the
-- literals.

theorem nestedReturnC ∀ (c d: Char) (hc: c = 'a') (hd: d = 'b'): c = 'a' := match c with
  | 'a' =>
    match d with
      | 'b' => rfl
      | _ => hc
  | c => hc

theorem nestedReturnD ∀ (c d: Char) (hc: c = 'a') (hd: d = 'b'): d = 'b' := match c with
  | 'a' =>
    match d with
      | 'b' => rfl
      | _ => hd
  | c => hd

theorem nestedBoth ∀ (c d: Char) (hc: c = 'a') (hd: d = 'b'): (c = 'a') ∧ (d = 'b') := match c with
  | 'a' =>
    match d with
      | 'b' => Both rfl rfl
      | _ => Both rfl hd
  | c => Both hc hd

theorem nestedSame ∀ (c: Char): (c = 'x') ∨ (c = c) := match c with
  | 'a' => Inr rfl
  | c =>
    match c with
      | 'x' => Inl rfl
      | _ => Inr rfl

theorem nestedOnlySame ∀ (c: Char): (c = 'x') ∨ (c = c) := match c with
  | 'x' => Inl rfl
  | _ => Inr rfl
