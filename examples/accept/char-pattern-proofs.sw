-- Proofs by char patterns: in an arm for `'a'`, the matched character *is*
-- `'a'`, so `byComputing` proves it equal to the literal. (A char pattern is
-- `MkChar 97 _`; the arm takes the proof field to be the literal's.)
import Std (Eq)

theorem firstIsA ∀ (c: Char) (h: c = 'a'): c = 'a' := match c with
  | 'a' => byComputing
  | _ => h

-- Several characters, and a default arm that uses the equation.
def next: Char → Char
  | 'a' => 'b'
  | 'b' => 'c'
  | c => c

theorem nextOfA ∀ (c: Char) (h: c = 'a'): next c = 'b' := match c with
  | 'a' => byComputing
  | 'b' => J (y e => next y = 'b') byComputing h.flipped
  | _ => J (y e => next y = 'b') byComputing h.flipped

-- The matched character by name in a `match`.
theorem isItself ∀ (c: Char): (c = 'x') ∨ (c = c) := match c with
  | 'x' => Inl (byComputing: c = 'x')
  | _ => Inr byComputing

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
  | '0', o => byComputing
  | '1', o => byComputing
  | _, Inl h => J (y e => bitChar (bitValue y) = y) byComputing h.flipped
  | _, Inr h => J (y e => bitChar (bitValue y) = y) byComputing h.flipped

theorem bitIsBit ∀ (c: Char) (o: (c = '0') ∨ (c = '1')): isBit c = True := match c, o with
  | '0', o => byComputing
  | '1', o => byComputing
  | _, Inl h => Eq.cong isBit h
  | _, Inr h => Eq.cong isBit h

-- A hypothesis about the character, refined in the arm.
theorem hypothesisRefined ∀ (c: Char) (h: next c = 'b'): (c = 'a') ∨ (next c = 'b') := match c with
  | 'a' => Inl byComputing
  | _ => Inr h

-- Two characters at once, nested in a pair.
theorem pairOfChars ∀ (p: Pair Char Char): (p = ('a', 'b')) ∨ (p = p) := match p with
  | ('a', 'b') => Inl byComputing
  | q => Inr byComputing

-- Running code with char arms is unchanged.
test "next" := next 'a' == 'b' ∧ next 'z' == 'z'
test "bits" := bitChar (bitValue '1') == '1' ∧ isBit '0' ∧ not (isBit '2')
-- The transport computes away on a literal. The lemmas are `def`s here: a
-- theorem is sealed (D3722), so `firstIsA 'a' byComputing` stays a call.
def firstIsADef (c: Char) (h: c = 'a'): c = 'a' := match c with
  | 'a' => byComputing
  | _ => h

def nextOfADef (c: Char) (h: c = 'a'): next c = 'b' := match c with
  | 'a' => byComputing
  | 'b' => J (y e => next y = 'b') byComputing h.flipped
  | _ => J (y e => next y = 'b') byComputing h.flipped

theorem firstIsAComputes: firstIsADef 'a' byComputing = byComputing := byComputing
theorem nextOfAComputes: nextOfADef 'a' byComputing = byComputing := byComputing

-- A `match` nested inside a char arm, on another char or on the same one,
-- gets the same treatment: in its arms the matched characters are the
-- literals.

theorem nestedReturnC ∀ (c d: Char) (hc: c = 'a') (hd: d = 'b'): c = 'a' := match c with
  | 'a' =>
    match d with
      | 'b' => byComputing
      | _ => hc
  | c => hc

theorem nestedReturnD ∀ (c d: Char) (hc: c = 'a') (hd: d = 'b'): d = 'b' := match c with
  | 'a' =>
    match d with
      | 'b' => byComputing
      | _ => hd
  | c => hd

theorem nestedBoth ∀ (c d: Char) (hc: c = 'a') (hd: d = 'b'): (c = 'a') ∧ (d = 'b') := match c with
  | 'a' =>
    match d with
      | 'b' => Both byComputing byComputing
      | _ => Both byComputing hd
  | c => Both hc hd

theorem nestedSame ∀ (c: Char): (c = 'x') ∨ (c = c) := match c with
  | 'a' => Inr byComputing
  | c =>
    match c with
      | 'x' => Inl byComputing
      | _ => Inr byComputing

theorem nestedOnlySame ∀ (c: Char): (c = 'x') ∨ (c = c) := match c with
  | 'x' => Inl byComputing
  | _ => Inr byComputing
