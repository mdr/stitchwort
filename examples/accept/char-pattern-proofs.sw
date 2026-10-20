-- Proofs by char patterns: in an arm for `'a'`, the matched character *is*
-- `'a'`, so `rfl` proves it equal to the literal. (A char pattern is
-- `MkChar 97 _`; the arm takes the proof field to be the literal's.)
import Std (Eq)

theorem firstIsA: (c: Char) -> c = 'a' -> c = 'a'
  | 'a', h => rfl
  | _, h => h

-- Several characters, and a default arm that uses the equation.
def next: Char -> Char
  | 'a' => 'b'
  | 'b' => 'c'
  | c   => c

theorem nextOfA: (c: Char) -> c = 'a' -> next c = 'b'
  | 'a', h => rfl
  | 'b', h => J (y e => next y = 'b') rfl (Eq.sym h)
  | _, h   => J (y e => next y = 'b') rfl (Eq.sym h)

-- The matched character by name in a `match`.
theorem isItself (c: Char): Or (c = 'x') (c = c) :=
  match c with
    | 'x' => Inl (rfl: c = 'x')
    | _   => Inr rfl

-- Proof by cases over a function that classifies characters: on each digit
-- the goal mentions the character itself.
def isBit: Char -> Bool
  | '0' => True
  | '1' => True
  | _   => False

def bitValue: Char -> Nat
  | '1' => 1
  | _   => 0

def bitChar: Nat -> Char
  | 0 => '0'
  | _ => '1'

theorem bitRoundTrip: (c: Char) -> Or (c = '0') (c = '1') -> bitChar (bitValue c) = c
  | '0', o       => rfl
  | '1', o       => rfl
  | _, Inl h     => J (y e => bitChar (bitValue y) = y) rfl (Eq.sym h)
  | _, Inr h     => J (y e => bitChar (bitValue y) = y) rfl (Eq.sym h)

theorem bitIsBit: (c: Char) -> Or (c = '0') (c = '1') -> isBit c = True
  | '0', o   => rfl
  | '1', o   => rfl
  | _, Inl h => Eq.cong isBit h
  | _, Inr h => Eq.cong isBit h

-- A hypothesis about the character, refined in the arm.
theorem hypothesisRefined: (c: Char) -> next c = 'b' -> Or (c = 'a') (next c = 'b')
  | 'a', h => Inl rfl
  | _, h   => Inr h

-- Two characters at once, nested in a pair.
theorem pairOfChars: (p: Pair Char Char) -> Or (p = ('a', 'b')) (p = p)
  | ('a', 'b') => Inl rfl
  | q          => Inr rfl

-- Running code with char arms is unchanged.
test "next" := next 'a' == 'b' && next 'z' == 'z'
test "bits" := bitChar (bitValue '1') == '1' && isBit '0' && not (isBit '2')
-- The transport computes away on a literal.
theorem firstIsAComputes: firstIsA 'a' rfl = rfl := rfl
theorem nextOfAComputes: nextOfA 'a' rfl = rfl := rfl

-- A `match` nested inside a char arm, on another char or on the same one,
-- gets the same treatment: in its arms the matched characters are the
-- literals.

theorem nestedReturnC: (c d: Char) -> c = 'a' -> d = 'b' -> c = 'a'
  | 'a', d, hc, hd =>
      match d with
        | 'b' => rfl
        | _   => hc
  | c, d, hc, hd => hc

theorem nestedReturnD: (c d: Char) -> c = 'a' -> d = 'b' -> d = 'b'
  | 'a', d, hc, hd =>
      match d with
        | 'b' => rfl
        | _   => hd
  | c, d, hc, hd => hd

theorem nestedBoth: (c d: Char) -> c = 'a' -> d = 'b' -> And (c = 'a') (d = 'b')
  | 'a', d, hc, hd =>
      match d with
        | 'b' => Both rfl rfl
        | _   => Both rfl hd
  | c, d, hc, hd => Both hc hd

theorem nestedSame: (c: Char) -> Or (c = 'x') (c = c)
  | 'a' => Inr rfl
  | c   =>
      match c with
        | 'x' => Inl rfl
        | _   => Inr rfl

theorem nestedOnlySame: (c: Char) -> Or (c = 'x') (c = c)
  | c =>
      match c with
        | 'x' => Inl rfl
        | _   => Inr rfl
