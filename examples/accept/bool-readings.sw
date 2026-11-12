-- A fact about a test, `e = True` or `e = False`, is taken apart, built and
-- used as the proposition the test reads as
-- (docs/proposals/bool-as-proposition.md §5, §6). A reading is a theorem
-- `test ↔ P` marked `@[reading]`, declared with the test's function; the
-- core declares them for `&&`, `||` and `not`.
import Std (Bool, Nat, Iff)

-- Taking a fact apart: each constructor pattern reads the test under it,
-- one layer at a time.
theorem nested (a b c: Bool) (h: (a && (b || c)) = True): b ∨ c :=
  match h with
    | Both _ (Inl hb) => Inl hb
    | Both _ (Inr hc) => Inr hc

-- `= False` has a reading of its own.
theorem notBoth (a b: Bool) (h: (a && b) = False): a = False ∨ b = False :=
  match h with
    | Inl na => Inl na
    | Inr nb => Inr nb

theorem neither (a b: Bool) (h: (a || b) = False): b = False :=
  let Both _ nb := h
  nb

-- `not a` reads as `a = False`, and `not a = False` as `a`.
theorem negated (a b: Bool) (h: (Bool.not a && b) = True): a = False :=
  let Both na _ := h
  na.read

-- A name stops the reading: `rest` stays the test fact `(b || c) = True`.
theorem stops (a b c: Bool) (h: (a && (b || c)) = True): (b || c) = True :=
  let Both _ rest := h
  rest

-- Building a fact from its reading.
theorem build (a b: Bool) (ha: a) (hb: b): (a && b) = True := Both ha hb

theorem buildEither (a b: Bool) (hb: b): (a || b) = True := Inr hb

theorem buildNot (a b: Bool) (na: a = False): (a && b) = False := Inl na

-- `.read`: the whole fact as its proposition. A fact `e = False` whose test
-- has no reading of its own reads as `¬e`.
theorem whole (a b: Bool) (h: (a && b) = True): a ∧ b := h.read

theorem refuted (a: Bool) (h: a = False): ¬a := h.read

-- A field of a fact is the field of its reading: `h.left` is `h.read.left`.
theorem field (a b: Bool) (h: (a && b) = True): b := h.right

-- A program's own test, with its own reading.
type InRange (lo x hi: Nat): Prop = {
  low: lo ≤ x,
  high: x ≤ hi
}

def inRange (lo x hi: Nat): Bool := lo <= x && x <= hi

@[reading]
theorem inRangeReads (lo x hi: Nat): inRange lo x hi ↔ InRange lo x hi := {
  forward = h => { low = h.left, high = h.right },
  backward = r => Both r.low r.high
}

theorem below (lo x hi: Nat) (h: inRange lo x hi): x ≤ hi :=
  match h with
    | { low, high } => high

theorem within (lo x hi: Nat) (low: lo ≤ x) (high: x ≤ hi): inRange lo x hi := { low, high }

-- The reader goes by the test as written: unfolded, the same fact is a `&&`.
theorem unfolded (lo x hi: Nat) (h: (lo <= x && x <= hi) = True): lo ≤ x :=
  let Both low _ := h
  low

-- A test with no reading of its own is unfolded to one that has.
def isDigitCode (n: Nat): Bool := inRange 48 n 57

theorem digitBelow (n: Nat) (h: isDigitCode n): n ≤ 57 := h.read.high
