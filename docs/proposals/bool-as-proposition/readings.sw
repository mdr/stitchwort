-- Probe for docs/proposals/bool-as-proposition.md §5 and §6: readings as
-- ordinary proved records, and the terms the patterns would elaborate to.
-- `Dec` stands in for D3480's `Decidable` record. Checks.
import Std (Bool, Eq, List, Nat, Void)

type Dec (p: Prop) = { does: Bool, sound: does = True → p, complete: p → does = True }

def andReading (a b: Bool): Dec (a = True ∧ b = True) :=
  { does = a && b, sound = h => Both (Bool.andLeft h) (Bool.andRight h), complete = h => Bool.andIntro h.left h.right }

def orReading (a b: Bool): Dec (a = True ∨ b = True) := {
  does = a || b,
  sound = h => Bool.orElim h (l => Inl l) (r => Inr r),
  complete = h =>
    match h with
      | Inl l => Bool.orLeft l
      | Inr r => Bool.orRight r
}

-- A negative reading: its `does` is `not` of the test, so it is found for
-- `(a && b) = False`.
def notAndReading (a b: Bool): Dec (a = False ∨ b = False) := {
  does = Bool.not (a && b),
  sound = h => Bool.andFalseElim a b (Bool.notTrue (a && b) h),
  complete = h =>
    match h with
      | Inl l => Bool.notOfFalse (a && b) (Bool.andFalseLeft a b l)
      | Inr r => Bool.notOfFalse (a && b) (Bool.andFalseRight a b r)
}

def anyReading (xs: List a) (f: a → Bool): Dec (∃ (x: a) => x ∈ xs ∧ f x = True) := {
  does = xs.any f,
  sound = h => List.anyTrueElim xs f _ h (x xIn fx => Witness x (Both xIn fx)),
  complete = h => match h with | Witness x (Both xIn fx) => List.anyOfMem xs f x fx xIn
}

-- A reading that is a function: used by applying the fact, built by a lambda.
def allReading (xs: List a) (f: a → Bool): Dec (∀ (x: a) => x ∈ xs → f x = True) := {
  does = xs.all f,
  sound = h => x xIn => List.allMember f xs h x xIn,
  complete = h => List.allOfAll f xs (List.allOfMem (x => f x = True) xs h)
}

-- Each reading's `does` is the test, by computation, with everything unknown.
theorem doesAnd ∀ (a b: Bool): (andReading a b).does = (a && b) := rfl
theorem doesAny ∀ (xs: List Nat) (f: Nat → Bool): (anyReading xs f).does = xs.any f := rfl
theorem doesAll ∀ (xs: List Nat) (f: Nat → Bool): (allReading xs f).does = xs.all f := rfl

-- `match h with | Both ha (Inl hb) | Both ha (Inr hc)`, as elaborated: one
-- layer per constructor pattern.
theorem nested ∀ (a b c: Bool) (h: (a && (b || c)) = True): b = True ∨ c = True :=
  match (andReading a (b || c)).sound h with
    | Both ha rest =>
      match (orReading b c).sound rest with
        | Inl hb => Inl hb
        | Inr hc => Inr hc

-- `Witness x (Both xIn (Both small big))` on an `any` fact.
theorem anyNested ∀ (xs: List Nat) (h: xs.any (x => 3 ≤ x && x ≤ 5) = True): ∃ (x: Nat) => x ∈ xs ∧ 3 ≤ x :=
  match (anyReading xs (x => 3 ≤ x && x ≤ 5)).sound h with
    | Witness x (Both xIn fx) =>
      match (andReading (Nat.leq 3 x) (Nat.leq x 5)).sound fx with
        | Both small big => Witness x (Both xIn small)

-- Building: `Both ha hb` where `(a && b) = True` is wanted.
theorem build ∀ (a b: Bool) (ha: a = True) (hb: b = True): (a && b) = True := (andReading a b).complete (Both ha hb)

-- `match h with | Inl na | Inr nb` on `h: (a && b) = False`.
theorem negative ∀ (a b: Bool) (h: (a && b) = False) (hb: b = True): a = False :=
  match (notAndReading a b).sound (Bool.notOfFalse (a && b) h) with
    | Inl na => na
    | Inr nb => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym nb) hb))

-- Applying an `all` fact, and building one with a lambda.
theorem useAll ∀ (xs: List Nat) (h: xs.all (x => x ≤ 9) = True) (y: Nat) (yIn: y ∈ xs): y ≤ 9 :=
  (allReading xs (x => x ≤ 9)).sound h y yIn
