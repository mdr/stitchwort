-- D2086: how Lean 4's `match` treats a discriminant holding numerals whose
-- type is still pending (OfNat with a default instance).

def two (m : Nat) (_p : m = 2) : Bool → Nat
  | true => m
  | false => 0

-- (1) Stitchwort's match-bad-motive.sw, in Lean. Lean's term-mode `match`
-- doesn't generalise hypotheses that mention a non-variable discriminant,
-- so this is accepted whatever the numerals do.
def bad (b : Bool) (q : two (List.length [1, 1]) rfl b = 2) : Nat :=
  match List.length [1, 1] with
  | 0 => 0
  | k + 1 => k

-- (2) Does the expected type's occurrence get abstracted when the
-- discriminant's numerals are pending? Branch type-checks only if it is.
def t1 : List.length [1, 1] = 2 :=
  match List.length [1, 1] with
  | 0 => sorry
  | n + 1 => (show n + 1 = 2 from sorry)

-- (3) The same, with the expected type's list at `Int`: does the occurrence
-- test choose the discriminant's element type (Int) by unification?
def t2 : List.length ([1, 1] : List Int) = 2 :=
  match List.length [1, 1] with
  | 0 => sorry
  | n + 1 => (show n + 1 = 2 from sorry)

-- (4) Control: discriminant fully typed.
def t3 : List.length ([1, 1] : List Int) = 2 :=
  match List.length ([1, 1] : List Nat) with
  | 0 => sorry
  | n + 1 => (show n + 1 = 2 from sorry)

-- (5) What type did t2's discriminant list get?
set_option pp.explicit true in
#print t2
