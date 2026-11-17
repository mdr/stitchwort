-- expect-error: E-AUTO-NONE
-- A theorem statement that spells out a Prop-valued `match`, and a lemma
-- whose `auto` argument spells out the same match: the compiler made a
-- different helper for each, so the hypothesis doesn't fit the search and
-- nothing decides the match. The message says to hold it in a small helper
-- definition (docs/proving-guide.md, "A statement that spells out a match").

type Choice = | A | B

def needsMatch (t: Choice)
    [auto h: match t with
      | A => 1 = 1
      | B => 2 = 2]:
    Nat :=
  1

theorem spelled ∀ (t: Choice)
    (h: match t with
      | A => 1 = 1
      | B => 2 = 2):
    needsMatch t = 1 :=
  byComputing
