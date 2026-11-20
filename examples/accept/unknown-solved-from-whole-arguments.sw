-- An implicit argument fixed only by an explicit argument's type, where
-- that type is a definition applied to a constructor: `Is (Nest 2 x) n`
-- against `Is ?doc n`. `Is` is a `∀` over `doc.size`, which `?doc` blocks
-- while `(Nest 2 x).size` computes, so comparing the two unfoldings can't
-- solve `?doc`; the calls' arguments do, once that comparison has failed
-- (SW-4305). An unknown inside an argument, rather than the whole of one,
-- isn't solved this way.

type Box =
  | Text (width: Nat)
  | Nest (by: Nat) (inner: Box)
  | Two (left right: Box)

def Box.size: Box → Nat
  | Text width => width
  | Nest by inner => by + inner.size
  | Two left right => left.size + right.size

def Is (doc: Box) (n: Nat): Prop := ∀ (k: Nat) => doc.size + k = n + k

theorem isSized ∀ [doc: Box] [n: Nat] (is: Is doc n): doc.size = n := rewrite (is 0)

theorem nestSized ∀ (x: Box) (n: Nat) (is: Is (Nest 2 x) n): x.size + 2 = n := isSized is

theorem isTwo ∀ [left right: Box] (n m: Nat) (first: Is left n) (second: Is right m): Is (Two left right) (n + m) :=
  k => rewrite (first 0), (second 0)

theorem textIs ∀ (width: Nat): Is (Text width) width := k => byComputing

theorem twoSized ∀ (x: Box) (n: Nat) (is: Is (Nest 2 x) n): (Two (Text 1) (Nest 2 x)).size = 1 + n :=
  isSized (isTwo 1 n (textIs 1) is)
