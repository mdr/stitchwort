-- A test fact read by hand to the end of a twenty-conjunct `&&` chain,
-- `h.read.right` nineteen times: the term `check --expand-facts` writes for
-- `byFacts` there. Each `.read` used to infer its receiver twice, once to
-- look for a function `read` and once to read the fact, so the chain took
-- time exponential in its length: over two minutes for twenty (SW-4498).
-- It checks in about 60 ms.

theorem longRead ∀ (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19: Bool)
    (h: (b0
      && b1
      && b2
      && b3
      && b4
      && b5
      && b6
      && b7
      && b8
      && b9
      && b10
      && b11
      && b12
      && b13
      && b14
      && b15
      && b16
      && b17
      && b18
      && b19)
      = True):
    b19 = True :=
  h.read.right.read.right.read.right.read.right.read.right.read.right.read.right.read.right.read.right.read.right.read.right.read.right.read.right.read.right.read.right.read.right.read.right.read.right.read.right
