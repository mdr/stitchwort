-- `byFacts` reads a test fact of twenty conjuncts to its end, as `cases`
-- does (18 ms against `cases`' 57). The term `--expand-facts` writes,
-- `h.read.right.read.right…`, checks in about 90 ms
-- (`facts_expand::facts_expansions_check_again`).

theorem longTest ∀ (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19: Bool)
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
    b19 = True ∧ b13 = True :=
  byFacts
