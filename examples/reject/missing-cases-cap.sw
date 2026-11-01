-- expect-error: E-NONEXHAUSTIVE
-- At most 20 missing cases are listed, then how many more: 23 are missing
-- here, so 3 are left out of the list (SW-1027).
type Letter =
  | LA
  | LB
  | LC
  | LD
  | LE
  | LF
  | LG
  | LH
  | LI
  | LJ
  | LK
  | LL
  | LM
  | LN
  | LO
  | LP
  | LQ
  | LR
  | LS
  | LT
  | LU
  | LV
  | LW
  | LX

def code: Letter → Nat
  | LA => 0
