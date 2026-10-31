-- expect-error: E-TYPE-MISMATCH
-- A number group's operand that waits: `r.g` waits for `r`'s type, which
-- only `h p` fixes, and fails once it is known, after the group has been
-- built. It still gets the group's notes (what made it `Int`, and what `-g`
-- means as an argument), as when `r` is annotated (`annotated`): the check
-- carries the error frames of the leaf and of the negated argument
-- (docs/proposals/postponement.md, step 4.1, D2091).

type P = { g: Int → Int }

def f (a: Int) (b: Int): Int := a + b

def later (p: P) (x: Int): Int :=
  let h := r => f -r.g x
  h p

def annotated (p: P) (x: Int): Int :=
  let h := (r: P) => f -r.g x
  h p
