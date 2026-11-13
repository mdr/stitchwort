-- R: a match body on the next line joins the header when it fits.
theorem timesOne (n: Nat): n * 1 = n :=
  match n with
    | Zero => rfl
    | Succ k => Eq.cong Succ (timesOne k)

def isZero (n: Nat): Bool :=
  match n with
    | Zero => True
    | Succ _ => False
