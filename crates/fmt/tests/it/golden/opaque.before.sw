-- `opaque` is a modifier like `export`; `unfolding` is a header
-- continuation line at +4, like `decreasing`, and the bare `:=` after it
-- stays in column 0 (docs/proposals/opaque-definitions.md).
export   opaque def double (n: Nat): Nat := n + n

opaque  def triple (n: Nat): Nat
      unfolding double ,  half
:=
      double n + n

theorem tripleTwo: triple 2 = 6
  unfolding triple :=
  rfl

opaque def countDown (n: Nat): Nat
        decreasing n
        unfolding double
:=
    if n < 1 then 0 else countDown (n - 1)
