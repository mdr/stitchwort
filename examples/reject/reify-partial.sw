-- expect-error: E-REIFY
-- A `Partial` computation may not finish, so a proof can't look at all of it.
theorem same (t: () -> {Partial} Nat): Unit :=
  match reify t with
    | return x => Trivial
