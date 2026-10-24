-- expect-error: E-REIFY
-- `{e}` doesn't say which abilities the computation has, so there's nothing
-- to split on.
theorem same (t: () -> {e} a): Unit :=
  match reify t with
    | return x => Trivial
