-- expect-error: E-REFL
-- A default is checked for any values of the earlier fields, since a
-- literal may give `size = 3` and leave `ok` out: it can't assume `size`
-- took its own default (docs/proposals/named-arguments.md §5.1 rule 2).

type Bad = {
  size: Nat := 8,
  ok: size = 8 := rfl
}
