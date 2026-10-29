-- expect-error: E-POSITIVITY
-- A field may not depend on an earlier field that holds the type being
-- defined (Lamiaux, Forster, Sozeau and Tabareau's `Fnat`): `same` says two
-- of the type's own values are equal, so the type would have to be defined
-- together with that equation (an inductive-inductive type), which nothing
-- here shows sound. Rocq 9.1 accepts it; Lean and their rule refuse it
-- (docs/proposals/nested-data-types.md §4.2, §5.3). An equation between
-- fields that don't hold the type is fine: `Checked` in
-- accept/nested-data-shapes.sw.
type Fnat: Type =
  | FZero
  | FSucc (n: Fnat) (m: Fnat) (same: n = m)
