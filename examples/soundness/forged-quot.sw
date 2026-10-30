-- expect-error: E-DUPLICATE
-- Lean Kernel Arena `forged-quot-ind` (docs/research/kernel.md C24): a
-- `Quot.ind` declared before ordinary definitions named `Quot` and
-- `Quot.mk` proved `False`, because the checker trusted the names. Here a
-- quotient is a term former (`Term::Quot`), and the names are reserved, so
-- a user type can't take them. Neighbour: accept/quot-forms.sw.
type Quot = | A | B
