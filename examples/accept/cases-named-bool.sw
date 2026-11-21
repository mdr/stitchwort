-- A `Bool` named is split into `True` and `False`; without `then`, each case
-- is closed as `cases` closes one (here by computation).
import Std (Bool)

theorem notBoth ∀ (b: Bool): (b && !b) = False := cases b

theorem andOrAbsorb ∀ (a b: Bool): (a && (a || b)) = a := cases a
