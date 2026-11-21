-- In a record or tuple, a name followed by `=` or `=>` starts the next field
-- or item, not a second value for `cases` to split.
import Std (Bool)

type Both = {
  left: ∀ (a: Bool) => (a || True) = True,
  right: ∀ (b: Bool) => (b && False) = False
}

def both: Both := { left = a => cases a, right = b => cases b }

theorem pair: (∀ (a: Bool) => (a || True) = True) ∧ (∀ (b: Bool) => (b && False) = False) :=
  (a => cases a, b => cases b)
