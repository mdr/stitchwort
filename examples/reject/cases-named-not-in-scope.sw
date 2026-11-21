-- expect-error: E-CASES
-- A name `cases` is told to split must be a variable or hypothesis in scope.
import Std (Bool)

theorem notSelf ∀ (a: Bool): (a && a) = a := cases b then byComputing
