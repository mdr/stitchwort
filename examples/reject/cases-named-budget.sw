-- expect-error: E-CASES-BUDGET
-- Three values of ten constructors each are a thousand cases: the error names
-- the split that went over the budget.
import Std (Bool)

type Digit = | D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9

def same (a b c: Digit): Bool := match a, b, c with
  | D0, D0, D0 => True
  | _, _, _ => False

theorem sameReversed ∀ (a b c: Digit): same a b c = same c b a := cases a, b, c then byComputing
