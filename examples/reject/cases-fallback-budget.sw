-- expect-error: E-CASES-BUDGET
-- The fallback split (docs/proposals/decide.md §6.1.3) counts against the
-- 64-case budget like any other: `a = b` isn't stuck on either variable, so
-- `cases` splits `c` (12 cases) and then, in each case, `b` and `a` (12
-- more each), and the error says that the split that crossed the budget
-- was a fallback. (Its second try, of 256 cases, runs out too.)
import Std (Bool)

type Month =
  | Jan
  | Feb
  | Mar
  | Apr
  | May
  | Jun
  | Jul
  | Aug
  | Sep
  | Oct
  | Nov
  | Dec

theorem sameOrNot ∀ (a b c: Month): (a = b ∨ a ≠ b) ∧ (b = c ∨ b ≠ c) := cases
