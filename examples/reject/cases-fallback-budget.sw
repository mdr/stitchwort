-- expect-error: E-CASES-BUDGET
-- The fallback split (docs/proposals/decide.md §6.1.3) counts against the
-- 64-case budget like any other: `a = b` isn't stuck on either variable, so
-- `cases` splits `b` (12 cases) and then, in each case, `a` (12 more each),
-- and the error says that the split that crossed the budget was a fallback.
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

theorem sameOrNot (a: Month) (b: Month): Or (a = b) (Not (a = b)) := cases
