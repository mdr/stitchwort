-- A hole in the body of an or-pattern's arm is checked once for each
-- alternative, so the goal lists each alternative's context and goal.
import Std (Text)

theorem shortText ∀ (text: Text) (spelt: text = "a" ∨ text = "bb"): text.length = 1 := match spelt with
  | Inl same | Inr same => ?
