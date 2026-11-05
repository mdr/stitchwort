def grade: Nat → Text
  | score if score >= 90 => "distinction"
  | score if score < 90 => "pass"
