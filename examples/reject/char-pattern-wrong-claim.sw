-- expect-error: E-REFL
-- In the arm for 'a', the character is 'a', so it isn't 'b'.
theorem wrongInArm (c: Char): Or (c = 'b') (c = c) :=
  match c with
    | 'a' => Inl rfl
    | _   => Inr rfl
