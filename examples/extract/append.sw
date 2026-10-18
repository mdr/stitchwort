-- A proven list library, extracted to JavaScript.
--
-- The differential test runs each `-- run:` line in the reference evaluator
-- and in the generated JS, and checks that the results agree.
--
-- run: appendNats [1, 2] [3]
-- run: appendNats [] []
-- run: appendNats [] [4, 5]
-- run: total [1, 2, 3]
-- run: total []

-- The length of two appended lists is the sum of their lengths.
theorem appendLength : (xs : List a) -> (ys : List a) ->
    List.length (List.append xs ys) = List.length xs + List.length ys
  | Nil,       ys => rfl
  | Cons x xs, ys => Eq.cong Succ (appendLength xs ys)

export def appendNats (xs : List Nat) (ys : List Nat) : List Nat := List.append xs ys

theorem appendNatsLength (xs : List Nat) (ys : List Nat) :
    List.length (appendNats xs ys) = List.length xs + List.length ys := appendLength xs ys

export def total : List Nat -> Nat
  | Nil       => 0
  | Cons x xs => x + total xs
