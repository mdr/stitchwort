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
    length (append xs ys) = length xs + length ys
appendLength Nil         ys = rfl
appendLength (Cons x xs) ys = cong Succ (appendLength xs ys)

export
appendNats : List Nat -> List Nat -> List Nat
appendNats xs ys = append xs ys

theorem appendNatsLength : (xs : List Nat) -> (ys : List Nat) ->
    length (appendNats xs ys) = length xs + length ys
appendNatsLength xs ys = appendLength xs ys

export
total : List Nat -> Nat
total Nil         = 0
total (Cons x xs) = x + total xs
