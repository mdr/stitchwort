-- expect-error: E-PARSE
-- In a pipe too, a brace-declared constructor's braces as an argument need
-- brackets.

type Ev = | Meeting { title: Text, minutes: Nat := 30 }

def keep (n: Nat) (e: Ev): Ev := e

def three: Nat := 3

def p: Ev := three |> keep Meeting { title = "a" }
