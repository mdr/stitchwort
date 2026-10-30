-- A `let`-bound lambda whose body may fail returns a computation, and each
-- call of it performs, also in a definition with no parameters and with only
-- literals as arguments (SW-911). The lambda's row is worked out from its
-- body and closed as `{Fail}`; its calls see that row as written.

import Std (Fail, Result)

-- One lambda, called twice with literals.
def twoSpans: {Fail} Nat :=
  let span := lo hi =>
    Fail.ensure (lo < hi) "out of order"
    hi - lo
  span 1 3 + span 2 5

-- One call, as the whole result.
def oneSpan: {Fail} Nat :=
  let span := lo hi =>
    Fail.ensure (lo < hi) "out of order"
    hi - lo
  span 1 3

-- Two lambdas, nested and flat, each called once.
def twoLambdas: {Fail} Nat :=
  let a := lo => hi =>
    Fail.ensure (lo < hi) "out of order"
    hi - lo
  let b := lo hi =>
    Fail.ensure (lo < hi) "out of order"
    hi - lo
  a 1 3 + b 2 5

-- A call that fails.
def badSpan: {Fail} Nat :=
  let span := lo hi =>
    Fail.ensure (lo < hi) "out of order"
    hi - lo
  span 1 3 + span 5 2

test "one lambda, two calls" := Fail.toResult (() => twoSpans) == Ok 5

test "one lambda, one call" := Fail.toResult (() => oneSpan) == Ok 2

test "two lambdas" := Fail.toResult (() => twoLambdas) == Ok 5

test "a call that fails" := Fail.toResult (() => badSpan) == Err "out of order"
