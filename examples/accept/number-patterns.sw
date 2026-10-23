-- Number patterns of any size. A column of numbers (with variables and `_`)
-- compares the argument with each number; it doesn't count down to it.
-- See docs/proposals/number-patterns.md.

import Std (Nat)

def statusText: Nat -> Text
  | 200 => "OK"
  | 201 => "Created"
  | 204 => "No Content"
  | 301 => "Moved Permanently"
  | 304 => "Not Modified"
  | 400 => "Bad Request"
  | 401 => "Unauthorized"
  | 403 => "Forbidden"
  | 404 => "Not Found"
  | 500 => "Internal Server Error"
  | 503 => "Service Unavailable"
  | _ => "Unknown"

test "200" := statusText 200 == "OK"
test "404" := statusText 404 == "Not Found"
test "503" := statusText 503 == "Service Unavailable"
test "other" := statusText 418 == "Unknown"

theorem notFound: statusText 404 = "Not Found" := rfl

-- Very large numbers are fine.
def isHuge: Nat -> Bool
  | 1000000000000000000000000000000 => True
  | _ => False

test "huge" := isHuge (1000000000000000000000000000000 * 1)
test "not huge" := not (isHuge 999999999999999999999999999999)

-- Inside an equation with a number, the argument *is* that number, so the
-- types of the result and of other arguments that mention it compute.
def isNotFound: (n: Nat) -> Decidable (n = 404)
  | 404 => Yes rfl
  | n => Nat.decEq n 404

def Shape: Nat -> Type
  | 404 => Text
  | _ => Bool

def pick: (n: Nat) -> Shape n -> Text
  | 404, t => t
  | n, s => "something else"

test "pick" := pick 404 "here" == "here"

-- Equations are tried from top to bottom. The `404` case still tries the
-- later equations when its own doesn't match.
def g: Nat -> Bool -> Nat
  | 404, True => 1
  | n, False => n
  | _, _ => 3

test "g 404 True" := g 404 True == 1
test "g 404 False" := g 404 False == 404
test "g 405 False" := g 405 False == 405
test "g 405 True" := g 405 True == 3

-- The same number in several equations.
def g2: Nat -> Bool -> Nat
  | 404, True => 1
  | 404, False => 2
  | _, _ => 3

test "g2" := g2 404 False == 2

-- Numbers mixed with `Succ` patterns: the column is split into `Zero` and
-- `Succ`, and `n` still names the whole argument.
def h: Nat -> Nat
  | 404 => 0
  | Succ (Succ k) => k
  | n => n

test "h 0" := h 0 == 0
test "h 1" := h 1 == 1
test "h 404" := h 404 == 0
test "h 405" := h 405 == 403

-- A first equation that matches everything wins: `constant` doesn't look at
-- its argument, and the second equation is never used.
def constant: Nat -> Nat
  | n => 1
  | 404 => 2

theorem constantAnything (n: Nat): constant n = 1 := rfl

-- Number patterns after a structural split keep the recursion structural.
def countDown: Nat -> Nat -> Nat
  | Zero, m => m
  | Succ n, 404 => countDown n 0
  | Succ n, m => countDown n (m + 1)

test "countDown" := countDown 3 403 == 1

-- For the shape of a number, match `Zero` and `Succ` (compare
-- reject/number-pattern-default.sw).
def ResultType: Nat -> Type
  | Zero => Nat
  | Succ _ => Bool

def make: (n: Nat) -> ResultType n
  | Zero => 0
  | Succ _ => False
