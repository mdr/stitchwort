-- Number patterns of any size. A column of numbers (with variables and `_`)
-- compares the argument with each number; it doesn't count down to it.
-- See docs/proposals/number-patterns.md.

statusText : Nat -> Text
statusText 200 = "OK"
statusText 201 = "Created"
statusText 204 = "No Content"
statusText 301 = "Moved Permanently"
statusText 304 = "Not Modified"
statusText 400 = "Bad Request"
statusText 401 = "Unauthorized"
statusText 403 = "Forbidden"
statusText 404 = "Not Found"
statusText 500 = "Internal Server Error"
statusText 503 = "Service Unavailable"
statusText _   = "Unknown"

test "200" = statusText 200 == "OK"
test "404" = statusText 404 == "Not Found"
test "503" = statusText 503 == "Service Unavailable"
test "other" = statusText 418 == "Unknown"

theorem notFound : statusText 404 = "Not Found"
notFound = rfl

-- Very large numbers are fine.
isHuge : Nat -> Bool
isHuge 1000000000000000000000000000000 = True
isHuge _                               = False

test "huge" = isHuge (1000000000000000000000000000000 * 1)
test "not huge" = not (isHuge 999999999999999999999999999999)

-- Inside an equation with a number, the argument *is* that number, so the
-- types of the result and of other arguments that mention it compute.
isNotFound : (n : Nat) -> Decidable (n = 404)
isNotFound 404 = Yes rfl
isNotFound n   = Nat.decEq n 404

Shape : Nat -> Type
Shape 404 = Text
Shape _   = Bool

pick : (n : Nat) -> Shape n -> Text
pick 404 t = t
pick n   s = "something else"

test "pick" = pick 404 "here" == "here"

-- Equations are tried from top to bottom. The `404` case still tries the
-- later equations when its own doesn't match.
g : Nat -> Bool -> Nat
g 404 True  = 1
g n   False = n
g _   _     = 3

test "g 404 True"  = g 404 True == 1
test "g 404 False" = g 404 False == 404
test "g 405 False" = g 405 False == 405
test "g 405 True"  = g 405 True == 3

-- The same number in several equations.
g2 : Nat -> Bool -> Nat
g2 404 True  = 1
g2 404 False = 2
g2 _   _     = 3

test "g2" = g2 404 False == 2

-- Numbers mixed with `Succ` patterns: the column is split into `Zero` and
-- `Succ`, and `n` still names the whole argument.
h : Nat -> Nat
h 404             = 0
h (Succ (Succ k)) = k
h n               = n

test "h 0"   = h 0 == 0
test "h 1"   = h 1 == 1
test "h 404" = h 404 == 0
test "h 405" = h 405 == 403

-- A first equation that matches everything wins: `constant` doesn't look at
-- its argument, and the second equation is never used.
constant : Nat -> Nat
constant n   = 1
constant 404 = 2

theorem constantAnything : (n : Nat) -> constant n = 1
constantAnything n = rfl

-- Number patterns after a structural split keep the recursion structural.
countDown : Nat -> Nat -> Nat
countDown Zero     m   = m
countDown (Succ n) 404 = countDown n 0
countDown (Succ n) m   = countDown n (m + 1)

test "countDown" = countDown 3 403 == 1

-- For the shape of a number, match `Zero` and `Succ` (compare
-- reject/number-pattern-default.sw).
ResultType : Nat -> Type
ResultType Zero     = Nat
ResultType (Succ _) = Bool

make : (n : Nat) -> ResultType n
make Zero     = 0
make (Succ _) = False
