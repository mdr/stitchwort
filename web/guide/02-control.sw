-- `let` names an intermediate value; the last line is the result.
def describe (n: Nat): Text :=
  let half := n / 2
  let kind := if n % 2 == 0 then "even" else "odd"
  "${n} is ${kind}, half is ${half}"

-- `match` takes values apart. Every case must be covered.
def countdown: Nat -> List Nat
  | 0      => []
  | Succ n => Cons (n + 1) (countdown n)

test "describe" := describe 7 == "7 is odd, half is 3"
test "countdown" := countdown 3 == [3, 2, 1]
