-- `==` on long texts: comparing two 100,000-character texts used to run out of resources while checking (the operands were computed at check time); now the test runs at run time.

def long: Nat -> Text
  | Zero   => ""
  | Succ n => "a" ++ long n

test "same long texts" := long 100000 == long 100000
test "different long texts" := not (long 100000 == long 99999)
