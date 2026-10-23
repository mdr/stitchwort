-- R12: the author's breaks are kept; a broken `else` or `then` sits at the
-- column of its `if`, or further in, at +2 from the line it continues.
def sign (n: Nat): Nat :=
  if n == 0 then 0
  else 1

def grade (n: Nat): Nat :=
  if n == 0 then 10
  else if n == 1 then 20
  else 30

def describe (n: Nat): Nat :=
  if n == 0
  then 100
  else
    let m := n + 1
    m * 2

def nested (a: Nat) (b: Nat): Nat :=
  if a == 0 then
    if b == 0 then 1
    else 2
  else
    if b == 0 then 3
    else 4
