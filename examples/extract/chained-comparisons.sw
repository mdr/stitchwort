-- A chain's middle is computed once, in the generated JavaScript too: the
-- snapshot of the generated code shows `twice` called once in each export.
--
-- run: inRange 3
-- run: inRange 4
-- run: inRange 5
-- run: named 4
-- run: named 9
-- run: asBool 2
-- run: asBool 5

def twice (n: Nat): Nat := n + n

export def inRange (n: Nat): Nat := if 3 <= twice n <= 9 then 1 else 0

export def named (n: Nat): Nat := if h: 3 <= twice n <= 9 then 1 else 0

export def asBool (n: Nat): Bool := 3 <= twice n <= 9
