-- A chain's middle is computed once, in the generated JavaScript too: the
-- snapshot of the generated code shows `twice` called once in each export,
-- also where the chain is one operand of a larger `if h:` proposition or a
-- match guard.
--
-- run: inRange 3
-- run: inRange 4
-- run: inRange 5
-- run: named 4
-- run: named 9
-- run: asBool 2
-- run: asBool 5
-- run: nested 0
-- run: nested 3
-- run: nested 5
-- run: either 0
-- run: either 3
-- run: either 5
-- run: negated 2
-- run: negated 5
-- run: guarded 0
-- run: guarded 3
-- run: guarded 5

def twice (n: Nat): Nat := n + n

export def inRange (n: Nat): Nat := if 3 <= twice n <= 9 then 1 else 0

export def named (n: Nat): Nat := if h: 3 <= twice n <= 9 then 1 else 0

export def asBool (n: Nat): Bool := 3 <= twice n <= 9

export def nested (n: Nat): Nat := if h: n != 0 && 3 <= twice n <= 9 then n else 0

export def either (n: Nat): Nat := if h: n = 0 || 3 <= twice n <= 9 then 1 else 0

export def negated (n: Nat): Nat := if h: !(3 <= twice n <= 9) then 1 else 0

export def guarded: Nat → Nat
  | k if h: k != 0 && 3 <= twice k <= 9 => 1
  | _ => 0
