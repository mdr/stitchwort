-- A pure `let` compiles to a function applied to the value: computed once,
-- with no effects machinery (no `Done`, no `runPure`) around it. A `let`
-- holding a proof is erased like a proof argument.
--
-- run: twice 4
-- run: clamp 1
-- run: clamp 7
-- run: below 3 5

export def twice (n : Nat) : Nat :=
  let m := n + 1
  m + m

export def clamp (n : Nat) : Nat :=
  let m := n + 1
  if m < 3 then 0 else m

def lessOf (a b : Nat) (h : a <= b) : Nat := b - a

export def below (a b : Nat) : Nat :=
  let h := Nat.leAddRight a b
  lessOf a (a + b) h
