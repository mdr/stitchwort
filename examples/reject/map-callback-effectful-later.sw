-- expect-error: E-ABILITY

import Std (List)

-- SW-437: a callback whose type becomes a computation only once an unknown
-- is solved (`Answer ?flag`, as in `examples/accept/effect-rows-uses.sw`).
-- The call's row is settled as the empty row while the callback's type is
-- still unknown (its result is expected to be a plain list); once the type
-- is known to perform `Log`, D1124 makes the call effectful, which a pure
-- function can't be. Before SW-437 the callback's computations were silently
-- kept as data: `say` never ran.
ability Log where
  say: Nat → {Log} ()

def sayAndDouble (n: Nat): {Log} Nat :=
  say n
  n + n

def ResultOf [r: Type] (f: Nat → r): Type := r

def Answer: Bool → Type
  | True => ResultOf sayAndDouble
  | False => Nat

type Tagged (flag: Bool): Type =
  | Tag (n: Nat)

def answerOf: (flag: Bool) → Nat → Answer flag
  | True, n => sayAndDouble n
  | False, n => n

def Tagged.number [flag: Bool]: Tagged flag → Nat
  | Tag n => n

def answer [flag: Bool] (tagged: Tagged flag): Answer flag := answerOf flag tagged.number

-- The flag is known from the list, an argument after the callback.
def countA (numbers: List (Tagged True)): Nat := List.length (List.map numbers answer)

def pick [flag: Bool] (xs: List (Tagged flag)) (ys: List (Tagged flag)): Nat := 0

-- The flag is known only from a later expression of the declaration.
def countLater (numbers: List (Tagged True)): Nat :=
  let tagged := [Tag 3, Tag 4]
  let n := List.length (List.map tagged answer)
  n + pick tagged numbers
