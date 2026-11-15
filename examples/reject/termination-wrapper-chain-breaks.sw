-- expect-error: E-TERMINATION
-- Pairs with accept/termination-wrapper-honest.sw: the part inside the
-- wrapper must be reached from the matched field through matches on that
-- field and its parts. Each of these matches something else, a lambda's
-- variable (named `v` too: levels count, not names), a function's result, a
-- grown `let` or a grown list, so `r` is as long as `v` or longer and each
-- function runs for ever. All four are refused.
type W (a: Type): Type = | MkW (x: a)

def apply (xs: List Nat) (k: List Nat → Nat): Nat := k [0, 0, ..xs]

def shadowed: W (List Nat) → Nat
  | MkW v => apply v (v =>
    match v with
      | [_, ..r] => shadowed (MkW r)
      | [] => 0)

def grow (xs: List Nat): List Nat := [0, 0, ..xs]

def throughResult: W (List Nat) → Nat
  | MkW v =>
    match grow v with
      | [_, ..r] => throughResult (MkW r)
      | [] => 0

def throughLet: W (List Nat) → Nat
  | MkW v =>
    let big := [0, 0, ..v]
    match big with
      | [_, ..r] => throughLet (MkW r)
      | [] => 0

def throughList: W (List Nat) → Nat
  | MkW v =>
    match [0, 0, ..v] with
      | [_, ..r] => throughList (MkW r)
      | [] => 0
