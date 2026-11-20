-- Where unfolding only the calls on the path can't reach every copy of a
-- `match`'s expression, the `match` uses the search over the computed goal,
-- as before. The walk opens at most 64 calls: here the first `label n`
-- opens and shows `isBig n`, then `pads n` uses up the rest on calls that
-- hold nothing, so the second `label n` stays folded with its copy hidden
-- inside. That disagrees with the search over the computed goal, which
-- replaces both, so its result is used: the `True` arm's goal is `[1, 8, 1]
-- = [1, 8, 1]`, which computes. (docs/proposals/partial-unfold.md §3.)
import Std (Bool, List, Nat)

def isBig (n: Nat): Bool := 10 < n

def label (n: Nat): Nat := if isBig n then 1 else 0

def pad (n: Nat): Nat := n

def pad8 (n: Nat): List Nat := [pad n, pad n, pad n, pad n, pad n, pad n, pad n, pad n]

def pads (n: Nat): List (List Nat) := [pad8 n, pad8 n, pad8 n, pad8 n, pad8 n, pad8 n, pad8 n, pad8 n]

theorem bothCopies ∀ (n: Nat):
    [label n, (pads n).length, label n] = [if isBig n then 1 else 0, 8, if isBig n then 1 else 0] :=
  match isBig n with
    | True => byComputing
    | False => byComputing
