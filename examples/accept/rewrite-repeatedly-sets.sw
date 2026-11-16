-- `rules name := [r1, <- r2]` names a set of rules, declared once and used
-- wherever a `rewrite repeatedly` lists rules: `[appends]`, or beside
-- others, `[steps, appends]`. A set may name other sets; their rules take
-- its place in order. Its rules are checked where it is declared, as
-- `rewrite repeatedly` checks rules, and are named lemmas and definitions
-- only (a hypothesis or an applied lemma goes in the call itself).
-- (docs/syntax.md, "rewrite repeatedly".)
import Std (Eq, List, Nat)

rules appends := [List.appendAssoc, List.appendNil]

rules lists := [appends, List.reverseCons]

def double (n: Nat): Nat := n + n

rules doubling := [double]

theorem regroup ∀ (xs ys zs: List Nat): ((xs ++ ys) ++ zs) ++ [] = xs ++ (ys ++ zs) := rewrite repeatedly [appends]

-- A set beside a hypothesis, and a set of sets.
theorem regroupFrom ∀ (xs ys zs: List Nat) (h: ys = zs): (xs ++ ys) ++ [] = xs ++ zs := rewrite repeatedly [h, lists]

theorem doubled ∀ (m: Nat) (h: m + m = 4): double m = 4 := rewrite repeatedly [doubling]

-- `at h` rewrites the type of `h` instead of the goal; `then t` sees `h`
-- rewritten, as with `rewrite … at h then t`.
theorem fromFact ∀ (xs ys zs: List Nat) (h: ((xs ++ ys) ++ zs) ++ [] = []): xs ++ (ys ++ zs) = [] :=
  rewrite repeatedly [appends] at h then h

-- Without `then`, `rewrite repeatedly … at h` is `h` itself, rewritten.
theorem fromFactAlone ∀ (xs ys: List Nat) (h: (xs ++ ys) ++ [] = [1]): xs ++ ys = [1] :=
  rewrite repeatedly [List.appendNil] at h
