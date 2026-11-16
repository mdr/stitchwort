-- `rewrite repeatedly [rules]`: the rules rewrite the goal wherever they
-- fit, each left to right (`<-` turns one round), until none fits, and then
-- the goal is closed by computing, by hypotheses that contradict each
-- other, or by a hypothesis of its type. With `then t`, `t` proves what is
-- left. The proof is the chain of `rewrite` steps it made; the kernel checks
-- it. (docs/syntax.md, "rewrite repeatedly"; docs/proposals/simp-revisited.md.)
import Std (Bool, Eq, List, Nat)

-- Equations from the library, their arguments left open: each fits
-- wherever its left side is, as often as it does.
theorem regroup ∀ (xs ys zs: List Nat): ((xs ++ ys) ++ zs) ++ [] = xs ++ (ys ++ zs) :=
  rewrite repeatedly [List.appendAssoc, List.appendNil]

-- Hypotheses are rules too, by name; so is the recursive call of a proof by
-- arms. `List.reverseSnoc` as the library proves it with `rewrite`, one rule
-- at a time and each with its arguments.
theorem reverseSnoc ∀ (xs: List a) (x: a): List.reverse (List.append xs [x]) = [x, ..List.reverse xs] := match xs with
  | [] => byComputing
  | [y, ..rest] => rewrite repeatedly [List.reverseCons, reverseSnoc rest x]

theorem chain ∀ (a b c: Nat) (first: a = b) (second: b = c): a + a = c + c := rewrite repeatedly [first, second]

-- A `Bool` fact is the equation `test = True`, so it rewrites the test.
def small (n: Nat): Bool := n < 10

theorem picked ∀ (n: Nat) (isSmall: small n): (if small n then 1 else 2) = 1 := rewrite repeatedly [isSmall]

-- A definition's name is one step of it, `double n = n + n`, where it is
-- written in the goal.
def double (n: Nat): Nat := n + n

theorem doubled ∀ (m: Nat) (h: m + m = 4): double m = 4 := rewrite repeatedly [double]

-- What the rules leave is closed by a hypothesis of its type.
theorem fromHypothesis ∀ (xs ys: List Nat) (h: xs ++ ys = ys): (xs ++ []) ++ ys = ys :=
  rewrite repeatedly [List.appendNil]

-- `then t` proves what is left; a closer such as `arithmetic` doesn't
-- depend on its exact form.
theorem thenArithmetic ∀ (xs: List Nat) (n: Nat) (h: n < xs.length): n < (xs ++ []).length + 1 :=
  rewrite repeatedly [List.appendNil] then arithmetic
