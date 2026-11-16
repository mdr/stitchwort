-- At a catch-all arm the goal is the arm as written, and "computes to" is
-- what the last case it is checked in computes to, with the matched value
-- written as the variable where it occurs whole: `f s` steps to `2` in each
-- case, because each is one of `f`'s own.
import Std (Char, Nat, Text, Bool, List, Option)

def f: Text → Nat
  | "ab" => 1
  | "" => 0
  | _ => 2

theorem steps ∀ (s: Text): f s ≠ 0 ∨ s = "" := match s with
  | "ab" => ?
  | "" => ?
  | _ => ?

-- Where the leaf's computation takes the text apart, the cells it mentions
-- are listed.
theorem length ∀ (p: Text → Prop) (s: Text): p s ∧ s.length = s.length := match s with
  | "ab" => ?
  | _ => ?

-- A value is folded back into the variable only where it has cells of its
-- own: `Blue` also occurs in `f c = Blue`, so the line says `Blue = Blue`.
type Color = | Red | Green | Blue

def paint: Color → Color
  | Red => Red
  | _ => Blue

theorem painted ∀ (c: Color): paint c = Blue := match c with
  | Red => ?
  | _ => ?

-- Nor are the cells of a split the arm didn't need: the catch-all must also
-- prove `False = True` for `Some False`, which stays visible.
def isSomeTrue: Option Bool → Bool
  | Some True => True
  | _ => False

theorem someTrue ∀ (o: Option Bool): isSomeTrue o = True := match o with
  | Some True => ?
  | _ => ?
