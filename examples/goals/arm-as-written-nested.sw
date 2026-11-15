-- A catch-all arm's goal is the match's goal with only the arm's own
-- patterns substituted, wherever the other arms' patterns went deeper.
import Std (Char, Nat, Text, Bool, List, Option)

-- The catch-all is also the case `None`, which the last leaf checked did not
-- show: the goal used to read `p (Some False)`.
theorem someTrue (p: Option Bool → Prop) (o: Option Bool): p o := match o with
  | Some True => ?
  | _ => ?

theorem someNumber (p: Option Nat → Prop) (o: Option Nat): p o := match o with
  | Some 3 => ?
  | _ => ?

theorem someText (p: Option Text → Prop) (o: Option Text): p o := match o with
  | Some "a" => ?
  | _ => ?

theorem singleton (p: List Nat → Prop) (l: List Nat): p l := match l with
  | [x] => ?
  | _ => ?

-- A pair of values matched at once: nothing is split that the arm didn't
-- ask for, but the arm is still checked more than once.
theorem pair (p: Nat → Char → Prop) (n: Nat) (c: Char): p n c := match (n, c) with
  | (5, 'x') => ?
  | _ => ?

-- Matching an expression: the goal says the expression, not a variable the
-- compiler made for it.
theorem expression (p: Text → Prop) (q: Nat → Text) (s: Nat): p (q s) := match q s with
  | "ab" => ?
  | _ => ?

-- A hole whose type is written by the arm is unchanged.
theorem written (p: Text → Prop) (s: Text): p s := match s with
  | "ab" => ?
  | other => (? : p other)
