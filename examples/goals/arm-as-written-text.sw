-- A catch-all after text literals shows the arm as written. The match
-- compiler splits the text into characters to test `"ab"` and `""`, and
-- checks the catch-all once per way those tests can fail, but the goal is
-- `p s`: the splits the arm's own patterns didn't ask for are undone, and the
-- goal says how many times the arm is checked.
import Std (Char, Nat, Text, Bool, List)

theorem plain ∀ (p: Text → Prop) (s: Text): p s := match s with
  | "ab" => ?
  | "" => ?
  | _ => ?

-- A hypothesis about the matched variable is shown about the variable too.
theorem withHypothesis ∀ (p: Text → Prop) (s: Text) (h: p s): p s := match s with
  | "ab" => ?
  | _ => ?

-- The arm's own name for the matched value is the one shown.
theorem named ∀ (p: Text → Prop) (s: Text): p s := match s with
  | "ab" => ?
  | other => ?

-- A name for the case itself (`match e: s`) is the one place the case's
-- shape stays: `rewrite` can use it. The goal is still about `s`.
theorem equation ∀ (p: Text → Prop) (s: Text): p s := match e: s with
  | "ab" => ?
  | _ => ?

-- Arms written as clauses.
theorem clauses ∀ (p: Text → Prop): (s: Text) → p s
  | "ab" => ?
  | _ => ?

-- A character, and a list of characters.
theorem character ∀ (p: Char → Prop) (c: Char): p c := match c with
  | 'a' => ?
  | _ => ?

theorem characters ∀ (p: List Char → Prop) (l: List Char): p l := match l with
  | ['a'] => ?
  | _ => ?
