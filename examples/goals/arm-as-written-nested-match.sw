-- expect-error: E-TYPE-MISMATCH
-- A `match` inside a catch-all arm: its arms are shown as written inside
-- the outer arm as written, and each is checked once for every case of
-- both arms.
import Std (Char, Nat, Text, Bool, List, Option)

-- The inner arms keep `o` as the outer catch-all leaves it, where the goal
-- used to read `p (Some False) "ab"`. The inner catch-all is checked in 10
-- cases: 5 texts for each of the outer arm's 2 cases.
theorem textInOption ∀ (p: Option Bool → Text → Prop) (o: Option Bool) (s: Text): p o s := match o with
  | Some True => ?
  | _ =>
    match s with
      | "ab" => ?
      | _ => ?

-- Three deep: each level's catch-all is undone.
theorem threeDeep ∀ (p: Option Bool → Option Bool → Nat → Prop) (o r: Option Bool) (n: Nat): p o r n := match o with
  | Some True => ?
  | _ =>
    match r with
      | None => ?
      | _ =>
        match n with
          | 0 => ?
          | _ => ?

-- What the outer arm's body changed before the inner `match` stays as it
-- made it: `h` is rewritten, `o` is still as the outer arm is written.
theorem rewrittenFirst ∀ (p: Option Bool → Text → Prop) (o: Option Bool) (s: Text) (n: Nat)
    (h: n + 0 = 3):
    p o s ∧ n = 3 :=
  match o with
    | Some True => ?
    | _ =>
      rewrite Std.Nat.addZero n at h then
        match s with
          | "ab" => ?
          | _ => ?

-- An error names its case at both levels.
theorem errorInBoth ∀ (p: Option Bool → Option Bool → Prop) (k: p None None) (o r: Option Bool): p o r := match o with
  | Some True => ?
  | _ =>
    match r with
      | Some True => ?
      | _ => k
