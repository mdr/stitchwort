-- expect-error: E-TYPE-MISMATCH
-- An error in an arm checked in several cases names the case it is in.
-- `hp _` is right for the one-character text only; the cases are the texts
-- that start with `"ab"` and carry on, and so on.
import Std (Char, Nat, Text, Bool, List)

theorem oneCharacter ∀ (p: Text → Prop) (hp: ∀ (c: Char) => p (MkText [c])) (s: Text): p s := match s with
  | "ab" => ?
  | "" => ?
  | _ => hp _
