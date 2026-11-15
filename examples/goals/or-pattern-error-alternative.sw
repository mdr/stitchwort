-- expect-error: E-TYPE-MISMATCH
-- An error in an or-pattern's arm is in one case, and the alternative
-- that makes it is marked.
import Std (Bool, Option, Text)

theorem alternatives ∀ (p: Text → Option Bool → Prop) (hn: ∀ (s: Text) => p s None) (s: Text) (o: Option Bool): p s o :=
  match s, o with
    | "ab", Some False => ?
    | _, (None | Some True) => hn s
    | _, _ => ?
