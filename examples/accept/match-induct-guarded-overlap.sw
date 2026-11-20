-- `f.induct` for a guarded arm that a later arm partly overlaps (G1, D3697):
-- one case per arm. The later arm's case takes, beside its variables and
-- induction hypothesis, that wherever the guarded arm's patterns match the
-- arguments, its guard is false: the hypothesis `withoutR.eq3` takes too.
import Std (Bool, Eq, List, Nat, Void)

type Kind = | Comma | Close | Word

def isComma: Kind → Bool
  | Comma => True
  | _ => False

def isCloser: Kind → Bool
  | Close => True
  | _ => False

def hasItem: List Kind → Bool
  | [] => False
  | [k, .._] => !isComma k

def withoutR (behind rest: List Kind): List Kind := match rest with
  | [] => behind
  | [comma, closer, ..after] if isComma comma && isCloser closer && hasItem behind => withoutR [closer, ..behind] after
  | [leaf, ..after] => withoutR [leaf, ..behind] after

theorem allWithout ∀ (q: Kind → Bool) (behind rest: List Kind)
    (kept: behind.all q = True)
    (coming: rest.all q = True):
    (withoutR behind rest).all q = True :=
  match induct (withoutR behind rest) with
    | eq1 _ => kept
    | eq2 _ comma closer after _ ih =>
      ih (Bool.andIntro (Bool.andLeft (Bool.andRight coming)) kept) (Bool.andRight (Bool.andRight coming))
    | eq3 _ leaf after _ ih => ih (Bool.andIntro (Bool.andLeft coming) kept) (Bool.andRight coming)

-- The same function with the pair test inside the arm.
def withoutR2 (behind rest: List Kind): List Kind := match rest with
  | [] => behind
  | [leaf, ..after] =>
    match after with
      | [closer, ..after1] =>
        if isComma leaf && isCloser closer && hasItem behind then withoutR2 [closer, ..behind] after1
        else withoutR2 [leaf, ..behind] after
      | [] => withoutR2 [leaf, ..behind] after

-- `eq3`'s hypothesis says the pair test failed: applied to the next leaf,
-- it is `(isComma leaf && isCloser closer && hasItem b) = False`, which
-- takes the `if`'s `else`.
theorem sameWithout ∀ (behind rest: List Kind): withoutR behind rest = withoutR2 behind rest := match induct (withoutR
    behind rest) with
  | eq1 _ => byComputing
  | eq2 b comma closer after guard ih => rewrite guard then ih
  | eq3 b leaf after notArm2 ih =>
    match after with
      | [] => byComputing
      | [closer, ..after1] => rewrite notArm2 closer after1 byComputing then ih
