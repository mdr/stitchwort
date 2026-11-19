-- Checks: withoutR written with an `if` inside a two-leaf arm gets withoutR.induct, and the proof is four alternatives.
import Std (Bool, Eq, List, Nat, Option, Pair)

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
  | [leaf] => [leaf, ..behind]
  | [comma, closer, ..after] =>
    if isComma comma && isCloser closer && hasItem behind then withoutR [closer, ..behind] after
    else withoutR [comma, ..behind] [closer, ..after]

theorem allWithout ∀ (q: Kind → Bool) (behind rest: List Kind)
    (kept: behind.all q = True)
    (coming: rest.all q = True):
    (withoutR behind rest).all q = True :=
  match induct (withoutR behind rest) with
    | eq1 _ => kept
    | eq2 _ _ => Bool.andIntro (Bool.andLeft coming) kept
    | eq3IfTrue _ _ _ _ _ ih =>
      ih (Bool.andIntro (Bool.andLeft (Bool.andRight coming)) kept) (Bool.andRight (Bool.andRight coming))
    | eq3IfFalse _ _ _ _ _ ih => ih (Bool.andIntro (Bool.andLeft coming) kept) (Bool.andRight coming)
