-- Expected to fail (E-NO-INDUCT): a guarded arm that a later arm partly overlaps (§3.1, gap G1).
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
  | [comma, closer, ..after] if isComma comma && isCloser closer && hasItem behind => withoutR [closer, ..behind] after
  | [leaf, ..after] => withoutR [leaf, ..behind] after

theorem allWithout ∀ (q: Kind → Bool) (behind rest: List Kind)
    (kept: behind.all q = True)
    (coming: rest.all q = True):
    (withoutR behind rest).all q = True :=
  match induct (withoutR behind rest) with | eq1 => ?
