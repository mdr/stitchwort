-- Shows: an ih premise hasItem [leaf, ..behind] displayed as its unfolding (isComma leaf).not. Open goals by design.
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

def pair (closer comma: Kind) (behind: List Kind): Bool := isComma comma && isCloser closer && hasItem behind

def kindOk (k: Kind) (rest: List Kind): Bool := match k, rest with
  | Comma, [Close, .._] => False
  | _, _ => True

def withoutP (behind rest: List Kind): List Kind := match rest with
  | [] => behind
  | [comma, closer, ..after] if pair closer comma behind => withoutP [closer, ..behind] after
  | [leaf, ..after] => withoutP [leaf, ..behind] after

theorem b ∀ (behind rest: List Kind)
    (item: hasItem behind = True)
    (ok: kindOk Comma rest = True):
    withoutP behind rest = withoutP behind rest :=
  match induct (withoutP behind rest) with
    | eq1 _ => byComputing
    | eq2 behind comma closer after g ih => ?
    | eq3 behind leaf after notArm2 ih => ?
