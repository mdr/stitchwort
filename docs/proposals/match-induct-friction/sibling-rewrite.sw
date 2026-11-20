-- Shows: rewrite walkR.eqK then ih closes a sibling walker's case, its arguments and hypotheses found in context (checks clean).
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

def walkA (behind rest: List Kind): List Kind := match rest with
  | [] => behind.reverse
  | [comma, closer, ..after] if isComma comma && isCloser closer && hasItem behind => walkA [closer, ..behind] after
  | [leaf, ..after] => walkA [leaf, ..behind] after

def walkR (behind rest: List Kind): List Kind := match rest with
  | [] => behind
  | [comma, closer, ..after] if isComma comma && isCloser closer && hasItem behind => walkR [closer, ..behind] after
  | [leaf, ..after] => walkR [leaf, ..behind] after
theorem t ∀ (behind rest: List Kind): walkA behind rest = (walkR behind rest).reverse := match induct (walkA behind
    rest) with
  | eq1 _ => byComputing
  | eq2 behind comma closer after guard ih => rewrite walkR.eq2 then ih
  | eq3 behind leaf after notArm2 ih => rewrite walkR.eq3 then ih
