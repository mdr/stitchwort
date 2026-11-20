-- Shows: the hypotheses one condition gets as a guard (an ∧ of Bools), as a named Bool guard (¬pair …), and as an if (… = True / … = False). Open goals by design.
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

def withoutR (behind rest: List Kind): List Kind := match rest with
  | [] => behind
  | [comma, closer, ..after] if isComma comma && isCloser closer && hasItem behind => withoutR [closer, ..behind] after
  | [leaf, ..after] => withoutR [leaf, ..behind] after

def withoutP (behind rest: List Kind): List Kind := match rest with
  | [] => behind
  | [comma, closer, ..after] if pair closer comma behind => withoutP [closer, ..behind] after
  | [leaf, ..after] => withoutP [leaf, ..behind] after

def withoutI (behind rest: List Kind): List Kind := match rest with
  | [] => behind
  | [leaf] => [leaf, ..behind]
  | [comma, closer, ..after] =>
    if isComma comma && isCloser closer && hasItem behind then withoutI [closer, ..behind] after
    else withoutI [comma, ..behind] [closer, ..after]

theorem a ∀ (behind rest: List Kind): withoutR behind rest = withoutR behind rest := match induct (withoutR behind
    rest) with ?

theorem b ∀ (behind rest: List Kind): withoutP behind rest = withoutP behind rest := match induct (withoutP behind
    rest) with ?

theorem c ∀ (behind rest: List Kind): withoutI behind rest = withoutI behind rest := match induct (withoutI behind
    rest) with ?
