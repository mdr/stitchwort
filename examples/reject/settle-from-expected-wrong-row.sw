-- expect-error: E-TYPE-MISMATCH
-- A lemma's ability arguments are taken from the goal before its arguments
-- are checked, so a parser whose row doesn't fit is blamed where it is
-- passed, with the two rows side by side, rather than the whole call with
-- the goal unfolded or the numeral `5` (SW-3282, SW-3305), with a note
-- saying where `t` came from (SW-3311).
import Std (List, Nat, Char, Bool)

ability St (s: Type) where
  put: s → {St s} ()

ability Src (t: Type) where
  next: () → {Src t} t

def Good (p: () → {Src t, St s} Char) (k: List t) (z: s): Prop := k = k

theorem good ∀ (p: () → {Src t, St s} Char) (k: List t) (z: s): Good p k z := byComputing

def counting(): {Src Char, St Nat} Char :=
  St.put 3
  Src.next()

def flagging(): {Src Char, St Bool} Char :=
  St.put Bool.True
  Src.next()

theorem wrongRow: Good counting ['c'] 5 := good flagging ['c'] 5
