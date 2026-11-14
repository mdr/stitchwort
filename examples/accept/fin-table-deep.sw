-- A table of 64 `Fin` numbers. Each number pattern is a chain of `FSucc`s
-- around `FZero`, and every link refines the context: the bound becomes
-- `Succ` of a new bound, the number `FSucc` of a new number, and every
-- entry that mentions them changes. The entries are chains themselves,
-- sharing their tails, so refining has to rebuild what they share once, not
-- each entry in full: that took about 10 s here, gave up on the last 17
-- arms' equations as too costly, and ran out of memory at 200 arms
-- (SW-2481).
import Std (Fin)

def code: (n: Nat) → Fin n → Nat
  | _, 0 => 0
  | _, 1 => 7
  | _, 2 => 14
  | _, 3 => 21
  | _, 4 => 28
  | _, 5 => 35
  | _, 6 => 42
  | _, 7 => 49
  | _, 8 => 56
  | _, 9 => 63
  | _, 10 => 6
  | _, 11 => 13
  | _, 12 => 20
  | _, 13 => 27
  | _, 14 => 34
  | _, 15 => 41
  | _, 16 => 48
  | _, 17 => 55
  | _, 18 => 62
  | _, 19 => 5
  | _, 20 => 12
  | _, 21 => 19
  | _, 22 => 26
  | _, 23 => 33
  | _, 24 => 40
  | _, 25 => 47
  | _, 26 => 54
  | _, 27 => 61
  | _, 28 => 4
  | _, 29 => 11
  | _, 30 => 18
  | _, 31 => 25
  | _, 32 => 32
  | _, 33 => 39
  | _, 34 => 46
  | _, 35 => 53
  | _, 36 => 60
  | _, 37 => 3
  | _, 38 => 10
  | _, 39 => 17
  | _, 40 => 24
  | _, 41 => 31
  | _, 42 => 38
  | _, 43 => 45
  | _, 44 => 52
  | _, 45 => 59
  | _, 46 => 2
  | _, 47 => 9
  | _, 48 => 16
  | _, 49 => 23
  | _, 50 => 30
  | _, 51 => 37
  | _, 52 => 44
  | _, 53 => 51
  | _, 54 => 58
  | _, 55 => 1
  | _, 56 => 8
  | _, 57 => 15
  | _, 58 => 22
  | _, 59 => 29
  | _, 60 => 36
  | _, 61 => 43
  | _, 62 => 50
  | _, 63 => 57
  | _, _ => 64
