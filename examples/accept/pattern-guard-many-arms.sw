-- Guarded catch-alls above many arms are linear, not exponential.

def tok: Char → Nat
  | c if c.toNat == 1001 => 1
  | c if c.toNat == 1002 => 2
  | c if c.toNat == 1003 => 3
  | c if c.toNat == 1004 => 4
  | c if c.toNat == 1005 => 5
  | c if c.toNat == 1006 => 6
  | c if c.toNat == 1007 => 7
  | c if c.toNat == 1008 => 8
  | c if c.toNat == 1009 => 9
  | c if c.toNat == 1010 => 10
  | 'a' => 0
  | 'b' => 0
  | 'c' => 0
  | 'd' => 0
  | 'e' => 0
  | 'f' => 0
  | 'g' => 0
  | 'h' => 0
  | 'i' => 0
  | 'j' => 0
  | 'k' => 0
  | 'l' => 0
  | 'm' => 0
  | 'n' => 0
  | 'o' => 0
  | 'p' => 0
  | 'q' => 0
  | 'r' => 0
  | 's' => 0
  | 't' => 0
  | 'u' => 0
  | 'v' => 0
  | 'w' => 0
  | 'x' => 0
  | 'y' => 0
  | 'z' => 0
  | _ => 99

test "tok" := tok 'a' == 0 ∧ tok '!' == 99
