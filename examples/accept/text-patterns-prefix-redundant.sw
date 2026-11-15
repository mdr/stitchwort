-- expect-warning: W-REDUNDANT
-- An arm a prefix pattern above it always takes first is never chosen: a
-- longer prefix, or an exact text, that starts with the same characters.
-- The other way round is fine: an exact text, then the prefix for the rest.
import Std (Nat, Text)

def kind: Text → Nat
  | "-" ++ rest => 1
  | "--" ++ name => 2
  | "-v" => 3
  | _ => 0

def flag: Text → Nat
  | "--" => 0
  | "--" ++ name => name.length
  | _ => 0

test "the prefix takes them" := kind "--x" == 1 && kind "-v" == 1
test "the exact text first" := flag "--" == 0 && flag "--ab" == 2
