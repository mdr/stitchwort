-- expect-error: E-TYPE-MISMATCH
-- A text pattern matches a `Text` or a `List Char`, nothing else.
def code (n: Nat): Nat := match n with
  | "one" => 1
  | _ => 0
