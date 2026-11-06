-- expect-error: E-NOT-A-RECORD
-- A pattern follows the declaration too: braces after `Some` are a record
-- pattern for its argument, so they need a record there.

def nameOf: Option Nat → Text
  | Some { name, .. } => name
  | None => "none"
