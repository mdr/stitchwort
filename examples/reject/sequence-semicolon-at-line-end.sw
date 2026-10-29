-- expect-error: E-PARSE
-- A block's lines need no `;` between them. A `;` at the end of a line
-- would start a sequence `(a; b)`, but the next line is the block's next
-- line, so nothing follows it.
import Std (Nat, Parse)
import Std.Parse (char, nat)

def number(): {Parse} Nat :=
  char ',';
  nat()
