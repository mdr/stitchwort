--| Slice 5a's formatter on small cases: namespace lines, imports, tests
--| and a definition's arms. The harness (`dev/fmt-twin s5a`) compares
--| every declaration within slices 1 to 5a with the Rust formatter's;
--| these pin the main shapes, each expected text being `stitchwort fmt`'s.

namespace Fmt.Tests
import Fmt (..)
import Std (Bool, Result, Text)

test "a namespace line, imports flat and broken, and the blank lines between" :=
  formats
      "namespace A.B -- c\nimport Std (Bool, foo as bar)\nimport C (..)\n\n\nimport Syntax (Arm, BindingKind, Comments, DefKind, Expr, Guard, Header, Imported, ImportItem, InfixKind, Let, Note, Param, Pattern)\n"
      "namespace A.B -- c\nimport Std (Bool, foo as bar)\nimport C (..)\n\nimport Syntax (\n  Arm,\n  BindingKind,\n  Comments,\n  DefKind,\n  Expr,\n  Guard,\n  Header,\n  Imported,\n  ImportItem,\n  InfixKind,\n  Let,\n  Note,\n  Param,\n  Pattern\n)\n"

test "an import holding a comment stays broken" :=
  formats "import X (\n  -- about a\n  a, -- after a\n\n  b as c\n)\n"
      "import X (\n  -- about a\n  a, -- after a\n\n  b as c\n)\n"

test "a test's body follows `:=` as a definition's" :=
  formats
      "test \"a\" := f \"x\" == 'c'\ntest \"long\" := someFunction aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb ccccccccccccccc\n"
      "test \"a\" := f \"x\" == 'c'\ntest \"long\" :=\n  someFunction aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n      ccccccccccccccc\n"

test "a definition's arms, one a line at 2, with comments and a blank line kept" :=
  formats
      "def f: Nat → Nat\n  | 0 => 1 -- one\n  -- above\n  | Succ n => n\n\n  | _ => 2\ndef g (n: Nat) (m: Nat): Nat → Nat → Nat\n  | 0, _ => 1\n  | n, m => n + m\n"
      "def f: Nat → Nat\n  | 0 => 1 -- one\n  -- above\n  | Succ n => n\n\n  | _ => 2\ndef g (n m: Nat): Nat → Nat → Nat\n  | 0, _ => 1\n  | n, m => n + m\n"

test "a pipe in an arm, and a pipe in a test, are outside the slice" :=
  refuses "test \"a\" := (xs |> length) == 1\n" && refuses "def f: Nat → Nat\n  | x => x |> g\n"
