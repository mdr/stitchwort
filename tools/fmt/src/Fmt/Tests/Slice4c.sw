--| Slice 4c's formatter on small cases: records, updates, a constructor's
--| named fields, spreads, record patterns and membership. The harness
--| (`dev/fmt-twin s4c`) compares every declaration within slices 1 to 5a,
--| 4b and 4c with the Rust formatter's; these pin the main shapes, each
--| expected text being `stitchwort fmt`'s.

namespace Fmt.Tests
import Fmt (..)
import Std (Bool, Result, Text)

test "record literals, updates, a constructor's fields and a field of an update" :=
  formats
      "def a: P := { x = 1, y }\ndef b (p: P): P := { p | x = 2 }\ndef f: Shape := Circle { radius = 1, centre = origin }\ntheorem t (p: P): { p | x = 3 }.x = 3 := rfl\n"
      "def a: P := { x = 1, y }\ndef b (p: P): P := { p | x = 2 }\ndef f: Shape := Circle { radius = 1, centre = origin }\ntheorem t ∀ (p: P): { p | x = 3 }.x = 3 := rfl\n"

test "spreads and membership, in a header and a body" :=
  formats
      "def c: List Nat := [1, ..xs]\ndef d (x: Nat) (s: Set Nat) (h: x ∈ s): Bool := x ∈ s && y ∉ t\ndef m: List Nat := [aaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, ccccccccccccccccccccccccccccccc, ..(f ddddddddddddd)]\n"
      "def c: List Nat := [1, ..xs]\ndef d (x: Nat) (s: Set Nat) (h: x ∈ s): Bool := x ∈ s && y ∉ t\ndef m: List Nat :=\n  [aaaaaaaaaaaaaaaaaaaaaaa, bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, ccccccccccccccccccccccccccccccc, ..(f ddddddddddddd)]\n"

test "record patterns in arms and after `let`, and a constructor's named fields" :=
  formats
      "def e: P → Nat\n  | { x, y = Some z, .. } => x + z\n  | { x, .. } => x\ndef g: Shape → Nat\n  | Circle { radius, .. } => radius\n  | _ => 0\ndef n: P → Nat\n  | { aaaaaaaaaaaaaaaaaaaaaaaaaaaaa = Some bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, cccccccccccccccccccccccccccccc = dddddddd, .. } => 0\ndef o: Nat := let { x, y } := p; x + y\n"
      "def e: P → Nat\n  | { x, y = Some z, .. } => x + z\n  | { x, .. } => x\ndef g: Shape → Nat\n  | Circle { radius, .. } => radius\n  | _ => 0\ndef n: P → Nat\n  | {\n      aaaaaaaaaaaaaaaaaaaaaaaaaaaaa = Some bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,\n      cccccccccccccccccccccccccccccc = dddddddd,\n      ..\n    } => 0\ndef o: Nat := let { x, y } := p; x + y\n"

test "a long record breaks one field a line, after `:=`, after an update's `|` and hugged by a call" :=
  formats
      "def h: Record := { aaaaaaaaaaaaaaaaaaaaaaaaaa = bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, cccccccccccccccccccccccc = ddddddddddddddddddddddd x }\ndef i (r: R): R := { r | aaaaaaaaaaaaaaaaaaaaaaaaaa = bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, cccccccccccccccccccccccc = ddddddddddddddddddddddd x }\ndef j: Nat := someFunction argument { aaaaaaaaaaaaaaaaaaaaaaaaaa = bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb, ccccccccccccccc = dddddddd x }\n"
      "def h: Record := {\n  aaaaaaaaaaaaaaaaaaaaaaaaaa = bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,\n  cccccccccccccccccccccccc = ddddddddddddddddddddddd x\n}\ndef i (r: R): R := { r |\n  aaaaaaaaaaaaaaaaaaaaaaaaaa = bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,\n  cccccccccccccccccccccccc = ddddddddddddddddddddddd x\n}\ndef j: Nat := someFunction argument {\n  aaaaaaaaaaaaaaaaaaaaaaaaaa = bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,\n  ccccccccccccccc = dddddddd x\n}\n"

test "comments in a record keep it broken, and a comment after `=` puts the value below" :=
  formats
      "def k: R := {\n  a = 1, -- one\n  b = 2\n}\ndef l: R := { a = 1,\n  -- above\n  b = 2 }\ndef q: R := { a = -- why\n  1 }\n"
      "def k: R := {\n  a = 1, -- one\n  b = 2\n}\ndef l: R := {\n  a = 1,\n  -- above\n  b = 2\n}\ndef q: R := {\n  a = -- why\n    1\n}\n"

test "the empty record and a comment after an update's record are outside the slice" :=
  refuses "def u: R := {}\n" && refuses "def v (r: R): R := { r -- c\n  | a = 1 }\n"
