--| Slice 2's formatter on small cases: headers with parameter groups,
--| lambdas, `∀`, `∃` and ability rows. The harness (`dev/fmt-twin s2`)
--| compares every declaration within slices 1 and 2 with the Rust
--| formatter's; these pin the rules' main shapes, each expected text being
--| `stitchwort fmt`'s.

namespace Fmt.Tests
import Fmt (..)
import Std (Bool, Result, Text)

test "binders are spaced, and a theorem's groups of one type merged" :=
  formats
      "def f (x y:Nat)[a :Type](h:x=y):{Fail,IO} List a:=g (z=>z+1) x\ntheorem t ∀ (n: Nat) (m: Nat): ∀ k => ∃ (j: Nat) => n + m = j := p\n"
      "def f (x y: Nat) [a: Type] (h: x = y): {Fail, IO} List a := g (z => z + 1) x\ntheorem t ∀ (n m: Nat): ∀ k => ∃ (j: Nat) => n + m = j := p\n"

test "a long header puts each premise on a line of its own, the conclusion at 4" :=
  formats
      "def v (x: Nat) (h: x = 1) (yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy: Nat) (k: yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy = 2) (zzzzzzzzzzzzzzzz: Nat): Nat := x\n"
      "def v (x: Nat)\n    (h: x = 1) (yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy: Nat)\n    (k: yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy = 2) (zzzzzzzzzzzzzzzz: Nat):\n    Nat :=\n  x\n"

test "the last line of a header's variables never holds one alone" :=
  formats
      "def u (aaaaaaaaaaaaaaaaaaaaaaaaaa: Nat) (bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb: Bool) (ccccccccccccccccccccccccccc: Text) (dddd: Int) (e: X): Nat := 1\n"
      "def u (aaaaaaaaaaaaaaaaaaaaaaaaaa: Nat) (bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb: Bool)\n    (ccccccccccccccccccccccccccc: Text) (dddd: Int) (e: X):\n    Nat :=\n  1\n"

test "a lambda after `:=` keeps its line, its body below" :=
  formats
      "def k: Nat → Nat := y => someOtherFunctionName y argumentOne argumentTwo argumentThree argumentFour argumentFive argument\n"
      "def k: Nat → Nat := y =>\n  someOtherFunctionName y argumentOne argumentTwo argumentThree argumentFour argumentFive argument\n"

test "an `∃` too long for its line breaks its body, never its binders" :=
  formats
      "def p: Prop := ∃ (aaaaaaaaaaaaaaa: Nat) (bbbbbbbbbbbbbbbbbbbbb: Nat) => someLongFunctionName aaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbb cccccccccccccccccccc\n"
      "def p: Prop :=\n  ∃ (aaaaaaaaaaaaaaa: Nat) (bbbbbbbbbbbbbbbbbbbbb: Nat) => someLongFunctionName aaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbb\n      cccccccccccccccccccc\n"

test "comments in a header keep its lines" :=
  formats "def g (x: Nat)\n    -- the colon\n    : Nat := x\ndef f (x: Nat) -- about x\n    (y: Nat): Nat := x\n"
      "def g (x: Nat)\n    -- the colon\n    : Nat :=\n  x\ndef f (x: Nat) -- about x\n    (y: Nat):\n    Nat :=\n  x\n"
