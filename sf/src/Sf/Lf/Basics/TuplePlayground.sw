-- Software Foundations, Volume 1: Logical Foundations, Basics.v, section
-- "Tuples" (module `TuplePlayground`), ported to Stitchwort. Copyright and
-- licence: sf/LICENSE-SF.

-- A namespace of its own, as the book's module is, so that `B0` and `B1`
-- here don't clash with the constructors of `Bin` at the end of the
-- chapter.

namespace Sf.Lf.Basics.TuplePlayground

-- A single constructor with several parameters can be used to make a
-- tuple type. As an example, take the four bits of a nybble (half a
-- byte). First a type `Bit` that resembles `Bool` (with constructors `B0`
-- and `B1` for the two bit values), then `Nybble`, which is essentially a
-- tuple of four bits.

type Bit = | B1 | B0

type Nybble = | Bits (b0: Bit) (b1: Bit) (b2: Bit) (b3: Bit)

-- Rocq's `Check (bits B1 B0 B1 B0) : nybble` asks for the type of an
-- expression and checks it. Stitchwort has no command inside a file for
-- that; in `stitchwort repl`, `:t Bits B1 B0 B1 B0` prints
-- `Bits B1 B0 B1 B0: Sf.Lf.Basics.TuplePlayground.Nybble`, and in the
-- editor the type shows on hover.

-- The `Bits` constructor wraps its contents. Pattern matching unwraps
-- them, as in `allZero`, which tests whether every bit of a nybble is
-- `B0`. (The underscore `_` is a wildcard pattern, which saves inventing
-- names for variables that aren't used.)

def allZero (nb: Nybble): Bool := match nb with
  | Bits B0 B0 B0 B0 => True
  | Bits _ _ _ _ => False

-- Rocq's `Compute` evaluates an expression and prints the result. Here a
-- `test` states the result and `stitchwort test` checks it; `stitchwort
-- eval` or the REPL prints a value instead.

test "allZero (Bits B1 B0 B1 B0)" := allZero (Bits B1 B0 B1 B0) == False

test "allZero (Bits B0 B0 B0 B0)" := allZero (Bits B0 B0 B0 B0) == True
