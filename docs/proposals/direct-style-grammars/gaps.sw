-- Evidence for docs/proposals/direct-style-grammars.md §2.5: what goes wrong
-- with effectful arguments today. This file is meant to be refused:
--
--   $ stitchwort check docs/proposals/direct-style-grammars/gaps.sw
--
-- reports E-CANNOT-INFER at `inArgument`, `inTuple` and `nested`,
-- E-TYPE-MISMATCH at `dependent`, and W-NO-EFFECT for `forgotten` (since
-- SW-889; nothing before). `unitInTuple` was E-NOT-EMPTY until SW-886.

import Std (Nat, Parse, Vec)
import Std.Parse (char, natDigits)

def shortNumber(): {Parse} Nat := natDigits 1 3

type Position = { x: Nat, y: Nat }

type Robot = { position: Position, speed: Nat }

def usePosition (p: Position): Nat := p.x

-- 1. A record literal with an effectful field, where a type is expected
-- but the literal is not the whole result: E-CANNOT-INFER. The same
-- literal as the whole body, or annotated, is fine.
def inArgument(): {Parse} Nat := usePosition { x = shortNumber(), y = 0 }

def inTuple(): {Parse} (Position, Nat) := ({ x = shortNumber(), y = 0 }, 1)

def nested(): {Parse} Robot := { position = { x = shortNumber(), y = 0 }, speed = 0 }

def wholeBody(): {Parse} Position := { x = shortNumber(), y = 0 }

def annotated(): {Parse} Robot := { position = ({ x = shortNumber(), y = 0 }: Position), speed = 0 }

-- 2. An effectful argument's value is unknown to the checker, so a later
-- parameter's type that mentions it can't be met: E-TYPE-MISMATCH,
-- "expected `Vec Nat x`, but this has type `Vec Nat 2`".
def sized (n: Nat) (v: Vec Nat n): Nat := n

def dependent(): {Parse} Nat := sized (shortNumber()) (Vec.replicate 2 0)

-- 3. `()` inside a tuple pattern was refused (`let () := …` alone was
-- fine); `_` worked. Accepted since SW-886.
def unitInTuple(): {Parse} Nat :=
  let ((), n) := (char ',', shortNumber())
  n

-- 4. A statement that names a parser without calling it is accepted and
-- does nothing. It had no warning; since SW-889 it is W-NO-EFFECT, "call
-- it: `shortNumber()`".
def forgotten(): {Parse} Nat :=
  char ','
  shortNumber
  shortNumber()
