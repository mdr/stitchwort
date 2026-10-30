-- SW-885: a record literal with an effectful field, as an argument, a
-- tuple part or a nested field (SW-883's gaps.sw cases), and `generic`,
-- where the parameter's type is fixed only by a later argument.
--
--   $ stitchwort check docs/proposals/postponement/sw885.sw
--
-- reports E-CANNOT-INFER at the literal in `inArgument`, `inTuple`,
-- `nested` and `generic` (30 Oct 2026).

import Std (List, Nat, Parse)
import Std.Parse (natDigits)

def shortNumber(): {Parse} Nat := natDigits 1 3

type Position = { x: Nat, y: Nat }

type Robot = { position: Position, speed: Nat }

def usePosition (p: Position): Nat := p.x

-- The parameter's type is known from the signature.
def inArgument(): {Parse} Nat := usePosition { x = shortNumber(), y = 0 }

def inTuple(): {Parse} (Position, Nat) := ({ x = shortNumber(), y = 0 }, 1)

def nested(): {Parse} Robot := { position = { x = shortNumber(), y = 0 }, speed = 0 }

-- The parameter's type is `a`, fixed only by the later argument.
def firstOf (x: a) (xs: List a): a := x

def generic (more: List Position): {Parse} Position := firstOf { x = shortNumber(), y = 0 } more

-- Fine today: the whole body, or annotated.
def wholeBody(): {Parse} Position := { x = shortNumber(), y = 0 }

def annotated(): {Parse} Nat := usePosition ({ x = shortNumber(), y = 0 }: Position)
