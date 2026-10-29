-- expect-warning: W-NO-EFFECT
-- A line of a block, or the first part of a sequence `a; b`, is run for its
-- effects and its value dropped. One that performs no effects does nothing:
-- a parser named but not called, a function missing its argument, a sum, or
-- a `map` written as if it changed the list. Each warns. Lines that perform
-- something don't, even when their value is dropped.
import Std (Nat, List, Parse)
import Std.Parse (char, natDigits)

def shortNumber(): {Parse} Nat := natDigits 1 3

def forgotten(): {Parse} Nat :=
  char ','
  shortNumber
  shortNumber()

def missingArgument(): {Parse} Nat := (char; shortNumber())

def sum (x: Nat): {Parse} Nat :=
  x + 1
  shortNumber()

def mapped (list: List Nat): List Nat :=
  list.map (n => n + 1)
  list

-- None of these warn.
def skipped(): {Parse} Nat :=
  shortNumber()
  char ','
  ()
  shortNumber()

def readEach (list: List Nat): {Parse} List Nat :=
  list.map (n => shortNumber())
  list
