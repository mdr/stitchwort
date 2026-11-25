-- An operation performed directly takes the lemma about the operation
-- (std's `Parse.givesMark`) even where a `@[walk]` lemma about a function
-- that performs it fits too: the lemmas about the operation itself are
-- tried first, and a function's only where none of them fits (the call as
-- a `match` in the proof leaves it, SW-4775).

import Std (Parse, Nat)

def markHere(): {Parse Nat} Parse.Mark Nat := Parse.mark()

@[walk]
theorem givesMarkHere: Parse.Gives Parse.Invariant.any (() => markHere()) ((at: Parse.Mark Nat) => True) :=
  Parse.givesMark

def marked(): {Parse Nat} Nat :=
  let here := Parse.mark()
  here.left

theorem givesMarked: Parse.Gives Parse.Invariant.any (() => marked()) (n => True) := byWalking []
