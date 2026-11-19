--| What the hang lemmas say an element trails, against `Expr.trails` (ticket 18g): for a paren, its closer's comment
--| or what it holds trails; for a call, its last argument's. `Expr.trails` reads the words from the back, past
--| closers, so the equations need the words read back to stop at a word that is no closer: one in what the paren
--| holds or in the last argument (`Coded`), or an opener with no comment after it.

namespace Fmt.TrailsProofs
import Std (Bool, Eq, List, Nat, Option, Text)
import Syntax (Expr, Word)
import Fmt (..)
import Fmt.AppHangProofs (lastArg)

--| Some word is no closer.
def Coded (words: List Word): Bool := words.any (word => !isCloserText word.text)

--| Words read back past closers stop at the first that is no closer, so what follows it is never read.
theorem trailsBackCoded ∀ (front back: List Word)
    (code: Coded front = True):
    trailsBack (front ++ back) = trailsBack front :=
  match front, code with
    | [word, ..rest], code =>
      match closer: isCloserText word.text with
        | True => rewrite trailsBackCoded rest back code
        | False => byComputing

--| Words read back stop before a last word that trails nothing.
theorem trailsBackQuiet ∀ (front: List Word) (last: Word)
    (quiet: last.trails = False):
    trailsBack (front ++ [last]) = trailsBack front :=
  match front with
    | [] => rewrite quiet, Bool.andFalse (isCloserText last.text)
    | [word, ..rest] =>
      match closer: isCloserText word.text with
        | True => rewrite trailsBackQuiet rest last quiet
        | False => byComputing

--| A paren trails as its closer or what it holds does, when the words read back stop inside it or at an opener that
--| trails nothing.
theorem parenTrails ∀ (open: Word) (inner: Expr) (close: Word)
    (closer: isCloserText close.text = True)
    (stops: open.trails = False ∨ Coded inner.words.reverse = True):
    (Paren open inner close).trails = (close.trails || inner.trails) :=
  match stops with
    | Inl quiet =>
      rewrite List.reverseSnoc [open, ..inner.words] close,
          List.reverseCons open inner.words,
          closer,
          trailsBackQuiet inner.words.reverse open quiet
    | Inr code =>
      rewrite List.reverseSnoc [open, ..inner.words] close,
          List.reverseCons open inner.words,
          closer,
          trailsBackCoded inner.words.reverse [open] code

--| A call's arguments' words, read back, start with its last argument's.
theorem itemsBack ∀ (argument: Expr) (rest: List Expr):
    ∃ (front: List Word) => (itemsWords [argument, ..rest]).reverse = (lastArg argument rest).words.reverse ++ front :=
  match rest with
    | [] => ([], rewrite List.appendNil argument.words, List.appendNil argument.words.reverse)
    | [next, ..more] =>
      let (front, back) := itemsBack next more
      (
        front ++ argument.words.reverse,
        rewrite List.reverseAppend argument.words (itemsWords [next, ..more]),
            back,
            List.appendAssoc (lastArg next more).words.reverse front argument.words.reverse
      )

--| A call trails as its last argument does, when that has a word that is no closer.
theorem appTrails ∀ (head argument: Expr) (rest: List Expr)
    (code: Coded (lastArg argument rest).words.reverse = True):
    (App head [argument, ..rest]).trails = (lastArg argument rest).trails :=
  let (front, back) := itemsBack argument rest
  rewrite List.reverseAppend head.words (itemsWords [argument, ..rest]),
      back,
      List.appendAssoc (lastArg argument rest).words.reverse front head.words.reverse,
      trailsBackCoded (lastArg argument rest).words.reverse (front ++ head.words.reverse) code

theorem codedSnoc ∀ (front: List Word) (last: Word)
    (code: isCloserText last.text = False):
    Coded (front ++ [last]) = True :=
  match front with
    | [] => rewrite code
    | [word, ..rest] =>
      match isCloserText word.text with
        | True => codedSnoc rest last code
        | False => byComputing
