--| How wide a document is printed flat: what a rule needs to know to decide
--| whether items fit side by side, without printing them in its own
--| layout.

namespace Fmt.Doc
import Std (Bool, Eq, Nat, Option, Text)

--| The page width of a flat measure: wider than any document a program
--| writes, so nothing in a flat print is cut short by the width.
def flatLimit: Nat := 1000000000

--| The width, in characters, of `doc` printed flat on one line, or `None`
--| if it can't be: it forces a line break (`forcesBreak`), or printing it
--| flat still holds one (a flat `Choice`'s first option, say, or a waiting
--| comment's break). A `LineSuffix` comment counts, as printed at the end.
def Doc.flatWidth (doc: Doc): Option Nat :=
  let flat := print (Flatten doc) flatLimit
  if doc.forcesBreak || flat.any (char => char == '\n') then None else Some flat.length

--| A document that forces a line break has no flat width.
theorem flatWidthForced ∀ (doc: Doc) (forced: doc.forcesBreak = True): doc.flatWidth = None := rewrite forced

--| An `if` that is `Some width` took its `else` branch, and the value is
--| `width`.
theorem ifSome ∀ (condition: Bool) (found width: Nat)
    (known: (if condition then None else Some found) = Some width):
    found = width ∧ condition = False :=
  match condition, known with | False, same => (Option.someInjective same, byComputing)

--| A disjunction that is false has a false right side.
theorem orFalseRight ∀ (left right: Bool) (plain: (left || right) = False): right = False :=
  match left, right, plain with | False, False, _ => byComputing

--| When `flatWidth` is a width, it is the length of the flat print, which
--| holds no line break.
theorem flatWidthPrint ∀ (doc: Doc) (width: Nat)
    (known: doc.flatWidth = Some width):
    (print (Flatten doc) flatLimit).length = width
      ∧ (print (Flatten doc) flatLimit).any (char => char == '\n') = False :=
  ifSome
    (doc.forcesBreak || (print (Flatten doc) flatLimit).any (char => char == '\n'))
    (print (Flatten doc) flatLimit).length
    width
    known
    |> (lengthIs, plain) => (lengthIs, orFalseRight doc.forcesBreak _ plain)

--| An instance of `flatWidthPrint`, so it isn't vacuous: two words with a
--| line between them are 5 wide flat.
theorem flatWidthExample: (Doc.concat [Doc.text "ab", Line, Doc.text "cd"]).flatWidth = Some 5 := byComputing
