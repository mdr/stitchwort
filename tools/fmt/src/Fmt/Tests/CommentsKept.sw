--| `CommentsKept` on slice 1's driver (SW-4233): sources in slice 1's grammar with comments in every kind of
--| place, each of which the driver formats keeping them, as `slice1KeepsComments` proves. The two blank lines
--| `CommentsKept` leaves out (D3695) are pinned too: the driver drops them, and the strict comparison sees it.
--| Views and holders are compared by their texts.

namespace Fmt.Tests
import Fmt (..)
import Std (Bool, List, Nat, Option, Result, Text)
import Syntax (Lexed, lex)
import Fmt.Driver1 (formatWithin1)
import Fmt.Grammar1 (inGrammar1)

def CommentView.shown (view: CommentView): Text :=
  view.text ++ (if view.ownLine then " own" else " trailing") ++ (if view.blankAbove then " blank;" else ";")

def Holder.shown (holder: Holder): Text :=
  holder.token
    ++ " "
    ++ holder.above.toText
    ++ (if holder.trailing then " trailing" else "")
    ++ (if holder.blankBelow then " blank;" else ";")

def viewsShown (views: List CommentView): Text := views.foldLeft "" (shown view => shown ++ view.shown)

def holdersShown (holders: List Holder): Text := holders.foldLeft "" (shown holder => shown ++ holder.shown)

--| `CommentsKept` as a test, or `strict`: with no blank line left out.
def commentsKeptTest (strict: Bool) (source output: Lexed): Bool :=
  let before := source.settledBare
  let after := output.settled
  if strict then
    viewsShown before.commentViews == viewsShown after.commentViews
      && holdersShown before.holders == holdersShown after.holders
  else
    viewsShown (unheaded before.commentViews) == viewsShown (unheaded after.commentViews)
      && holdersShown (before.holders.map Holder.forDocs) == holdersShown (after.holders.map Holder.forDocs)

def keptBy (strict: Bool) (source out: Text): Bool := match lex source, lex out with
  | Ok before, Ok after => commentsKeptTest strict before after
  | _, _ => False

--| The source is in slice 1's grammar, the driver formats it, and `CommentsKept` holds (`strict`: with every blank
--| line).
def formatKeeps (strict: Bool) (source: Text): Bool :=
  inGrammar1 source
    && match formatWithin1 source with
      | Ok out => keptBy strict source out
      | Err _ => False

def keepsComments (source: Text): Bool := formatKeeps False source

def keepsEveryBlank (source: Text): Bool := formatKeeps True source

test "comments kept: a blank line between comments and a declaration, a name, a type, `:=`" :=
  keepsComments "-- c\n\ndef d: A := a\n"
    && keepsComments "def\n  -- c\n\n  d: A := a\n"
    && keepsComments "def d:\n  -- c\n\n  A := a\n"
    && keepsComments "def d: A\n  -- c\n\n  := a\n"
    && keepsComments "def d: A := -- c\n\n  -- e\n  a\n"

test "comments kept: inside expressions, above and below" :=
  keepsComments "def d: A := a +\n\n  -- c\n\n  b\n"
    && keepsComments "def d: A := a\n  -- c\n\n  + b\n"
    && keepsComments "def d: A := f (\n  -- c\n\n  a)\n"
    && keepsComments "def d: A := f\n  -- c\n\n  a\n"
    && keepsComments "def d: A := f\n  -- c\n\n  (a)\n"
    && keepsComments "def d: A := [a,\n  -- c\n\n  b]\n"
    && keepsComments "def d: A := [a\n  -- c\n  ]\n"

test "comments kept: commas, arrows and the end of the file" :=
  keepsComments "def d: A := [a, -- c\n  ]\n"
    && keepsComments "def d: A := [a\n\n  -- c\n  ,\n  ]\n"
    && keepsComments "def d: A -> -- c\n  B := a\n"
    && keepsComments "def d: A ->\n\n  -- c\n  B := a\n"
    && keepsComments "def d: A := a\n\n-- c\n\n-- e\n"
    && keepsComments "\n\n\ndef d: A := a\n"

test "comments kept with every blank line, where the driver keeps them all" :=
  keepsEveryBlank "-- c\n\ndef d: A := a\n"
    && keepsEveryBlank "def d: A := a +\n\n  -- c\n\n  b\n"
    && keepsEveryBlank "def d: A := [a\n  -- c\n  ]\n"
    && keepsEveryBlank "def d: A := a\n\n-- c\n\n-- e\n"

--| D3695: the blank line above a file's first comment, and between a closer and the comments above it, are dropped
--| by the driver and left out of `CommentsKept`.
test "comments kept but for the blank lines D3695 leaves out" :=
  keepsComments "\n-- c\ndef d: A := a\n"
    && !keepsEveryBlank "\n-- c\ndef d: A := a\n"
    && keepsComments "\n\n-- c\ndef d: A := a\n"
    && keepsComments "\n-- c\n"
    && !keepsEveryBlank "\n-- c\n"
    && keepsComments "def d: A := (a\n  -- c\n\n  )\n"
    && !keepsEveryBlank "def d: A := (a\n  -- c\n\n  )\n"
    && keepsComments "def d: A := (a, b\n  -- c\n\n  )\n"
    && keepsComments "def d: A := [a,\n  -- c\n\n  ]\n"
    && !keepsEveryBlank "def d: A := [a,\n  -- c\n\n  ]\n"
