--| SW-4153 experiment: an item with a kept blank line and no comments, entered mid-line (the separator before it laid
--| as a space, which `Lays` allows), against the same item displaced.
namespace BlankMid
import Std (Bool, Doc, IO, List, Nat, Option, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.OutputStatements (..)

def hangsText (text: Text): Bool := match lex text with
  | Ok out => hangs out.leaves
  | Err _ => False

def flag (b: Bool): Text := if b then "T" else "F"

def build (displace: Bool) (first second: Expr): Doc :=
  let a1 := firstAround False False False 1
  let a2 := firstAround False False first.trails (1 + first.size)
  let second :=
    if displace then Doc.concat [BreakParent, LineStart, Blank, Displaced (second.el { a2 | hoisted = True })]
    else second.el a2
  Doc.concat [
    Doc.text "def",
    Doc.text " ",
    Doc.text "x:",
    Doc.text " ",
    Doc.text "Nat",
    Doc.text " ",
    Doc.text ":=",
    Nest 2
      (Doc.concat [
        HardLine,
        Doc.text "[",
        Nest 2 (Doc.concat [HardLine, first.el a1, Closing ",", Doc.text " ", second]),
        HardLine,
        Closing "]"
      ])
  ]

def one (displace: Bool) (first second: Expr) (width: Nat): Text :=
  let printed := Doc.print (build displace first second) width
  Text.concat [
    "--- displace=",
    flag displace,
    " width=",
    width.toText,
    " hangs=",
    flag (hangsText printed),
    "\n",
    printed
  ]

def check (source: Text): Text := match tidiedOf source with
  | None => "notidy"
  | Some file =>
    match file.decls with
      | [Definition [] header (Assigned _ (ListOf _ [first, second] _ _))] => Text.concat [
        "blankBefore=",
        flag second.lead.comments.blankBefore,
        "\n",
        Text.joinWith ([False, True].flatMap (d => [8, 30].map (w => one d first second w))) "\n"
      ]
      | _ => "shape"

def casesFrom (current: List Text): List Text → List Text
  | [] => []
  | [line, ..rest] =>
    if line == "###" then [Text.concat current.reverse, ..casesFrom [] rest] else casesFrom ["\n", line, ..current] rest

def main(): {IO} () := IO.write (Text.joinWith ((casesFrom [] IO.readAll().lines).map check) "\n=====\n")
