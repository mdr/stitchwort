--| SW-4130's computed check: for each slice 1 declaration of a source's tidied tree with the tree facts, the printed
--| text at several widths lexes to leaves that keep `hangs` (what `DeclElements` gives through `printedHangs1`).
namespace ElementsGate
import Std (Bool, Doc, IO, List, Nat, Option, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Driver1 (..)
import Fmt.OutputStatements (..)
import Fmt.OneLineStatements (..)
import Fmt.StandsProofs (..)

def Word.gHomedAfter (word: Word) (before: Bool): Bool := !word.trails || word.noted || before

def Expr.gHomed: Expr → Bool
  | Atom _ _ => True
  | Paren open inner close => inner.gHomed && close.gHomedAfter (Paren open inner close).trailsBeforeClose
  | Tuple open items trailing close =>
    gAllHomed items && close.gHomedAfter (Tuple open items trailing close).trailsBeforeClose
  | ListOf open items trailing close =>
    gAllHomed items && close.gHomedAfter (ListOf open items trailing close).trailsBeforeClose
  | App head arguments => head.gHomed && gAllHomed arguments
  | Infix InfixBinary left _ right => left.gHomed && right.gHomed
  | Infix InfixArrow left operator right => left.gHomed && right.gHomed && !operator.trails && !right.noted
  | Prefix _ operand => operand.gHomed
  | _ => False

def gAllHomed: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.gHomed && gAllHomed rest

def Decl.gHomed: Decl → Bool
  | Definition [] header (Assigned _ value) => header.result.gHomed && value.gHomed
  | _ => False

def flag (b: Bool): Text := if b then "T" else "F"

def hangsAtWidth (doc: Doc) (width: Nat): Bool := match lex (Doc.print doc width) with
  | Ok out => hangs out.leaves
  | Err _ => False

def declLine (decl: Decl): Text :=
  let facts := decl.within1 && decl.shaped1 && decl.settled1 && decl.lexical1 && decl.unreturned1
  match decl.doc1 with
    | None => "nodoc"
    | Some doc =>
      let all := [6, 12, 20, 30, 45, 60, 80, 120].all (width => hangsAtWidth doc width)
      Text.concat [
        "facts=",
        flag facts,
        " settled=",
        flag decl.settled1,
        " homed=",
        flag decl.gHomed,
        " edge=",
        flag decl.edgeQuiet1,
        " one=",
        flag decl.oneLine1,
        " hangs=",
        flag all
      ]

def check (source: Text): Text := match tidiedOf source with
  | None => "notidy"
  | Some file => if !file.within1 then "outside" else Text.joinWith (file.decls.map declLine) "\n"

--| The sources in lines, each ended by a line `###`.
def casesFrom (current: List Text): List Text → List Text
  | [] => []
  | [line, ..rest] =>
    if line == "###" then [Text.concat current.reverse, ..casesFrom [] rest] else casesFrom ["\n", line, ..current] rest

def main(): {IO} () := IO.write (Text.joinWith ((casesFrom [] IO.readAll().lines).map check) "\n")
