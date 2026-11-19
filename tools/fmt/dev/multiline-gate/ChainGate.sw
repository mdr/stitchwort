--| SW-4149's check of `LinkFacts`' right operand: at each chain node of a declaration with the tree facts, what the
--| operator and the right operand carry (comments above or after), and whether the right operand's element, where the
--| chain lays it, keeps `hangs` after `->`, which glues the fold. `LinkFacts` before SW-4149 asked `HangsAt` of every
--| right operand that is no chain of the same level: from every seat, the glued one after `->` among them.
namespace ChainGate
import Std (Bool, Doc, IO, List, Nat, Option, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Driver1 (..)
import Fmt.OutputStatements (..)
import Fmt.OneLineStatements (..)
import Fmt.StandsProofs (..)

--| Counts: chain nodes, operators with comments above, operators with a comment after, right operands with comments
--| above, those whose element fails `hangs` after `A -> ` at some width, and noted operators whose leaf does.
type Counts = {
  nodes: Nat,
  opNoted: Nat,
  opTrails: Nat,
  rightNoted: Nat,
  gluedFails: Nat,
  opGluedFails: Nat
}

def zero: Counts := { nodes = 0, opNoted = 0, opTrails = 0, rightNoted = 0, gluedFails = 0, opGluedFails = 0 }

def add (one two: Counts): Counts := {
  nodes = one.nodes + two.nodes,
  opNoted = one.opNoted + two.opNoted,
  opTrails = one.opTrails + two.opTrails,
  rightNoted = one.rightNoted + two.rightNoted,
  gluedFails = one.gluedFails + two.gluedFails,
  opGluedFails = one.opGluedFails + two.opGluedFails
}

def bit (b: Bool): Nat := if b then 1 else 0

def hangsAtWidth (doc: Doc) (width: Nat): Bool := match lex (Doc.print doc width) with
  | Ok out => hangs out.leaves
  | Err _ => False

--| The right operand's element after `A -> `, at eight widths.
def gluedHangs (doc: Doc): Bool :=
  let whole := Doc.concat [Doc.text "A", Doc.text " ", Doc.text "->", Doc.text " ", doc]
  [6, 12, 20, 30, 45, 60, 80, 120].all (width => hangsAtWidth whole width)

def walk (expr: Expr) (around: Around): Counts := match expr with
  | Paren _ inner _ => walk inner (around.next False 1)
  | Prefix _ operand => walk operand (around.next False 1)
  | Infix _ left operator right =>
    let rightAround := around.next operator.trails (left.size + 1)
    let here := {
      nodes = 1,
      opNoted = bit operator.noted,
      opTrails = bit operator.trails,
      rightNoted = bit right.noted,
      gluedFails = bit (right.noted && !gluedHangs (right.el rightAround)),
      opGluedFails =
        let operatorAround := around.next left.trails left.size
        bit (operator.noted && !gluedHangs (operator.leaf operatorAround operatorAround.at))
    }
    add here (add (walk left around) (walk right rightAround))
  | App head arguments => add (walk head around) (walkAll arguments (around.next False head.size))
  | Tuple _ items _ _ => walkAll items (around.next False 1)
  | ListOf _ items _ _ => walkAll items (around.next False 1)
  | _ => zero

def walkAll (exprs: List Expr) (around: Around): Counts := match exprs with
  | [] => zero
  | [expr, ..rest] => add (walk expr around) (walkAll rest (around.next False expr.size))

def declCounts (decl: Decl): Counts := match decl with
  | Definition [] header (Assigned _ value) =>
    let start: Around := { before = False, hoisted = True, item = False, at = 3, inArm = False }
    add (walk header.result start) (walk value { start | at = 4 + header.result.size })
  | _ => zero

def declLine (decl: Decl): Text :=
  let facts := decl.within1 && decl.shaped1 && decl.settled1 && decl.lexical1 && decl.unreturned1
  let counts := declCounts decl
  Text.concat [
    "facts=",
    if facts then "T" else "F",
    " nodes=",
    counts.nodes.toText,
    " opNoted=",
    counts.opNoted.toText,
    " opTrails=",
    counts.opTrails.toText,
    " rightNoted=",
    counts.rightNoted.toText,
    " gluedFails=",
    counts.gluedFails.toText,
    " opGluedFails=",
    counts.opGluedFails.toText
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
