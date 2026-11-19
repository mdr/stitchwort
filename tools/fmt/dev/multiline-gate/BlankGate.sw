--| SW-4153's check: an item's kept blank line with no comments above it (`[BreakParent, LineStart, Blank]`) is always
--| entered right after a line break when printed, so dropping its `LineStart` prints the same text.
namespace BlankGate
import Std (Bool, Doc, IO, List, Nat, Option, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Driver1 (..)
import Fmt.OutputStatements (..)
import Fmt.OneLineStatements (..)
import Fmt.StandsProofs (..)

def strip (doc: Doc): Doc := match doc with
  | Concat docs => Concat (stripAll docs)
  | Fill items => Fill (stripList items)
  | Choice options => Choice (stripList options)
  | Nest more inner => Nest more (strip inner)
  | Align inner => Align (strip inner)
  | AlignInset inner => AlignInset (strip inner)
  | Displaced inner => Displaced (strip inner)
  | OneLineBelow inner => OneLineBelow (strip inner)
  | Flatten inner => Flatten (strip inner)
  | Group inner hard => Group (strip inner) hard
  | NarrowGroup max inner hard => NarrowGroup max (strip inner) hard
  | IdGroup id inner hard => IdGroup id (strip inner) hard
  | IfBroken id broken flat => IfBroken id (strip broken) (strip flat)
  | other => other

def stripAll (docs: List Doc): List Doc := match docs with
  | [BreakParent, LineStart, Blank, ..rest] => [BreakParent, Blank, ..stripAll rest]
  | [doc, ..rest] => [strip doc, ..stripAll rest]
  | [] => []

def count (doc: Doc): Nat := match doc with
  | Concat docs => countAll docs
  | Fill items => countList items
  | Choice options => countList options
  | Nest _ inner => count inner
  | Align inner => count inner
  | AlignInset inner => count inner
  | Displaced inner => count inner
  | OneLineBelow inner => count inner
  | Flatten inner => count inner
  | Group inner _ => count inner
  | NarrowGroup _ inner _ => count inner
  | IdGroup _ inner _ => count inner
  | IfBroken _ broken flat => count broken + count flat
  | _ => 0

def countList (docs: List Doc): Nat := match docs with
  | [] => 0
  | [doc, ..rest] => count doc + countList rest

def countAll (docs: List Doc): Nat := match docs with
  | [BreakParent, LineStart, Blank, ..rest] => 1 + countAll rest
  | [doc, ..rest] => count doc + countAll rest
  | [] => 0

def flag (b: Bool): Text := if b then "T" else "F"

def declLine (decl: Decl): Text :=
  let facts := decl.within1 && decl.shaped1 && decl.settled1 && decl.lexical1 && decl.unreturned1
  match decl.doc1 with
    | None => "nodoc"
    | Some doc =>
      let same := [6, 12, 20, 30, 45, 60, 80, 120].all (width => Doc.print doc width == Doc.print (strip doc) width)
      Text.concat ["facts=", flag facts, " blanks=", (count doc).toText, " same=", flag same]

def check (source: Text): Text := match tidiedOf source with
  | None => "notidy"
  | Some file => if !file.within1 then "outside" else Text.joinWith (file.decls.map declLine) "\n"

def casesFrom (current: List Text): List Text → List Text
  | [] => []
  | [line, ..rest] =>
    if line == "###" then [Text.concat current.reverse, ..casesFrom [] rest] else casesFrom ["\n", line, ..current] rest

def main(): {IO} () := IO.write (Text.joinWith ((casesFrom [] IO.readAll().lines).map check) "\n")

def stripList (docs: List Doc): List Doc := match docs with
  | [] => []
  | [doc, ..rest] => [strip doc, ..stripList rest]
