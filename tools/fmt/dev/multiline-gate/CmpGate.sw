--| A "printed output unchanged" check (SW-4155): every declaration's printed text at eight widths, slice 1's document and slice 5a's.
namespace CmpGate
import Std (Bool, Doc, IO, List, Nat, Option, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Driver1 (..)
import Fmt.OutputStatements (..)

def widths: List Nat := [6, 12, 20, 30, 45, 60, 80, 120]

def printsOf (tag: Text) (doc: Option Doc): Text := match doc with
  | None => Text.concat [tag, ":none"]
  | Some doc => Text.concat [tag, ":\n", Text.joinWith (widths.map (width => Doc.print doc width)) "\n~~\n"]

def declLine (decl: Decl): Text := Text.concat [
  "@@ within1=",
  if decl.within1 then "T" else "F",
  "\n",
  printsOf "doc1" decl.doc1,
  "\n",
  printsOf "doc5a" decl.doc5a
]

def check (source: Text): Text := match tidiedOf source with
  | None => "notidy"
  | Some file => Text.joinWith (file.decls.map declLine) "\n"

def casesFrom (current: List Text): List Text → List Text
  | [] => []
  | [line, ..rest] =>
    if line == "###" then [Text.concat current.reverse, ..casesFrom [] rest] else casesFrom ["\n", line, ..current] rest

def main(): {IO} () := IO.write (Text.joinWith ((casesFrom [] IO.readAll().lines).map check) "\n####\n")
