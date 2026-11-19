--| The multi-line read-back gate (SW-4121, SW-4126): `run.sh` copies this module into `tools/fmt/src` to run it.
--|   stitchwort run MultilineGate.mainA < FILE.cases
--|   stitchwort run MultilineGate.mainB < FILE.cases
--| FILE.cases: sources, each ended by a line `###`.
namespace MultilineGate
import Std (Bool, IO, List, Nat, Option, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Driver1 (..)
import Fmt.OutputStatements (..)
import Fmt.TriviaStatements (..)
import Fmt.StandsProofs (..)
import Fmt.SettleOutputProofs (..)
import Fmt.PassProofs (..)
import Syntax.SettleProofs (tokens)

--| Whether a declaration's printed tokens lie on one line, its value perhaps on the next: after `def`, the name and
--| `:`, no token of the type starts a line, and none of the value after its first. The gate only classifies by it
--| (`one` or `multi`); the driver no longer tests it.
def gateOnLine: List Token → Bool
  | [_, _, _, ..rest] => gateTypeOnLine rest
  | _ => False

def gateTypeOnLine: List Token → Bool
  | [] => True
  | [token, ..rest] => if token.kind == ColonEq then gateValueOnLine rest else !token.lineStart && gateTypeOnLine rest

def gateValueOnLine: List Token → Bool
  | [] => True
  | [_, ..rest] => rest.all (token => !token.lineStart)

def Decl.gateOneLine (decl: Decl): Bool := gateOnLine (tokens decl.leaves1)

def SourceFile.gateOneLine (file: SourceFile): Bool := file.decls.all Decl.gateOneLine

def flag (b: Bool): Text := if b then "T" else "F"

--| The driver without its one-line test.
def loose (source: Text): Option Text := match lex source with
  | Err _ => None
  | Ok lexed =>
    if !leavesWithin1 lexed.leaves then None
    else
      match parseFile lexed.settledOnce with
        | Err _ => None
        | Ok parsed => if !parsed.within1 then None else Some parsed.tidy1.printed1

--| Check A: the printer's side. `one` or `multi`, then: tree facts, hung, stood, lexes, groups hang, reads back,
--| formats to itself.
def checkA (source: Text): Text := match lex source with
  | Err _ => "nolex"
  | Ok lexed =>
    if !leavesWithin1 lexed.leaves then "leaves"
    else
      match parseFile lexed.settledOnce with
        | Err _ => "noparse"
        | Ok parsed =>
          if !parsed.within1 then "outside"
          else
            let file := parsed.tidy1
            let facts :=
              file.shaped1
                && file.settled1
                && file.lexical1
                && file.commaFree
                && file.unreturned1
                && file.decls.all Decl.unreturned1
            let lexes := match lex file.printed1 with
              | Ok out => sameLexed out file.lexed1
              | Err _ => False
            let groupsHang := (groupsOf file.lexed1.settledOnce.leaves).all hangs
            let reads := readsBack file.lexed1 file
            let again := loose file.printed1 == Some file.printed1
            Text.concat [
              if file.gateOneLine then "one " else "multi ",
              flag facts,
              flag file.hung1,
              flag file.stood1,
              flag lexes,
              flag groupsHang,
              flag reads,
              flag again
            ]

--| A group's tokens on one line, glued where they were glued.
def flatFrom (before: Option Token): List Leaf → Text
  | [] => "\n"
  | [leaf, ..rest] =>
    let gap := match before with
      | None => ""
      | Some previous => if !leaf.token.lineStart && endColumn previous == leaf.token.column then "" else " "
    Text.concat [gap, leaf.token.text, flatFrom (Some leaf.token) rest]

--| Check B: the statement without the printer. A layout whose groups hang parses to the tree its tokens make on
--| one line.
def checkB (layout: Text): Text := match lex layout with
  | Err _ => "nolex"
  | Ok lexed =>
    let settled := lexed.settledOnce
    let groups := groupsOf settled.leaves
    let hung := groups.all hangs
    let multi := groups.any (group => !gateOnLine (group.map (leaf => leaf.token)))
    match lex (Text.concat (groups.map (flatFrom None))) with
      | Err _ => "noflatlex"
      | Ok flatLexed =>
        if !leavesWithin1 flatLexed.leaves then "leaves"
        else
          match parseFile flatLexed.settledOnce with
            | Err _ => "flatnoparse"
            | Ok want =>
              if !want.within1 then "outside"
              else
                let head := Text.concat [if multi then "multi " else "one ", "hung=", flag hung]
                match parseFile settled with
                  | Err _ => Text.concat [head, " PARSEFAIL"]
                  | Ok got => Text.concat [head, " same=", flag (got.meaning.plain.dump == want.meaning.plain.dump)]

def outA (sources: List Text): Text := Text.joinWith (sources.map checkA) "\n"

def outB (sources: List Text): Text := Text.joinWith (sources.map checkB) "\n"

--| The sources in lines, each ended by a line `###`.
def casesFrom (current: List Text): List Text → List Text
  | [] => []
  | [line, ..rest] =>
    if line == "###" then [Text.concat current.reverse, ..casesFrom [] rest] else casesFrom ["\n", line, ..current] rest

def mainA(): {IO} () := IO.write (outA (casesFrom [] IO.readAll().lines))

def mainB(): {IO} () := IO.write (outB (casesFrom [] IO.readAll().lines))
