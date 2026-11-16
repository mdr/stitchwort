/-
The printer: a port, function for function, of
`tools/toyfmt/src/Toy/Doc/Print.sw`. Lean wants a definition before its
use, so the functions come bottom-up; each is otherwise as in the toy.
-/
import Toy.Doc

namespace Toy
open Doc

inductive Mode where
  | Flat
  | Break

def Mode.isFlat : Mode → Bool
  | .Flat => true
  | .Break => false

inductive Cmd where
  | Print (indent : Nat) (mode : Mode) (doc : Doc)
  | FillSep (indent : Nat) (item : Doc)

structure Printer where
  width : Nat
  out : List Text
  column : Nat
  owed : Option Nat
  atLineStart : Bool
  suffixes : List Text
  lineIndent : Nat
  newlinesAtEnd : Nat
  started : Bool

open Cmd Mode

def Doc.joinLines : List Doc → List Doc
  | [] => []
  | [only] => [only]
  | item :: items => item :: Line :: joinLines items

def trimSpaces : List Text → List Text
  | [] => []
  | last :: earlier => if last.all (· == ' ') then trimSpaces earlier else last :: earlier

def fitsFrom (fuel : Nat) (stack : List (Mode × Doc)) (rest : List Cmd) (left : Nat) (suffix : Bool) : Bool :=
  match fuel with
  | 0 => true
  | more + 1 =>
    match stack with
    | [] =>
      match rest with
      | Print _ mode doc :: others => fitsFrom more [(mode, doc)] others left suffix
      | _ => true
    | (mode, doc) :: stack =>
      match doc with
      | .Empty => fitsFrom more stack rest left suffix
      | Blank => fitsFrom more stack rest left suffix
      | LineSuffix _ => fitsFrom more stack rest left true
      | BreakParent => !mode.isFlat && fitsFrom more stack rest left suffix
      | Chunk _ width =>
        if suffix then false else width <= left && fitsFrom more stack rest (left - width) suffix
      | Line => !mode.isFlat || (!suffix && 1 <= left && fitsFrom more stack rest (left - 1) suffix)
      | SoftLine => !mode.isFlat || (!suffix && fitsFrom more stack rest left suffix)
      | HardLine => !mode.isFlat
      | LineStart => !mode.isFlat
      | CommentEnd => !mode.isFlat
      | LineStartHere => !mode.isFlat
      | Nest _ inner => fitsFrom more ((mode, inner) :: stack) rest left suffix
      | Flatten inner => fitsFrom more ((Flat, inner) :: stack) rest left suffix
      | Group inner hard =>
        if hard && mode.isFlat then false
        else fitsFrom more ((if hard then Break else mode, inner) :: stack) rest left suffix
      | Concat docs => fitsFrom more (docs.map (fun inner => (mode, inner)) ++ stack) rest left suffix
      | Fill items =>
        if mode.isFlat then
          fitsFrom more ((Doc.joinLines items).map (fun inner => (mode, inner)) ++ stack) rest left suffix
        else
          match items with
          | [] => true
          | first :: _ => fitsFrom more [(Flat, first)] [] left false
      | OneLineBelow _ => true
      | Choice options =>
        match (if mode.isFlat then options.head? else options.getLast?) with
        | none => fitsFrom more stack rest left suffix
        | some option => fitsFrom more ((mode, option) :: stack) rest left suffix

def fits (fuel : Nat) (next : List (Mode × Doc)) (rest : List Cmd) (left : Nat) : Bool :=
  fitsFrom fuel next rest left false

def fitsFlat (fuel : Nat) (doc : Doc) (left : Nat) : Bool := fits fuel [(Flat, doc)] [] left

namespace Printer

def start (width : Nat) : Printer where
  width := width
  out := []
  column := 0
  owed := none
  atLineStart := true
  suffixes := []
  lineIndent := 0
  newlinesAtEnd := 0
  started := false

def left (printer : Printer) : Nat := printer.width - printer.owed.getD printer.column

def payIndent (printer : Printer) : Printer :=
  match printer.owed with
  | none => printer
  | some 0 => { printer with owed := none, column := 0 }
  | some indent => { printer with out := Text.replicate indent ' ' :: printer.out, owed := none, column := indent }

def put (printer : Printer) (text : Text) (width : Nat) : Printer :=
  let paid := printer.payIndent
  { paid with
    out := text :: paid.out,
    column := paid.column + width,
    atLineStart := false,
    newlinesAtEnd := 0,
    started := true }

def continuation (printer : Printer) (indent : Nat) : Nat := Nat.max indent (printer.lineIndent + 2)

def flushOne (printer : Printer) (comment : Text) : Printer :=
  let spaced := if printer.atLineStart then printer.payIndent else { printer with out := Text.space :: printer.out }
  { spaced with out := comment :: spaced.out, atLineStart := false, newlinesAtEnd := 0, started := true }

def flushSuffixes (printer : Printer) : Printer :=
  printer.suffixes.foldl flushOne { printer with suffixes := [] }

def newline (printer : Printer) (indent : Nat) : Printer :=
  let flushed := { printer with out := trimSpaces printer.out }.flushSuffixes
  { flushed with
    out := Text.newline :: flushed.out,
    column := 0,
    owed := some indent,
    atLineStart := true,
    lineIndent := indent,
    newlinesAtEnd := flushed.newlinesAtEnd + 1,
    started := true }

def write (printer : Printer) (indent : Nat) (text : Text) (width : Nat) : Printer :=
  if text.isEmpty then printer
  else if printer.suffixes.isEmpty then printer.put text width
  else if text.all (· == ' ') then printer
  else (printer.newline (printer.continuation indent)).put text width

def lineStart (printer : Printer) (indent : Nat) : Printer :=
  if printer.atLineStart then printer else printer.newline (printer.continuation indent)

def blank (printer : Printer) : Printer :=
  if printer.atLineStart && printer.started && printer.newlinesAtEnd < 2 then
    { printer with out := Text.newline :: printer.out, newlinesAtEnd := printer.newlinesAtEnd + 1 }
  else printer

def fitsHere (printer : Printer) (total : Nat) (next : List (Mode × Doc)) (rest : List Cmd) : Bool :=
  fitsFrom total next rest printer.left (!printer.suffixes.isEmpty)

def choose (printer : Printer) (total indent : Nat) (rest : List Cmd) : (options : List Doc) → Doc
  | [] => Doc.Empty
  | [last] => last
  | option :: others =>
    let fitting := match option with
      | OneLineBelow inner => printer.width >= indent + 2 && fitsFlat total inner (printer.width - indent - 2)
      | _ => printer.fitsHere total [(Break, option)] rest
    if fitting then option else printer.choose total indent rest others

def printDoc (printer : Printer) (total indent : Nat) (mode : Mode) (doc : Doc) (rest : List Cmd) :
    Printer × List Cmd :=
  match doc with
  | .Empty => (printer, rest)
  | BreakParent => (printer, rest)
  | Chunk text width => (printer.write indent text width, rest)
  | Line =>
    if mode.isFlat && printer.suffixes.isEmpty then (printer.write indent Text.space 1, rest)
    else (printer.newline indent, rest)
  | SoftLine => if mode.isFlat && printer.suffixes.isEmpty then (printer, rest) else (printer.newline indent, rest)
  | HardLine => (printer.newline indent, rest)
  | LineStart => (printer.lineStart indent, rest)
  | CommentEnd => (printer.newline printer.lineIndent, rest)
  | LineStartHere =>
    if printer.atLineStart then ({ printer with owed := some indent, lineIndent := indent }, rest)
    else (printer.newline indent, rest)
  | Blank => (printer.blank, rest)
  | Nest more inner => (printer, Print (indent + more) mode inner :: rest)
  | OneLineBelow inner => (printer, Print (indent + 2) mode HardLine :: Print (indent + 2) mode inner :: rest)
  | Flatten inner => (printer, Print indent Flat inner :: rest)
  | Group inner hard =>
    let flat := mode.isFlat || (!hard && printer.fitsHere total [(Flat, inner)] rest)
    (printer, Print indent (if flat then Flat else Break) inner :: rest)
  | Concat docs => (printer, docs.map (Print indent mode) ++ rest)
  | Fill items =>
    match items with
    | [] => (printer, rest)
    | first :: others =>
      if mode.isFlat then (printer, (Doc.joinLines items).map (Print indent Flat) ++ rest)
      else
        let stack := others.map (FillSep indent) ++ rest
        let firstMode := if printer.fitsHere total [(Flat, first)] stack then Flat else Break
        (printer, Print indent firstMode first :: stack)
  | Choice options =>
    let chosen := if mode.isFlat then options.headD Doc.Empty else printer.choose total indent rest options
    (printer, Print indent mode chosen :: rest)
  | LineSuffix comment => ({ printer with suffixes := printer.suffixes ++ [comment] }, rest)

def step (printer : Printer) (total : Nat) (cmd : Cmd) (rest : List Cmd) : Printer × List Cmd :=
  match cmd with
  | FillSep indent item =>
    if printer.suffixes.isEmpty && fits total [(Flat, item)] rest (printer.left - 1) then
      (printer.write indent Text.space 1, Print indent Flat item :: rest)
    else (printer.newline indent, Print indent Break item :: rest)
  | Print indent mode doc => printer.printDoc total indent mode doc rest

def run (printer : Printer) (total fuel : Nat) (stack : List Cmd) : Printer :=
  match fuel, stack with
  | 0, _ => printer
  | _, [] => printer
  | more + 1, cmd :: rest =>
    let (next, stack) := printer.step total cmd rest
    next.run total more stack

end Printer

def print (doc : Doc) (width : Nat) : Text :=
  let fuel := 3 * doc.size + 3
  let done := ((Printer.start width).run fuel fuel [Print 0 Break doc]).flushSuffixes
  Text.join done.out.reverse

end Toy
