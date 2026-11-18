--| Reads `stitchwort dev doc`'s dump, the layout documents the Rust formatter
--| builds, and checks the engine against it: each declaration's document is
--| built as a `Doc` value, printed in 120 columns, and compared with the text
--| Rust's engine printed for it (the engine harness, `fmt --stage engine`).
--|
--| The dump is, per declaration, a line `decl N`, a line `size K` (the nodes
--| of the document written out in full), a line `text ESCAPED` (what Rust
--| printed), then the document one node a line in pre-order: the tag,
--| a space and the arguments, the children following. A node's tag fixes how
--| many children it has: none, one, two (`IfBroken`), or the number after
--| the tag (`Concat`, `Fill`, `Choice`). A text is the rest of its line, with
--| `\\`, `\n` and `\r` for backslash, line feed and carriage return. A doc
--| that Rust uses in several places is `Shared ID` and its doc the first
--| time and `Ref ID` after, so a declaration's size is small even where
--| written out in full it is not.
--|
--| Nodes `Doc` doesn't have yet are read too (as empty) and make the
--| declaration "unsupported" for the kinds they are, so it is counted and
--| not compared.

namespace Fmt.DocDump
import Std (Bool, Char, Doc, List, Nat, Option, Result, Text)
import Std.Doc (..)

--| What the engine did with one declaration of the dump.
type Outcome =
  | Matched
  --| Rust's printed text and `Doc`'s differ: the first line that differs.
  | Mismatched (line: Nat) (expected: Text) (got: Text)
  --| The document uses these node kinds, which `Doc` doesn't have.
  | Unsupported (kinds: List Text)
  --| The document written out in full has this many nodes, more than
  --| `sizeLimit`: `Doc.size` and `forcesBreak` walk it in full, so the engine
  --| would need them cached on shared docs first. Not read.
  | Oversized (size: Nat)

--| What a node's line stands for: a leaf, or a node that takes `children`
--| documents and builds from them.
type Node =
  | Leaf (doc: Doc)
  | Open (children: Nat) (build: List Doc → Doc)
  --| A doc another place will use again, under this number.
  | Share (id: Nat)
  --| The doc of the `Shared` with this number.
  | Ref (id: Nat)
  | Bad (message: Text)

--| A node still waiting for children.
type Frame = { remaining: Nat, build: List Doc → Doc, got: List Doc, id: Nat }

--| The reader's state between lines: the nodes waiting for children, the
--| docs shared so far by number, the finished root if there is one, and the
--| unsupported kinds seen.
type Reader = {
  stack: List Frame,
  shared: List (Nat, Doc),
  root: Option Doc,
  kinds: List Text
}

--| Whether the characters are all among `)`, `]`, `}` and `,`, and there is
--| at least one: Rust's engine treats such a text as a closer.
def isCloser (text: Text): Bool :=
  !text.toList.isEmpty && text.all (char => char == ')' || char == ']' || char == '}' || char == ',')

--| The document for a text node: a `Closing` for a closer, a `Chunk` for
--| anything else.
def textDoc (text: Text): Doc := if isCloser text then Closing text else Doc.text text

def unescapeLoop (acc: List Char): List Char → List Char
  | [] => acc.reverse
  | ['\\', next, ..rest] =>
    let char :=
      if next == 'n' then '\n'
      else if next == 'r' then '\r'
      else next
    unescapeLoop [char, ..acc] rest
  | [char, ..rest] => unescapeLoop [char, ..acc] rest

--| A dump line's text with its escapes undone.
def unescape (text: Text): Text := Text.fromList (unescapeLoop [] text.toList)

def escapeChar (char: Char): List Char :=
  if char == '\\' then ['\\', '\\']
  else if char == '\n' then ['\\', 'n']
  else if char == '\r' then ['\\', 'r']
  else [char]

--| A text for a dump line: backslash, line feed and carriage return escaped.
def escape (text: Text): Text := Text.fromList (text.toList.concatMap escapeChar)

--| The first child, or an empty document.
def first (docs: List Doc): Doc := docs.headOr Nothing

--| A node with the number of children in its argument, built from them.
def counted (tag line argument: Text) (build: List Doc → Doc): (Node, Option Text) := match argument.toNat with
  | Some count => (Open count build, None)
  | None => (Bad "${tag}: no count in `${line}`", None)

--| A node with one child and a number in its argument.
def numbered (tag line argument: Text) (build: Nat → Doc → Doc): (Node, Option Text) := match argument.toNat with
  | Some number => (Open 1 (docs => build number (first docs)), None)
  | None => (Bad "${tag}: no number in `${line}`", None)

--| A leaf numbered by the line's argument.
def numberedLeaf (tag line argument: Text) (build: Nat → Doc): (Node, Option Text) := match argument.toNat with
  | Some number => (Leaf (build number), None)
  | None => (Bad "${tag}: no number in `${line}`", None)

--| The node a line stands for, and the kind of node `Doc` lacks if it is one.
def parseNode (line: Text): (Node, Option Text) :=
  let (tag, argument) := match line.splitOnce " " with
    | Some pair => (pair.fst, pair.snd)
    | None => (line, "")
  match tag with
    | "Nil" => (Leaf Nothing, None)
    | "Shared" =>
      match argument.toNat with
        | Some id => (Share id, None)
        | None => (Bad "Shared: no number in `${line}`", None)
    | "Ref" =>
      match argument.toNat with
        | Some id => (Ref id, None)
        | None => (Bad "Ref: no number in `${line}`", None)
    | "Text" => (Leaf (textDoc (unescape argument)), None)
    | "Line" => (Leaf Line, None)
    | "SoftLine" => (Leaf SoftLine, None)
    | "HardLine" => (Leaf HardLine, None)
    | "Blank" => (Leaf Blank, None)
    | "BreakParent" => (Leaf BreakParent, None)
    | "LineStart" => (Leaf LineStart, None)
    | "LineStartHere" => (Leaf LineStartHere, None)
    | "LineSuffix" => (Leaf (LineSuffix (unescape argument)), None)
    | "Nest" => numbered tag line argument (indent inner => Nest indent inner)
    | "Group" => (Open 1 (docs => Doc.group (first docs)), None)
    | "Flat" => (Open 1 (docs => Flatten (first docs)), None)
    | "OneLineBelow" => (Open 1 (docs => OneLineBelow (first docs)), None)
    | "Concat" => counted tag line argument Doc.concat
    | "Fill" => counted tag line argument Fill
    | "Choice" => counted tag line argument Choice
    | "Align" => (Open 1 (docs => Align (first docs)), None)
    | "AlignInset" => (Open 1 (docs => AlignInset (first docs)), None)
    | "Displaced" => (Open 1 (docs => Displaced (first docs)), None)
    | "NarrowGroup" => numbered tag line argument (max inner => inner.narrowGroup max)
    | "IdGroup" => numbered tag line argument (id inner => inner.idGroup id)
    | "IfBroken" =>
      match argument.toNat with
        | Some id => (Open 2 (docs => IfBroken id (first docs) (docs.drop 1 |> first)), None)
        | None => (Bad "IfBroken: no number in `${line}`", None)
    | "Mark" => numberedLeaf tag line argument Mark
    | "CloserLine" => numberedLeaf tag line argument CloserLine
    | "TextBlock" => (Leaf Nothing, Some tag)
    | _ => (Bad "unknown node `${line}`", None)

--| A finished document goes to the node waiting for it, which finishes in
--| its turn if it was waiting for only that one; a node that was a
--| `Shared` is remembered under its number.
def complete (doc: Doc) (shared: List (Nat, Doc)): (stack: List Frame) → (List Frame, List (Nat, Doc), Option Doc)
  | [] => ([], shared, Some doc)
  | [frame, ..rest] =>
    let got := [doc, ..frame.got]
    if frame.remaining <= 1 then
      let built := frame.build got.reverse
      complete built (if frame.id == 0 then shared else [(frame.id, built), ..shared]) rest
    else ([{ frame | remaining = frame.remaining - 1, got }, ..rest], shared, None)

--| The reader after a finished document.
def Reader.finish (reader: Reader) (kinds: List Text) (doc: Doc): Result Reader Text :=
  let (stack, shared, root) := complete doc reader.shared reader.stack
  Ok { stack, shared, root, kinds }

--| Takes one line of the document.
def Reader.read (reader: Reader) (line: Text): Result Reader Text := match reader.root with
  | Some _ => Err "a node after the document's root: `${line}`"
  | None =>
    let (node, kind) := parseNode line
    let kinds := match kind with
      | Some tag => if reader.kinds.contains tag then reader.kinds else [tag, ..reader.kinds]
      | None => reader.kinds
    match node with
      | Bad message => Err message
      | Leaf doc => reader.finish kinds doc
      | Ref id =>
        match reader.shared.lookup id with
          | Some doc => reader.finish kinds doc
          | None => Err "a reference to a doc that isn't shared yet: `${line}`"
      | Share id => Ok { reader | stack = [{ remaining = 1, build = first, got = [], id }, ..reader.stack], kinds }
      | Open children build =>
        if children == 0 then reader.finish kinds (build [])
        else Ok { reader | stack = [{ remaining = children, build, got = [], id = 0 }, ..reader.stack], kinds }

def readLines (reader: Reader): (lines: List Text) → Result Reader Text
  | [] => Ok reader
  | [line, ..rest] =>
    match reader.read line with
      | Ok next => readLines next rest
      | Err message => Err message

--| One declaration read: its number, Rust's text, the size of its document
--| written out in full, and the document (empty if it is oversized), with
--| the unsupported kinds it holds (sorted).
type Declaration = {
  number: Text,
  expected: Text,
  size: Nat,
  doc: Doc,
  kinds: List Text
}

--| The most nodes of a document written out in full that the harness reads.
def sizeLimit: Nat := 50000

--| Reads one declaration's lines: `decl N`, `size K`, `text ESCAPED`, then
--| the nodes.
def readDeclaration: (lines: List Text) → Result Declaration Text
  | [header, sized, printed, ..nodes] =>
    match header.stripPrefix "decl ", Option.flatMap (sized.stripPrefix "size ") Text.toNat, printed.stripPrefix
        "text " with
      | Some number, Some size, Some text =>
        if size > sizeLimit then Ok { number, expected = "", size, doc = Nothing, kinds = [] }
        else
          match readLines { stack = [], shared = [], root = None, kinds = [] } nodes with
            | Err message => Err "declaration ${number}: ${message}"
            | Ok reader =>
              match reader.root with
                | Some doc => Ok { number, expected = unescape text, size, doc, kinds = reader.kinds.sort }
                | None => Err "declaration ${number}: the document ends inside a node"
      | _, _, _ => Err "a declaration starts with `decl N`, `size K` and `text ...`, not `${header}`"
  | _ => Err "a declaration with no text line"

--| The dump's lines cut into declarations at each `decl` line.
def groupDeclarations (current: List Text) (done: List (List Text)): (lines: List Text) → List (List Text)
  | [] => (if current.isEmpty then done else [current.reverse, ..done]).reverse
  | [line, ..rest] =>
    if line.startsWith "decl " then
      groupDeclarations [line] (if current.isEmpty then done else [current.reverse, ..done]) rest
    else groupDeclarations [line, ..current] done rest

--| The first line where two texts differ, with the line's number from 1.
def firstDifference (index: Nat): List Text → List Text → Option (Nat, Text, Text)
  | [], [] => None
  | [a, ..rest], [b, ..others] => if a == b then firstDifference (index + 1) rest others else Some (index, a, b)
  | [a, .._], [] => Some (index, a, "<end>")
  | [], [b, .._] => Some (index, "<end>", b)

--| The width the rules print in.
def width: Nat := 120

--| What the engine does with a declaration.
def Declaration.outcome (declaration: Declaration): Outcome :=
  if declaration.size > sizeLimit then Oversized declaration.size
  else if !declaration.kinds.isEmpty then Unsupported declaration.kinds
  else
    match firstDifference 1 declaration.expected.lines (print declaration.doc width).lines with
      | None => Matched
      | Some (line, expected, got) => Mismatched line expected got

--| The answer for a whole dump: a line for each declaration, `decl N
--| matched`, `decl N unsupported KIND,KIND`, `decl N oversized SIZE` or `decl N mismatched LINE`
--| followed by the two lines as `  expected: ESCAPED` and `  got: ESCAPED`.
def answer (dump: Text): Result Text Text :=
  let lines := dump.lines.filter (line => !line.isEmpty)
  report (groupDeclarations [] [] lines)

def report: (groups: List (List Text)) → Result Text Text
  | [] => Ok ""
  | [group, ..rest] =>
    match readDeclaration group with
      | Err message => Err message
      | Ok declaration =>
        match report rest with
          | Err message => Err message
          | Ok more => Ok "${describe declaration}${more}"

def describe (declaration: Declaration): Text := match declaration.outcome with
  | Matched => "decl ${declaration.number} matched\n"
  | Unsupported kinds => "decl ${declaration.number} unsupported ${kinds.joinWith ","}\n"
  | Oversized size => "decl ${declaration.number} oversized ${size}\n"
  | Mismatched line expected got =>
    "decl ${declaration.number} mismatched ${line}\n  expected: ${escape expected}\n  got: ${escape got}\n"
