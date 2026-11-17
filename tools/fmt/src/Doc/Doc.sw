--| The layout engine's documents: what to print and where lines may break,
--| after Wadler's "A prettier printer" and Prettier. A port of the core of
--| the Rust formatter's engine (`crates/fmt/src/printer/engine.rs`): the
--| pieces Sprig's rules need, without `Align`, the id groups, `Verbatim`
--| and text blocks.
--|
--| A `Group` prints on one line if all of it, plus whatever must follow it
--| on that line, fits in the width; otherwise every break directly in it
--| breaks, and each inner group decides again for itself. Width is counted
--| in characters: `∀` and `→` are one column each.

namespace Fmt.Doc
import Std (List, Text)

type Doc =
  | Empty
  --| Text without line breaks, and its width in characters.
  | Chunk (text: Text) (width: Nat)
  --| A space if its group prints flat, otherwise a line break.
  | Line
  --| Nothing if its group prints flat, otherwise a line break.
  | SoftLine
  --| Always a line break. A group holding one never prints flat.
  | HardLine
  --| An empty line here, if this is the start of a line and the line before
  --| isn't already empty: an author's kept blank line.
  | Blank
  --| The contents, with line breaks indented this many more columns.
  | Nest (indent: Nat) (inner: Doc)
  --| Printed flat if it fits, otherwise with every line in it broken.
  --| `hard` says it holds a hard break, so it never prints flat.
  | Group (inner: Doc) (hard: Bool)
  | Concat (docs: List Doc)
  --| Items separated by line breaks that break only where the next item
  --| doesn't fit on the line.
  | Fill (items: List Doc)
  --| The contents printed flat whatever their width; as an option of a
  --| `Choice`, it is taken only if it fits.
  | Flatten (inner: Doc)
  --| The first option whose first line (and what follows it on that line)
  --| fits; the last if none does.
  | Choice (options: List Doc)
  --| A line below at +2 holding the doc; as an option of a `Choice` it is
  --| taken only if the doc fits flat on that one line.
  | OneLineBelow (inner: Doc)
  --| A trailing comment: printed, after one space, at the end of the line
  --| it is on, after any `Closing` that joins that line. A group that
  --| would put a chunk after it breaks; a chunk that still follows it on
  --| the line starts the next line instead (a comment break), indented as
  --| a continuation line.
  | LineSuffix (comment: Text)
  --| A closing bracket or a comma: text that stays on its line when a
  --| trailing comment waits there, written before the comment. Which
  --| closers share a comment's line is the layout's choice, so the printed
  --| comment follows them and reading puts it back (rule N).
  | Closing (text: Text)
  --| A line break here unless at the start of a line: before an own-line
  --| comment. A line started this way is a comment break, indented as a
  --| continuation line.
  | LineStart
  --| A line break after an own-line comment, to a line indented as the
  --| comment's: what follows stays where the comment is.
  | CommentEnd
  --| A line break at the indentation in force, or at the start of a line,
  --| that line moved there: own-line comments before a closing bracket, at
  --| its items' indentation.
  | LineStartHere
  --| Forces every group around it to break.
  | BreakParent

def Doc.text (text: Text): Doc := Chunk text text.length

def Doc.group (inner: Doc): Doc := Group inner inner.forcesBreak

--| The docs in order, leaving out the empty ones.
def Doc.concat (docs: List Doc): Doc := match docs.filter (doc => not doc.isEmpty) with
  | [] => Empty
  | [only] => only
  | several => Concat several

--| The docs with `separator` between each two.
def joined (docs: List Doc) (separator: Doc): Doc := Doc.concat (Doc.joinedWith separator docs)

def Doc.joinedWith (separator: Doc): (docs: List Doc) → List Doc
  | [] => []
  | [only] => [only]
  | [doc, ..docs] => [doc, separator, ..Doc.joinedWith separator docs]

def Doc.isEmpty: Doc → Bool := matches | Empty

--| Whether printing this always breaks a line, so a group around it can't
--| be flat.
def Doc.forcesBreak: Doc → Bool
  | HardLine => True
  | LineStart => True
  | CommentEnd => True
  | LineStartHere => True
  | BreakParent => True
  | OneLineBelow _ => True
  | Group _ hard => hard
  | Nest _ inner => inner.forcesBreak
  | Flatten inner => inner.forcesBreak
  | Concat docs => Doc.anyForcesBreak docs
  | Fill items => Doc.anyForcesBreak items
  | Choice options => Doc.allForceBreak options
  | _ => False

def Doc.anyForcesBreak: List Doc → Bool
  | [] => False
  | [doc, ..docs] => doc.forcesBreak || Doc.anyForcesBreak docs

def Doc.allForceBreak: List Doc → Bool
  | [] => True
  | [doc, ..docs] => doc.forcesBreak && Doc.allForceBreak docs

--| The number of nodes, which bounds the printer's steps: each node is
--| pushed on its work list at most twice.
def Doc.size: Doc → Nat
  | Nest _ inner => 1 + inner.size
  | Group inner _ => 1 + inner.size
  | Flatten inner => 1 + inner.size
  | OneLineBelow inner => 2 + inner.size
  | Concat docs => 1 + Doc.sizes docs
  | Fill items => 1 + 2 * Doc.sizes items
  | Choice options => 1 + Doc.sizes options
  | _ => 1

def Doc.sizes: List Doc → Nat
  | [] => 0
  | [doc, ..docs] => doc.size + Doc.sizes docs
