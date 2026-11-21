--| What a printed declaration's group says, and what read-back takes of it (SW-4077, SW-4079): the facts
--| `PrintedGroup` of one printed declaration and its group of leaves, on any number of lines, and the split
--| `GroupSplit` that `readsBackHung` reads. `Fmt.TopReadBack` reads the group back; `Fmt.GroupSlots` splits it.

namespace Fmt.GroupFacts
import Std (Bool, List, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Driver1 (..)
import Fmt.OutputStatements (..)
import Fmt.PassProofs (..)
import Syntax.SettleProofs (tokens)
import Syntax.ParseCarries (codeWords)
import Syntax.ReadBackRuns (plainHeader)
import Syntax.ReadBackLine (Spelt)

--| `calm` of a declaration, and for the file's first (`top`) its `def`'s first flag cleared: what `calmTop` makes of
--| each declaration.
def Decl.calmAt (decl: Decl) (top: Bool): Decl := match top, decl.calm with
  | True, Definition attributes header body => Definition attributes { header | keyword = header.keyword.topped } body
  | _, calmed => calmed

--| A group's items as `readsBackHung` takes them: `def`, the name, `:`, the type's, `:=` and the value's;
--| `read` is the definition they make, its type and value spelt by their items and within slice 1.
def GroupSplit (group: List Leaf) (read: Decl) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr):
    Prop :=
  items group = [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]]
    ∧ read = Definition [] (plainHeader keyword name colon result) (Assigned colonEq.leaf.word.comments value)
    ∧ keyword.kind = KwDef
    ∧ (name.kind = Lower ∨ name.kind = Upper)
    ∧ colon.kind = Colon
    ∧ colonEq.kind = ColonEq
    ∧ Spelt result typeRead
    ∧ Spelt value valueRead
    ∧ result.within1 = True
    ∧ value.within1 = True

--| What the output says of one printed declaration `decl` and the group of leaves the second run parses for it: the
--| tree facts of `decl` the driver gives, its printed leaves keeping the line rule (`hangs`, which the driver's
--| `hung` gives every declaration), the group's tokens those printed tokens
--| (comment placement moves only comments), and the group's words `read`'s, where `read` is `calm` of `decl`
--| (`printedSettle1`).
def PrintedGroup (decl read: Decl) (group: List Leaf): Prop :=
  decl.within1 = True
    ∧ decl.shaped = True
    ∧ decl.settled = True
    ∧ decl.lexical = True
    ∧ decl.commaFree = True
    ∧ hangs decl.leaves = True
    ∧ tokens group = tokens decl.leaves
    ∧ codeWords group = read.words
    ∧ (∃ (top: Bool) => read = decl.calmAt top)
