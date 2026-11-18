--| `printedSplit1` is false as stated (SW-4077): `def d: A := -1 n` meets every fact `PrintedGroup` asks, prints as
--| written and reads back, but its value is a call whose head is `-` on a numeral, which `Spelt` doesn't spell (a
--| call's head is an atom or a bracket there), so no `GroupSplit` exists.

namespace Fmt.PrefixHeadSplit
import Std (Bool, Eq, List, Option, Void)
import Syntax (..)
import Fmt (..)
import Fmt.OutputStatements (..)
import Fmt.TopReadBack (..)
import Syntax.ReadBackLine (Spelt)
import Syntax.ReadBackRuns (plainHeader)

--| Whether a definition's value is no call, or a call whose head is an atom or a bracket: what `Spelt` asks of a
--| call.
def valueHeadAtomic: Decl → Bool
  | Definition _ _ (Assigned _ (App head [_, .._])) => head.atomic1
  | _ => True

--| A spelt value's call, if it is one, has an atom or a bracket for its head.
theorem speltHeadAtomic ∀ (attributes: List Attributes) (header: Header) (colonEq: Comments)
    (value: Expr) (read: List Item)
    (spelt: Spelt value read):
    valueHeadAtomic (Definition attributes header (Assigned colonEq value)) = True :=
  match value, spelt with
    | App head [_, .._], (_, _, _, _, headAtomic, _, _, _, _) => headAtomic
    | App _ [], never => Void.impossible never
    | Atom _ _, _ => byComputing
    | Paren _ _ _, _ => byComputing
    | Tuple _ _ _ _, _ => byComputing
    | ListOf _ _ _ _, _ => byComputing
    | Prefix _ _, _ => byComputing
    | Infix _ _ _ _, _ => byComputing
    | _, never => Void.impossible never

--| No group splits for a read whose value is a call with a head of another kind.
theorem noSplitOf ∀ (group: List Leaf) (read: Decl)
    (headed: valueHeadAtomic read = False)
    (found: ∃ (keyword name colon colonEq: Item) (typeRead valueRead: List Item) (result value: Expr) => GroupSplit
        group read keyword name colon colonEq typeRead valueRead result value):
    Void :=
  let (keyword, name, colon, colonEq, typeRead, valueRead, result, value, split) := found
  let (_, isRead, _, _, _, _, _, valueSpelt, _, _) := split
  let atomic :=
    speltHeadAtomic [] (plainHeader keyword name colon result) colonEq.leaf.word.comments value valueRead valueSpelt
  let readAtomic: valueHeadAtomic read = True := Eq.trans (Eq.cong valueHeadAtomic isRead) atomic
  (Bool.falseNotTrue (Eq.trans headed.flipped readAtomic)).impossible

--| `def d: A := -1 n`, as the driver tidies it (`prefixHeadTidied`).
def prefixHeadDecl: Decl :=
  Definition []
    {
      exportKeyword = None,
      opaqueKeyword = None,
      kind = DefPlain,
      keyword = Comments.none,
      name = fixedWord "d" Comments.none,
      forallKeyword = None,
      params = [],
      colon = Comments.none,
      result = Atom Upper (fixedWord "A" Comments.none),
      decreasingClause = None,
      unfoldingClause = None
    }
    (Assigned Comments.none
      (App (Prefix (fixedWord "-" Comments.none) (Atom Num (fixedWord "1" Comments.none))) [
        Atom Lower (fixedWord "n" Comments.none)
      ]))

--| The driver's tree of `def d: A := -1 n` is `prefixHeadDecl`, and the formatter prints it as written.
theorem prefixHeadTidied: (match tidiedOf "def d: A := -1 n\n" with
      | Some file =>
        file.dump == ({ decls = [prefixHeadDecl], end = Comments.none }: SourceFile).dump
          && file.printed1 == "def d: A := -1 n\n"
      | None => False)
      = True :=
  byComputing

--| `prefixHeadDecl` is a slice 1 one-line declaration whose printed group is its own leaves, `calm` of it the read.
theorem prefixHeadPrinted: PrintedGroup prefixHeadDecl (prefixHeadDecl.calmAt True) prefixHeadDecl.leaves1 := (
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  byComputing,
  (True, byComputing)
)

--| Its value's head is no atom or bracket.
theorem prefixHeadValue: valueHeadAtomic (prefixHeadDecl.calmAt True) = False := byComputing

--| `printedSplit1`'s statement fails of `def d: A := -1 n`.
theorem printedSplitFails ∀
    (split: ∀ (decl read: Decl) (group: List Leaf) (printed: PrintedGroup decl read
        group) => ∃ (keyword name colon colonEq: Item) (typeRead valueRead: List Item) (result value: Expr) =>
      GroupSplit group read keyword name colon colonEq typeRead valueRead result value):
    Void :=
  noSplitOf prefixHeadDecl.leaves1
    (prefixHeadDecl.calmAt True)
    prefixHeadValue
    (split prefixHeadDecl (prefixHeadDecl.calmAt True) prefixHeadDecl.leaves1 prefixHeadPrinted)
