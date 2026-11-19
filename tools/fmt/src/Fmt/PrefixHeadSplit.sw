--| A call whose head is `-` on a numeral, `def d: A := -1 n`, as `printedSplit1` meets it (SW-4077): the driver's tree,
--| printed as written, meets every fact `PrintedGroup` asks. `Spelt` spells such a head (`headFits`), and
--| `Syntax.ReadBackLine.readsBackNegativeHeadExample` reads the line back.

namespace Fmt.PrefixHeadSplit
import Std (Bool, List, Option)
import Syntax (..)
import Fmt (..)
import Fmt.OutputStatements (..)
import Fmt.TopReadBack (..)

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
