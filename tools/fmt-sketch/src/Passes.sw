--| The four tidy passes (self-hosted-fmt.md §2), each the shared
--| traversal with one step, and `tidy`, the four in order. Two of their
--| parts are stage 4's to write and stand open here: where a type may
--| stand without its brackets, and which parameters merge.

namespace Fmt.Sketch
import Std (Bool, List, Option, Text)

-- P1: `∀` after a theorem's name.

def addForall: Declaration → Declaration
  | Headed kind attributes keywords name None parameters rest =>
    if wantsForall kind parameters rest then Headed kind attributes keywords name (Some Comments.none) parameters rest
    else Headed kind attributes keywords name None parameters rest
  | other => other

def SourceFile.withForall (file: SourceFile): SourceFile := file.traverse { Steps.keep | declaration = addForall }

-- P2: no comma before a closer.

def SourceFile.withoutTrailingCommas (file: SourceFile): SourceFile :=
  file.traverse { Steps.keep | comma = (flag => False) }

-- P3: no spare bracket pair after a row or around a parameter's whole
-- type.

--| Whether the grammar reads `expr`, written without brackets at `slot`,
--| as the expression it is: the pass's side condition, in place of the
--| Rust pass's trial parse. After a row a function type keeps its pair
--| although the grammar would read it (D2307).
def Expr.standsAt (expr: Expr) (slot: Slot): Bool := ?

--| Without the comment-free pairs around it whose content may stand at
--| `slot`, the innermost first.
def stripSpare (slot: Slot): Expr → Expr
  | Pair open inner close =>
    if open.isNone && close.isNone && (stripSpare slot inner).standsAt slot then stripSpare slot inner
    else Pair open inner close
  | other => other

def dropSpare (slot: Slot) (expr: Expr): Expr := match slot with
  | Elsewhere => expr
  | _ => stripSpare slot expr

def SourceFile.withoutSpareBrackets (file: SourceFile): SourceFile := file.traverse { Steps.keep | term = dropSpare }

-- P4: adjacent parameters of one type merge.

--| Adjacent groups with the same brackets and the same type, token for
--| token, joined: no `auto`, no default, no comment in either, and a
--| type that names none of the names (`merge.rs`). It compares types as
--| P3 left them, which is why P3 runs first.
def mergeGroups: List Parameter → List Parameter := ?

def SourceFile.withMergedParameters (file: SourceFile): SourceFile :=
  file.traverse { Steps.keep | parameters = mergeGroups }

def SourceFile.tidy (file: SourceFile): SourceFile :=
  file.withForall.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters

--| The four steps in one traversal. `tidyFused` says it is `tidy`; if it
--| is proved, the driver walks the tree once, not four times.
def tidySteps: Steps := { term = dropSpare, parameters = mergeGroups, comma = (flag => False), declaration = addForall }
