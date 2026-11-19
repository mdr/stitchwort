--| The line rule against the parser's modes (H2 of SW-4121's plan): an item the rule steps over doesn't stop a
--| reading whose block column the rule bounds (`hungStops`), and the bound carries from one item to the next, into a
--| block and into a bracket.

namespace Syntax.ReadBackHungBounds
import Std (Bool, List, Nat, Option)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackLine (Quiet, leadKind)
import Syntax.ReadBackHung (..)

--| An item the line rule steps over doesn't stop a reading whose limit the rule bounds. A `:=` outside brackets is
--| the exception: the rule lets it start a line anywhere.
theorem hungStops ∀ (modes: Modes) (state next: HangState) (item: Item)
    (quiet: Quiet modes)
    (bound: bounds modes state = True)
    (stepped: state.step item.leaf = Some next)
    (deep: deepAll [item] = True)
    (inside: (item.kind == ColonEq) = False):
    modes.stops item = False :=
  ?

--| After an expression's first leaf, the bound holds of the state it left.
theorem boundsPast ∀ (modes: Modes) (state next: HangState) (item: Item)
    (bound: bounds modes (state.entered item.leaf) = True)
    (stepped: state.step item.leaf = Some next)
    (plain: (item.kind == Comma || item.kind.isCloser || item.kind == ColonEq || item.kind == Colon) = False):
    bounds modes next = True :=
  ?

--| A block opened at an item that starts its expression and its line bounds the state that item enters.
theorem boundsBlock ∀ (modes: Modes) (state: HangState) (item: Item) (allow: Option Nat) (kind: LineKind)
    (starts: state.start = True)
    (lineStart: item.leaf.token.lineStart = True):
    bounds
      (lineModes (blockModes modes item.leaf.token.column True) item.leaf.token.column True allow kind)
      (state.entered item.leaf)
      = True :=
  ?

--| The same item is right of the limit: `BlockAt`'s first clause.
theorem rightOfBound ∀ (modes: Modes) (state next: HangState) (item: Item)
    (bound: bounds modes state = True)
    (stepped: state.step item.leaf = Some next)
    (lineStart: item.leaf.token.lineStart = True)
    (opens: leadKind item.kind = True):
    rightOfLimit item.leaf.token.column modes.limit = True :=
  ?
