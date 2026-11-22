--| What `expr` reads on any lines, one depth at a time (H5 of SW-4121's plan, the block case): given `fullHung` below
--| `depth`, `fullHung` at `depth`. `Syntax.ReadBackHungTop.fullHung` ties the knot by induction on the depth.

namespace Syntax.ReadBackHungFull
import Std (Bool, DecEq, Eq, List, Nat, Option)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackEnds (..)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungInline (..)
import Syntax.ReadBackHungBounds (boundsBlock, rightOfBound)
import Syntax.ReadBackHungAtomsLemmas (..)

--| A spelt expression at the start of a type, a value or a bracket's item (`state.start`), or after `->`
--| (`state.glue`), whose leaves and what follows keep the line rule, is what `expr` reads: inline where its first item
--| starts no block (`inlineHung`); else a one-line block at that item's column, read by `inlineHung` under the block's
--| modes (`open` from `allow`, `bound` by `boundsBlock`, `BlockAt`'s first clause by `rightOfBound`, its second by
--| `stepInBracket` or `stepAtTop`).
--|
--| Proof idea: the line rule steps over the first item, so it doesn't stop the modes the state bounds
--| (`leadHung`). Where it starts a block it starts its line, which after `->` the rule refuses, so the state is at a
--| start and the item's column is recorded: in its bracket's slot or as the type's or value's column. What follows
--| the expression is read from the state that column is in force in (`speltHung`), where the rule lets no leaf start
--| a line at it: the block reads one line.
theorem fullHungStep ∀ (depth: Nat) (inner: FullHungBelow depth): FullHungAt depth :=
  modes expr read rest state quiet deep spelt free lineRead lineRest placed bound hung deepItems ends =>
    let (item, more, isRead, lead) := speltStarts expr read spelt
    let sameSpelt: Spelt expr [item, ..more] := rewrite <- isRead then spelt
    let lineItems: lineAll [item, ..more] = True := rewrite <- isRead then lineRead
    let hungItems: hangsFrom state (leavesOf ([item, ..more] ++ rest)) = True := rewrite <- isRead then hung
    let deepAllItems: deepAll ([item, ..more] ++ rest) = True := rewrite <- isRead then deepItems
    let (open, entered, _) := leadHung modes state item (more ++ rest) quiet lead bound hungItems
    let (next, stepped, _) := hungStep state item.leaf (leavesOf (more ++ rest)) hungItems
    let (_, hungRest) := speltHung modes expr [item, ..more] rest state sameSpelt bound hungItems
    let column := item.leaf.token.column
    rewrite isRead then
      fullOfStarts
        (TreeN depth)
        modes
        item
        more
        rest
        expr
        (startsBlock modes item)
        byComputing
        (inline =>
          inlineHung modes quiet expr item more rest depth state inner deep sameSpelt free lineItems lineRest open
              entered hungItems deepAllItems ends)
        (blockStarts =>
          let lineStart: item.leaf.token.lineStart = True := Bool.andLeft blockStarts
          let starts: state.start = True := match placed with
            | Inl atStart => atStart
            | Inr glued =>
              let none := gluedNoLine state item.leaf glued lineStart
              (Option.someNotNone next (Eq.trans stepped.flipped none)).impossible
          let single: continuesAt column rest = False := match rest, hungRest with
            | [], _ => byComputing
            | [after, ..later], hungRest =>
              let (_, steppedAfter, _) := hungStep (state.entered item.leaf) after.leaf (leavesOf later) hungRest
              rewrite continuesItem column after later then
                freshContinues state _ item.leaf after.leaf starts lineStart steppedAfter
          (
            rightOfBound modes state next item bound stepped lineStart lead,
            single,
            startNotOther item.kind lead,
            kind =>
              let lined := lineModes (blockModes modes column True) column True (Some item.index) kind
              let lineQuiet: QuietModes lined :=
                { noGuard = quiet.noGuard, noCalc = quiet.noCalc, noRule = quiet.noRule }
              inlineHung lined lineQuiet expr item more rest depth state inner deep sameSpelt free lineItems lineRest
                (rewrite quiet.noGuard, quiet.noCalc, quiet.noRule, DecEq.neSelf (Some item.index))
                (boundsBlock modes state item (Some item.index) kind starts lineStart)
                hungItems
                deepAllItems
                ends
          ))
