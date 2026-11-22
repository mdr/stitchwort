--| The line rule's state through a call's parts, for H6 of SW-4121's plan: an argument's first item doesn't stop a
--| reading the state before it bounds, so it starts an atom (`argStartsHung`) and ends what comes before it
--| (`argEndsHung`); and `fullHung` below a depth holds below every smaller one (`belowLess`).

namespace Syntax.ReadBackHungAppLemmas
import Std (Bool, Eq, List, Nat, Option, Parse, Void)
import Syntax (..)
import Fmt (..)
import Syntax.ReadBackProofs (..)
import Syntax.ReadBackRuns (..)
import Syntax.ReadBackTree (..)
import Syntax.ReadBackLine (..)
import Syntax.ReadBackHung (..)
import Syntax.ReadBackHungBounds (boundsPast)
import Syntax.ReadBackHungAtomsLemmas (hungStep, leadHung, leadPlain)

--| `fullHung` below a depth holds below any smaller depth.
theorem belowLess ∀ (small big: Nat) (le: small <= big) (inner: FullHungBelow big): FullHungBelow small :=
  smaller less => inner smaller (arithmetic [less, le])

--| After an expression's first item, the bound that held of the state the item entered holds of the state it left.
theorem pastFirst ∀ (modes: Modes) (state: HangState) (item: Item) (rest: List Item)
    (lead: leadKind item.kind = True)
    (bound: bounds modes (state.entered item.leaf) = True)
    (hung: hangsFrom state (leavesOf [item, ..rest]) = True):
    ∃ (next: HangState) => bounds modes next = True ∧ hangsFrom next (leavesOf rest) = True :=
  let (next, stepped, hungRest) := hungStep state item.leaf (leavesOf rest) hung
  (next, boundsPast modes state next item bound stepped (leadPlain item.kind lead), hungRest)

--| A sign spaced as an argument's, before an atom, negates an argument, whether or not it starts a line.
theorem argumentPrefixHung ∀ (sign next: Item) (later: List Item)
    (signed: signKind sign.kind = True)
    (glue: argumentGlue [sign, next, ..later] = True)
    (opens: next.kind.opensAtom = True):
    argumentPrefix [sign, next, ..later] = True :=
  let spaced: (sign.afterOperand && (!sign.glued && next.glued)) = True := rewrite signed at glue then glue
  let (afterOperand, glues) := Bool.andElim _ _ spaced
  let (unglued, nextGlued) := Bool.andElim _ _ glues
  match starts: sign.leaf.token.lineStart with
    | True => rewrite signOr sign.kind signed, afterOperand, nextGlued, opens
    | False => rewrite signOr sign.kind signed, afterOperand, Bool.notTrue _ unglued, nextGlued, opens

--| A spelt argument of this part, its first item not stopping the reading, starts an atom.
theorem argStartsHung ∀ (modes: Modes) (argument: Expr) (first: Item) (more later: List Item)
    (spelt: Spelt argument [first, ..more])
    (fits: argumentFits argument [first, ..more] = True)
    (open: modes.stops first = False):
    startsAtomOn modes [first, ..more ++ later] = True :=
  match signed: argument.signed with
    | False =>
      let (start, inside, isRead, starts) := speltPlainStarts argument [first, ..more] spelt signed
      rewrite peekFirst modes first (more ++ later) open,
          firstKind first start more inside isRead,
          startOpens start.kind starts
    | True =>
      match argument, spelt, fits, signed with
        | Prefix _ operand, (sign, inner, isRead, isSign, _, _, _, operandSpelt), fits, _ =>
          let isSign1: first = sign := List.consInjectiveHead isRead
          let isInner: more = inner := Eq.cong (.drop 1) isRead
          let (next, others, isOperand, nextStarts) :=
            speltPlainStarts operand inner operandSpelt (atomicUnsigned operand (Bool.andLeft fits))
          let glueInner: argumentGlue [sign, ..inner] = True :=
            Eq.trans (Eq.cong (taken => argumentGlue taken) isRead).flipped (Bool.andRight fits)
          let glueNext: argumentGlue [sign, next, ..others] = True :=
            Eq.trans (Eq.cong (taken => argumentGlue [sign, ..taken]) isOperand).flipped glueInner
          let glue: argumentGlue [sign, next, ..others ++ later] = True := glueNext
          rewrite isSign1,
              isInner,
              isOperand,
              peekFirst modes sign ([next, ..others] ++ later) (rewrite <- isSign1 then open) then
            signStartsAtom modes sign.kind
              [sign, next, ..others ++ later]
              isSign
              (argumentPrefixHung sign next (others ++ later) isSign glue (startOpensAtom next.kind nextStarts))
        | Infix _ _ _ _ | App _ _, _, fits, _ => (Bool.falseNotTrue fits).impossible
        | other, _, _, never => (Bool.falseNotTrue never).impossible

--| What follows an argument, on any lines: the next argument, whose first item the state before it bounds, or what
--| follows the call.
theorem argEndsHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (head: Bool) (kind: Tok) (exprs: List Expr) (steps: List (List Item, Expr)) (rest: List Item) (state: HangState)
    (spelt: SpeltArgs exprs steps)
    (line: lineAll (Parse.loopReads [] steps ++ rest) = True)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf (Parse.loopReads [] steps ++ rest)) = True)
    (ends: UnaryEnds modes rest):
    AtomEnds modes head kind (Parse.loopReads [] steps ++ rest) :=
  match exprs, spelt with
    | [], isEmpty => rewrite isEmpty then ends.atom head kind
    | [argument, ..more], (read, later, isSteps, _, argSpelt, _) =>
      let (first, inside, isRead, lead) := speltStarts argument read argSpelt
      let reads: Parse.loopReads [] steps = [first, ..inside ++ Parse.loopReads [] later] := rewrite isSteps, isRead
      let joined: [first, ..inside] ++ (Parse.loopReads [] later ++ rest) = Parse.loopReads [] steps ++ rest :=
        rewrite reads then Eq.cong (Cons first) (List.appendAssoc inside (Parse.loopReads [] later) rest).flipped
      let lineFirst: lineAll ([first, ..inside] ++ (Parse.loopReads [] later ++ rest)) = True :=
        Eq.trans (Eq.cong lineAll joined) line
      let hungFirst: hangsFrom state (leavesOf ([first, ..inside] ++ (Parse.loopReads [] later ++ rest))) = True :=
        Eq.trans (Eq.cong (taken => hangsFrom state (leavesOf taken)) joined) hung
      let (open, _, _) :=
        leadHung modes state first (inside ++ (Parse.loopReads [] later ++ rest)) quiet lead bound hungFirst
      rewrite <- joined then
        endsBeforeSpelt modes head kind argument first inside
          (Parse.loopReads [] later ++ rest)
          (rewrite <- isRead then argSpelt)
          open
          lineFirst
