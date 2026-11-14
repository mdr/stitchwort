--| The stack scan and the grammar agree: a line is balanced exactly when
--| the scan from no open brackets ends with none open (`balancedScan`,
--| `scanBalanced`), and a start of a line is legal exactly when the scan
--| doesn't stop at an illegal closer.

namespace Aoc.Year2021.Day10.Proofs
import Aoc.Year2021.Day10 (..)
import Aoc.Year2021.Day10.Spec (..)
import Std (Bool, DecEq, Eq, Exists, List, Nat, Void)

--| What the scan of the rest does after a scan of the start.
def continue (start: Scan) (rest: List Token): Scan := match start with
  | Corrupted illegal => Corrupted illegal
  | Unclosed open => scan open rest

--| Scanning two pieces is scanning the first, then the second from where it
--| left off.
theorem scanAppend ∀ (stack: List Bracket) (xs ys: List Token): scan stack (xs ++ ys) = continue (scan stack xs) ys :=
  match stack, xs with
    | stack, [] => rfl
    | stack, [Opener bracket, ..rest] => scanAppend [bracket, ..stack] rest ys
    | [], [Closer bracket, ..rest] => rfl
    | [top, ..below], [Closer bracket, ..rest] =>
      match same: top == bracket with
        | True => scanAppend below rest ys
        | False => rfl

--| A balanced piece leaves the stack as it found it.
theorem balancedScan ∀ (stack: List Bracket) (rest: List Token):
    Balanced line → scan stack (line ++ rest) = scan stack rest
  | Empty => rfl
  | Concat [xs := a] [ys := b] first second =>
    rewrite List.appendAssoc a b rest in
      Eq.trans (balancedScan stack (b ++ rest) first) (balancedScan stack rest second)
  | Wrap [xs := inside] bracket inner =>
    rewrite List.appendAssoc inside [Closer bracket] rest in
      Eq.trans (balancedScan [bracket, ..stack] [Closer bracket, ..rest] inner) (closeTop bracket stack rest)

--| A closer matching the top of the stack takes it off.
theorem closeTop ∀ (bracket: Bracket) (stack: List Bracket) (rest: List Token):
    scan [bracket, ..stack] [Closer bracket, ..rest] = scan stack rest :=
  rewrite DecEq.refl bracket in rfl

--| The tokens a scan has read, cut at the brackets still open: `base`,
--| then each open bracket (outermost first) with what follows it. `frames`
--| lists them innermost first.
def flatten (base: List Token): List (Bracket, List Token) → List Token
  | [] => base
  | [(bracket, piece), ..frames] => flatten base frames ++ [Opener bracket, ..piece]

--| Every piece between the open brackets is balanced.
def AllBalanced (base: List Token): List (Bracket, List Token) → Prop
  | [] => Balanced base
  | [(_, piece), ..frames] => Balanced piece ∧ AllBalanced base frames

--| Closing the innermost open bracket, as lists.
theorem closeShape ∀ (start: List Token) (opener: Token) (piece: List Token) (closer: Token) (rest: List Token):
    (start ++ [opener, ..piece]) ++ [closer, ..rest] = (start ++ [opener, ..piece ++ [closer]]) ++ rest :=
  rewrite List.appendAssoc start [opener, ..piece] [closer, ..rest],
      List.appendAssoc start [opener, ..piece ++ [closer]] rest,
      List.appendAssoc piece [closer] rest in
    rfl

--| If the scan from the open brackets of `frames` ends with none open,
--| what was read and what is left make a balanced line.
theorem framesBalanced ∀ (base: List Token):
    ∀ (frames: List (Bracket, List Token)) => AllBalanced base frames
      → ∀ (line: List Token) => scan (frames.map Pair.fst) line = Unclosed [] → Balanced (flatten base frames ++ line)
  | [], ok, [], h => rewrite List.appendNil base in ok
  | [(bracket, piece), ..frames], ok, [], h => cases
  | frames, ok, [Opener bracket, ..rest], h =>
    let next := framesBalanced base [(bracket, []), ..frames] (Both Empty ok) rest h
    rewrite List.appendAssoc (flatten base frames) [Opener bracket] rest at next in next
  | [], ok, [Closer closer, ..rest], h => cases
  | [(bracket, piece)], Both inner ok, [Closer closer, ..rest], h =>
    match same: bracket == closer with
      | True =>
        let next :=
          framesBalanced
            (base ++ [Opener bracket, ..piece ++ [Closer bracket]])
            []
            (Concat ok (Wrap bracket inner))
            rest
            h
        rewrite <- same.read, closeShape base (Opener bracket) piece (Closer bracket) rest in next
  | [(bracket, piece), (outer, outerPiece), ..frames], Both inner (Both outerOk ok), [Closer closer, ..rest], h =>
    match same: bracket == closer with
      | True =>
        let closed := [Opener bracket, ..piece ++ [Closer bracket]]
        let next :=
          framesBalanced base
            [(outer, outerPiece ++ closed), ..frames]
            (Both (Concat outerOk (Wrap bracket inner)) ok)
            rest
            h
        let start := flatten base frames ++ [Opener outer, ..outerPiece]
        rewrite <- same.read,
            closeShape start (Opener bracket) piece (Closer bracket) rest,
            List.appendAssoc (flatten base frames) [Opener outer, ..outerPiece] closed in
          next

--| A line whose scan from no open brackets ends with none open is balanced.
theorem scanBalanced ∀ (line: List Token) (h: scan [] line = Unclosed []): Balanced line :=
  framesBalanced [] [] Empty line h

--| Closing every open bracket, innermost first, leaves none open.
theorem closeAll ∀ (stack: List Bracket): scan stack (stack.map Closer) = Unclosed [] := match stack with
  | [] => rfl
  | [bracket, ..below] => Eq.trans (closeTop bracket below (below.map Closer)) (closeAll below)

--| A start the scan reads to the end is legal: closing what is open
--| finishes it.
theorem legalOfUnclosed ∀ (start: List Token) (stack: List Bracket) (h: scan [] start = Unclosed stack): Legal start :=
  Witness
    (stack.map Closer)
    (scanBalanced (start ++ stack.map Closer) (rewrite scanAppend [] start (stack.map Closer), h in closeAll stack))

--| A legal start isn't one the scan stops in.
theorem notCorruptedOfLegal ∀ (start: List Token) (illegal: Bracket)
    (legal: Legal start)
    (h: scan [] start = Corrupted illegal):
    Void :=
  match legal with
    | Witness ending balanced =>
      let whole := balancedScan [] [] balanced
      let stops: Corrupted illegal = Unclosed [] :=
        rewrite List.appendNil (start ++ ending), scanAppend [] start ending, h at whole in whole
      cases

def illegalOr (fallback: Bracket): Scan → Bracket
  | Corrupted illegal => illegal
  | Unclosed _ => fallback

theorem corruptedInjective ∀ (a b: Bracket) (h: Corrupted a = Corrupted b): a = b := Eq.cong (illegalOr a) h

--| Every start of a legal start is legal.
theorem legalOfLonger ∀ (start more: List Token): Legal (start ++ more) → Legal start
  | Witness ending balanced => Witness (more ++ ending) (rewrite <- List.appendAssoc start more ending in balanced)

--| An opener is never illegal: a legal start stays legal with one more.
theorem legalOpener ∀ (start: List Token) (bracket: Bracket) (legal: Legal start): Legal (start ++ [Opener bracket]) :=
  match e: scan [] start with
    | Corrupted illegal => Void.exfalso (notCorruptedOfLegal start illegal legal e)
    | Unclosed stack =>
      legalOfUnclosed
        (start ++ [Opener bracket])
        [bracket, ..stack]
        (rewrite scanAppend [] start [Opener bracket], e in rfl)
