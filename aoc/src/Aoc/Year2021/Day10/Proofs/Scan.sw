--| The stack scan and the grammar agree: a line is balanced exactly when
--| the scan from no open brackets ends with none open (`balancedScan`,
--| `scanBalanced`), and a start of a line is legal exactly when the scan
--| doesn't stop at an illegal closer.

namespace Aoc.Year2021.Day10.Proofs
import Aoc.Year2021.Day10 (..)
import Aoc.Year2021.Day10.Spec (..)
import Std (Bool, DecEq, Eq, Exists, List, Nat, Void)

--| What the scan of the rest does after a scan of the start.
def continue (start: Scan) (rest: List Token): Scan :=
  match start with
    | Corrupted illegal => Corrupted illegal
    | Unclosed open => scan open rest

--| Scanning two pieces is scanning the first, then the second from where it
--| left off.
theorem scanAppend: (stack: List Bracket) → (xs: List Token) → (ys: List Token) → scan stack (xs ++ ys) = continue (scan stack xs) ys
  | stack, Nil, ys => rfl
  | stack, Cons (Opener bracket) rest, ys => scanAppend (Cons bracket stack) rest ys
  | Nil, Cons (Closer bracket) rest, ys => rfl
  | Cons top below, Cons (Closer bracket) rest, ys =>
    match same: top == bracket with
      | True => scanAppend below rest ys
      | False => rfl

--| A balanced piece leaves the stack as it found it.
theorem balancedScan (stack: List Bracket) (rest: List Token): Balanced line → scan stack (line ++ rest) = scan stack rest
  | Empty => rfl
  | Concat [xs := a] [ys := b] first second =>
    rewrite List.appendAssoc a b rest in Eq.trans (balancedScan stack (b ++ rest) first) (balancedScan stack rest second)
  | Wrap [xs := inside] bracket inner =>
    rewrite List.appendAssoc inside [Closer bracket] rest in Eq.trans (balancedScan (Cons bracket stack) (Cons (Closer bracket) rest) inner) (closeTop bracket stack rest)

--| A closer matching the top of the stack takes it off.
theorem closeTop (bracket: Bracket) (stack: List Bracket) (rest: List Token): scan (Cons bracket stack) (Cons (Closer bracket) rest) = scan stack rest :=
  rewrite DecEq.refl bracket in rfl

--| The tokens a scan has read, cut at the brackets still open: `base`,
--| then each open bracket (outermost first) with what follows it. `frames`
--| lists them innermost first.
def flatten (base: List Token): List (Bracket, List Token) → List Token
  | Nil => base
  | Cons (bracket, piece) frames => flatten base frames ++ Cons (Opener bracket) piece

--| Every piece between the open brackets is balanced.
def AllBalanced (base: List Token): List (Bracket, List Token) → Prop
  | Nil => Balanced base
  | Cons (_, piece) frames => Balanced piece ∧ AllBalanced base frames

--| Closing the innermost open bracket, as lists.
theorem closeShape (start: List Token) (opener: Token) (piece: List Token) (closer: Token) (rest: List Token):
    (start ++ Cons opener piece) ++ Cons closer rest = (start ++ Cons opener (piece ++ [closer])) ++ rest :=
  rewrite List.appendAssoc start (Cons opener piece) (Cons closer rest), List.appendAssoc start (Cons opener (piece ++ [closer])) rest, List.appendAssoc piece [closer] rest in rfl

--| If the scan from the open brackets of `frames` ends with none open,
--| what was read and what is left make a balanced line.
theorem framesBalanced (base: List Token): (frames: List (Bracket, List Token)) → AllBalanced base frames → (line: List Token) →
    scan (frames.map Pair.fst) line = Unclosed Nil → Balanced (flatten base frames ++ line)
  | Nil, ok, Nil, h => rewrite List.appendNil base in ok
  | Cons (bracket, piece) frames, ok, Nil, h => cases
  | frames, ok, Cons (Opener bracket) rest, h =>
    let next := framesBalanced base (Cons (bracket, Nil) frames) (Both Empty ok) rest h
    rewrite List.appendAssoc (flatten base frames) [Opener bracket] rest at next in next
  | Nil, ok, Cons (Closer closer) rest, h => cases
  | Cons (bracket, piece) Nil, Both inner ok, Cons (Closer closer) rest, h =>
    match same: bracket == closer with
      | False => cases
      | True =>
        let next := framesBalanced (base ++ Cons (Opener bracket) (piece ++ [Closer bracket])) Nil (Concat ok (Wrap bracket inner)) rest h
        rewrite <- DecEq.sound bracket closer same, closeShape base (Opener bracket) piece (Closer bracket) rest in next
  | Cons (bracket, piece) (Cons (outer, outerPiece) frames), Both inner (Both outerOk ok), Cons (Closer closer) rest, h =>
    match same: bracket == closer with
      | False => cases
      | True =>
        let closed := Cons (Opener bracket) (piece ++ [Closer bracket])
        let next := framesBalanced base (Cons (outer, outerPiece ++ closed) frames) (Both (Concat outerOk (Wrap bracket inner)) ok) rest h
        let start := flatten base frames ++ Cons (Opener outer) outerPiece
        rewrite <- DecEq.sound bracket closer same, closeShape start (Opener bracket) piece (Closer bracket) rest, List.appendAssoc (flatten base frames) (Cons (Opener outer) outerPiece) closed in next

--| A line whose scan from no open brackets ends with none open is balanced.
theorem scanBalanced (line: List Token) (h: scan Nil line = Unclosed Nil): Balanced line := framesBalanced Nil Nil Empty line h

--| Closing every open bracket, innermost first, leaves none open.
theorem closeAll: (stack: List Bracket) → scan stack (stack.map Closer) = Unclosed Nil
  | Nil => rfl
  | Cons bracket below => Eq.trans (closeTop bracket below (below.map Closer)) (closeAll below)

--| A start the scan reads to the end is legal: closing what is open
--| finishes it.
theorem legalOfUnclosed (start: List Token) (stack: List Bracket) (h: scan Nil start = Unclosed stack): Legal start :=
  Witness (stack.map Closer) (scanBalanced (start ++ stack.map Closer) (rewrite scanAppend Nil start (stack.map Closer), h in closeAll stack))

--| A legal start isn't one the scan stops in.
theorem notCorruptedOfLegal (start: List Token) (illegal: Bracket) (legal: Legal start) (h: scan Nil start = Corrupted illegal): Void :=
  match legal with
    | Witness ending balanced =>
      let whole := balancedScan Nil Nil balanced
      let stops: Corrupted illegal = Unclosed Nil := rewrite List.appendNil (start ++ ending), scanAppend Nil start ending, h at whole in whole
      cases

def illegalOr (fallback: Bracket): Scan → Bracket
  | Corrupted illegal => illegal
  | Unclosed _ => fallback

theorem corruptedInjective (a: Bracket) (b: Bracket) (h: Corrupted a = Corrupted b): a = b := Eq.cong (illegalOr a) h

--| Every start of a legal start is legal.
theorem legalOfLonger (start: List Token) (more: List Token): Legal (start ++ more) → Legal start
  | Witness ending balanced => Witness (more ++ ending) (rewrite <- List.appendAssoc start more ending in balanced)

--| An opener is never illegal: a legal start stays legal with one more.
theorem legalOpener (start: List Token) (bracket: Bracket) (legal: Legal start): Legal (start ++ [Opener bracket]) :=
  match e: scan Nil start with
    | Corrupted illegal => Void.exfalso (notCorruptedOfLegal start illegal legal e)
    | Unclosed stack => legalOfUnclosed (start ++ [Opener bracket]) (Cons bracket stack) (rewrite scanAppend Nil start [Opener bracket], e in rfl)
