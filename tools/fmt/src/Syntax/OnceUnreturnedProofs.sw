--| `settledOnce` keeps comments that end in neither a carriage return nor a space (SW-4089), said of the words the
--| parser reads: the lexer's comments are such (`Syntax.LexUnreturnedProofs`), rule N only moves them and trims
--| spaces, which these have none of.

namespace Syntax.OnceUnreturnedProofs
import Std (Bool, Char, DecEq, Eq, List, Nat, Option, Text)
import Syntax (..)
import Fmt (..)
import Syntax.SettleProofs (
  alphabet1,
  laidOut,
  leafTexts,
  leavesTextsSplit,
  lexedTexts,
  plain1,
  plainFromOf,
  settledKeepsComments,
  tokens,
  tokensReverseOnto,
  triviaTexts
)
import Syntax.SettleBareProofs (..)
import Syntax.SettleOnceProofs (..)
import Syntax.LexUnreturnedProofs (plainEnd)

--| Rule 5's trim leaves a text with no space at its end as it is.
theorem trimEndPlain ∀ (text: Text) (plain: plainEnd text = True): trimEnd text = text :=
  let unspaced: text.endsWith " " = False := Bool.notTrue _ (Bool.andRight plain)
  rewrite unspaced

theorem allTrimPlain ∀ (texts: List Text) (plain: texts.all plainEnd = True): (texts.map trimEnd).all plainEnd = True :=
  match texts with
    | [] => byComputing
    | [text, ..rest] =>
      let same := trimEndPlain text (Bool.andLeft plain)
      Bool.andIntro (rewrite same then Bool.andLeft plain) (allTrimPlain rest (Bool.andRight plain))

theorem leavesPlainTexts ∀ (leaves: List Leaf)
    (all: (leafTexts leaves).all plainEnd = True):
    leaves.all (leaf => (triviaTexts leaf.trivia).all plainEnd) = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      let split :=
        rewrite textsCons leaf rest, allAppendB (triviaTexts leaf.trivia) (leafTexts rest) plainEnd at all then all
      Bool.andIntro (Bool.andLeft split) (leavesPlainTexts rest (Bool.andRight split))

theorem wordsPlainTexts ∀ (leaves: List Leaf)
    (all: leaves.all (leaf => (triviaTexts leaf.trivia).all plainEnd) = True):
    (wordsOf leaves).all (word => word.comments.texts.all plainEnd) = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      match comma: leaf.kind != Comma with
        | False => wordsPlainTexts rest (Bool.andRight all)
        | True =>
          Bool.andIntro (rewrite wordTexts leaf then Bool.andLeft all) (wordsPlainTexts rest (Bool.andRight all))

--| The words of the leaves the formatter parses, `settledOnce`, and its end, hold only comments that end in neither a
--| carriage return nor a space, if the lexer's leaves do and are laid out and `plain` in the alphabet.
--|
--| Proof idea: as `onceSettledProved`. `settledOnce`'s words are those of `settledBare`, rule N on the leaves without
--| their last commas; dropping those keeps the comments' texts (`textsWithout`), and rule N only moves comments and
--| trims spaces (`settledKeepsComments`, `trimEndPlain`).
theorem onceTextsPlain ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True)
    (plain: plain1 (tokens lexed.leaves) = True)
    (laid: laidOut False lexed.leaves = True)
    (unreturned: (lexedTexts lexed).all plainEnd = True):
    (wordsOf lexed.settledOnce.leaves).all (word => word.comments.texts.all plainEnd) = True
      ∧ lexed.settledOnce.end.comments.texts.all plainEnd = True :=
  let leaves := lexed.leaves
  let plainF := plainFromOf (tokens leaves) plain
  let out := withoutR [] leaves
  let swapped: withoutLastCommas [] leaves = out.reverseOnto [] := withoutFromR [] leaves
  let lexedB: Lexed := { lexed | leaves = withoutLastCommas [] lexed.leaves }
  let laidB: laidOut False lexedB.leaves = True :=
    rewrite swapped then laidOnto out [] (laidWithout [] leaves byComputing laid plainF) byComputing
  let plainB: plain1 (tokens lexedB.leaves) = True :=
    rewrite swapped then plainOfJoin out (plainWithout [] leaves plain plainF)
  let tokensB: ∀ (q: Token → Bool) (kept: (tokens leaves).all q = True) => (tokens lexedB.leaves).all q = True :=
    q kept =>
      rewrite swapped, tokensReverseOnto out [], allReverseOnto (tokens out) [] q then
        Bool.andIntro (allTokensWithout q [] leaves plainF byComputing kept) byComputing
  let withinB: alphabet1 lexedB.leaves = True := tokensB (token => token.kind.within1) within
  let split :=
    rewrite leavesTextsSplit leaves lexed.end,
        allAppendB (leafTexts leaves) (triviaTexts lexed.end) plainEnd at unreturned then
      unreturned
  let leavesB: (leafTexts lexedB.leaves).all plainEnd = True :=
    rewrite swapped, textsReverseOnto plainEnd out [] then
      Bool.andIntro
        (textsWithout plainEnd [] leaves byComputing laid plainF byComputing (Bool.andLeft split))
        byComputing
  let textsB: (lexedTexts lexedB).all plainEnd = True :=
    rewrite leavesTextsSplit lexedB.leaves lexedB.end,
        allAppendB (leafTexts lexedB.leaves) (triviaTexts lexedB.end) plainEnd then
      Bool.andIntro leavesB (Bool.andRight split)
  let settled := lexedB.settled
  let textsS: (lexedTexts settled).all plainEnd = True :=
    rewrite settledKeepsComments lexedB withinB laidB then allTrimPlain (lexedTexts lexedB) textsB
  let (leavesEq, endEq) := bareSettles lexed within plain
  let wordsEq: wordsOf lexed.settledOnce.leaves = wordsOf settled.leaves :=
    Eq.trans (wordsOfDropF [] lexed.settledOnce.leaves).flipped (rewrite leavesEq)
  let textsSplit :=
    rewrite leavesTextsSplit settled.leaves settled.end,
        allAppendB (leafTexts settled.leaves) (triviaTexts settled.end) plainEnd at textsS then
      textsS
  let wordTextsS := wordsPlainTexts settled.leaves (leavesPlainTexts settled.leaves (Bool.andLeft textsSplit))
  let endTextsS: lexedB.settled.end.comments.texts.all plainEnd = True :=
    rewrite endTexts lexedB.settled.end then Bool.andRight textsSplit
  (rewrite wordsEq then wordTextsS, rewrite endEq then endTextsS)
