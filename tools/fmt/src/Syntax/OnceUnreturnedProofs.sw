--| `settledOnce` keeps comments that end in neither a carriage return nor a space (SW-4089), said of the words the
--| parser reads: the lexer's comments are such (`Syntax.LexUnreturnedProofs`), comment placement only moves them and trims
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
  settledKeepsComments,
  sourcePlain1,
  sourcePlainFromOf,
  tokens,
  tokensReverseOnto,
  triviaTexts
)
import Syntax.SettleBareProofs (..)
import Syntax.SettleMarkProofs (..)
import Syntax.SettleOnceProofs (..)
import Syntax.LexUnreturnedProofs (plainEnd)

--| Trim leaves a text with no space at its end as it is.
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
        rewrite textsCons leaf rest, List.allAppendAnd (triviaTexts leaf.trivia) (leafTexts rest) plainEnd at all then
          all
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
--| Proof idea: as `onceSettledProved`. `settledOnce`'s words are those of `settledBare` (`bareSettles`), comment placement on the leaves without
--| their last commas; dropping those keeps the comments' texts (`textsWithout`), and comment placement only moves comments and
--| trims spaces (`settledKeepsComments`, `trimEndPlain`).
theorem onceTextsPlain ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True)
    (plain: sourcePlain1 (tokens lexed.leaves) = True)
    (laid: laidOut False lexed.leaves = True)
    (unreturned: (lexedTexts lexed).all plainEnd = True):
    (wordsOf lexed.settledOnce.leaves).all (word => word.comments.texts.all plainEnd) = True
      ∧ lexed.settledOnce.end.comments.texts.all plainEnd = True :=
  let leaves := lexed.leaves
  let plainF := sourcePlainFromOf (tokens leaves) plain
  let out := withoutR [] leaves
  let swapped: withoutLastCommas [] leaves = out.reverseOnto [] := withoutFromR [] leaves
  let lexedB: Lexed := { lexed | leaves = withoutLastCommas [] lexed.leaves }
  let laidB: laidOut False lexedB.leaves = True :=
    rewrite swapped then laidOnto out [] (laidWithout [] leaves byComputing laid) byComputing
  let plainB: plain1 (tokens lexedB.leaves) = True :=
    rewrite swapped then plainOfJoin out (plainWithout [] leaves (joinStart leaves plain) plainF)
  let tokensB: ∀ (q: Token → Bool) (blind: ∀ (token: Token) (start: Bool) => q { token | lineStart = start }
    = q token) (kept: (tokens leaves).all q = True) => (tokens lexedB.leaves).all q = True :=
    q blind kept =>
      rewrite swapped, tokensReverseOnto out [], List.allReverseOntoAnd (tokens out) [] q then
        Bool.andIntro (allTokensWithout q blind [] leaves byComputing kept) byComputing
  let withinB: alphabet1 lexedB.leaves = True :=
    tokensB (token => token.kind.within1) (token start => byComputing) within
  let split :=
    rewrite leavesTextsSplit leaves lexed.end,
        List.allAppendAnd (leafTexts leaves) (triviaTexts lexed.end) plainEnd at unreturned then
      unreturned
  let leavesB: (leafTexts lexedB.leaves).all plainEnd = True :=
    rewrite swapped, textsReverseOnto plainEnd out [] then
      Bool.andIntro (textsWithout plainEnd [] leaves byComputing laid byComputing (Bool.andLeft split)) byComputing
  let textsB: (lexedTexts lexedB).all plainEnd = True :=
    rewrite leavesTextsSplit lexedB.leaves lexedB.end,
        List.allAppendAnd (leafTexts lexedB.leaves) (triviaTexts lexedB.end) plainEnd then
      Bool.andIntro leavesB (Bool.andRight split)
  let settled := lexedB.settled
  let textsS: (lexedTexts settled).all plainEnd = True :=
    rewrite settledKeepsComments lexedB withinB laidB then allTrimPlain (lexedTexts lexedB) textsB
  let (leavesEq, endEq) := bareSettles lexed within plain
  let dropped := dropF [] lexed.settledOnce.leaves
  let wordsEq: wordsOf lexed.settledOnce.leaves = wordsOf settled.leaves := calc wordsOf lexed.settledOnce.leaves
    _ = wordsOf dropped := (wordsOfDropF [] lexed.settledOnce.leaves).flipped
    _ = wordsOf (dropped.map Leaf.unstarted) := (wordsOfUnstarted dropped).flipped
    _ = wordsOf (settled.leaves.map Leaf.unstarted) := rewrite leavesEq
    _ = wordsOf settled.leaves := wordsOfUnstarted settled.leaves
  let textsSplit :=
    rewrite leavesTextsSplit settled.leaves settled.end,
        List.allAppendAnd (leafTexts settled.leaves) (triviaTexts settled.end) plainEnd at textsS then
      textsS
  let wordTextsS := wordsPlainTexts settled.leaves (leavesPlainTexts settled.leaves (Bool.andLeft textsSplit))
  let endTextsS: lexedB.settled.end.comments.texts.all plainEnd = True :=
    rewrite endTexts lexedB.settled.end then Bool.andRight textsSplit
  (rewrite wordsEq then wordTextsS, rewrite endEq then endTextsS)
