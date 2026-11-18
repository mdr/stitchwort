--| `printedSettle1` (SW-4043, ticket G of docs/reviews/SW-4025-output-statements.md, sketched in
--| docs/reviews/SW-4042-trivia-statement.md §5): rule N on the formatter's output gives the tree's words back, from
--| `stands` of each declaration's printed leaves (`printedStands1`, taken as the hypothesis `SourceFile.stood1`).
--| Rule 1 walks each comment `stands` owes back to its word (`homeStands`); the other rules find nothing to do.

namespace Fmt.SettleOutputProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Text, Void)
import Syntax (..)
import Fmt (..)
import Fmt.OutputStatements (..)
import Fmt.TriviaStatements (..)
import Syntax.ParseCarries (codeWords)
import Syntax.SettleProofs (
  barsQuiet1,
  chainSteps,
  chainTo,
  endsOn,
  landedHere,
  movableQuiet1,
  passable,
  skippedQuiet1,
  stopsAt,
  tokens,
  trailingAtTokens,
  withinOfTokens,
  emptyOf,
  bareComma
)

-- What rule 1 has passed.

--| The leaf's kind is a closer's exactly when its text is one: true of the leaves the formatter's output lexes to.
def Leaf.agrees (leaf: Leaf): Bool := leaf.kind.isCloser == isCloserText leaf.token.text

--| The leaf is the word: `headedAs` it, with the same trailing comment, and of a closer's kind if a closer.
def Leaf.fits (leaf: Leaf) (word: Word): Bool :=
  leaf.headedAs word && leaf.trivia.trailing.map (comment => comment.text) == word.comments.after && leaf.agrees

--| No comment on the leaf.
def Leaf.bare (leaf: Leaf): Bool := leaf.trivia.trailing.isNone && leaf.trivia.leading.isEmpty

--| Leaves rule 1 has passed, newest first, against the words they hold, newest first, with no comment owed: each
--| comma bare and after some word, each other leaf its word.
def matched: List Leaf → List Word → Bool
  | [], done => done.isEmpty
  | [leaf, ..earlier], done =>
    if leaf.kind == Comma then !done.isEmpty && leaf.bare && matched earlier done
    else
      match done with
        | [] => False
        | [word, ..older] => leaf.fits word && matched earlier older

--| A comment on `leaf` stays there under rule 1: what `chainTo` asks of a chain's last leaf.
def lands (leaf: Leaf) (earlier: List Leaf): Bool := !passable leaf || earlier.isEmpty || stopsAt leaf earlier

--| As `matched`, with the comment `text` owed: the newest leaves are bare commas and closers that start no line, each
--| its word, then the leaf of the word that owes the comment, which holds none yet and is one the comment lands on.
def owing (text: Text): List Leaf → List Word → Bool
  | [], _ => False
  | [leaf, ..earlier], done =>
    if leaf.kind == Comma then leaf.bare && !leaf.token.lineStart && owing text earlier done
    else
      match done with
        | [] => False
        | [word, ..older] =>
          if word.comments.after == Some text then
            leaf.trivia.trailing.isNone
              && leaf.headedAs word
              && leaf.agrees
              && lands leaf earlier
              && matched earlier older
          else leaf.kind.isCloser && !leaf.token.lineStart && leaf.fits word && owing text earlier older

--| `matched`, or `owing` what is owed.
def held (owed: Option Text) (behind: List Leaf) (done: List Word): Bool := match owed with
  | None => matched behind done
  | Some text => owing text behind done

theorem matchedEmpty ∀ (behind: List Leaf) (m: matched behind [] = True): behind = [] := match behind with
  | [] => byComputing
  | [leaf, ..earlier] =>
    match comma: leaf.kind == Comma with
      | False => Void.impossible (Bool.falseNotTrue m)

--| What `fits` says, as equations.
theorem fitsParts ∀ (leaf: Leaf) (word: Word)
    (fits: leaf.fits word = True):
    leaf.token.text = word.text
      ∧ leaf.word.comments.above = word.comments.above
      ∧ leaf.word.comments.blankBefore = word.comments.blankBefore
      ∧ leaf.trivia.trailing.map (comment => comment.text) = word.comments.after
      ∧ leaf.kind.isCloser = isCloserText leaf.token.text :=
  let headed := Bool.andLeft fits
  let rest := Bool.andRight fits
  (
    DecEq.sound (Bool.andLeft headed),
    DecEq.sound (Bool.andLeft (Bool.andRight headed)),
    DecEq.sound (Bool.andRight (Bool.andRight headed)),
    DecEq.sound (Bool.andLeft rest),
    DecEq.sound (Bool.andRight rest)
  )

--| A leaf that fits a word is it.
theorem fitsWord ∀ (leaf: Leaf) (word: Word) (fits: leaf.fits word = True): leaf.word = word := match word with
  | { text, comments = { above, after, blankBefore } } =>
    let (textSame, aboveSame, blankSame, afterSame, _) :=
      fitsParts leaf { text, comments = { above, after, blankBefore } } fits
    rewrite textSame, aboveSame, blankSame, afterSame

--| Where rule 1 looks back for a comment ending the line before a closer, the leaves have one exactly when the words
--| do: `endsOn` of the leaves is `trailsBack` of their words.
theorem endsOnMatched ∀ (behind: List Leaf) (done: List Word)
    (m: matched behind done = True):
    endsOn behind = trailsBack done :=
  match behind with
    | [] => rewrite emptyOf done m
    | [leaf, ..earlier] =>
      match comma: leaf.kind == Comma with
        | True =>
          let bare := Bool.andLeft (Bool.andRight m)
          let later := Bool.andRight (Bool.andRight m)
          match trailing: leaf.trivia.trailing with
            | None =>
              match earlier with
                | [] =>
                  let notEmpty: (!done.isEmpty) = True := Bool.andLeft m
                  Void.impossible (Bool.falseNotTrue (rewrite later at notEmpty then notEmpty))
                | [next, ..more] => endsOnMatched [next, ..more] done later
        | False =>
          match done with
            | [word, ..older] =>
              let (textSame, _, _, afterSame, agrees) := fitsParts leaf word (Bool.andLeft m)
              let later := Bool.andRight m
              match trailing: leaf.trivia.trailing with
                | Some comment => rewrite <- afterSame
                | None =>
                  rewrite <- afterSame, <- textSame, <- agrees then
                    match closer: leaf.kind.isCloser with
                      | False =>
                        match earlier with
                          | [] => byComputing
                          | [_, .._] => byComputing
                      | True =>
                        match earlier with
                          | [] => rewrite emptyOf older later
                          | [next, ..more] => endsOnMatched [next, ..more] older later

--| The words of matched leaves, in order.
theorem matchedWords ∀ (behind acc: List Leaf) (done: List Word)
    (m: matched behind done = True):
    codeWords (behind.reverseOnto acc) = done.reverseOnto (codeWords acc) :=
  match behind with
    | [] => rewrite emptyOf done m
    | [leaf, ..earlier] =>
      match comma: leaf.kind == Comma with
        | True =>
          let skip: codeWords [leaf, ..acc] = codeWords acc := rewrite comma
          rewrite matchedWords earlier [leaf, ..acc] done (Bool.andRight (Bool.andRight m)), skip
        | False =>
          match done with
            | [word, ..older] =>
              let keep: codeWords [leaf, ..acc] = [word, ..codeWords acc] :=
                rewrite comma, fitsWord leaf word (Bool.andLeft m)
              rewrite matchedWords earlier [leaf, ..acc] older (Bool.andRight m), keep

--| Matched leaves' commas are bare.
theorem matchedBare ∀ (behind: List Leaf) (done: List Word)
    (m: matched behind done = True):
    behind.all bareComma = True :=
  match behind with
    | [] => byComputing
    | [leaf, ..earlier] =>
      match comma: leaf.kind == Comma with
        | True =>
          let bare := Bool.andLeft (Bool.andRight m)
          match leaf.trivia.trailing, leaf.trivia.leading with
            | None, [] => matchedBare earlier done (Bool.andRight m)
        | False =>
          match done with
            | [word, ..older] => Bool.andIntro (Bool.orRight byComputing) (matchedBare earlier older (Bool.andRight m))

theorem orFalseIs ∀ (a: Bool) (h: (a || False) = True): a = True := match a with | True => byComputing

--| A comment is owed only once a word has been passed.
theorem owingNonEmpty ∀ (text: Text) (behind: List Leaf) (done: List Word)
    (owes: owing text behind done = True):
    (!done.isEmpty) = True :=
  match behind with
    | [leaf, ..earlier] =>
      match comma: leaf.kind == Comma with
        | True => owingNonEmpty text earlier done (Bool.andRight (Bool.andRight owes))
        | False =>
          match done with
            | [word, ..older] => byComputing

theorem homedReverseOnto ∀ (xs ys: List Word) (homed: homedBack (xs.reverseOnto ys) = True): homedBack ys = True :=
  match xs with
    | [] => homed
    | [x, ..rest] => Bool.andRight (homedReverseOnto rest [x, ..ys] homed)

--| A word's leaf holding the word's comment is one rule 1 leaves it on, given `homedBack` of the words: a closer
--| holding one starts its line, and has own-line comments or follows a line ending with a comment.
theorem landing ∀ (leaf: Leaf) (word: Word) (behind: List Leaf) (done: List Word)
    (notComma: (leaf.kind == Comma) = False)
    (headed: leaf.headedAs word = True)
    (agrees: leaf.agrees = True)
    (trails: word.comments.after.isSome = True)
    (open: (!leaf.kind.isCloser || leaf.token.lineStart) = True)
    (m: matched behind done = True)
    (homed: homedBack [word, ..done] = True):
    lands leaf behind = True :=
  match comma: leaf.kind == Comma with
    | False =>
      match closer: leaf.kind.isCloser with
        | False => byComputing
        | True =>
          let textSame: leaf.token.text = word.text := DecEq.sound (Bool.andLeft headed)
          let aboveSame: leaf.word.comments.above = word.comments.above :=
            DecEq.sound (Bool.andLeft (Bool.andRight headed))
          let closes: isCloserText word.text = True := rewrite <- textSame, <- DecEq.sound agrees then closer
          let first := Bool.andLeft homed
          let reasons: (done.isEmpty || word.noted || trailsBack done) = True :=
            rewrite closes, trails at first then first
          match empty: done.isEmpty with
            | True => rewrite matchedEmpty behind (rewrite emptyOf done empty at m then m)
            | False =>
              let stops: stopsAt leaf behind = True := match noted: word.noted with
                | True =>
                  match leaf.trivia.leading with
                    | [] => Void.impossible (Bool.falseNotTrue (rewrite <- aboveSame at noted then noted))
                    | [_, .._] => Bool.andIntro open byComputing
                | False => Bool.andIntro open (Bool.orRight (rewrite endsOnMatched behind done m then reasons))
              Bool.orRight stops

--| Rule 1's walk from a comma or closer holding the owed comment ends on the word that owes it, and leaves the leaves
--| matched.
theorem owingPlaced ∀ (text: Text) (behind: List Leaf) (done: List Word) (comment: Comment)
    (owes: owing text behind done = True)
    (named: comment.text = text):
    ∃ (steps: Nat) => chainTo (Succ steps) behind = True
      ∧ matched (trailingAt behind (Succ steps) comment) done = True :=
  match behind with
    | [leaf, ..earlier] =>
      match comma: leaf.kind == Comma with
        | True =>
          let (steps, chain, placed) := owingPlaced text earlier done comment (Bool.andRight (Bool.andRight owes)) named
          let chained: chainTo (Succ (Succ steps)) [leaf, ..earlier] = True :=
            Bool.andIntro (Bool.orLeft comma) (Bool.andIntro (Bool.andLeft (Bool.andRight owes)) chain)
          let still: matched [leaf, ..trailingAt earlier (Succ steps) comment] done = True :=
            rewrite comma then
              Bool.andIntro
                (owingNonEmpty text earlier done (Bool.andRight (Bool.andRight owes)))
                (Bool.andIntro (Bool.andLeft owes) placed)
          (Succ steps, chained, still)
        | False =>
          match done with
            | [word, ..older] =>
              match owed: word.comments.after == Some text with
                | True =>
                  let headed := Bool.andLeft (Bool.andRight owes)
                  let agrees := Bool.andLeft (Bool.andRight (Bool.andRight owes))
                  let landsHere := Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight owes)))
                  let rest := Bool.andRight (Bool.andRight (Bool.andRight (Bool.andRight owes)))
                  let trailSame: (Some comment.text == word.comments.after) = True :=
                    rewrite named, DecEq.sound owed then DecEq.refl (Some text)
                  let fitted: (leaf.withTrailing (Some comment)).fits word = True :=
                    Bool.andIntro headed (Bool.andIntro trailSame agrees)
                  let still: matched [leaf.withTrailing (Some comment), ..earlier] [word, ..older] = True :=
                    rewrite comma then Bool.andIntro fitted rest
                  (0, landsHere, still)
                | False =>
                  let closer := Bool.andLeft owes
                  let notStart := Bool.andLeft (Bool.andRight owes)
                  let fitted := Bool.andLeft (Bool.andRight (Bool.andRight owes))
                  let rest := Bool.andRight (Bool.andRight (Bool.andRight owes))
                  let (steps, chain, placed) := owingPlaced text earlier older comment rest named
                  let chained: chainTo (Succ (Succ steps)) [leaf, ..earlier] = True :=
                    Bool.andIntro (Bool.orRight closer) (Bool.andIntro notStart chain)
                  let still: matched [leaf, ..trailingAt earlier (Succ steps) comment] [word, ..older] = True :=
                    rewrite comma then Bool.andIntro fitted placed
                  (Succ steps, chained, still)

--| The first leaf, if any, is no comma.
def notCommaFirst: List Leaf → Bool
  | [] => True
  | [leaf, .._] => !(leaf.kind == Comma)

def kindWithin (leaf: Leaf): Bool := leaf.kind.within1

--| Rule 1 on leaves that stand against their words gives each leaf its word: the comments `stands` owes on past
--| closers and commas go back to the word that owes them, and every comma is left bare.
--|
--| Proof idea: by induction on the leaves left, keeping `held`: with nothing owed the leaves passed are matched,
--| with a comment owed they are a chain of commas and closers back to the word that owes it (`owing`). A comma or
--| closer holding the owed comment walks it back along that chain (`chainSteps`, `owingPlaced`); a word holding its
--| own comment keeps it, as it is no closer or one the comment lands on (`landing`, from `homedBack` of the words
--| and `endsOnMatched`).
theorem homeStands ∀ (owed: Option Text) (behind rest: List Leaf) (done words: List Word)
    (standing: stands owed words rest = True)
    (state: held owed behind done = True)
    (lead: (!done.isEmpty || notCommaFirst rest) = True)
    (homed: homedBack (words.reverseOnto done) = True)
    (behindWithin: behind.all kindWithin = True)
    (within: rest.all kindWithin = True)
    (agree: rest.all Leaf.agrees = True):
    matched (homeFrom behind None rest).reverse (words.reverseOnto done) = True :=
  match rest with
    | [] =>
      match owed with
        | None => rewrite emptyOf words (Bool.andLeft standing), List.reverseReverse behind then state
        | Some text => Void.impossible (Bool.falseNotTrue (Bool.andRight standing))
    | [leaf, ..after] =>
      let leafWithin: leaf.kind.within1 = True := Bool.andLeft within
      let afterWithin := Bool.andRight within
      let leafAgrees := Bool.andLeft agree
      let afterAgree := Bool.andRight agree
      let pushedWithin: [leaf, ..behind].all kindWithin = True := Bool.andIntro leafWithin behindWithin
      match comma: leaf.kind == Comma with
        | True =>
          let leadingEmpty: leaf.trivia.leading.isEmpty = True := Bool.andLeft standing
          let tuck := Bool.andRight (Bool.andRight standing)
          let filled: (!done.isEmpty) = True := match owed with
            | None => orFalseIs (!done.isEmpty) lead
            | Some text => owingNonEmpty text behind done state
          let leadNext: (!done.isEmpty || notCommaFirst after) = True := Bool.orLeft filled
          match owed, trailing: leaf.trivia.trailing with
            | None, None =>
              let next: matched [leaf, ..behind] done = True :=
                rewrite comma then
                  Bool.andIntro filled (Bool.andIntro (Bool.andIntro (rewrite trailing) leadingEmpty) state)
              homeStands None
                [leaf, ..behind]
                after
                done
                words
                tuck
                next
                leadNext
                homed
                pushedWithin
                afterWithin
                afterAgree
            | Some text, None =>
              match start: leaf.token.lineStart with
                | False =>
                  let next: owing text [leaf, ..behind] done = True :=
                    rewrite comma then
                      Bool.andIntro
                        (Bool.andIntro (rewrite trailing) leadingEmpty)
                        (Bool.andIntro (rewrite start) state)
                  homeStands
                    (Some text)
                    [leaf, ..behind]
                    after
                    done
                    words
                    tuck
                    next
                    leadNext
                    homed
                    pushedWithin
                    afterWithin
                    afterAgree
            | Some text, Some comment =>
              match start: leaf.token.lineStart with
                | False =>
                  match named: comment.text == text with
                    | True =>
                      let (steps, chain, placed) := owingPlaced text behind done comment state (DecEq.sound named)
                      let walked: stepsBack leaf behind after 0 = Succ steps :=
                        Eq.trans
                          (chainSteps leaf behind after
                            (Succ steps)
                            0
                            leafWithin
                            behindWithin
                            (Bool.orLeft comma)
                            start
                            chain)
                          arithmetic
                      let moved := leaf.withTrailing None
                      let target := trailingAt behind (Succ steps) comment
                      let next: matched [moved, ..target] done = True :=
                        rewrite comma then
                          Bool.andIntro filled (Bool.andIntro (Bool.andIntro byComputing leadingEmpty) placed)
                      let movedWithin: [moved, ..target].all kindWithin = True :=
                        Bool.andIntro leafWithin
                          (withinOfTokens target behind (trailingAtTokens behind (Succ steps) comment) behindWithin)
                      match moves: movable leaf behind after with
                        | True =>
                          rewrite walked then
                            homeStands None
                              [moved, ..target]
                              after
                              done
                              words
                              tuck
                              next
                              leadNext
                              homed
                              movedWithin
                              afterWithin
                              afterAgree
                        | False =>
                          Void.impossible
                            (Bool.trueNotFalse
                              (rewrite movableQuiet1 leaf behind after leafWithin, comma, start at moves then moves))
        | False =>
          match words with
            | [word, ..later] =>
              let headed: leaf.headedAs word = True := Bool.andLeft standing
              let clause := Bool.andRight standing
              let filledNext: (!([word, ..done]).isEmpty || notCommaFirst after) = True := Bool.orLeft byComputing
              match owed, afterIs: word.comments.after with
                | Some text, None =>
                  let closer: leaf.kind.isCloser = True := Bool.andLeft clause
                  let tuck := Bool.andRight clause
                  match trailing: leaf.trivia.trailing with
                    | None =>
                      match start: leaf.token.lineStart with
                        | False =>
                          let fitted: leaf.fits word = True :=
                            Bool.andIntro headed (Bool.andIntro (rewrite trailing, afterIs) leafAgrees)
                          let next: owing text [leaf, ..behind] [word, ..done] = True :=
                            rewrite comma, afterIs then
                              Bool.andIntro closer (Bool.andIntro (rewrite start) (Bool.andIntro fitted state))
                          homeStands
                            (Some text)
                            [leaf, ..behind]
                            after
                            [word, ..done]
                            later
                            tuck
                            next
                            filledNext
                            homed
                            pushedWithin
                            afterWithin
                            afterAgree
                    | Some comment =>
                      match start: leaf.token.lineStart with
                        | False =>
                          match named: comment.text == text with
                            | True =>
                              let (steps, chain, placed) :=
                                owingPlaced text behind done comment state (DecEq.sound named)
                              let walked: stepsBack leaf behind after 0 = Succ steps :=
                                Eq.trans
                                  (chainSteps leaf behind after
                                    (Succ steps)
                                    0
                                    leafWithin
                                    behindWithin
                                    (Bool.orRight closer)
                                    start
                                    chain)
                                  arithmetic
                              let moved := leaf.withTrailing None
                              let target := trailingAt behind (Succ steps) comment
                              let fitted: moved.fits word = True :=
                                Bool.andIntro headed (Bool.andIntro (rewrite afterIs) leafAgrees)
                              let next: matched [moved, ..target] [word, ..done] = True :=
                                rewrite comma then Bool.andIntro fitted placed
                              let movedWithin: [moved, ..target].all kindWithin = True :=
                                Bool.andIntro leafWithin
                                  (withinOfTokens target behind
                                    (trailingAtTokens behind (Succ steps) comment)
                                    behindWithin)
                              match moves: movable leaf behind after with
                                | True =>
                                  rewrite walked then
                                    homeStands None
                                      [moved, ..target]
                                      after
                                      [word, ..done]
                                      later
                                      tuck
                                      next
                                      filledNext
                                      homed
                                      movedWithin
                                      afterWithin
                                      afterAgree
                                | False =>
                                  Void.impossible
                                    (Bool.trueNotFalse
                                      (rewrite movableQuiet1 leaf behind after leafWithin, comma, closer at moves then
                                        moves))
                | None, None =>
                  match trailing: leaf.trivia.trailing with
                    | None =>
                      let fitted: leaf.fits word = True :=
                        Bool.andIntro headed (Bool.andIntro (rewrite trailing, afterIs) leafAgrees)
                      let next: matched [leaf, ..behind] [word, ..done] = True :=
                        rewrite comma then Bool.andIntro fitted state
                      homeStands None
                        [leaf, ..behind]
                        after
                        [word, ..done]
                        later
                        clause
                        next
                        filledNext
                        homed
                        pushedWithin
                        afterWithin
                        afterAgree
                | None, Some text =>
                  let open := Bool.andLeft clause
                  let tuck := Bool.andRight clause
                  let landsHere: lands leaf behind = True :=
                    landing leaf word behind done comma headed leafAgrees
                      (rewrite afterIs)
                      open
                      state
                      (homedReverseOnto later [word, ..done] homed)
                  match trailing: leaf.trivia.trailing with
                    | None =>
                      let next: owing text [leaf, ..behind] [word, ..done] = True :=
                        rewrite comma, afterIs, DecEq.refl (Some text) then
                          Bool.andIntro
                            (rewrite trailing)
                            (Bool.andIntro headed (Bool.andIntro leafAgrees (Bool.andIntro landsHere state)))
                      homeStands
                        (Some text)
                        [leaf, ..behind]
                        after
                        [word, ..done]
                        later
                        tuck
                        next
                        filledNext
                        homed
                        pushedWithin
                        afterWithin
                        afterAgree
                    | Some comment =>
                      let named := Bool.andLeft tuck
                      let fitted: leaf.fits word = True :=
                        Bool.andIntro headed
                          (Bool.andIntro
                            (rewrite trailing, afterIs, DecEq.sound named then DecEq.refl (Some text))
                            leafAgrees)
                      let next: matched [leaf, ..behind] [word, ..done] = True :=
                        rewrite comma then Bool.andIntro fitted state
                      let kept :=
                        homeStands None
                          [leaf, ..behind]
                          after
                          [word, ..done]
                          later
                          (Bool.andRight tuck)
                          next
                          filledNext
                          homed
                          pushedWithin
                          afterWithin
                          afterAgree
                      match moves: movable leaf behind after with
                        | False => kept
                        | True =>
                          rewrite landedHere leaf behind after 0 leafWithin behindWithin landsHere,
                              barsQuiet1 leaf behind after leafWithin then
                            kept
