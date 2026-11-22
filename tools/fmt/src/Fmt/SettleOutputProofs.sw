--| `printedSettle1` (SW-4043, ticket G of docs/reviews/SW-4025-output-statements.md, sketched in
--| docs/reviews/SW-4042-trivia-statement.md §5): comment placement on the formatter's output gives the tree's words back, from
--| `stands` of each declaration's printed leaves (`printedStands1`, taken as the hypothesis `SourceFile.stood`).
--| The back-walk walks each comment `stands` owes back to its word (`homeStands`); the other rules find nothing to do.

namespace Fmt.SettleOutputProofs
import Std (Bool, DecEq, Eq, List, Nat, Option, Text, Void)
import Syntax (..)
import Fmt (..)
import Fmt.OutputStatements (..)
import Fmt.TriviaStatements (..)
import Fmt.FileLexProofs (laidNotesFalse, printedFileLexes1)
import Fmt.OutputFileProofs (declStartsKw, printedAlphabet1, printedGroups1, printedPlain1)
import Syntax.ParseSettledStatements (..)
import Syntax.ReadBackHungFrameLemmas (wordIsNoArrow)
import Fmt.CalmProofs (..)
import Syntax.ParseCarries (codeWords)
import Syntax.SettleOnceProofs (isMarked, markedTokens)
import Syntax.SettleProofs (
  alphabet1,
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
  bareComma,
  alphabet1Leaves,
  arrowsIdleAll,
  commasIdle,
  homeFromTokens,
  letsQuiet1,
  plain1,
  plainFrom,
  plainFromOf,
  tokensReverseOnto
)
import Syntax.SettleSplitProofs (
  codeWordsAppend,
  declsWordsOpen,
  endsOpen,
  endsOpenReverse,
  groupsConcat,
  startsOpen,
  startsOpenConcat,
  trailsBackAppend
)
import Syntax.ParseWalk (wordWithinWithin)
import Syntax.SharedFacts (arrowsBareSuffix)

-- What the back-walk has passed.

--| The leaf's kind is a closer's exactly when its text is one: true of the leaves the formatter's output lexes to.
def Leaf.agrees (leaf: Leaf): Bool := leaf.kind.isCloser == isCloserText leaf.token.text

--| The leaf is the word: `headedAs` it, with the same trailing comment, and of a closer's kind if a closer.
def Leaf.fits (leaf: Leaf) (word: Word): Bool :=
  leaf.headedAs word && leaf.trivia.trailing.map (comment => comment.text) == word.comments.after && leaf.agrees

--| No comment on the leaf.
def Leaf.bare (leaf: Leaf): Bool := leaf.trivia.trailing.isNone && leaf.trivia.leading.isEmpty

--| Leaves the back-walk has passed, newest first, against the words they hold, newest first, with no comment owed: each
--| comma bare and after some word, each other leaf its word.
def matched: List Leaf → List Word → Bool
  | [], done => done.isEmpty
  | [leaf, ..earlier], done =>
    if leaf.kind == Comma then !done.isEmpty && leaf.bare && matched earlier done
    else
      match done with
        | [] => False
        | [word, ..older] => leaf.fits word && matched earlier older

--| A comment on `leaf` stays there under the back-walk: what `chainTo` asks of a chain's last leaf.
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
theorem fitsParts ∀ [leaf: Leaf] (word: Word)
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
      fitsParts { text, comments = { above, after, blankBefore } } fits
    rewrite textSame, aboveSame, blankSame, afterSame

--| Where the back-walk looks back for a comment ending the line before a closer, the leaves have one exactly when the words
--| do: `endsOn` of the leaves is `trailsBack` of their words.
theorem endsOnMatched ∀ (behind: List Leaf) (done: List Word)
    (m: matched behind done = True):
    endsOn behind = trailsBack done :=
  match behind with
    | [] => rewrite List.eqNilOfIsEmpty done m
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
              let (textSame, _, _, afterSame, agrees) := fitsParts word (Bool.andLeft m)
              let later := Bool.andRight m
              match trailing: leaf.trivia.trailing with
                | Some comment => rewrite <- afterSame
                | None =>
                  rewrite <- afterSame, <- textSame, <- agrees then
                    match closer: leaf.kind.isCloser with
                      | False => cases earlier then byComputing
                      | True =>
                        match earlier with
                          | [] => rewrite List.eqNilOfIsEmpty older later
                          | [next, ..more] => endsOnMatched [next, ..more] older later

--| The words of matched leaves, in order.
theorem matchedWords ∀ (behind acc: List Leaf) (done: List Word)
    (m: matched behind done = True):
    codeWords (behind.reverseOnto acc) = done.reverseOnto (codeWords acc) :=
  match behind with
    | [] => rewrite List.eqNilOfIsEmpty done m
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

--| A word's leaf holding the word's comment is one the back-walk leaves it on, given `homedBack` of the words: a closer
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
            | True => rewrite matchedEmpty behind (rewrite List.eqNilOfIsEmpty done empty at m then m)
            | False =>
              let stops: stopsAt leaf behind = True := match noted: word.noted with
                | True =>
                  match leaf.trivia.leading with
                    | [] => Void.impossible (Bool.falseNotTrue (rewrite <- aboveSame at noted then noted))
                    | [_, .._] => Bool.andIntro open byComputing
                | False => Bool.andIntro open (Bool.orRight (rewrite endsOnMatched behind done m then reasons))
              Bool.orRight stops

--| The back-walk from a comma or closer holding the owed comment ends on the word that owes it, and leaves the leaves
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

--| The back-walk on leaves that stand against their words gives each leaf its word: the comments `stands` owes on past
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
    matched (homeFrom False behind None rest).reverse (words.reverseOnto done) = True :=
  match rest with
    | [] =>
      match owed with
        | None => rewrite List.eqNilOfIsEmpty words (Bool.andLeft standing), List.reverseReverse behind then state
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
            | None => Bool.orFalseTrue (!done.isEmpty) lead
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
                      let walked: stepsBack False leaf behind after 0 = Succ steps :=
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
                              let walked: stepsBack False leaf behind after 0 = Succ steps :=
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

-- The file.

--| A comment line the file loop prints reads back as it is: its text doesn't end in a carriage return or a space,
--| which the lexer takes off (`crDropped`).
def Note.unreturned (note: Note): Bool := !note.text.endsWith "\r" && !note.text.endsWith " "

--| No own-line comment the file loop prints ends in a carriage return: those above each declaration and at the end.
def SourceFile.unreturned (file: SourceFile): Bool :=
  file.decls.all (decl => decl.firstComments.above.all Note.unreturned) && file.end.above.all Note.unreturned

--| The words the output's tree has, all declarations' in a row.
def SourceFile.words (file: SourceFile): List Word := (file.calmTop.decls.map Decl.words).concat

--| The comments the file loop prints above the first declaration read back as those `topped` leaves on its keyword.
theorem toppedAboveRead ∀ (keyword: Comments)
    (plain: keyword.above.all Note.unreturned = True):
    readNotes (laidNotes True keyword.above) = keyword.topped.above :=
  match above: keyword.above with
    | [] => byComputing
    | [first, ..more] =>
      match first with
        | { text, blankBefore } =>
          rewrite unreturnedSame text (Bool.andLeft plain), notesRead more (Bool.andRight plain)

--| The first declaration's keyword has a blank line before it after `topped` just when the file loop prints one.
theorem toppedBlankRead ∀ (keyword: Comments):
    ((if keyword.blankBefore && !(True && keyword.above.isEmpty) then 1 else 0) > 0) = keyword.topped.blankBefore :=
  match above: keyword.above with
    | [] =>
      match keyword.blankBefore with
        | True => byComputing
        | False => byComputing
    | [first, ..more] =>
      match keyword.blankBefore with
        | True => byComputing
        | False => byComputing

theorem toppedAfter ∀ (keyword: Comments): keyword.topped.after = keyword.after := match above: keyword.above with
  | [] => byComputing
  | [first, ..more] => byComputing

--| Each declaration's leaves in the file stand against its words in the output's tree (`stood`), the `def` holding the
--| comments the file loop prints above it.
theorem standsEachFile ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True)
    (stood: file.stood = True)
    (unreturned: file.unreturned = True):
    standsEach (file.calmTop.decls.map Decl.words) (groupsFrom True file.decls) = True :=
  let starts := leavesStart1 file within shaped settled lexical
  match file with
    | { decls, end } =>
      let withinDecls: decls.all Decl.within1 = True := within
      match decls with
        | [] => byComputing
        | [Definition [] header (Assigned colonEq value), ..rest] =>
          let plain := Bool.andLeft (Bool.andLeft unreturned)
          let keyword := header.keyword
          Bool.andIntro
            (standsDecl header colonEq value True keyword.topped
              (Bool.andLeft stood)
              (Bool.andLeft starts)
              (toppedAboveRead keyword plain)
              (toppedBlankRead keyword)
              (toppedAfter keyword))
            (standsRest rest
              (Bool.andRight withinDecls)
              (Bool.andRight stood)
              (Bool.andRight (Bool.andLeft unreturned))
              (Bool.andRight starts))

--| Every declaration's printed leaves start with no comma (they start with `def`: `printedTokens1`).
theorem leavesStart1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True):
    file.decls.all (decl => notCommaFirst decl.leaves) = True :=
  startsEach file.decls within shaped (Bool.andLeft settled) lexical

theorem startsEach ∀ (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (shaped: decls.all Decl.shaped = True)
    (settled: decls.all Decl.settled = True)
    (lexical: decls.all Decl.lexical = True):
    decls.all (decl => notCommaFirst decl.leaves) = True :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      let first :=
        declStartsKw decl (Bool.andLeft within) (Bool.andLeft shaped) (Bool.andLeft settled) (Bool.andLeft lexical)
      let head: notCommaFirst decl.leaves = True := match leaves: decl.leaves with
        | [leaf, .._] =>
          let isDef: leaf.token.kind = KwDef := DecEq.sound first
          rewrite isDef
      Bool.andIntro head
        (startsEach rest (Bool.andRight within) (Bool.andRight shaped) (Bool.andRight settled) (Bool.andRight lexical))

--| The leaves of declarations after the first stand against their calm words.
theorem standsRest ∀ (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (stood: decls.all Decl.stands = True)
    (plain: decls.all (decl => decl.firstComments.above.all Note.unreturned) = True)
    (starts: decls.all (decl => notCommaFirst decl.leaves) = True):
    standsEach ((decls.map Decl.calm).map Decl.words) (groupsFrom False decls) = True :=
  match decls with
    | [] => byComputing
    | [Definition [] header (Assigned colonEq value), ..rest] =>
      let keyword := header.keyword
      let aboveRead: readNotes (laidNotes False keyword.above) = keyword.above :=
        rewrite laidNotesFalse keyword.above then notesRead keyword.above (Bool.andLeft plain)
      let blankRead: ((if keyword.blankBefore && !(False && keyword.above.isEmpty) then 1 else 0) > 0)
        = keyword.blankBefore :=
        match keyword.blankBefore with
          | True | False => byComputing
      Bool.andIntro
        (standsDecl header colonEq value False keyword
          (Bool.andLeft stood)
          (Bool.andLeft starts)
          aboveRead
          blankRead
          byComputing)
        (standsRest rest (Bool.andRight within) (Bool.andRight stood) (Bool.andRight plain) (Bool.andRight starts))

theorem emptySame ∀ (more others: List Word) (alike: AllAlike more others): more.isEmpty = others.isEmpty :=
  match more, others, alike with
    | [], [], _ => byComputing
    | [m, ..ms], [o, ..os], _ => byComputing

--| The look back, own-line comments and closers a word has don't change under `calm`: homed words stay homed.
theorem homedBackAlike ∀ (before after: List Word) (alike: AllAlike before after): homedBack before = homedBack after :=
  match before, after, alike with
    | [], [], _ => byComputing
    | [first, ..more], [second, ..others], (same, rest) =>
      rewrite alikeTrails first second same,
          alikeCloser first second same,
          alikeNoted first second same,
          trailsBackAlike more others rest,
          homedBackAlike more others rest,
          emptySame more others rest

--| Alike words keep the comment texts `commentText` allows.
theorem textsAlike ∀ (before after: List Word)
    (alike: AllAlike before after)
    (texts: before.all (word => word.comments.texts.all commentText) = True):
    after.all (word => word.comments.texts.all commentText) = True :=
  match before, after, alike with
    | [], [], _ => byComputing
    | [first, ..more], [second, ..others], (same, rest) =>
      Bool.andIntro
        (rewrite <- alikeTexts first second same then Bool.andLeft texts)
        (textsAlike more others rest (Bool.andRight texts))

--| A newest-first list homed in two parts is homed whole, if the older part starts the look back at an open word.
theorem homedBackAppend ∀ (xs ys: List Word)
    (ends: endsOpen xs = True)
    (front: homedBack xs = True)
    (back: homedBack ys = True):
    homedBack (xs ++ ys) = True :=
  match xs with
    | [word] =>
      let open := Bool.notTrue (isCloserText word.text) ends
      Bool.andIntro (rewrite open) back
    | [word, next, ..rest] =>
      let ih := homedBackAppend [next, ..rest] ys ends (Bool.andRight front) back
      let first := Bool.andLeft front
      let kept := trailsBackAppend [next, ..rest] ys ends
      Bool.andIntro (rewrite kept then first) ih

--| The words of declarations, each homed and none starting with a closer, are homed joined, read newest first.
theorem homedConcat ∀ (pieces: List (List Word))
    (open: pieces.all startsOpen = True)
    (homed: pieces.all (piece => homedBack piece.reverse) = True):
    homedBack pieces.concat.reverse = True :=
  match pieces with
    | [] => byComputing
    | [piece, ..more] =>
      let rest := homedConcat more (Bool.andRight open) (Bool.andRight homed)
      let opens := startsOpenConcat more (Bool.andRight open)
      rewrite List.reverseAppend piece more.concat then
        match joined: more.concat with
          | [] => Bool.andLeft homed
          | [word, ..others] =>
            homedBackAppend
              (List.reverse [word, ..others])
              piece.reverse
              (endsOpenReverse word others (Bool.notTrue (isCloserText word.text) opens))
              rest
              (Bool.andLeft homed)

theorem allConcat ∀ (pieces: List (List Word)) (p: Word → Bool)
    (all: pieces.all (piece => piece.all p) = True):
    pieces.concat.all p = True :=
  match pieces with
    | [] => byComputing
    | [piece, ..more] =>
      List.allAppendTrue piece more.concat p (Bool.andLeft all) (allConcat more p (Bool.andRight all))

--| A declaration's words and its calm words, the `def` given other comments alike its own, are alike.
theorem declWordsAlike ∀ (header: Header) (colonEq: Comments) (value: Expr) (keyword: Comments)
    (within: (Definition [] header (Assigned colonEq value)).within1 = True)
    (kept: (fixedWord "def" header.keyword).alike (fixedWord "def" keyword)):
    AllAlike
      (Definition [] header (Assigned colonEq value)).words
      (Definition [] { header.calm | keyword } (Assigned (colonEq.kept False False) (value.calm False))).words :=
  match header with
    | {
        exportKeyword = None,
        opaqueKeyword = None,
        kind = DefPlain,
        keyword = original,
        name,
        forallKeyword = None,
        params = [],
        colon,
        result,
        decreasingClause = None,
        unfoldingClause = None
      } =>
      allAlikeAppend
        [fixedWord "def" original, name, fixedWord ":" colon]
        [fixedWord "def" keyword, name.kept False False, fixedWord ":" (colon.kept False False)]
        (result.words ++ [fixedWord ":=" colonEq] ++ value.words)
        ((result.calm False).words ++ [fixedWord ":=" (colonEq.kept False False)] ++ (value.calm False).words)
        (kept, (keptAlike name False False, (keptAlike (fixedWord ":" colon) False False, byComputing)))
        (allAlikeAppend result.words
          (result.calm False).words
          ([fixedWord ":=" colonEq] ++ value.words)
          ([fixedWord ":=" (colonEq.kept False False)] ++ (value.calm False).words)
          (wordsCalm result False (Bool.andRight (Bool.andLeft within)))
          (keptAlike (fixedWord ":=" colonEq) False False, wordsCalm value False (Bool.andRight within)))

theorem toppedAlike ∀ (keyword: Comments): (fixedWord "def" keyword).alike (fixedWord "def" keyword.topped) :=
  match keyword.above with | [] | [_, .._] => (byComputing, byComputing, byComputing, byComputing)

theorem restSettled ∀ (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (settled: decls.all Decl.settled = True):
    ((decls.map Decl.calm).map Decl.words).all (piece => homedBack piece.reverse) = True
      ∧ ((decls.map Decl.calm).map Decl.words).all (piece => piece.all (word => word.comments.texts.all commentText))
        = True :=
  match decls with
    | [] => (byComputing, byComputing)
    | [Definition [] header (Assigned colonEq value), ..rest] =>
      let alike: AllAlike
        (Definition [] header (Assigned colonEq value)).words
        (Definition [] header (Assigned colonEq value)).calm.words :=
        declWordsAlike header colonEq value header.keyword
          (Bool.andLeft within)
          (alikeRefl (fixedWord "def" header.keyword))
      let own := Bool.andLeft settled
      let (restHomed, restTexts) := restSettled rest (Bool.andRight within) (Bool.andRight settled)
      let same :=
        homedBackAlike _ _
          (allAlikeReverse
            (Definition [] header (Assigned colonEq value)).words
            (Definition [] header (Assigned colonEq value)).calm.words
            alike)
      (
        Bool.andIntro (rewrite <- same then Bool.andLeft own) restHomed,
        Bool.andIntro
          (textsAlike
            (Definition [] header (Assigned colonEq value)).words
            (Definition [] header (Assigned colonEq value)).calm.words
            alike
            (Bool.andRight (Bool.andRight own)))
          restTexts
      )

--| The output tree's words are settled as the tree's are: `calm` and `calmTop` change only blank-line flags.
--|
--| Proof idea: each declaration's words are alike its calm words (`declWordsAlike`, from `wordsCalm`; the first `def`
--| has its flag cleared, `toppedAlike`), and alike words keep what `homedBack` and the comment texts read
--| (`homedBackAlike`, `textsAlike`); no declaration starts with a closer, so the joined words are homed
--| (`homedConcat`).
theorem wordsSettled1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (settled: file.settled = True):
    homedBack (file.words.reverseOnto []) = True
      ∧ file.words.all (word => word.comments.texts.all commentText) = True :=
  match file with
    | { decls, end } =>
      let withinDecls: decls.all Decl.within1 = True := within
      match decls with
        | [] => (byComputing, byComputing)
        | [Definition [] header (Assigned colonEq value), ..rest] =>
          let keyword := header.keyword
          let firstDecl :=
            Definition []
              { header.calm | keyword = keyword.topped }
              (Assigned (colonEq.kept False False) (value.calm False))
          let alike: AllAlike (Definition [] header (Assigned colonEq value)).words firstDecl.words :=
            declWordsAlike header colonEq value keyword.topped (Bool.andLeft withinDecls) (toppedAlike keyword)
          let own := Bool.andLeft (Bool.andLeft settled)
          let (restHomed, restTexts) :=
            restSettled rest (Bool.andRight withinDecls) (Bool.andRight (Bool.andLeft settled))
          let same :=
            homedBackAlike _ _
              (allAlikeReverse (Definition [] header (Assigned colonEq value)).words firstDecl.words alike)
          let pieces :=
            (SourceFile.calmTop { decls = [Definition [] header (Assigned colonEq value), ..rest], end }).decls.map
                Decl.words
          (
            homedConcat pieces (declsWordsOpen _) (Bool.andIntro (rewrite <- same then Bool.andLeft own) restHomed),
            allConcat pieces
              (word => word.comments.texts.all commentText)
              (Bool.andIntro
                (textsAlike
                  (Definition [] header (Assigned colonEq value)).words
                  firstDecl.words
                  alike
                  (Bool.andRight (Bool.andRight own)))
                restTexts)
          )

def arrowText (word: Word): Bool := operatorTok word.text == Some Arrow

--| The words end in a word that isn't `->`: no `->` ends a declaration.
def endsQuiet: List Word → Bool
  | [] => False
  | [word] => !arrowText word
  | [_, ..rest] => endsQuiet rest

def quietOrEmpty (words: List Word): Bool := words.isEmpty || endsQuiet words

theorem endsQuietJoin ∀ (xs ys: List Word) (quiet: endsQuiet ys = True): endsQuiet (xs ++ ys) = True := match xs with
  | [] => quiet
  | [x] =>
    match ys with
      | [y, ..more] => quiet
  | [x, next, ..rest] => endsQuietJoin [next, ..rest] ys quiet

theorem endsQuietAppend ∀ (xs ys: List Word)
    (front: endsQuiet xs = True)
    (back: quietOrEmpty ys = True):
    endsQuiet (xs ++ ys) = True :=
  match ys with
    | [] => rewrite List.appendNil xs then front
    | [y, ..more] => endsQuietJoin xs [y, ..more] back

theorem endsQuietCons ∀ (word: Word) (rest: List Word)
    (quiet: endsQuiet rest = True):
    endsQuiet [word, ..rest] = True :=
  match rest with | [next, ..more] => quiet

theorem markedArrow ∀ (leaf: Leaf) (kind: Tok) (text: Text)
    (sameText: leaf.token.text = text)
    (sameKind: leaf.token.kind = kind)
    (marked: leaf.marked = True)
    (notArrow: (kind == Arrow) = False):
    (operatorTok text == Some Arrow) = False :=
  match leaf with
    | { token = { kind = k, text = t, column, lineStart }, trivia } =>
      let arrows := Bool.andRight marked
      rewrite sameText, sameKind at arrows then
        match isArrow: operatorTok text == Some Arrow with
          | False => byComputing
          | True => Void.impossible (Bool.falseNotTrue (rewrite notArrow at arrows then arrows))

--| A name or numeral lexed as one token isn't `->`.
theorem atomNotArrow ∀ (kind: Tok) (text: Text)
    (word: kind.wordWithin1 = True)
    (lexes: textLexesAs text kind = True):
    (operatorTok text == Some Arrow) = False :=
  match ran: lex text with
    | Ok lexed =>
      match leaves: lexed.leaves with
        | [leaf] =>
          let sameText: leaf.token.text = text := DecEq.sound (Bool.andLeft lexes)
          let sameKind: leaf.token.kind = kind := DecEq.sound (Bool.andRight lexes)
          let within: alphabet1 lexed.leaves = True :=
            rewrite leaves then Bool.andIntro (rewrite sameKind then wordWithinWithin kind word) byComputing
          let laid := lexLaid1 text lexed ran within
          let all: lexed.leaves.all Leaf.marked = True := Bool.andLeft (Bool.andRight laid)
          markedArrow leaf kind text sameText sameKind
            (Bool.andLeft (rewrite leaves at all then all))
            (wordIsNoArrow kind word)

theorem closeQuiet ∀ [close: Word] (text: Text)
    (same: close.text = text)
    (plain: (operatorTok text == Some Arrow) = False):
    endsQuiet [close] = True :=
  rewrite same, plain

theorem exprEndsQuiet ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical = True):
    endsQuiet expr.words = True :=
  match expr with
    | Atom kind word =>
      let notArrow := atomNotArrow kind word.text (Bool.andLeft within) lexical
      rewrite notArrow
    | Paren open inner close =>
      endsQuietJoin
        [open, ..inner.words]
        [close]
        (closeQuiet ")" (DecEq.sound (Bool.andLeft (Bool.andRight lexical))) byComputing)
    | Tuple open items _ close =>
      endsQuietJoin
        [open, ..itemsWords items]
        [close]
        (closeQuiet ")" (DecEq.sound (Bool.andLeft (Bool.andRight lexical))) byComputing)
    | ListOf open items _ close =>
      endsQuietJoin
        [open, ..itemsWords items]
        [close]
        (closeQuiet "]" (DecEq.sound (Bool.andLeft (Bool.andRight lexical))) byComputing)
    | App head arguments =>
      endsQuietAppend head.words
        (itemsWords arguments)
        (exprEndsQuiet head (Bool.andLeft within) (Bool.andLeft lexical))
        (itemsQuiet arguments (Bool.andRight within) (Bool.andRight lexical))
    | Infix kind left operator right =>
      match kind with
        | InfixBinary | InfixArrow =>
          endsQuietJoin left.words
            [operator, ..right.words]
            (endsQuietCons operator right.words
              (exprEndsQuiet right (Bool.andLeft (Bool.andRight within)) (Bool.andRight (Bool.andRight lexical))))
        | _ => cases
    | Prefix operator operand =>
      endsQuietCons operator operand.words (exprEndsQuiet operand (Bool.andLeft within) (Bool.andRight lexical))

theorem itemsQuiet ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (lexical: allLexical items = True):
    quietOrEmpty (itemsWords items) = True :=
  match items with
    | [] => byComputing
    | [item, ..rest] =>
      Bool.orRight
        (endsQuietAppend item.words
          (itemsWords rest)
          (exprEndsQuiet item (Bool.andLeft within) (Bool.andLeft lexical))
          (itemsQuiet rest (Bool.andRight within) (Bool.andRight lexical)))

--| Alike words end alike.
theorem endsQuietAlike ∀ (before after: List Word) (alike: AllAlike before after): endsQuiet before = endsQuiet after :=
  match before, after, alike with
    | [], [], _ => byComputing
    | [word], [other], (same, _) => rewrite (Eq.cong (text => operatorTok text == Some Arrow) same.left)
    | [word], [other, further, ..more], _ => cases
    | [word, next, ..rest], [other], _ => cases
    | [word, next, ..rest], [other, further, ..more], (same, tail) =>
      endsQuietAlike [next, ..rest] [further, ..more] tail

theorem arrowsBareAlike ∀ (before after: List Word)
    (alike: AllAlike before after):
    arrowsBare before = arrowsBare after :=
  match before, after, alike with
    | [], [], _ => byComputing
    | [word], [other], _ => byComputing
    | [word], [other, further, ..more], _ => cases
    | [word, next, ..rest], [other], _ => cases
    | [word, next, ..rest], [other, further, ..more], (same, tail) =>
      let (nextSame, _) := tail
      rewrite same.left,
          alikeTrails word other same,
          alikeNoted next further nextSame,
          arrowsBareAlike [next, ..rest] [further, ..more] tail

def headQuiet: List Word → Bool
  | [] => True
  | [word, ..rest] => !arrowText word

theorem arrowQuietPair ∀ (word next: Word)
    (quiet: (!arrowText word) = True):
    (operatorTok word.text != Some Arrow || (!word.trails && !next.noted)) = True :=
  let plain: arrowText word = False := Bool.notTrue _ quiet
  Bool.orLeft quiet

--| `->` stays bare across a seam, if the first part doesn't end in one.
theorem arrowsJoin ∀ (xs ys: List Word)
    (front: arrowsBare xs = True)
    (back: arrowsBare ys = True)
    (quiet: quietOrEmpty xs = True):
    arrowsBare (xs ++ ys) = True :=
  match xs with
    | [] => back
    | [x] =>
      match ys with
        | [] => byComputing
        | [y, ..more] => Bool.andIntro (arrowQuietPair x y quiet) back
    | [x, next, ..rest] =>
      Bool.andIntro (Bool.andLeft front) (arrowsJoin [next, ..rest] ys (Bool.andRight front) back quiet)

theorem headQuietSnoc ∀ (zs: List Word) (word: Word)
    (filled: zs.isEmpty = False):
    headQuiet (zs ++ [word]) = headQuiet zs :=
  match zs with | [z, ..more] => byComputing

theorem wordsFilled ∀ (xs acc: List Word) (filled: acc.isEmpty = False): (xs.reverseOnto acc).isEmpty = False :=
  match xs with
    | [] => filled
    | [x, ..rest] => wordsFilled rest [x, ..acc] byComputing

theorem headQuietReverse ∀ (words: List Word) (quiet: endsQuiet words = True): headQuiet words.reverse = True :=
  match words with
    | [word] => quiet
    | [word, next, ..rest] =>
      let filled: (List.reverse [next, ..rest]).isEmpty = False := wordsFilled rest [next] byComputing
      rewrite List.reverseCons word [next, ..rest], headQuietSnoc (List.reverse [next, ..rest]) word filled then
        headQuietReverse [next, ..rest] quiet

theorem arrowsConcat ∀ (pieces: List (List Word))
    (bare: pieces.all arrowsBare = True)
    (quiet: pieces.all endsQuiet = True):
    arrowsBare pieces.concat = True :=
  match pieces with
    | [] => byComputing
    | [piece, ..more] =>
      arrowsJoin piece more.concat
        (Bool.andLeft bare)
        (arrowsConcat more (Bool.andRight bare) (Bool.andRight quiet))
        (Bool.orRight (Bool.andLeft quiet))

theorem quietConcat ∀ (pieces: List (List Word))
    (quiet: pieces.all endsQuiet = True):
    quietOrEmpty pieces.concat = True :=
  match pieces with
    | [] => byComputing
    | [piece, ..more] =>
      Bool.orRight (endsQuietAppend piece more.concat (Bool.andLeft quiet) (quietConcat more (Bool.andRight quiet)))

theorem declEndsQuiet ∀ (header: Header) (colonEq: Comments) (value: Expr)
    (within: value.within1 = True)
    (lexical: value.lexical = True):
    endsQuiet (Definition [] header (Assigned colonEq value)).words = True :=
  endsQuietJoin
    [fixedWord "def" header.keyword, header.name, fixedWord ":" header.colon]
    (header.result.words ++ [fixedWord ":=" colonEq, ..value.words])
    (endsQuietJoin header.result.words
      [fixedWord ":=" colonEq, ..value.words]
      (endsQuietCons (fixedWord ":=" colonEq) value.words (exprEndsQuiet value within lexical)))

--| A printed leaf has a closer's kind exactly when it has a closer's text.
theorem printedAgrees1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True):
    file.lexed.leaves.all Leaf.agrees = True :=
  let laid :=
    lexLaid1 file.printed1 file.lexed
      (printedFileLexes1 file within shaped settled lexical)
      (printedAlphabet1 file within shaped settled lexical)
  agreesOfMarked file.lexed.leaves (Bool.andLeft (Bool.andRight laid))

--| A leaf whose text says whether it is a closer, as its kind does, has the kind a closer's text has.
theorem agreesOfMarked ∀ (leaves: List Leaf) (marked: leaves.all Leaf.marked = True): leaves.all Leaf.agrees = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      let same: isCloserText leaf.token.text = leaf.kind.isCloser := DecEq.sound (Bool.andLeft (Bool.andLeft marked))
      Bool.andIntro (rewrite same then DecEq.refl leaf.kind.isCloser) (agreesOfMarked rest (Bool.andRight marked))

--| Each declaration's words, calmed, keep `->` bare and end in no `->`, since the tree's do.
theorem restArrows ∀ (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (lexical: decls.all Decl.lexical = True)
    (settled: decls.all Decl.settled = True):
    ((decls.map Decl.calm).map Decl.words).all arrowsBare = True
      ∧ ((decls.map Decl.calm).map Decl.words).all endsQuiet = True :=
  match decls with
    | [] => (byComputing, byComputing)
    | [Definition [] header (Assigned colonEq value), ..rest] =>
      let alike: AllAlike
        (Definition [] header (Assigned colonEq value)).words
        (Definition [] header (Assigned colonEq value)).calm.words :=
        declWordsAlike header colonEq value header.keyword
          (Bool.andLeft within)
          (alikeRefl (fixedWord "def" header.keyword))
      let own := Bool.andLeft settled
      let (restBare, restQuiet) :=
        restArrows rest (Bool.andRight within) (Bool.andRight lexical) (Bool.andRight settled)
      let ends :=
        declEndsQuiet header colonEq value
          (Bool.andRight (Bool.andLeft within))
          (Bool.andRight (Bool.andRight (Bool.andLeft lexical)))
      (
        Bool.andIntro
          (rewrite <- arrowsBareAlike
                (Definition [] header (Assigned colonEq value)).words
                (Definition [] header (Assigned colonEq value)).calm.words
                alike then
            Bool.andLeft (Bool.andRight own))
          restBare,
        Bool.andIntro
          (rewrite <- endsQuietAlike
                (Definition [] header (Assigned colonEq value)).words
                (Definition [] header (Assigned colonEq value)).calm.words
                alike then
            ends)
          restQuiet
      )

theorem wordsArrows ∀ (file: SourceFile)
    (within: file.within1 = True)
    (lexical: file.lexical = True)
    (settled: file.settled = True):
    arrowsBare file.words = True ∧ headQuiet file.words.reverse = True :=
  match file with
    | { decls, end } =>
      let withinDecls: decls.all Decl.within1 = True := within
      let lexicalDecls: decls.all Decl.lexical = True := lexical
      match decls with
        | [] => (byComputing, byComputing)
        | [Definition [] header (Assigned colonEq value), ..rest] =>
          let keyword := header.keyword
          let firstDecl :=
            Definition []
              { header.calm | keyword = keyword.topped }
              (Assigned (colonEq.kept False False) (value.calm False))
          let alike: AllAlike (Definition [] header (Assigned colonEq value)).words firstDecl.words :=
            declWordsAlike header colonEq value keyword.topped (Bool.andLeft withinDecls) (toppedAlike keyword)
          let own := Bool.andLeft (Bool.andLeft settled)
          let (restBare, restQuiet) :=
            restArrows rest
              (Bool.andRight withinDecls)
              (Bool.andRight lexicalDecls)
              (Bool.andRight (Bool.andLeft settled))
          let ends :=
            declEndsQuiet header colonEq value
              (Bool.andRight (Bool.andLeft withinDecls))
              (Bool.andRight (Bool.andRight (Bool.andLeft lexicalDecls)))
          let pieces :=
            (SourceFile.calmTop { decls = [Definition [] header (Assigned colonEq value), ..rest], end }).decls.map
                Decl.words
          let bareFirst: arrowsBare firstDecl.words = True :=
            rewrite <- arrowsBareAlike (Definition [] header (Assigned colonEq value)).words firstDecl.words alike then
              Bool.andLeft (Bool.andRight own)
          let bare := Bool.andIntro bareFirst restBare
          let quietFirst: endsQuiet firstDecl.words = True :=
            rewrite <- endsQuietAlike (Definition [] header (Assigned colonEq value)).words firstDecl.words alike then
              ends
          let quiet := Bool.andIntro quietFirst restQuiet
          (
            arrowsConcat pieces bare quiet,
            headQuietReverse pieces.concat
              (endsQuietAppend firstDecl.words
                ((rest.map Decl.calm).map Decl.words).concat
                (Bool.andLeft quiet)
                (quietConcat ((rest.map Decl.calm).map Decl.words) restQuiet))
          )

--| The newest leaf placed so far that follows what's been placed: bare or leading comments agree with the word.
def leadMatch (acc: List Leaf) (after: List Word): Bool := match acc with
  | [] => True
  | [next, .._] =>
    if next.kind == Comma then next.trivia.leading.isEmpty
    else
      match after with
        | [] => False
        | [word, .._] => next.trivia.leading.isEmpty == !word.noted

def tailQuiet (done after: List Word): Bool := match after with
  | [] => headQuiet done
  | _ => True

--| What `arrowsBare` reads of a leaf and the one after it.
def arrowPair (leaf: Leaf) (acc: List Leaf): Bool := match acc with
  | [] => True
  | [next, .._] =>
    !(leaf.kind == Arrow) || (leaf.trivia.trailing.isNone && (next.trivia.leading.isEmpty || next.kind == Arrow))

theorem pairPush ∀ (leaf: Leaf) (acc: List Leaf)
    (pair: arrowPair leaf acc = True)
    (bare: Syntax.SettleProofs.arrowsBare acc = True):
    Syntax.SettleProofs.arrowsBare [leaf, ..acc] = True :=
  match acc with
    | [] => byComputing
    | [next, ..more] => Bool.andIntro pair bare

theorem leadingEmptySame ∀ (leaf: Leaf) (word: Word)
    (fits: leaf.fits word = True):
    leaf.trivia.leading.isEmpty = word.comments.above.isEmpty :=
  let (_, aboveSame, _, _, _) := fitsParts word fits
  match leaf.trivia.leading with | [] | [_, .._] => rewrite <- aboveSame

theorem listReverseJoin ∀ (word: Word) (older after: List Word):
    [word, ..older].reverse ++ after = older.reverse ++ [word, ..after] :=
  rewrite List.reverseCons word older, List.appendAssoc older.reverse [word] after

--| The back-walk's result, built from the newest leaves back, keeps `->` bare: each leaf placed passes what it owes
--| `arrowsBare` from its word's, whose neighbour is the word placed before.
theorem arrowsOnto ∀ (behind acc: List Leaf) (done after: List Word)
    (m: matched behind done = True)
    (marked: behind.all Leaf.marked = True)
    (words: arrowsBare (done.reverse ++ after) = True)
    (quiet: tailQuiet done after = True)
    (lead: leadMatch acc after = True)
    (bare: Syntax.SettleProofs.arrowsBare acc = True):
    Syntax.SettleProofs.arrowsBare (behind.reverseOnto acc) = True :=
  match behind with
    | [] => bare
    | [leaf, ..earlier] =>
      match comma: leaf.kind == Comma with
        | True =>
          let kept := Bool.andLeft (Bool.andRight m)
          let pair: arrowPair leaf acc = True := match acc with
            | [] => byComputing
            | [next, ..more] => Bool.orLeft (rewrite DecEq.sound comma)
          let leading: leaf.trivia.leading.isEmpty = True := Bool.andRight kept
          arrowsOnto earlier
            [leaf, ..acc]
            done
            after
            (Bool.andRight (Bool.andRight m))
            (Bool.andRight marked)
            words
            quiet
            (rewrite comma then leading)
            (pairPush leaf acc pair bare)
        | False =>
          match done with
            | [word, ..older] =>
              let fits := Bool.andLeft m
              let (textSame, _, _, trailSame, _) := fitsParts word fits
              let emptySame := leadingEmptySame leaf word fits
              let joined: arrowsBare (older.reverse ++ [word, ..after]) = True :=
                rewrite listReverseJoin word older after at words then words
              let newLead: leadMatch [leaf, ..acc] [word, ..after] = True :=
                rewrite comma, emptySame then
                  match word.comments.above.isEmpty with
                    | True | False => byComputing
              let pair: arrowPair leaf acc = True := match isArrow: leaf.kind == Arrow with
                | False =>
                  match acc with
                    | [] => byComputing
                    | [following, .._] => Bool.orLeft byComputing
                | True =>
                  let arrowPart := Bool.andRight (Bool.andLeft marked)
                  let opArrow: (operatorTok leaf.token.text == Some Arrow) = True := DecEq.sound arrowPart
                  let arrowW: arrowText word = True := rewrite textSame at opArrow then opArrow
                  match after with
                    | [] => Void.impossible (Bool.falseNotTrue (rewrite arrowW at quiet then quiet))
                    | [next, ..more] =>
                      let suffix := arrowsBareSuffix older.reverse [word, next, ..more] joined
                      let first := Bool.andLeft suffix
                      let na: ((operatorTok word.text != Some Arrow): Bool) = False :=
                        Bool.notOfTrue (arrowText word) arrowW
                      let rest: (!word.trails && !next.noted) = True := Bool.orOfLeftFalse _ _ first na
                      let trailsNot: (!word.trails) = True := Bool.andLeft rest
                      let nextNot: (!next.noted) = True := Bool.andRight rest
                      let untrailed: leaf.trivia.trailing.isNone = True := match tr: leaf.trivia.trailing with
                        | None => byComputing
                        | Some comment =>
                          let held: word.comments.after = Some comment.text := trailSame.flipped
                          Void.impossible (Bool.falseNotTrue (rewrite held at trailsNot then trailsNot))
                      match acc with
                        | [] => byComputing
                        | [following, ..others] =>
                          let leading: following.trivia.leading.isEmpty = True :=
                            match gap: following.kind == Comma with
                              | True => lead
                              | False => rewrite DecEq.sound lead then nextNot
                          Bool.orRight (Bool.andIntro untrailed (Bool.orLeft leading))
              arrowsOnto earlier
                [leaf, ..acc]
                older
                [word, ..after]
                (Bool.andRight m)
                (Bool.andRight marked)
                joined
                byComputing
                newLead
                (pairPush leaf acc pair bare)

--| After the back-walk no `->` holds a comment and none comes before an own-line comment.
--|
--| Proof idea: the back-walk's result is the leaves matched to the words (`m`), so `arrowsBare` of the leaves follows from
--| `arrowsBare` of the words (`arrowsOnto`): an `->` leaf is an `->` word (the lexer marks its kind by its text), whose
--| neighbour is the next word, or a bare comma. The words keep `->` bare (the tree's are `settled`, `calm` keeps what
--| it reads) and no declaration ends in `->` (`exprEndsQuiet`), so `->` is bare across declarations too.
theorem homedArrowsBare ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True)
    (hung: file.hung = True)
    (m: matched (homeFrom False [] None file.lexed.leaves).reverse (file.words.reverseOnto []) = True):
    Syntax.SettleProofs.arrowsBare (homeFrom False [] None file.lexed.leaves) = True :=
  let leaves := file.lexed.leaves
  let homed := homeFrom False [] None leaves
  let laid :=
    lexLaid1 file.printed1 file.lexed
      (printedFileLexes1 file within shaped settled lexical)
      (printedAlphabet1 file within shaped settled lexical)
  let marked: leaves.all isMarked = True := Bool.andLeft (Bool.andRight laid)
  let tokensSame: tokens homed = tokens leaves := Eq.trans (homeFromTokens False [] None leaves) byComputing
  let markedHomed: homed.all isMarked = True :=
    Eq.trans (markedTokens homed) (rewrite tokensSame then Eq.trans (Eq.flipped (markedTokens leaves)) marked)
  let (bare, quiet) := wordsArrows file within lexical settled
  let reversed: arrowsBare ((file.words.reverseOnto []).reverse ++ []) = True :=
    rewrite List.appendNil (file.words.reverseOnto []).reverse, List.reverseReverse file.words then bare
  let done :=
    arrowsOnto homed.reverse []
      (file.words.reverseOnto [])
      []
      m
      (List.allReverseOntoTrue isMarked homed [] markedHomed byComputing)
      reversed
      quiet
      byComputing
      byComputing
  rewrite <- List.reverseReverse homed then done
--| The parser's groups of the back-walk's result are the declarations, each with its words.
theorem groupsBack ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True)
    (hung: file.hung = True)
    (stood: file.stood = True)
    (unreturned: file.unreturned = True)
    (m: matched (homeFrom False [] None file.lexed.leaves).reverse (file.words.reverseOnto []) = True):
    (groupsOf (homeFrom False [] None file.lexed.leaves)).map codeWords = file.calmTop.decls.map Decl.words :=
  let leaves := file.lexed.leaves
  let homed := homeFrom False [] None leaves
  let tokensSame: tokens homed = tokens leaves := Eq.trans (homeFromTokens False [] None leaves) byComputing
  let groupsSame: groupTokens (groupsOf homed) = groupTokens (groupsFrom True file.decls) :=
    Eq.trans
      (splitTokens Splitter.start [] [] [] [] homed leaves tokensSame byComputing byComputing)
      (Eq.cong groupTokens (printedGroups1 file within shaped settled lexical hung))
  let lengths: (groupsOf homed).map codeLength = (file.calmTop.decls.map Decl.words).map (all => all.length) :=
    Eq.trans
      (codeLengthsTokens _ _ groupsSame)
      (standsLengths _ _ (standsEachFile file within shaped settled lexical stood unreturned))
  let wordsOf: codeWords homed = file.words := calc codeWords homed
    _ = codeWords (homed.reverse.reverseOnto []) := rewrite List.reverseReverse homed
    _ = (file.words.reverseOnto []).reverseOnto [] := matchedWords homed.reverse [] (file.words.reverseOnto []) m
    _ = file.words := List.reverseReverse file.words
  piecesWords (groupsOf homed) (file.calmTop.decls.map Decl.words) (rewrite groupsConcat homed then wordsOf) lengths

--| The end's comments read back as the tree's.
theorem endBack ∀ (file: SourceFile)
    (within: file.within1 = True)
    (settled: file.settled = True)
    (unreturned: file.unreturned = True):
    file.lexed.end.trimmed.comments = file.calmTop.end :=
  match file with
    | { decls, end = { above, after, blankBefore } } =>
      let texts := notesTexts above after.toList (Bool.andLeft (Bool.andRight settled))
      let plain := Bool.andRight unreturned
      match after with
        | None =>
          match decls with
            | [] =>
              match above with
                | [] => byComputing
                | [first, ..rest] =>
                  let firstSame := noteBack first (Bool.andLeft plain) (Bool.andLeft texts)
                  let restSame := notesBack rest (Bool.andRight plain) (Bool.andRight texts)
                  match first with
                    | { text, blankBefore = firstBlank } =>
                      let textSame: trimEnd (withoutReturn text) = text := Eq.cong (note => note.text) firstSame
                      rewrite textSame, restSame
            | [first, ..rest] =>
              match first with
                | Namespace _ _ => rewrite laidNotesFalse above, notesBack above plain texts
                | Import _ _ _ _ _ => rewrite laidNotesFalse above, notesBack above plain texts
                | Definition attributes header (Assigned colonEq value) =>
                  rewrite laidNotesFalse above, notesBack above plain texts
                | Definition attributes header Primitive => rewrite laidNotesFalse above, notesBack above plain texts
                | Definition attributes header (Arms arms) => rewrite laidNotesFalse above, notesBack above plain texts
                | Data _ _ _ _ _ _ _ => rewrite laidNotesFalse above, notesBack above plain texts
                | Ability _ _ _ _ _ => rewrite laidNotesFalse above, notesBack above plain texts
                | Test _ _ _ _ => rewrite laidNotesFalse above, notesBack above plain texts
                | RuleSetDecl _ _ _ _ => rewrite laidNotesFalse above, notesBack above plain texts
        | Some other => Void.impossible (Bool.falseNotTrue (Bool.andRight (Bool.andRight settled)))

--| A note the file loop prints reads back as it is.
theorem noteBack ∀ (note: Note)
    (plain: note.unreturned = True)
    (text: commentText note.text = True):
    { text = (noteComment note).trimmed.text, blankBefore = (noteComment note).trimmed.blankLines > 0 } = note :=
  match note with
    | { text = written, blankBefore } =>
      let unspaced: written.endsWith " " = False := Bool.notTrue _ (Bool.andRight (Bool.andRight text))
      let kept: trimReturns written.toList = written.toList :=
        trimReturnsSame written.toList (Bool.notTrue _ (Bool.andLeft plain)) (Bool.notTrue _ (Bool.andRight plain))
      let unspacedKept: Text.startsWithChars [' '] (written.toList.reverseOnto []) = False := unspaced
      rewrite kept, unspacedKept then cases written, blankBefore then byComputing

theorem notesBack ∀ (notes: List Note)
    (plain: notes.all Note.unreturned = True)
    (texts: notes.all (note => commentText note.text) = True):
    ((notes.map noteComment).map Comment.trimmed).map (comment =>
      { text = comment.text, blankBefore = comment.blankLines > 0 })
      = notes :=
  match notes with
    | [] => byComputing
    | [note, ..rest] =>
      rewrite noteBack note (Bool.andLeft plain) (Bool.andLeft texts),
          notesBack rest (Bool.andRight plain) (Bool.andRight texts)

--| The comment texts of notes and what follows them.
theorem notesTexts ∀ (notes: List Note) (rest: List Text)
    (texts: (notes.map (note => note.text) ++ rest).all commentText = True):
    notes.all (note => commentText note.text) = True :=
  match notes with
    | [] => byComputing
    | [note, ..more] => Bool.andIntro (Bool.andLeft texts) (notesTexts more rest (Bool.andRight texts))

--| Characters that end in neither a carriage return nor a space keep all of them when the lexer takes those off the
--| end.
theorem trimReturnsSame ∀ (chars: List Char)
    (plain: Text.startsWithChars ['\r'] chars.reverse = False)
    (unspaced: Text.startsWithChars [' '] chars.reverse = False):
    trimReturns chars = chars :=
  match chars with
    | [] => byComputing
    | [char, ..rest] =>
      match rest with
        | [] =>
          match cut: char == '\r' with
            | True =>
              let same := DecEq.sound cut
              Void.impossible (Bool.trueNotFalse (rewrite same at plain then plain))
            | False =>
              match cutSpace: char == ' ' with
                | True =>
                  let same := DecEq.sound cutSpace
                  Void.impossible (Bool.trueNotFalse (rewrite same at unspaced then unspaced))
                | False => byComputing
        | [next, ..more] =>
          let filled: (List.reverse [next, ..more]).isEmpty = False := List.reverseOntoNonEmpty more [next] byComputing
          let tail: Text.startsWithChars ['\r'] (List.reverse [next, ..more]) = False :=
            rewrite <- Text.startsWithCharsHead '\r' (List.reverse [next, ..more]) [char] filled then
              rewrite List.reverseCons char [next, ..more] at plain then plain
          let tailSpace: Text.startsWithChars [' '] (List.reverse [next, ..more]) = False :=
            rewrite <- Text.startsWithCharsHead ' ' (List.reverse [next, ..more]) [char] filled then
              rewrite List.reverseCons char [next, ..more] at unspaced then unspaced
          let same := trimReturnsSame [next, ..more] tail tailSpace
          match cut: char == '\r' with
            | True => rewrite same
            | False =>
              match cutSpace: char == ' ' with
                | True | False => rewrite same

--| A text that doesn't end in a carriage return or a space keeps it all when the lexer takes those off.
theorem unreturnedSame ∀ (text: Text)
    (plain: (!text.endsWith "\r" && !text.endsWith " ") = True):
    withoutReturn text = text :=
  match text with
    | MkText chars =>
      rewrite trimReturnsSame chars (Bool.notTrue _ (Bool.andLeft plain)) (Bool.notTrue _ (Bool.andRight plain))

--| Trimming leaves whose comments are words' comment texts changes nothing.
--| A comment whose text trim leaves alone.
def Comment.clean (comment: Comment): Bool := commentText comment.text

--| Every comment on the leaf is `clean`.
def Leaf.clean (leaf: Leaf): Bool :=
  leaf.trivia.leading.all Comment.clean
    && (match leaf.trivia.trailing with
      | None => True
      | Some comment => comment.clean)

theorem commentClean ∀ (comment: Comment) (clean: comment.clean = True): comment.trimmed = comment := match comment with
  | { text, column, blankLines } =>
    let unspaced: text.endsWith " " = False := Bool.notTrue _ (Bool.andRight (Bool.andRight clean))
    rewrite unspaced

theorem commentsClean ∀ (comments: List Comment)
    (clean: comments.all Comment.clean = True):
    comments.map Comment.trimmed = comments :=
  match comments with
    | [] => byComputing
    | [comment, ..rest] => rewrite commentClean comment (Bool.andLeft clean), commentsClean rest (Bool.andRight clean)

theorem leafClean ∀ (leaf: Leaf) (clean: leaf.clean = True): { leaf | trivia = leaf.trivia.trimmed } = leaf :=
  match leaf with
    | { token, trivia = { leading, blankLines, trailing } } =>
      let leadingSame := commentsClean leading (Bool.andLeft clean)
      match trailing with
        | None => rewrite leadingSame
        | Some comment => rewrite leadingSame, commentClean comment (Bool.andRight clean)

theorem trimIdle ∀ (leaves: List Leaf)
    (clean: leaves.all Leaf.clean = True):
    leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed }) = leaves :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] => rewrite leafClean leaf (Bool.andLeft clean), trimIdle rest (Bool.andRight clean)

--| A leaf's own-line comments' texts, read as its word's, are clean when the word's are.
theorem leadingClean ∀ (comments: List Comment) (rest: List Text)
    (texts: (comments.map (comment => { text = comment.text, blankBefore = comment.blankLines > 0 })
      |> .map (note => note.text)
      |> (notes => notes ++ rest)
      |> .all commentText)
      = True):
    comments.all Comment.clean = True ∧ rest.all commentText = True :=
  match comments with
    | [] => (byComputing, texts)
    | [comment, ..more] =>
      let (moreClean, restClean) := leadingClean more rest (Bool.andRight texts)
      (Bool.andIntro (Bool.andLeft texts) moreClean, restClean)

theorem leafCleanOfTexts ∀ (leaf: Leaf) (texts: leaf.word.comments.texts.all commentText = True): leaf.clean = True :=
  let (leading, trailing) :=
    leadingClean leaf.trivia.leading (leaf.trivia.trailing.map (comment => comment.text)).toList texts
  match leaf.trivia.trailing with
    | None => Bool.andIntro leading byComputing
    | Some comment => Bool.andIntro leading (Bool.andLeft trailing)

--| Matched leaves are clean when their words' comments are.
theorem matchedClean ∀ (behind: List Leaf) (done: List Word)
    (m: matched behind done = True)
    (texts: done.all (word => word.comments.texts.all commentText) = True):
    behind.all Leaf.clean = True :=
  match behind with
    | [] => byComputing
    | [leaf, ..earlier] =>
      match comma: leaf.kind == Comma with
        | True =>
          let bare := Bool.andLeft (Bool.andRight m)
          match leaf.trivia.trailing, leaf.trivia.leading with
            | None, [] => Bool.andIntro byComputing (matchedClean earlier done (Bool.andRight m) texts)
        | False =>
          match done with
            | [word, ..older] =>
              let wordTexts: leaf.word.comments.texts.all commentText = True :=
                rewrite fitsWord leaf word (Bool.andLeft m) then Bool.andLeft texts
              Bool.andIntro
                (leafCleanOfTexts leaf wordTexts)
                (matchedClean earlier older (Bool.andRight m) (Bool.andRight texts))

theorem leadOf ∀ (leaves: List Leaf) (plain: plain1 (tokens leaves) = True): notCommaFirst leaves = True :=
  match leaves with
    | [] => byComputing
    | [leaf, .._] =>
      match comma: leaf.kind == Comma with
        | False => byComputing

--| `printedSettle1` (`Fmt.OutputStatements`), with `stood` (`printedStands1`'s conclusion, ticket F) and
--| `unreturned` as hypotheses. `unreturned` is needed: an own-line comment ending in a carriage return, which
--| `settled` allows, is printed with it and read back without it (`returnLost`).
--|
--| Proof idea: the leaves stand against the output tree's words (`standsFile`), so the back-walk gives each leaf its word
--| and leaves the commas bare (`homeStands`); the comma carry, arrow lift and let lift then find nothing to move (`commasIdle`, `arrowsIdleAll`,
--| `letsQuiet1`), the comments are trimmed already (`trimIdle`), and the parser's groups are the declarations
--| (`groupsBack`).
theorem printedSettle1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True)
    (hung: file.hung = True)
    (stood: file.stood = True)
    (unreturned: file.unreturned = True):
    (groupsOf file.lexed.settled.leaves).map codeWords = file.calmTop.decls.map Decl.words
      ∧ file.lexed.settled.end.comments = file.calmTop.end :=
  let leaves := file.lexed.leaves
  let homed := homeFrom False [] None leaves
  let (homedWords, texts) := wordsSettled1 file within settled
  let plain := printedPlain1 file within shaped settled lexical hung
  let leavesWithin := alphabet1Leaves leaves (printedAlphabet1 file within shaped settled lexical)
  let m: matched homed.reverse (file.words.reverseOnto []) = True :=
    homeStands None [] leaves [] file.words
      (standsFile file within shaped settled lexical stood unreturned)
      byComputing
      (Bool.orRight (leadOf leaves plain))
      homedWords
      byComputing
      leavesWithin
      (printedAgrees1 file within shaped settled lexical)
  let bare: homed.all bareComma = True :=
    rewrite <- List.reverseReverse homed then
      List.allReverseOntoTrue bareComma homed.reverse [] (matchedBare _ _ m) byComputing
  let tokensSame: tokens homed = tokens leaves := Eq.trans (homeFromTokens False [] None leaves) byComputing
  let plainHomed: plainFrom (tokens homed) = True := rewrite tokensSame then plainFromOf (tokens leaves) plain
  let homedWithin := withinOfTokens homed leaves tokensSame leavesWithin
  let commasSame: commasFrom [] None homed file.lexed.end = { leaves = homed, end = file.lexed.end } :=
    commasIdle [] homed file.lexed.end bare
  let arrowsSame: arrows homed = homed :=
    arrowsIdleAll homed (homedArrowsBare file within shaped settled lexical hung m) plainHomed
  let letsSame: letsFrom [] homed = homed := letsQuiet1 [] homed byComputing homedWithin
  let trimSame: homed.map (leaf => { leaf | trivia = leaf.trivia.trimmed }) = homed :=
    let wordsTexts :=
      List.allReverseOntoTrue (word => word.comments.texts.all commentText) file.words [] texts byComputing
    let clean: homed.all Leaf.clean = True :=
      rewrite <- List.reverseReverse homed then
        List.allReverseOntoTrue Leaf.clean homed.reverse [] (matchedClean _ _ m wordsTexts) byComputing
    trimIdle homed clean
  let leavesSame: file.lexed.settled.leaves = homed := rewrite commasSame, arrowsSame, letsSame, trimSame
  let endSame: file.lexed.settled.end = file.lexed.end.trimmed := rewrite commasSame
  (
    rewrite leavesSame then groupsBack file within shaped settled lexical hung stood unreturned m,
    rewrite endSame then endBack file within settled unreturned
  )

-- Standing, joined.

--| `stands` joins: leaves standing against words, with nothing owed at their end, followed by more that stand.
theorem standsAppend ∀ (owed: Option Text) (words more: List Word) (leaves rest: List Leaf)
    (first: stands owed words leaves = True)
    (second: stands None more rest = True):
    stands owed (words ++ more) (leaves ++ rest) = True :=
  match leaves with
    | [] =>
      match owed with
        | None => rewrite List.eqNilOfIsEmpty words (Bool.andLeft first) then second
        | Some text => Void.impossible (Bool.falseNotTrue (Bool.andRight first))
    | [leaf, ..after] =>
      match comma: leaf.kind == Comma with
        | True =>
          match tuck: tucked owed leaf with
            | None => Void.impossible (Bool.falseNotTrue (Bool.andRight (Bool.andRight first)))
            | Some still =>
              Bool.andIntro
                (Bool.andLeft first)
                (Bool.andIntro
                  (Bool.andLeft (Bool.andRight first))
                  (standsAppend still words more after rest (Bool.andRight (Bool.andRight first)) second))
        | False =>
          match words with
            | [word, ..later] =>
              let headed := Bool.andLeft first
              let clause := Bool.andRight first
              match owed, afterIs: word.comments.after with
                | Some text, None =>
                  match tuck: tucked (Some text) leaf with
                    | None => Void.impossible (Bool.falseNotTrue (Bool.andRight clause))
                    | Some still =>
                      Bool.andIntro headed
                        (Bool.andIntro
                          (Bool.andLeft clause)
                          (standsAppend still later more after rest (Bool.andRight clause) second))
                | None, None =>
                  Bool.andIntro headed
                    (Bool.andIntro
                      (Bool.andLeft clause)
                      (standsAppend None later more after rest (Bool.andRight clause) second))
                | None, Some text =>
                  let open := Bool.andLeft clause
                  let tuck := Bool.andRight clause
                  match trailing: leaf.trivia.trailing with
                    | None =>
                      Bool.andIntro headed
                        (Bool.andIntro open (standsAppend (Some text) later more after rest tuck second))
                    | Some comment =>
                      Bool.andIntro headed
                        (Bool.andIntro open
                          (Bool.andIntro
                            (Bool.andLeft tuck)
                            (standsAppend None later more after rest (Bool.andRight tuck) second)))

--| A word's leaf given other own-line comments and blank lines stands as before against the word given the same,
--| if it is headed as that word.
theorem standsHeaded ∀ (leaf: Leaf) (leaves: List Leaf) (word: Word) (words: List Word) (above: List Comment)
    (blank: Nat) (comments: Comments)
    (notComma: (leaf.kind == Comma) = False)
    (standing: stands None [word, ..words] [leaf, ..leaves] = True)
    (sameAfter: comments.after = word.comments.after)
    (fresh: ({ leaf | trivia = { leaf.trivia | leading = above, blankLines = blank } }).headedAs {
      text = word.text,
      comments
    }
      = True):
    stands None [{ text = word.text, comments }, ..words] (headed above blank [leaf, ..leaves]) = True :=
  match comma: leaf.kind == Comma with
    | False =>
      rewrite sameAfter then
        match afterIs: word.comments.after with
          | None => Bool.andIntro fresh (Bool.andRight standing)
          | Some text =>
            match trailing: leaf.trivia.trailing with
              | None => Bool.andIntro fresh (Bool.andRight standing)
              | Some comment => Bool.andIntro fresh (Bool.andRight standing)

-- The file's leaves stand.

--| Own-line comments as a leaf's word reads them.
def readNotes (comments: List Comment): List Note :=
  comments.map (comment => { text = comment.text, blankBefore = comment.blankLines > 0 })

theorem noteRead ∀ (note: Note)
    (plain: note.unreturned = True):
    { text = (noteComment note).text, blankBefore = (noteComment note).blankLines > 0 } = note :=
  match note with | { text, blankBefore } => rewrite unreturnedSame text plain then cases blankBefore then byComputing

theorem notesRead ∀ (notes: List Note)
    (plain: notes.all Note.unreturned = True):
    readNotes (notes.map noteComment) = notes :=
  match notes with
    | [] => byComputing
    | [note, ..rest] => rewrite noteRead note (Bool.andLeft plain), notesRead rest (Bool.andRight plain)

--| A declaration's leaves in the file stand against its calm words, the `def` holding `keyword`'s comments, when the
--| file loop's notes and blank line read back as those.
theorem standsDecl ∀ (header: Header) (colonEq: Comments) (value: Expr) (empty: Bool) (keyword: Comments)
    (stood: (Definition [] header (Assigned colonEq value)).stands = True)
    (start: notCommaFirst (Definition [] header (Assigned colonEq value)).leaves = True)
    (aboveRead: readNotes (laidNotes empty header.keyword.above) = keyword.above)
    (blankRead: ((if header.keyword.blankBefore && !(empty && header.keyword.above.isEmpty) then 1 else 0) > 0)
      = keyword.blankBefore)
    (afterSame: keyword.after = header.keyword.after):
    stands None
      [fixedWord "def" keyword, ..((Definition [] header (Assigned colonEq value)).calm.words.drop 1)]
      ((Definition [] header (Assigned colonEq value)).laid empty)
      = True :=
  match leaves: (Definition [] header (Assigned colonEq value)).leaves with
    | [leaf, ..rest] =>
      match comma: leaf.kind == Comma with
        | False =>
          let textOk: (leaf.token.text == "def") = True := Bool.andLeft (Bool.andLeft stood)
          let blank := if header.keyword.blankBefore && !(empty && header.keyword.above.isEmpty) then 1 else 0
          let newLeaf :=
            { leaf | trivia = { leaf.trivia | leading = laidNotes empty header.keyword.above, blankLines = blank } }
          let aboveOk: (newLeaf.word.comments.above == keyword.above) = True :=
            rewrite aboveRead then DecEq.refl keyword.above
          let blankOk: (newLeaf.word.comments.blankBefore == keyword.blankBefore) = True :=
            rewrite blankRead then DecEq.refl keyword.blankBefore
          let fresh: newLeaf.headedAs { text = "def", comments = keyword } = True :=
            Bool.andIntro textOk (Bool.andIntro aboveOk blankOk)
          standsHeaded leaf rest
            (fixedWord "def" { above = [], after = header.keyword.after, blankBefore = False })
            ((Definition [] header (Assigned colonEq value)).calm.words.drop 1)
            (laidNotes empty header.keyword.above)
            (if header.keyword.blankBefore && !(empty && header.keyword.above.isEmpty) then 1 else 0)
            keyword
            comma
            stood
            afterSame
            fresh

-- The parser's groups.

def groupTokens (groups: List (List Leaf)): List (List Token) := groups.map tokens

--| The parser cuts leaves into groups by their tokens alone.
theorem splitTokens ∀ (state: Splitter) (current other: List Leaf)
    (groups others: List (List Leaf)) (leaves rest: List Leaf)
    (same: tokens leaves = tokens rest)
    (sameCurrent: tokens current = tokens other)
    (sameGroups: groupTokens groups = groupTokens others):
    groupTokens (splitFrom state current groups leaves) = groupTokens (splitFrom state other others rest) :=
  match leaves, rest with
    | [], [] =>
      let flush := (all: List Leaf) (done: List (List Leaf)) => if all.isEmpty then done else [all.reverse, ..done]
      calc groupTokens (flush current groups).reverse
        _ = (groupTokens (flush current groups)).reverse := List.mapReverse (flush current groups) tokens
        _ = (groupTokens (flush other others)).reverse :=
          Eq.cong (all => all.reverse) (flushTokens current other groups others sameCurrent sameGroups)
        _ = groupTokens (flush other others).reverse := Eq.flipped (List.mapReverse (flush other others) tokens)
    | [leaf, ..after], [twin, ..beyond] =>
      let headSame: twin.token = leaf.token := Eq.flipped (Eq.cong (tokens => tokens.headOr leaf.token) same)
      let tailSame: tokens after = tokens beyond := Eq.cong (tokens => tokens.drop 1) same
      let token := leaf.token
      let inside := state.depth > 0 || state.opening
      let continues := state.openBrackets > 0 && (token.kind == Comma || token.kind.isCloser)
      rewrite headSame then
        match starts: token.column == 0
          && token.kind != ColonEq
          && ((!inside && !state.attributesOnly && !continues) || (inside && token.kind.startsGroup)) with
          | True =>
            splitTokens _
              [leaf]
              [twin] _ _
              after
              beyond
              tailSame
              (rewrite headSame)
              (flushTokens current other groups others sameCurrent sameGroups)
          | False =>
            splitTokens _
              [leaf, ..current]
              [twin, ..other]
              groups
              others
              after
              beyond
              tailSame
              (rewrite headSame, sameCurrent)
              sameGroups

theorem tokensReverse ∀ (leaves: List Leaf): tokens leaves.reverse = (tokens leaves).reverse :=
  tokensReverseOnto leaves []

--| Closing the group in progress keeps the groups' tokens alike.
theorem flushTokens ∀ (current other: List Leaf) (groups others: List (List Leaf))
    (sameCurrent: tokens current = tokens other)
    (sameGroups: groupTokens groups = groupTokens others):
    groupTokens (if current.isEmpty then groups else [current.reverse, ..groups])
      = groupTokens (if other.isEmpty then others else [other.reverse, ..others]) :=
  match current, other with
    | [], [] => sameGroups
    | [first, ..more], [second, ..later] =>
      let reversed: tokens [first, ..more].reverse = tokens [second, ..later].reverse := calc tokens
        [first, ..more].reverse
        _ = (tokens [first, ..more]).reverse := tokensReverse [first, ..more]
        _ = (tokens [second, ..later]).reverse := Eq.cong (all => all.reverse) sameCurrent
        _ = tokens [second, ..later].reverse := Eq.flipped (tokensReverse [second, ..later])
      List.consEqOfEq _ _ _ _ reversed sameGroups

-- Standing, group by group.

--| Each group of leaves stands against its words.
def standsEach: List (List Word) → List (List Leaf) → Bool
  | [], [] => True
  | [words, ..more], [leaves, ..rest] => stands None words leaves && standsEach more rest
  | _, _ => False

theorem standsConcat ∀ (words: List (List Word)) (groups: List (List Leaf))
    (each: standsEach words groups = True):
    stands None words.concat groups.concat = True :=
  match words, groups with
    | [], [] => byComputing
    | [first, ..more], [group, ..rest] =>
      standsAppend None first more.concat group rest.concat
        (Bool.andLeft each)
        (standsConcat more rest (Bool.andRight each))

--| The file's leaves stand against the output tree's words.
theorem standsFile ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped = True)
    (settled: file.settled = True)
    (lexical: file.lexical = True)
    (stood: file.stood = True)
    (unreturned: file.unreturned = True):
    stands None file.words file.lexed.leaves = True :=
  standsConcat _ _ (standsEachFile file within shaped settled lexical stood unreturned)

--| Leaves standing against words have a non-comma leaf for each word.
theorem standsLength ∀ (owed: Option Text) (words: List Word) (leaves: List Leaf)
    (standing: stands owed words leaves = True):
    (codeWords leaves).length = words.length :=
  match leaves with
    | [] =>
      match owed with
        | None => rewrite List.eqNilOfIsEmpty words (Bool.andLeft standing)
        | Some text => Void.impossible (Bool.falseNotTrue (Bool.andRight standing))
    | [leaf, ..after] =>
      match comma: leaf.kind == Comma with
        | True =>
          match tuck: tucked owed leaf with
            | None => Void.impossible (Bool.falseNotTrue (Bool.andRight (Bool.andRight standing)))
            | Some still => standsLength still words after (Bool.andRight (Bool.andRight standing))
        | False =>
          match words with
            | [word, ..later] =>
              let clause := Bool.andRight standing
              let next := (still: Option Text) (rest: stands still later after = True) =>
                Eq.cong (n => n + 1) (standsLength still later after rest)
              match owed, afterIs: word.comments.after with
                | Some text, None =>
                  match tuck: tucked (Some text) leaf with
                    | None => Void.impossible (Bool.falseNotTrue (Bool.andRight clause))
                    | Some still => next still (Bool.andRight clause)
                | None, None => next None (Bool.andRight clause)
                | None, Some text =>
                  match trailing: leaf.trivia.trailing with
                    | None => next (Some text) (Bool.andRight clause)
                    | Some comment => next None (Bool.andRight (Bool.andRight clause))

def codeLength (leaves: List Leaf): Nat := (codeWords leaves).length

theorem codeLengthTokens ∀ (xs ys: List Leaf) (same: tokens xs = tokens ys): codeLength xs = codeLength ys :=
  match xs, ys with
    | [], [] => byComputing
    | [x, ..xr], [y, ..yr] =>
      let headSame: y.token = x.token := Eq.flipped (Eq.cong (all => all.headOr x.token) same)
      let rest := codeLengthTokens xr yr (Eq.cong (all => all.drop 1) same)
      let kindSame: y.kind = x.kind := Eq.cong (token => token.kind) headSame
      match comma: x.kind == Comma with
        | True =>
          let twin: (y.kind == Comma) = True := rewrite kindSame then comma
          rewrite twin then rest
        | False =>
          let twin: (y.kind == Comma) = False := rewrite kindSame then comma
          rewrite twin then Eq.cong (n => n + 1) rest

theorem codeLengthsTokens ∀ (xs ys: List (List Leaf))
    (same: groupTokens xs = groupTokens ys):
    xs.map codeLength = ys.map codeLength :=
  match xs, ys with
    | [], [] => byComputing
    | [x, ..xr], [y, ..yr] =>
      List.consEqOfEq _ _ _ _
        (codeLengthTokens x y (Eq.cong (all => all.headOr []) same))
        (codeLengthsTokens xr yr (Eq.cong (all => all.drop 1) same))

theorem standsLengths ∀ (words: List (List Word)) (groups: List (List Leaf))
    (each: standsEach words groups = True):
    groups.map codeLength = words.map (all => all.length) :=
  match words, groups with
    | [], [] => byComputing
    | [first, ..more], [group, ..rest] =>
      List.consEqOfEq _ _ _ _
        (standsLength None first group (Bool.andLeft each))
        (standsLengths more rest (Bool.andRight each))

--| Pieces whose words, joined, are the words wanted, each with as many words as wanted of it, have those words.
theorem piecesWords ∀ (pieces: List (List Leaf)) (words: List (List Word))
    (joined: codeWords pieces.concat = words.concat)
    (lengths: pieces.map codeLength = words.map (all => all.length)):
    pieces.map codeWords = words :=
  match pieces, words with
    | [], [] => byComputing
    | [piece, ..rest], [first, ..more] =>
      let split: codeWords piece ++ codeWords rest.concat = first ++ more.concat :=
        Eq.trans (Eq.flipped (codeWordsAppend piece rest.concat)) joined
      let (pieceSame, restSame) :=
        List.appendCancel
          (codeWords piece)
          first
          (codeWords rest.concat)
          more.concat
          split
          (Eq.cong (all => all.headOr 0) lengths)
      List.consEqOfEq _ _ _ _ pieceSame (piecesWords rest more restSame (Eq.cong (all => all.drop 1) lengths))

-- Witnesses for the narrow hypotheses.

--| `a -- c` as a word and its leaf before the lexer reaches the comment.
def ownerLeaf: Leaf := { token = { kind = Lower, text = "a", column = 0, lineStart = True }, trivia = Trivia.empty }

def ownerWord: Word := { text = "a", comments = { above = [], after = Some "-- c", blankBefore = False } }

theorem owingNonEmptyExample: (![ownerWord].isEmpty) = True := owingNonEmpty "-- c" [ownerLeaf] [ownerWord] byComputing

theorem landingExample: lands ownerLeaf [] = True :=
  landing ownerLeaf ownerWord [] [] byComputing byComputing byComputing byComputing byComputing byComputing byComputing

theorem noteBackExample: {
      text = (noteComment { text = "-- a", blankBefore = True }).trimmed.text,
      blankBefore = (noteComment { text = "-- a", blankBefore = True }).trimmed.blankLines > 0
    }
      = { text = "-- a", blankBefore = True } :=
  noteBack { text = "-- a", blankBefore = True } byComputing byComputing

theorem commentCleanExample: ({ text = "-- a", column = 4, blankLines = 0 }: Comment).trimmed
      = { text = "-- a", column = 4, blankLines = 0 } :=
  commentClean { text = "-- a", column = 4, blankLines = 0 } byComputing
