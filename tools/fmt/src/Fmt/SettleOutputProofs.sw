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
import Fmt.FileLexProofs (laidNotesFalse)
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
  bareComma,
  alphabet1Leaves,
  allReverseOnto,
  arrowsIdleAll,
  commasIdle,
  homeFromTokens,
  letsQuiet1,
  plain1,
  plainFrom,
  plainFromOf
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

-- The file.

--| A comment line the file loop prints reads back as it is: its text doesn't end in a carriage return, which the
--| lexer takes off (`crDropped`).
def Note.unreturned (note: Note): Bool := !note.text.endsWith "\r"

--| No own-line comment the file loop prints ends in a carriage return: those above each declaration and at the end.
def SourceFile.unreturned1 (file: SourceFile): Bool :=
  file.decls.all (decl => decl.firstComments.above.all Note.unreturned) && file.end.above.all Note.unreturned

--| The words the output's tree has, all declarations' in a row.
def SourceFile.words1 (file: SourceFile): List Word := (file.calmTop.decls.map Decl.words).concat

--| The file's leaves stand against its words: each declaration's (`stood1`), the `def` holding the comments the file
--| loop prints above it.
theorem standsFile ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped1 = True)
    (settled: file.settled1 = True)
    (lexical: file.lexical1 = True)
    (stood: file.stood1 = True)
    (unreturned: file.unreturned1 = True):
    stands None file.words1 file.lexed1.leaves = True :=
  let starts := leavesStart1 file within shaped settled lexical
  match file with
    | { decls, end } =>
      let withinDecls: decls.all Decl.within1 = True := within
      match decls with
        | [] => byComputing
        | [Definition [] header (Assigned colonEq value), ..rest] =>
          let plain := Bool.andLeft (Bool.andLeft unreturned)
          let keyword := header.keyword
          let aboveTop: readNotes (laidNotes True keyword.above) = keyword.topped.above :=
            match above: keyword.above with
              | [] => byComputing
              | [first, ..more] =>
                match first with
                  | { text, blankBefore } =>
                    rewrite unreturnedSame text (Bool.andLeft plain), notesRead more (Bool.andRight plain)
          let blankTop: ((if keyword.blankBefore && !(True && keyword.above.isEmpty) then 1 else 0) > 0)
            = keyword.topped.blankBefore :=
            match above: keyword.above with
              | [] =>
                match keyword.blankBefore with
                  | True => byComputing
                  | False => byComputing
              | [first, ..more] =>
                match keyword.blankBefore with
                  | True => byComputing
                  | False => byComputing
          let afterTop: keyword.topped.after = keyword.after := match above: keyword.above with
            | [] => byComputing
            | [first, ..more] => byComputing
          standsAppend None _ _ _ _
            (standsDecl header colonEq value True keyword.topped
              (Bool.andLeft stood)
              (Bool.andLeft starts)
              aboveTop
              blankTop
              afterTop)
            (standsRest rest
              (Bool.andRight withinDecls)
              (Bool.andRight stood)
              (Bool.andRight (Bool.andLeft unreturned))
              (Bool.andRight starts))

--| Every declaration's printed leaves start with no comma (they start with `def`: `printedTokens1`).
theorem leavesStart1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped1 = True)
    (settled: file.settled1 = True)
    (lexical: file.lexical1 = True):
    file.decls.all (decl => notCommaFirst decl.leaves1) = True :=
  ?

--| The leaves of declarations after the first stand against their calm words.
theorem standsRest ∀ (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (stood: decls.all Decl.stands1 = True)
    (plain: decls.all (decl => decl.firstComments.above.all Note.unreturned) = True)
    (starts: decls.all (decl => notCommaFirst decl.leaves1) = True):
    stands None ((decls.map Decl.calm).map Decl.words).concat (groupsFrom False decls).concat = True :=
  match decls with
    | [] => byComputing
    | [Definition [] header (Assigned colonEq value), ..rest] =>
      let keyword := header.keyword
      let aboveRead: readNotes (laidNotes False keyword.above) = keyword.above :=
        rewrite laidNotesFalse keyword.above then notesRead keyword.above (Bool.andLeft plain)
      let blankRead: ((if keyword.blankBefore && !(False && keyword.above.isEmpty) then 1 else 0) > 0)
        = keyword.blankBefore :=
        match keyword.blankBefore with
          | True => byComputing
          | False => byComputing
      standsAppend None _ _ _ _
        (standsDecl header colonEq value False keyword
          (Bool.andLeft stood)
          (Bool.andLeft starts)
          aboveRead
          blankRead
          byComputing)
        (standsRest rest (Bool.andRight within) (Bool.andRight stood) (Bool.andRight plain) (Bool.andRight starts))

--| The output tree's words are settled as the tree's are: `calm` and `calmTop` change only blank-line flags.
theorem wordsSettled1 ∀ (file: SourceFile)
    (settled: file.settled1 = True):
    homedBack (file.words1.reverseOnto []) = True
      ∧ file.words1.all (word => word.comments.texts.all commentText) = True :=
  ?

--| A printed leaf has a closer's kind exactly when it has a closer's text.
theorem printedAgrees1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped1 = True)
    (settled: file.settled1 = True)
    (lexical: file.lexical1 = True):
    file.lexed1.leaves.all Leaf.agrees = True :=
  ?

--| After rule 1 no `->` holds a comment and none comes before an own-line comment.
theorem homedArrowsBare ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped1 = True)
    (settled: file.settled1 = True)
    (lexical: file.lexical1 = True)
    (hung: file.hung1 = True)
    (stood: file.stood1 = True)
    (unreturned: file.unreturned1 = True):
    Syntax.SettleProofs.arrowsBare (homeFrom [] None file.lexed1.leaves) = True :=
  ?

--| The parser's groups of rule 1's result are the declarations, each with its words.
theorem groupsBack ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped1 = True)
    (settled: file.settled1 = True)
    (lexical: file.lexical1 = True)
    (hung: file.hung1 = True)
    (stood: file.stood1 = True)
    (unreturned: file.unreturned1 = True)
    (m: matched (homeFrom [] None file.lexed1.leaves).reverse (file.words1.reverseOnto []) = True):
    (groupsOf (homeFrom [] None file.lexed1.leaves)).map codeWords = file.calmTop.decls.map Decl.words :=
  ?

--| The end's comments read back as the tree's.
theorem endBack ∀ (file: SourceFile)
    (within: file.within1 = True)
    (settled: file.settled1 = True)
    (unreturned: file.unreturned1 = True):
    file.lexed1.end.trimmed.comments = file.calmTop.end :=
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
      rewrite unreturnedSame written plain, unspaced then
        match blankBefore with
          | True => byComputing
          | False => byComputing

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

--| A text that doesn't end in a carriage return keeps it all when the lexer takes one off.
theorem unreturnedSame ∀ (text: Text) (plain: (!text.endsWith "\r") = True): withoutReturn text = text :=
  match chars: text.toList.reverse with
    | [] => byComputing
    | [last, ..earlier] =>
      match same: Text.sameChar '\r' last with
        | False => byComputing

--| Trimming leaves whose comments are words' comment texts changes nothing.
--| A comment whose text rule 5 leaves alone.
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

theorem wordClean ∀ (leaf: Leaf) (texts: leaf.word.comments.texts.all commentText = True): leaf.clean = True :=
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
                (wordClean leaf wordTexts)
                (matchedClean earlier older (Bool.andRight m) (Bool.andRight texts))

theorem leadOf ∀ (leaves: List Leaf) (plain: plain1 (tokens leaves) = True): notCommaFirst leaves = True :=
  match leaves with
    | [] => byComputing
    | [leaf, .._] =>
      match comma: leaf.kind == Comma with
        | False => byComputing

--| `printedSettle1` (`Fmt.OutputStatements`), with `stood1` (`printedStands1`'s conclusion, ticket F) and
--| `unreturned1` as hypotheses. `unreturned1` is needed: an own-line comment ending in a carriage return, which
--| `settled1` allows, is printed with it and read back without it (`returnLost`).
--|
--| Proof idea: the leaves stand against the output tree's words (`standsFile`), so rule 1 gives each leaf its word
--| and leaves the commas bare (`homeStands`); rules 2 to 4 then find nothing to move (`commasIdle`, `arrowsIdleAll`,
--| `letsQuiet1`), the comments are trimmed already (`trimIdle`), and the parser's groups are the declarations
--| (`groupsBack`).
theorem printedSettle1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: file.shaped1 = True)
    (settled: file.settled1 = True)
    (lexical: file.lexical1 = True)
    (hung: file.hung1 = True)
    (stood: file.stood1 = True)
    (unreturned: file.unreturned1 = True):
    (groupsOf file.lexed1.settled.leaves).map codeWords = file.calmTop.decls.map Decl.words
      ∧ file.lexed1.settled.end.comments = file.calmTop.end :=
  let leaves := file.lexed1.leaves
  let homed := homeFrom [] None leaves
  let (homedWords, texts) := wordsSettled1 file settled
  let plain := printedPlain1 file within shaped settled lexical hung
  let leavesWithin := alphabet1Leaves leaves (printedAlphabet1 file within shaped settled lexical)
  let m: matched homed.reverse (file.words1.reverseOnto []) = True :=
    homeStands None [] leaves [] file.words1
      (standsFile file within shaped settled lexical stood unreturned)
      byComputing
      (Bool.orRight (leadOf leaves plain))
      homedWords
      byComputing
      leavesWithin
      (printedAgrees1 file within shaped settled lexical)
  let bare: homed.all bareComma = True :=
    rewrite <- List.reverseReverse homed then allReverseOnto bareComma homed.reverse [] (matchedBare _ _ m) byComputing
  let tokensSame: tokens homed = tokens leaves := Eq.trans (homeFromTokens [] None leaves) byComputing
  let plainHomed: plainFrom (tokens homed) = True := rewrite tokensSame then plainFromOf (tokens leaves) plain
  let homedWithin := withinOfTokens homed leaves tokensSame leavesWithin
  let commasSame: commasFrom [] None homed file.lexed1.end = { leaves = homed, end = file.lexed1.end } :=
    commasIdle [] homed file.lexed1.end bare
  let arrowsSame: arrows homed = homed :=
    arrowsIdleAll homed (homedArrowsBare file within shaped settled lexical hung stood unreturned) plainHomed
  let letsSame: letsFrom [] homed = homed := letsQuiet1 [] homed byComputing homedWithin
  let trimSame: homed.map (leaf => { leaf | trivia = leaf.trivia.trimmed }) = homed :=
    let wordsTexts := allReverseOnto (word => word.comments.texts.all commentText) file.words1 [] texts byComputing
    let clean: homed.all Leaf.clean = True :=
      rewrite <- List.reverseReverse homed then
        allReverseOnto Leaf.clean homed.reverse [] (matchedClean _ _ m wordsTexts) byComputing
    trimIdle homed clean
  let leavesSame: file.lexed1.settled.leaves = homed := rewrite commasSame, arrowsSame, letsSame, trimSame
  let endSame: file.lexed1.settled.end = file.lexed1.end.trimmed := rewrite commasSame
  (
    rewrite leavesSame then groupsBack file within shaped settled lexical hung stood unreturned m,
    rewrite endSame then endBack file within settled unreturned
  )

-- Cases.

--| Every hypothesis of `printedSettle1` but `unreturned1` holds of a source's tidied tree, and its conclusion fails.
def returnFails (source: Text): Bool := match tidiedOf source with
  | None => False
  | Some file =>
    file.within1
      && file.shaped1
      && file.settled1
      && file.lexical1
      && file.hung1
      && file.stood1
      && !file.unreturned1
      && !wordsBack file

--| `unreturned1` is needed: `-- a\r\r\n` keeps one `\r` in the tree's comment (the lexer strips only the last), the
--| file loop prints it, and the lexer reads the printed line back without it. Above a declaration and at the end.
theorem returnLost: (returnFails "-- a\r\r\ndef d: A := b\n" && returnFails "def d: A := b\n-- a\r\r\n") = True :=
  byComputing

-- Standing, joined.

--| `stands` joins: leaves standing against words, with nothing owed at their end, followed by more that stand.
theorem standsAppend ∀ (owed: Option Text) (words more: List Word) (leaves rest: List Leaf)
    (first: stands owed words leaves = True)
    (second: stands None more rest = True):
    stands owed (words ++ more) (leaves ++ rest) = True :=
  match leaves with
    | [] =>
      match owed with
        | None => rewrite emptyOf words (Bool.andLeft first) then second
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
  match note with
    | { text, blankBefore } =>
      rewrite unreturnedSame text plain then
        match blankBefore with
          | True => byComputing
          | False => byComputing

theorem notesRead ∀ (notes: List Note)
    (plain: notes.all Note.unreturned = True):
    readNotes (notes.map noteComment) = notes :=
  match notes with
    | [] => byComputing
    | [note, ..rest] => rewrite noteRead note (Bool.andLeft plain), notesRead rest (Bool.andRight plain)

--| A declaration's leaves in the file stand against its calm words, the `def` holding `keyword`'s comments, when the
--| file loop's notes and blank line read back as those.
theorem standsDecl ∀ (header: Header) (colonEq: Comments) (value: Expr) (empty: Bool) (keyword: Comments)
    (stood: (Definition [] header (Assigned colonEq value)).stands1 = True)
    (start: notCommaFirst (Definition [] header (Assigned colonEq value)).leaves1 = True)
    (aboveRead: readNotes (laidNotes empty header.keyword.above) = keyword.above)
    (blankRead: ((if header.keyword.blankBefore && !(empty && header.keyword.above.isEmpty) then 1 else 0) > 0)
      = keyword.blankBefore)
    (afterSame: keyword.after = header.keyword.after):
    stands None
      [fixedWord "def" keyword, ..((Definition [] header (Assigned colonEq value)).calm.words.drop 1)]
      ((Definition [] header (Assigned colonEq value)).laid1 empty)
      = True :=
  match leaves: (Definition [] header (Assigned colonEq value)).leaves1 with
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
