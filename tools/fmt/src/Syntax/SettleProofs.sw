--| Proofs about rule N (`Syntax/Settle.sw`, `Lexed.settled`) for slice 1 of the proved formatter
--| (docs/proposals/self-hosted-fmt-s1-sketch.md, ticket 15).

namespace Syntax.SettleProofs
import Std (Bool, Char, DecEq, Eq, Finite, List, Nat, Option, Text, Void)
import Syntax (..)
import Fmt (..)

--| The leaves' tokens, comments aside.
def tokens (leaves: List Leaf): List Token := leaves.map (leaf => leaf.token)

theorem tokensReverseOnto ∀ (xs acc: List Leaf): tokens (xs.reverseOnto acc) = (tokens xs).reverseOnto (tokens acc) :=
  List.mapReverseOnto xs acc (leaf => leaf.token)

--| `trailingAt` moves a comment between leaves and keeps their tokens.
theorem trailingAtTokens ∀ (behind: List Leaf) (steps: Nat) (comment: Comment):
    tokens (trailingAt behind steps comment) = tokens behind :=
  match behind, steps with
    | [], _ => byComputing
    | [leaf, ..earlier], Zero => byComputing
    | [leaf, ..earlier], Succ Zero => byComputing
    | [leaf, ..earlier], Succ (Succ more) =>
      Eq.cong (tail => [leaf.token, ..tail]) (trailingAtTokens earlier (Succ more) comment)

--| One step of a pass that keeps tokens: the leaf, maybe with other
--| comments, goes on the settled leaves, which keep their tokens.
theorem consTokens ∀ (x leaf: Leaf) (settled behind later after: List Leaf)
    (same: x.token = leaf.token)
    (sameBehind: tokens settled = tokens behind)
    (sameLater: tokens later = tokens after):
    tokens ([x, ..settled].reverseOnto later) = tokens (behind.reverseOnto [leaf, ..after]) :=
  calc tokens ([x, ..settled].reverseOnto later)
    _ = (tokens settled).reverseOnto (tokens [x, ..later]) := tokensReverseOnto settled [x, ..later]
    _ = (tokens behind).reverseOnto (tokens [leaf, ..after]) := rewrite same, sameBehind, sameLater
    _ = tokens (behind.reverseOnto [leaf, ..after]) := (tokensReverseOnto behind [leaf, ..after]).flipped

--| Rule 1 keeps the tokens.
theorem homeFromTokens ∀ (behind: List Leaf) (bumped: Option Comment) (rest: List Leaf):
    tokens (homeFrom behind bumped rest) = tokens (behind.reverseOnto rest) :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let step := (x: Leaf) (settled: List Leaf) (next: Option Comment) (same: x.token = leaf.token) (sameBehind: tokens
          settled
        = tokens behind) =>
        Eq.trans
          (homeFromTokens [x, ..settled] next after)
          (consTokens x leaf settled behind after after same sameBehind byComputing)
      match bumped with
        | None =>
          match leaf.trivia.trailing with
            | None => step leaf behind None byComputing byComputing
            | Some comment =>
              match movable leaf behind after with
                | False => step leaf behind None byComputing byComputing
                | True =>
                  match stepsBack leaf behind after 0 with
                    | Zero =>
                      match barBelow leaf behind after with
                        | True => step (leaf.withTrailing None) behind (Some comment.unspaced) byComputing byComputing
                        | False => step leaf behind None byComputing byComputing
                    | Succ more =>
                      step
                        (leaf.withTrailing None)
                        (trailingAt behind (Succ more) comment)
                        None
                        byComputing
                        (trailingAtTokens behind (Succ more) comment)
        | Some bump =>
          let lifted := leaf.withLeading [bump, ..leaf.trivia.leading]
          match lifted.trivia.trailing with
            | None => step lifted behind None byComputing byComputing
            | Some comment =>
              match movable lifted behind after with
                | False => step lifted behind None byComputing byComputing
                | True =>
                  match stepsBack lifted behind after 0 with
                    | Zero =>
                      match barBelow lifted behind after with
                        | True => step (lifted.withTrailing None) behind (Some comment.unspaced) byComputing byComputing
                        | False => step lifted behind None byComputing byComputing
                    | Succ more =>
                      step
                        (lifted.withTrailing None)
                        (trailingAt behind (Succ more) comment)
                        None
                        byComputing
                        (trailingAtTokens behind (Succ more) comment)

--| Rule 2 keeps the tokens.
theorem commasFromTokens ∀ (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia):
    tokens (commasFrom done carried rest end).leaves = tokens (done.reverseOnto rest) :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let step := (x: Leaf) (next: Option Carried) (same: x.token = leaf.token) =>
        Eq.trans
          (commasFromTokens [x, ..done] next after end)
          (consTokens x leaf done done after after same byComputing byComputing)
      match carried with
        | None =>
          match commaCarries leaf.trivia with
            | None => step leaf None byComputing
            | Some carry =>
              match leaf.kind == Comma with
                | True => step { leaf | trivia = Trivia.empty } (Some carry) byComputing
                | False => step leaf None byComputing
        | Some held =>
          let received := { leaf | trivia = held.into leaf.trivia }
          match commaCarries received.trivia with
            | None => step received None byComputing
            | Some carry =>
              match leaf.kind == Comma with
                | True => step { leaf | trivia = Trivia.empty } (Some carry) byComputing
                | False => step received None byComputing

--| Rule 3 keeps the tokens.
theorem arrowsFromTokens ∀ (done: List Leaf) (current: Leaf) (rest: List Leaf):
    tokens (arrowsFrom done current rest) = tokens (done.reverseOnto [current, ..rest]) :=
  match rest with
    | [] => byComputing
    | [next, ..more] =>
      match current.kind == Arrow && (!next.trivia.leading.isEmpty || current.trivia.trailing.isSome) with
        | True =>
          let moved := { current |
            trivia = { current.trivia |
              leading = current.trivia.leading
                ++ (current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse [])
                ++ next.trivia.leading,
              trailing = None
            }
          }
          Eq.trans
            (arrowsFromTokens [moved, ..done] (next.withLeading []) more)
            (consTokens moved current done done
              [next.withLeading [], ..more]
              [next, ..more]
              byComputing
              byComputing
              byComputing)
        | False =>
          Eq.trans
            (arrowsFromTokens [current, ..done] next more)
            (consTokens current current done done [next, ..more] [next, ..more] byComputing byComputing byComputing)

theorem arrowsTokens ∀ (leaves: List Leaf): tokens (arrows leaves) = tokens leaves := match leaves with
  | [] => byComputing
  | [first, ..rest] => arrowsFromTokens [] first rest

--| Rule 4 keeps the tokens.
theorem letsFromTokens ∀ (behind rest: List Leaf): tokens (letsFrom behind rest) = tokens (behind.reverseOnto rest) :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      match leaf.trivia.trailing with
        | None =>
          Eq.trans
            (letsFromTokens [leaf, ..behind] after)
            (consTokens leaf leaf behind behind after after byComputing byComputing byComputing)
        | Some comment =>
          match leaf.kind == ColonEq && letBefore behind 0 && semicolonAfter after 0 with
            | True =>
              let moved := { leaf |
                trivia = { leaf.trivia | leading = leaf.trivia.leading ++ [comment.unspaced], trailing = None }
              }
              Eq.trans
                (letsFromTokens [moved, ..behind] after)
                (consTokens moved leaf behind behind after after byComputing byComputing byComputing)
            | False =>
              Eq.trans
                (letsFromTokens [leaf, ..behind] after)
                (consTokens leaf leaf behind behind after after byComputing byComputing byComputing)

theorem trimmedTokens ∀ (leaves: List Leaf):
    tokens (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) = tokens leaves :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] => Eq.cong (tail => [leaf.token, ..tail]) (trimmedTokens rest)

--| Rule N moves comments and nothing else: the tokens are the lexer's.
theorem settledKeepsTokens ∀ (lexed: Lexed): tokens lexed.settled.leaves = tokens lexed.leaves :=
  let homed := homeFrom [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  calc tokens lexed.settled.leaves
    _ = tokens (letsFrom [] (arrows commas.leaves)) := trimmedTokens (letsFrom [] (arrows commas.leaves))
    _ = tokens (arrows commas.leaves) := letsFromTokens [] (arrows commas.leaves)
    _ = tokens commas.leaves := arrowsTokens commas.leaves
    _ = tokens homed := commasFromTokens [] None homed lexed.end
    _ = tokens lexed.leaves := homeFromTokens [] None lexed.leaves

theorem allReverseOnto ∀ (p: a → Bool) (xs acc: List a)
    (allXs: xs.all p = True)
    (allAcc: acc.all p = True):
    (xs.reverseOnto acc).all p = True :=
  match xs with
    | [] => allAcc
    | [x, ..rest] =>
      match held: p x with
        | True => allReverseOnto p rest [x, ..acc] allXs (rewrite held then allAcc)

--| A comma with no comment.
def bareComma (leaf: Leaf): Bool := (leaf.trivia.leading.isEmpty && leaf.trivia.trailing.isNone) || leaf.kind != Comma

theorem carriesNoneBare ∀ (trivia: Trivia)
    (none: commaCarries trivia = None):
    (trivia.leading.isEmpty && trivia.trailing.isNone) = True :=
  match trivia.leading, trivia.trailing with
    | [], None => byComputing
    | [_, .._], _ => cases

theorem notCommaBare ∀ (leaf: Leaf) (other: (leaf.kind == Comma) = False): bareComma leaf = True :=
  Bool.orRight (rewrite other)

--| After rule 2 no comma holds a comment.
theorem commasFromBare ∀ (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia)
    (doneBare: done.all bareComma = True):
    (commasFrom done carried rest end).leaves.all bareComma = True :=
  match rest with
    | [] => allReverseOnto bareComma done [] doneBare byComputing
    | [leaf, ..after] =>
      let received := { leaf | trivia = carried.map (carry => carry.into leaf.trivia) |> .getOrElse leaf.trivia }
      match c: commaCarries received.trivia with
        | None =>
          commasFromBare
            [received, ..done]
            None
            after
            end
            (rewrite Bool.orLeft (carriesNoneBare received.trivia c) then doneBare)
        | Some carry =>
          match k: leaf.kind == Comma with
            | True => commasFromBare [{ received | trivia = Trivia.empty }, ..done] (Some carry) after end doneBare
            | False => commasFromBare [received, ..done] None after end (rewrite notCommaBare received k then doneBare)

theorem withoutLeadingBare ∀ (leaf: Leaf) (bare: bareComma leaf = True): bareComma (leaf.withLeading []) = True := cases

theorem kindNotComma ∀ (leaf: Leaf) (kind: Tok)
    (is: (leaf.kind == kind) = True)
    (other: (kind == Comma) = False):
    (leaf.kind == Comma) = False :=
  rewrite DecEq.sound is then other

--| Rule 3 gives a comma no comment.
theorem arrowsFromBare ∀ (done: List Leaf) (current: Leaf) (rest: List Leaf)
    (doneBare: done.all bareComma = True)
    (currentBare: bareComma current = True)
    (restBare: rest.all bareComma = True):
    (arrowsFrom done current rest).all bareComma = True :=
  match rest with
    | [] => allReverseOnto bareComma done [current] doneBare (rewrite currentBare)
    | [next, ..more] =>
      match nextBare: bareComma next with
        | True =>
          match moves: current.kind == Arrow && (!next.trivia.leading.isEmpty || current.trivia.trailing.isSome) with
            | True =>
              let moved := { current |
                trivia = { current.trivia |
                  leading = current.trivia.leading
                    ++ (current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse [])
                    ++ next.trivia.leading,
                  trailing = None
                }
              }
              arrowsFromBare
                [moved, ..done]
                (next.withLeading [])
                more
                (rewrite notCommaBare moved (kindNotComma current Arrow (Bool.andLeft moves) byComputing) then doneBare)
                (withoutLeadingBare next nextBare)
                restBare
            | False => arrowsFromBare [current, ..done] next more (rewrite currentBare then doneBare) nextBare restBare

theorem arrowsBareCommas ∀ (leaves: List Leaf)
    (bare: leaves.all bareComma = True):
    (arrows leaves).all bareComma = True :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] =>
      match firstBare: bareComma first with
        | True => arrowsFromBare [] first rest byComputing firstBare bare

--| Rule 4 gives a comma no comment.
theorem letsFromBare ∀ (behind rest: List Leaf)
    (behindBare: behind.all bareComma = True)
    (restBare: rest.all bareComma = True):
    (letsFrom behind rest).all bareComma = True :=
  match rest with
    | [] => allReverseOnto bareComma behind [] behindBare byComputing
    | [leaf, ..after] =>
      match leafBare: bareComma leaf with
        | True =>
          match leaf.trivia.trailing with
            | None => letsFromBare [leaf, ..behind] after behindBare restBare
            | Some comment =>
              match moves: leaf.kind == ColonEq && letBefore behind 0 && semicolonAfter after 0 with
                | True =>
                  let moved := { leaf |
                    trivia = { leaf.trivia | leading = leaf.trivia.leading ++ [comment.unspaced], trailing = None }
                  }
                  letsFromBare
                    [moved, ..behind]
                    after
                    (rewrite notCommaBare moved (kindNotComma leaf ColonEq (Bool.andLeft moves) byComputing) then
                      behindBare)
                    restBare
                | False => letsFromBare [leaf, ..behind] after behindBare restBare

--| Rule 5 gives a comma no comment.
theorem trimmedBare ∀ (leaves: List Leaf)
    (bare: leaves.all bareComma = True):
    (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })).all bareComma = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      match leafBare: bareComma leaf with
        | True =>
          let trimmedLeaf: bareComma { leaf | trivia = leaf.trivia.trimmed } = True := cases
          rewrite trimmedLeaf then trimmedBare rest bare

--| After rule N no comma holds a comment, so the tree needs no place for
--| one.
theorem settledCommasBare ∀ (lexed: Lexed): lexed.settled.leaves.all bareComma = True :=
  let homed := homeFrom [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  trimmedBare
    (letsFrom [] (arrows commas.leaves))
    (letsFromBare []
      (arrows commas.leaves)
      byComputing
      (arrowsBareCommas commas.leaves (commasFromBare [] None homed lexed.end byComputing)))

-- Under slice 1's alphabet there is no `let` and no `|`, so rule N's
-- clauses for an expression `let`'s `:=` and a record update's bar do
-- nothing.

--| Every leaf's token is in slice 1's alphabet.
def alphabet1 (leaves: List Leaf): Bool := (tokens leaves).all (token => token.kind.within1)

theorem alphabet1Leaves ∀ (leaves: List Leaf)
    (within: alphabet1 leaves = True):
    leaves.all (leaf => leaf.kind.within1) = True :=
  rewrite List.allMapBool leaves (token => token.kind.within1) (leaf => leaf.token) at within then within

--| Rule N keeps slice 1's alphabet, since it keeps the tokens.
theorem settledAlphabet1 ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True):
    alphabet1 lexed.settled.leaves = True :=
  rewrite settledKeepsTokens lexed then within

theorem within1NotLet ∀ (kind: Tok) (within: kind.within1 = True): (kind == KwLet) = False :=
  let checked := Finite.check (kind => !kind.within1 || !(kind == KwLet)) byComputing kind
  Bool.notTrue (kind == KwLet) (rewrite within at checked then checked)

theorem within1NotPipe ∀ (kind: Tok) (within: kind.within1 = True): (kind == Pipe) = False :=
  let checked := Finite.check (kind => !kind.within1 || !(kind == Pipe)) byComputing kind
  Bool.notTrue (kind == Pipe) (rewrite within at checked then checked)

--| Without a `let` behind, no `:=` is an expression `let`'s.
theorem letBeforeNone ∀ (behind: List Leaf) (depth: Nat)
    (noLet: behind.all (leaf => leaf.kind.within1) = True):
    letBefore behind depth = False :=
  match behind with
    | [] => byComputing
    | [leaf, ..earlier] =>
      match within: leaf.kind.within1 with
        | True =>
          match leaf.kind.isCloser with
            | True => letBeforeNone earlier (depth + 1) noLet
            | False =>
              match leaf.kind.isOpener with
                | True => rewrite letBeforeNone earlier (depth - 1) noLet then Bool.andFalse (depth > 0)
                | False =>
                  match depth > 0 with
                    | True => letBeforeNone earlier depth noLet
                    | False =>
                      match isLet: leaf.kind == KwLet with
                        | True => Eq.trans isLet.flipped (within1NotLet leaf.kind within)
                        | False =>
                          match leaf.kind == Semi || leaf.kind == FatArrow || leaf.kind.startsDeclaration with
                            | True => byComputing
                            | False => letBeforeNone earlier depth noLet

--| Under slice 1's alphabet rule 4 does nothing.
theorem letsQuiet1 ∀ (behind rest: List Leaf)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True)
    (restWithin: rest.all (leaf => leaf.kind.within1) = True):
    letsFrom behind rest = behind.reverseOnto rest :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      match within: leaf.kind.within1 with
        | True =>
          let next := letsQuiet1 [leaf, ..behind] after (rewrite within then behindWithin) restWithin
          match leaf.trivia.trailing with
            | None => next
            | Some comment =>
              rewrite letBeforeNone behind 0 behindWithin, Bool.andFalse (leaf.kind == ColonEq) then next

theorem notPipe1 ∀ (leaf: Leaf) (within: leaf.kind.within1 = True): leaf.kind ≠ Pipe :=
  DecEq.soundFalse leaf.kind Pipe (within1NotPipe leaf.kind within)

--| Under slice 1's alphabet rule 1 walks past commas and closers only.
theorem skippedQuiet1 ∀ (leaf: Leaf) (behind ahead: List Leaf)
    (within: leaf.kind.within1 = True):
    skipped leaf behind ahead = (leaf.kind == Comma || leaf.kind.isCloser) :=
  match comma: leaf.kind == Comma with
    | True => rewrite skipped.eq.comma leaf behind ahead (DecEq.sound comma)
    | False => rewrite skipped.eq.alt3 leaf behind ahead (DecEq.soundFalse leaf.kind Comma comma) (notPipe1 leaf within)

--| Under slice 1's alphabet rule 1 moves comments from commas that don't
--| start their lines and from closers only.
theorem movableQuiet1 ∀ (leaf: Leaf) (behind ahead: List Leaf)
    (within: leaf.kind.within1 = True):
    movable leaf behind ahead = ((leaf.kind == Comma && !leaf.token.lineStart) || leaf.kind.isCloser) :=
  match comma: leaf.kind == Comma with
    | True =>
      let isComma := DecEq.sound comma
      rewrite movable.eq.comma leaf behind ahead isComma, isComma, Bool.orFalse
    | False => rewrite movable.eq.alt3 leaf behind ahead (DecEq.soundFalse leaf.kind Comma comma) (notPipe1 leaf within)

--| Under slice 1's alphabet no bar's comment starts the line below.
theorem barsQuiet1 ∀ (leaf: Leaf) (behind ahead: List Leaf)
    (within: leaf.kind.within1 = True):
    barBelow leaf behind ahead = False :=
  rewrite barBelow.eq.alt2 leaf behind ahead (previous tail head tail2 isBehind isAhead => notPipe1 leaf within)

-- Rule 5: a comment's text, trimmed, has no space at its end.

theorem dropSpacesStart ∀ (chars: List Char):
    Text.startsWithChars [' '] (chars.dropWhile (char => char == ' ')) = False :=
  match chars with
    | [] => byComputing
    | [char, ..rest] =>
      match space: char == ' ' with
        | True => dropSpacesStart rest
        | False =>
          let other: Text.sameChar ' ' char = False := calc Text.sameChar ' ' char
            _ = Nat.equal (Char.toNat char) (Char.toNat ' ') := Nat.equalComm (Char.toNat ' ') (Char.toNat char)
            _ = False := space
          rewrite other

--| Trimming twice is trimming once.
theorem trimEndTwice ∀ (text: Text): trimEnd (trimEnd text) = trimEnd text := match spaced: text.endsWith " " with
  | False =>
    let unspaced: Text.startsWithChars [' '] (text.toList.reverseOnto []) = False := spaced
    rewrite unspaced
  | True =>
    let kept := (text.toList.reverseOnto []).dropWhile (char => char == ' ')
    let back: (kept.reverseOnto []).reverseOnto [] = kept := List.reverseReverse kept
    rewrite back, dropSpacesStart (text.toList.reverseOnto [])

def optionText: Option Comment → List Text
  | Some comment => [comment.text]
  | None => []

--| A token's comment texts, own-line ones first.
def triviaTexts (trivia: Trivia): List Text :=
  trivia.leading.map (comment => comment.text) ++ optionText trivia.trailing

def leavesTexts (leaves: List Leaf) (end: Trivia): List Text := match leaves with
  | [] => triviaTexts end
  | [leaf, ..rest] => triviaTexts leaf.trivia ++ leavesTexts rest end

--| The comment texts of a lexed file, in order.
def lexedTexts (lexed: Lexed): List Text := leavesTexts lexed.leaves lexed.end

theorem commentsTrimmed ∀ (comments: List Comment):
    ((comments.map Comment.trimmed).map (comment => comment.text)).map trimEnd
      = (comments.map Comment.trimmed).map (comment => comment.text) :=
  match comments with
    | [] => byComputing
    | [comment, ..rest] => rewrite trimEndTwice comment.text, commentsTrimmed rest

theorem triviaTrimmed ∀ (trivia: Trivia): (triviaTexts trivia.trimmed).map trimEnd = triviaTexts trivia.trimmed :=
  let leading := (trivia.leading.map Comment.trimmed).map (comment => comment.text)
  let trailing: (optionText (trivia.trailing.map Comment.trimmed)).map trimEnd
    = optionText (trivia.trailing.map Comment.trimmed) :=
    match trivia.trailing with
      | None => byComputing
      | Some comment => rewrite trimEndTwice comment.text
  calc (triviaTexts trivia.trimmed).map trimEnd
    _ = leading.map trimEnd ++ (optionText (trivia.trailing.map Comment.trimmed)).map trimEnd :=
      List.mapAppend leading (optionText (trivia.trailing.map Comment.trimmed)) trimEnd
    _ = triviaTexts trivia.trimmed := rewrite commentsTrimmed trivia.leading, trailing

theorem leavesTrimmed ∀ (leaves: List Leaf) (end: Trivia):
    (leavesTexts (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) end.trimmed).map trimEnd
      = leavesTexts (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) end.trimmed :=
  match leaves with
    | [] => triviaTrimmed end
    | [leaf, ..rest] =>
      let others := leavesTexts (rest.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) end.trimmed
      calc (triviaTexts leaf.trivia.trimmed ++ others).map trimEnd
        _ = (triviaTexts leaf.trivia.trimmed).map trimEnd ++ others.map trimEnd :=
          List.mapAppend (triviaTexts leaf.trivia.trimmed) others trimEnd
        _ = triviaTexts leaf.trivia.trimmed ++ others := rewrite triviaTrimmed leaf.trivia, leavesTrimmed rest end

--| After rule N no comment's text ends in a space.
theorem settledTrimmed ∀ (lexed: Lexed): (lexedTexts lexed.settled).map trimEnd = lexedTexts lexed.settled :=
  let homed := homeFrom [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  leavesTrimmed (letsFrom [] (arrows commas.leaves)) commas.end

-- Rule 3: no `->` keeps a comment after it.

--| No `->` that a token follows has a trailing comment, and the token after
--| it has no own-line comments unless it is another `->` (which takes them
--| from the token after it in turn; no file that parses has `-> ->`).
def arrowsBare: List Leaf → Bool
  | [first, next, ..rest] =>
    (!(first.kind == Arrow) || (first.trivia.trailing.isNone && (next.trivia.leading.isEmpty || next.kind == Arrow)))
      && arrowsBare [next, ..rest]
  | _ => True

--| What `arrowsFrom` leaves before its current leaf is the leaves done, in
--| order.
theorem arrowsFromOnto ∀ (done: List Leaf) (current: Leaf) (rest: List Leaf):
    arrowsFrom done current rest = done.reverseOnto (arrowsFrom [] current rest) :=
  match rest with
    | [] => byComputing
    | [next, ..more] =>
      match current.kind == Arrow && (!next.trivia.leading.isEmpty || current.trivia.trailing.isSome) with
        | True =>
          let moved := { current |
            trivia = { current.trivia |
              leading = current.trivia.leading
                ++ (current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse [])
                ++ next.trivia.leading,
              trailing = None
            }
          }
          rewrite arrowsFromOnto [moved, ..done] (next.withLeading []) more,
              arrowsFromOnto [moved] (next.withLeading []) more
        | False => rewrite arrowsFromOnto [current, ..done] next more, arrowsFromOnto [current] next more

theorem emptyOf ∀ (xs: List a) (empty: xs.isEmpty = True): xs = [] := match xs with | [] => byComputing

theorem optionNone ∀ (option: Option a) (none: option.isSome = False): option.isNone = True := match option with
  | None => byComputing

theorem headBare ∀ (next head: Leaf)
    (empty: next.trivia.leading = [])
    (kind: head.kind = next.kind)
    (same: (next.kind == Arrow) = True ∨ head = next):
    (head.trivia.leading.isEmpty || head.kind == Arrow) = True :=
  match same with
    | Inl isArrow => Bool.orRight (rewrite kind then isArrow)
    | Inr isNext => rewrite isNext, empty

--| Rule 3's result is `arrowsBare`, and starts with its first leaf, which
--| changed only if it is an `->`.
--|
--| Proof idea: by induction on the leaves; the leaf after the current one
--| starts the rest's result unchanged unless it is an `->`, so when the
--| current leaf is an `->` the comments rule 3 took from that leaf are the
--| only ones it could have had.
theorem arrowsFromBare1 ∀ (current: Leaf) (rest: List Leaf):
    ∃ (head: Leaf) (tail: List Leaf) => arrowsFrom [] current rest = [head, ..tail]
      ∧ head.kind = current.kind
      ∧ ((current.kind == Arrow) = True ∨ head = current)
      ∧ arrowsBare [head, ..tail] = True :=
  match rest with
    | [] => (current, [], byComputing, byComputing, Inr byComputing, byComputing)
    | [next, ..more] =>
      let moved := { current |
        trivia = { current.trivia |
          leading = current.trivia.leading
            ++ (current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse [])
            ++ next.trivia.leading,
          trailing = None
        }
      }
      match isArrow: current.kind == Arrow with
        | False =>
          let (head, tail, gives, _, _, bare) := arrowsFromBare1 next more
          let result: arrowsFrom [] current [next, ..more] = [current, head, ..tail] :=
            rewrite arrowsFromOnto [current] next more, gives
          (current, [head, ..tail], result, byComputing, Inr byComputing, rewrite isArrow then bare)
        | True =>
          match moves: !next.trivia.leading.isEmpty || current.trivia.trailing.isSome with
            | True =>
              let (head, tail, gives, kind, same, bare) := arrowsFromBare1 (next.withLeading []) more
              let movedBare: arrowsBare [moved, head, ..tail] = True :=
                rewrite isArrow, headBare (next.withLeading []) head byComputing kind same then bare
              (
                moved,
                [head, ..tail],
                (rewrite arrowsFromOnto [moved] (next.withLeading []) more, gives),
                byComputing,
                Inl byComputing,
                movedBare
              )
            | False =>
              let (head, tail, gives, kind, same, bare) := arrowsFromBare1 next more
              let empty := emptyOf next.trivia.leading (Bool.notFalse _ (Bool.orFalseLeft _ _ moves))
              let untrailed := optionNone current.trivia.trailing (Bool.orFalseRight _ _ moves)
              let currentBare: arrowsBare [current, head, ..tail] = True :=
                rewrite isArrow, untrailed, headBare next head empty kind same then bare
              (
                current,
                [head, ..tail],
                (rewrite arrowsFromOnto [current] next more, gives),
                byComputing,
                Inr byComputing,
                currentBare
              )

theorem arrowsArrowsBare ∀ (leaves: List Leaf): arrowsBare (arrows leaves) = True := match leaves with
  | [] => byComputing
  | [first, ..rest] =>
    let (head, tail, gives, _, _, bare) := arrowsFromBare1 first rest
    rewrite gives then bare

theorem trimmedArrowsBare ∀ (leaves: List Leaf)
    (bare: arrowsBare leaves = True):
    arrowsBare (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) = True :=
  match leaves with
    | [] => byComputing
    | [only] => byComputing
    | [first, second, ..rest] =>
      let later := trimmedArrowsBare [second, ..rest] (Bool.andRight bare)
      match first.trivia.trailing, second.trivia.leading with
        | None, [] => rewrite later, Bool.andTrue then Bool.andLeft bare
        | None, [_, .._] => rewrite later, Bool.andTrue then Bool.andLeft bare
        | Some _, [] => rewrite later, Bool.andTrue then Bool.andLeft bare
        | Some _, [_, .._] => rewrite later, Bool.andTrue then Bool.andLeft bare

--| After rule N no `->` holds a trailing comment, and the token after it
--| no own-line comments, unless that token is another `->`.
theorem settledArrowsBare1 ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True):
    arrowsBare lexed.settled.leaves = True :=
  let homed := homeFrom [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  let arrowed := arrows commas.leaves
  let arrowedWithin: alphabet1 arrowed = True := calc alphabet1 arrowed
    _ = alphabet1 lexed.leaves :=
      rewrite arrowsTokens commas.leaves, commasFromTokens [] None homed lexed.end, homeFromTokens [] None lexed.leaves
    _ = True := within
  let quiet: letsFrom [] arrowed = arrowed := letsQuiet1 [] arrowed byComputing (alphabet1Leaves arrowed arrowedWithin)
  trimmedArrowsBare (letsFrom [] arrowed) (rewrite quiet then arrowsArrowsBare commas.leaves)

-- Comments kept in order. Rules 2 to 5 keep them for any leaves; rule 1
-- needs leaves as the lexer gives them.

--| The leaves' comment texts, in order.
def leafTexts: List Leaf → List Text
  | [] => []
  | [leaf, ..rest] => triviaTexts leaf.trivia ++ leafTexts rest

theorem leavesTextsSplit ∀ (leaves: List Leaf) (end: Trivia):
    leavesTexts leaves end = leafTexts leaves ++ triviaTexts end :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      rewrite leavesTextsSplit rest end then
        (List.appendAssoc (triviaTexts leaf.trivia) (leafTexts rest) (triviaTexts end)).flipped

theorem leafTextsReverseOnto ∀ (xs acc: List Leaf):
    leafTexts (xs.reverseOnto acc) = leafTexts (xs.reverseOnto []) ++ leafTexts acc :=
  match xs with
    | [] => byComputing
    | [x, ..rest] =>
      calc leafTexts (rest.reverseOnto [x, ..acc])
        _ = leafTexts (rest.reverseOnto []) ++ (triviaTexts x.trivia ++ leafTexts acc) :=
          leafTextsReverseOnto rest [x, ..acc]
        _ = (leafTexts (rest.reverseOnto []) ++ triviaTexts x.trivia) ++ leafTexts acc :=
          (List.appendAssoc (leafTexts (rest.reverseOnto [])) (triviaTexts x.trivia) (leafTexts acc)).flipped
        _ = leafTexts (rest.reverseOnto [x]) ++ leafTexts acc :=
          rewrite leafTextsReverseOnto rest [x], List.appendNil (triviaTexts x.trivia)

--| One step of a pass that keeps each leaf's comments: the leaf, with the
--| same comment texts, goes on the settled leaves.
theorem consTexts ∀ (x leaf: Leaf) (settled behind after: List Leaf)
    (same: triviaTexts x.trivia = triviaTexts leaf.trivia)
    (sameBehind: leafTexts (settled.reverseOnto []) = leafTexts (behind.reverseOnto [])):
    leafTexts ([x, ..settled].reverseOnto after) = leafTexts (behind.reverseOnto [leaf, ..after]) :=
  calc leafTexts (settled.reverseOnto [x, ..after])
    _ = leafTexts (settled.reverseOnto []) ++ (triviaTexts x.trivia ++ leafTexts after) :=
      leafTextsReverseOnto settled [x, ..after]
    _ = leafTexts (behind.reverseOnto []) ++ (triviaTexts leaf.trivia ++ leafTexts after) := rewrite same, sameBehind
    _ = leafTexts (behind.reverseOnto [leaf, ..after]) := (leafTextsReverseOnto behind [leaf, ..after]).flipped

--| Rule 4 keeps the comments in order.
theorem letsFromTexts ∀ (behind rest: List Leaf):
    leafTexts (letsFrom behind rest) = leafTexts (behind.reverseOnto rest) :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      match leaf.trivia.trailing with
        | None =>
          Eq.trans
            (letsFromTexts [leaf, ..behind] after)
            (consTexts leaf leaf behind behind after byComputing byComputing)
        | Some comment =>
          match leaf.kind == ColonEq && letBefore behind 0 && semicolonAfter after 0 with
            | True =>
              let moved := { leaf |
                trivia = { leaf.trivia | leading = leaf.trivia.leading ++ [comment.unspaced], trailing = None }
              }
              let same: triviaTexts moved.trivia = triviaTexts leaf.trivia :=
                rewrite List.mapAppend leaf.trivia.leading [comment.unspaced] (comment => comment.text), List.appendNil
              Eq.trans
                (letsFromTexts [moved, ..behind] after)
                (consTexts moved leaf behind behind after same byComputing)
            | False =>
              Eq.trans
                (letsFromTexts [leaf, ..behind] after)
                (consTexts leaf leaf behind behind after byComputing byComputing)

theorem arrowMovesTexts ∀ (current next: Leaf) (rest: List Text):
    triviaTexts { current.trivia |
      leading = current.trivia.leading
        ++ (current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse [])
        ++ next.trivia.leading,
      trailing = None
    }
      ++ (triviaTexts (next.withLeading []).trivia ++ rest)
      = triviaTexts current.trivia ++ (triviaTexts next.trivia ++ rest) :=
  match current.trivia.trailing with
    | None => rewrite repeatedly [List.mapAppend, List.appendAssoc, List.appendNil]
    | Some comment => rewrite repeatedly [List.mapAppend, List.appendAssoc]

--| Rule 3 keeps the comments in order.
theorem arrowsFromTexts ∀ (current: Leaf) (rest: List Leaf):
    leafTexts (arrowsFrom [] current rest) = leafTexts [current, ..rest] :=
  match rest with
    | [] => byComputing
    | [next, ..more] =>
      match current.kind == Arrow && (!next.trivia.leading.isEmpty || current.trivia.trailing.isSome) with
        | True =>
          let moved := { current |
            trivia = { current.trivia |
              leading = current.trivia.leading
                ++ (current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse [])
                ++ next.trivia.leading,
              trailing = None
            }
          }
          rewrite arrowsFromOnto [moved] (next.withLeading []) more, arrowsFromTexts (next.withLeading []) more then
            arrowMovesTexts current next (leafTexts more)
        | False => rewrite arrowsFromOnto [current] next more, arrowsFromTexts next more

theorem arrowsTexts ∀ (leaves: List Leaf): leafTexts (arrows leaves) = leafTexts leaves := match leaves with
  | [] => byComputing
  | [first, ..rest] => arrowsFromTexts first rest

def carriedTexts: Option Carried → List Text
  | Some carried => carried.comments.map (comment => comment.text)
  | None => []

theorem intoTexts ∀ (carried: Carried) (trivia: Trivia):
    triviaTexts (carried.into trivia) = carried.comments.map (comment => comment.text) ++ triviaTexts trivia :=
  match trivia.leading with
    | [] => byComputing
    | [first, ..more] => rewrite repeatedly [List.mapAppend, List.appendAssoc]

theorem receivedTexts ∀ (carried: Option Carried) (trivia: Trivia):
    triviaTexts (carried.map (carry => carry.into trivia) |> .getOrElse trivia)
      = carriedTexts carried ++ triviaTexts trivia :=
  match carried with
    | None => byComputing
    | Some carry => intoTexts carry trivia

theorem carriesTexts ∀ (trivia: Trivia) (carry: Carried)
    (carries: commaCarries trivia = Some carry):
    carriedTexts (Some carry) = triviaTexts trivia :=
  match trivia.leading, trivia.trailing with
    | [], Some comment => cases
    | [first, ..more], Some comment =>
      cases then rewrite List.mapAppend more [{ comment | blankLines = trivia.blankLines }] (comment => comment.text)
    | [first, ..more], None => rewrite List.appendNil then cases

--| Rule 2 keeps the comments in order: a comma's go to the token after it.
theorem commasFromTexts ∀ (done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia):
    leafTexts (commasFrom done carried rest end).leaves ++ triviaTexts (commasFrom done carried rest end).end
      = leafTexts (done.reverseOnto []) ++ (carriedTexts carried ++ (leafTexts rest ++ triviaTexts end)) :=
  match rest with
    | [] => rewrite receivedTexts carried end
    | [leaf, ..after] =>
      let received := { leaf | trivia = carried.map (carry => carry.into leaf.trivia) |> .getOrElse leaf.trivia }
      let receivedText: triviaTexts received.trivia = carriedTexts carried ++ triviaTexts leaf.trivia :=
        receivedTexts carried leaf.trivia
      let kept := commasFromTexts [received, ..done] None after end
      let keptText: leafTexts (commasFrom [received, ..done] None after end).leaves
        ++ triviaTexts (commasFrom [received, ..done] None after end).end
        = leafTexts (done.reverseOnto []) ++ (carriedTexts carried ++ (leafTexts [leaf, ..after] ++ triviaTexts end)) :=
        rewrite kept, leafTextsReverseOnto done [received], receivedText then
          rewrite repeatedly [List.appendAssoc, List.appendNil]
      match c: commaCarries received.trivia with
        | None => keptText
        | Some carry =>
          match leaf.kind == Comma with
            | True =>
              let emptied := { received | trivia = Trivia.empty }
              rewrite commasFromTexts [emptied, ..done] (Some carry) after end,
                  leafTextsReverseOnto done [emptied],
                  carriesTexts received.trivia carry c,
                  receivedText then
                rewrite repeatedly [List.appendAssoc]
            | False => keptText

theorem trimmedTriviaTexts ∀ (trivia: Trivia): triviaTexts trivia.trimmed = (triviaTexts trivia).map trimEnd :=
  let leading: (trivia.leading.map Comment.trimmed).map (comment => comment.text)
    = (trivia.leading.map (comment => comment.text)).map trimEnd :=
    rewrite List.mapMap trivia.leading (comment => comment.text) Comment.trimmed,
        List.mapMap trivia.leading trimEnd (comment => comment.text)
  match trivia.trailing with
    | None => rewrite List.mapAppend, leading
    | Some comment => rewrite List.mapAppend, leading

--| Rule 5 trims each comment and keeps them in order.
theorem trimmedTexts ∀ (leaves: List Leaf) (end: Trivia):
    leavesTexts (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) end.trimmed
      = (leavesTexts leaves end).map trimEnd :=
  match leaves with
    | [] => trimmedTriviaTexts end
    | [leaf, ..rest] => rewrite List.mapAppend, trimmedTriviaTexts leaf.trivia, trimmedTexts rest end

--| Rules 2 to 5 keep the comments in order, trimmed: rule N keeps them if
--| rule 1 does.
theorem settledTextsAfterHome ∀ (lexed: Lexed):
    lexedTexts lexed.settled = (leafTexts (homeFrom [] None lexed.leaves) ++ triviaTexts lexed.end).map trimEnd :=
  let homed := homeFrom [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  let arrowed := arrows commas.leaves
  calc lexedTexts lexed.settled
    _ = (leavesTexts (letsFrom [] arrowed) commas.end).map trimEnd := trimmedTexts (letsFrom [] arrowed) commas.end
    _ = (leafTexts (letsFrom [] arrowed) ++ triviaTexts commas.end).map trimEnd :=
      rewrite leavesTextsSplit (letsFrom [] arrowed) commas.end
    _ = (leafTexts commas.leaves ++ triviaTexts commas.end).map trimEnd :=
      rewrite letsFromTexts [] arrowed, arrowsTexts commas.leaves
    _ = (leafTexts homed ++ triviaTexts lexed.end).map trimEnd := rewrite commasFromTexts [] None homed lexed.end

-- Rule 1 keeps the comments in order, for leaves as the lexer gives them
-- under slice 1's alphabet. A trailing comment moves back past commas and
-- closers; the walk must pass no comment and land on a leaf with no
-- trailing comment of its own.

--| Leaves as the lexer lays them out: a leaf with own-line comments
--| starts its line, and so does the leaf after a trailing comment.
--| `pending`: the leaf before had a trailing comment.
def laidOut (pending: Bool) (leaves: List Leaf): Bool := match leaves with
  | [] => True
  | [leaf, ..rest] =>
    (leaf.trivia.leading.isEmpty || leaf.token.lineStart)
      && (!pending || leaf.token.lineStart)
      && laidOut leaf.trivia.trailing.isSome rest

--| A comma or closer: under slice 1's alphabet, what rule 1 walks past.
def passable (leaf: Leaf): Bool := leaf.kind == Comma || leaf.kind.isCloser

--| Rule 1's walk back from `current` (`stepsBack`'s steps) passes no
--| comment: each leaf it passes has no own-line comments, and the leaf
--| before it no trailing comment.
def walkClean (current: Leaf) (behind ahead: List Leaf): Bool := match behind with
  | [] => True
  | [previous, ..earlier] =>
    if !skipped current behind ahead then True
    else if current.token.lineStart
      && (!current.trivia.leading.isEmpty || endsWithComment behind [current, ..ahead]) then
      True
    else
      current.trivia.leading.isEmpty && previous.trivia.trailing.isNone && walkClean previous earlier [current, ..ahead]

--| The `steps` newest leaves of `behind` (`steps` at least 1) hold no
--| comment a moved comment would pass or replace: the newest `steps - 1`
--| are commas or closers with no comments, and the one after has no
--| trailing comment.
def quietFor (steps: Nat) (behind: List Leaf): Bool := match steps, behind with
  | Succ Zero, [target, .._] => target.trivia.trailing.isNone
  | Succ (Succ more), [leaf, ..earlier] =>
    leaf.trivia.leading.isEmpty && leaf.trivia.trailing.isNone && passable leaf && quietFor (Succ more) earlier
  | _, _ => False

--| Where a clean walk ends: it passes no leaf, or `current` has no
--| own-line comments, is a comma or closer, and the leaves it passes are
--| quiet.
--|
--| Proof idea: by induction on `behind`, following `stepsBack` and
--| `walkClean`, which test the same conditions.
theorem walkSteps ∀ (current: Leaf) (behind ahead: List Leaf) (steps: Nat)
    (clean: walkClean current behind ahead = True)
    (within: current.kind.within1 = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True):
    ∃ (passed: Nat) => stepsBack current behind ahead steps = steps + passed
      ∧ (passed = 0 ∨ (current.trivia.leading.isEmpty ∧ passable current ∧ quietFor passed behind)) :=
  match behind with
    | [] => (0, arithmetic, Inl byComputing)
    | [previous, ..earlier] =>
      match skips: skipped current [previous, ..earlier] ahead with
        | False => (0, arithmetic, Inl byComputing)
        | True =>
          match stops: current.token.lineStart
            && (!current.trivia.leading.isEmpty || endsWithComment [previous, ..earlier] [current, ..ahead]) with
            | True => (0, arithmetic, Inl byComputing)
            | False =>
              let leadEmpty := Bool.andLeft clean
              let previousUntrailed := Bool.andLeft (Bool.andRight clean)
              let previousClean := Bool.andRight (Bool.andRight clean)
              let currentPassable: passable current = True :=
                Eq.trans (skippedQuiet1 current [previous, ..earlier] ahead within).flipped skips
              let (passed, walked, quiet) :=
                walkSteps previous earlier
                  [current, ..ahead]
                  (Succ steps)
                  previousClean
                  (Bool.andLeft behindWithin)
                  (Bool.andRight behindWithin)
              let quietHere: quietFor (Succ passed) [previous, ..earlier] = True := match passed, quiet with
                | Zero, _ => previousUntrailed
                | Succ more, Inl zero => cases
                | Succ more, Inr (previousLead, previousPassable, quietEarlier) =>
                  Bool.andIntro previousLead
                    (Bool.andIntro previousUntrailed (Bool.andIntro previousPassable quietEarlier))
              (Succ passed, rewrite walked then arithmetic, Inr (leadEmpty, currentPassable, quietHere))

--| A comment moved back over quiet leaves comes after all their comments.
theorem movedTexts ∀ (behind: List Leaf) (steps: Nat) (comment: Comment)
    (quiet: quietFor steps behind = True):
    leafTexts ((trailingAt behind steps comment).reverseOnto [])
      = leafTexts (behind.reverseOnto []) ++ [comment.text] :=
  match steps, behind with
    | Succ Zero, [target, ..earlier] =>
      match target.trivia.trailing with
        | None =>
          rewrite leafTextsReverseOnto earlier [target.withTrailing (Some comment)],
              leafTextsReverseOnto earlier [target] then
            rewrite repeatedly [List.appendAssoc]
    | Succ (Succ more), [leaf, ..earlier] =>
      match leaf.trivia.leading, leaf.trivia.trailing with
        | [], None =>
          rewrite leafTextsReverseOnto (trailingAt earlier (Succ more) comment) [leaf],
              leafTextsReverseOnto earlier [leaf],
              movedTexts earlier (Succ more) comment (Bool.andRight quiet) then
            rewrite repeatedly [List.appendAssoc, List.appendNil]

--| After a comment moves back, the line still ends with it, seen from the
--| comma or closer it left.
theorem movedEnds ∀ (x: Leaf) (behind ahead: List Leaf) (steps: Nat) (comment: Comment)
    (untrailed: x.trivia.trailing.isNone = True)
    (xPassable: passable x = True)
    (xWithin: x.kind.within1 = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True)
    (quiet: quietFor steps behind = True):
    endsWithComment [x, ..trailingAt behind steps comment] ahead = True :=
  match x.trivia.trailing with
    | None =>
      match steps, behind with
        | Succ Zero, [target, ..earlier] =>
          rewrite skippedQuiet1 x [target.withTrailing (Some comment), ..earlier] ahead xWithin, xPassable
        | Succ (Succ more), [leaf, ..earlier] =>
          rewrite skippedQuiet1 x [leaf, ..trailingAt earlier (Succ more) comment] ahead xWithin, xPassable then
            movedEnds leaf earlier
              [x, ..ahead]
              (Succ more)
              comment
              (Bool.andLeft (Bool.andRight quiet))
              (Bool.andLeft (Bool.andRight (Bool.andRight quiet)))
              (Bool.andLeft behindWithin)
              (Bool.andRight behindWithin)
              (Bool.andRight (Bool.andRight (Bool.andRight quiet)))

--| Rule 1's walk is clean from any next leaf laid out as the lexer lays
--| it out, given whether the leaf before had a trailing comment.
def CleanFor (behind: List Leaf) (pending: Bool): Prop :=
  ∀ (next: Leaf) (ahead: List Leaf) => (next.trivia.leading.isEmpty || next.token.lineStart) = True
    → (!pending || next.token.lineStart) = True
    → walkClean next behind ahead = True

theorem withinOfTokens ∀ (xs ys: List Leaf)
    (same: tokens xs = tokens ys)
    (within: ys.all (leaf => leaf.kind.within1) = True):
    xs.all (leaf => leaf.kind.within1) = True :=
  let viaTokens: (tokens ys).all (token => token.kind.within1) = True :=
    rewrite List.allMapBool ys (token => token.kind.within1) (leaf => leaf.token) then within
  rewrite <- List.allMapBool xs (token => token.kind.within1) (leaf => leaf.token), same then viaTokens

--| A leaf with no trailing comment keeps the walk clean.
theorem cleanUntrailed ∀ (leaf: Leaf) (behind: List Leaf) (pending later: Bool)
    (clean: CleanFor behind pending)
    (laid: (leaf.trivia.leading.isEmpty || leaf.token.lineStart) = True)
    (afterPending: (!pending || leaf.token.lineStart) = True)
    (untrailed: leaf.trivia.trailing.isNone = True):
    CleanFor [leaf, ..behind] later :=
  next ahead nextLaid nextPending =>
    match skipped next [leaf, ..behind] ahead with
      | False => byComputing
      | True =>
        match stops: next.token.lineStart
          && (!next.trivia.leading.isEmpty || endsWithComment [leaf, ..behind] [next, ..ahead]) with
          | True => byComputing
          | False =>
            match next.trivia.leading with
              | [] => Bool.andIntro untrailed (clean leaf [next, ..ahead] laid afterPending)
              | [first, ..more] => Void.impossible (Bool.trueNotFalse (rewrite nextLaid at stops then stops))

--| A leaf with a trailing comment stops every walk from the leaf after it,
--| which starts its line.
theorem cleanTrailed ∀ (leaf: Leaf) (behind: List Leaf)
    (ends: ∀ (ahead: List Leaf) => endsWithComment [leaf, ..behind] ahead = True):
    CleanFor [leaf, ..behind] True :=
  next ahead nextLaid nextPending =>
    match skipped next [leaf, ..behind] ahead with
      | False => byComputing
      | True => rewrite nextPending, ends [next, ..ahead], Bool.orTrue

--| Rule 1 keeps the comments in order, for leaves laid out as the lexer
--| lays them out, under slice 1's alphabet.
--|
--| Proof idea: by induction on the leaves left, keeping `CleanFor`: the
--| walk from the next leaf passes no comment (`walkSteps`), so a comment
--| moved back lands after everything it passes (`movedTexts`); and a leaf
--| that held a trailing comment, kept or moved, stops the walk from the
--| leaf after it, which starts its line (`movedEnds`).
theorem homeFromTexts ∀ (behind rest: List Leaf) (pending: Bool)
    (clean: CleanFor behind pending)
    (laid: laidOut pending rest = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True)
    (restWithin: rest.all (leaf => leaf.kind.within1) = True):
    leafTexts (homeFrom behind None rest) = leafTexts (behind.reverseOnto rest) :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let leafLaid := Bool.andLeft laid
      let leafPending := Bool.andLeft (Bool.andRight laid)
      let afterLaid := Bool.andRight (Bool.andRight laid)
      let within := Bool.andLeft restWithin
      let afterWithin := Bool.andRight restWithin
      let withLeaf: [leaf, ..behind].all (leaf => leaf.kind.within1) = True := rewrite within then behindWithin
      let kept := (later: Bool) (cleanLater: CleanFor [leaf, ..behind] later) (laidLater: laidOut later after = True) =>
        Eq.trans
          (homeFromTexts [leaf, ..behind] after later cleanLater laidLater withLeaf afterWithin)
          (consTexts leaf leaf behind behind after byComputing byComputing)
      match trailing: leaf.trivia.trailing with
        | None => kept False (cleanUntrailed leaf behind pending False clean leafLaid leafPending byComputing) afterLaid
        | Some comment =>
          let trailed := cleanTrailed leaf behind (ahead => byComputing)
          match movable leaf behind after with
            | False => kept True trailed afterLaid
            | True =>
              let (passed, walked, quiet) :=
                walkSteps leaf behind after 0 (clean leaf after leafLaid leafPending) within behindWithin
              rewrite walked then
                match passed, quiet with
                  | Zero, _ => rewrite barsQuiet1 leaf behind after within then kept True trailed afterLaid
                  | Succ more, Inl zero => cases
                  | Succ more, Inr (leadEmpty, leafPassable, quietBehind) =>
                    let moved := leaf.withTrailing None
                    let target := trailingAt behind (Succ more) comment
                    let movedWithin: [moved, ..target].all (leaf => leaf.kind.within1) = True :=
                      rewrite within then
                        withinOfTokens target behind (trailingAtTokens behind (Succ more) comment) behindWithin
                    let movedClean: CleanFor [moved, ..target] True := cleanTrailed moved target (ahead =>
                      movedEnds moved behind ahead
                        (Succ more)
                        comment
                        byComputing
                        leafPassable
                        within
                        behindWithin
                        quietBehind)
                    let empty := emptyOf leaf.trivia.leading leadEmpty
                    calc leafTexts (homeFrom [moved, ..target] None after)
                      _ = leafTexts ([moved, ..target].reverseOnto after) :=
                        homeFromTexts [moved, ..target] after True movedClean afterLaid movedWithin afterWithin
                      _ = leafTexts (target.reverseOnto []) ++ (triviaTexts moved.trivia ++ leafTexts after) :=
                        leafTextsReverseOnto target [moved, ..after]
                      _ = (leafTexts (behind.reverseOnto []) ++ [comment.text])
                          ++ (triviaTexts moved.trivia ++ leafTexts after) :=
                        rewrite movedTexts behind (Succ more) comment quietBehind
                      _ = leafTexts (behind.reverseOnto []) ++ (triviaTexts leaf.trivia ++ leafTexts after) :=
                        rewrite empty, trailing then rewrite repeatedly [List.appendAssoc]
                      _ = leafTexts (behind.reverseOnto [leaf, ..after]) :=
                        (leafTextsReverseOnto behind [leaf, ..after]).flipped

--| Rule N keeps every comment, in order, less the spaces at its end, for
--| leaves laid out as the lexer lays them out, under slice 1's alphabet.
theorem settledKeepsComments ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True)
    (laid: laidOut False lexed.leaves = True):
    lexedTexts lexed.settled = (lexedTexts lexed).map trimEnd :=
  let homed: leafTexts (homeFrom [] None lexed.leaves) = leafTexts lexed.leaves :=
    homeFromTexts [] lexed.leaves False
      (next ahead nextLaid nextPending => byComputing)
      laid
      byComputing
      (alphabet1Leaves lexed.leaves within)
  calc lexedTexts lexed.settled
    _ = (leafTexts (homeFrom [] None lexed.leaves) ++ triviaTexts lexed.end).map trimEnd := settledTextsAfterHome lexed
    _ = (leavesTexts lexed.leaves lexed.end).map trimEnd := rewrite homed, leavesTextsSplit lexed.leaves lexed.end

-- Rule 1's result is homed: a closer keeps a trailing comment only where
-- rule 1 itself would stop it, so it starts its line and has own-line
-- comments or follows code that ends with a comment.

--| `endsWithComment` under slice 1's alphabet, where a bar never comes up.
def endsOn: List Leaf → Bool
  | [] => False
  | [leaf, ..earlier] =>
    if leaf.trivia.trailing.isSome then True
    else if earlier.isEmpty || !passable leaf then False
    else endsOn earlier

theorem endsOnQuiet1 ∀ (line ahead: List Leaf)
    (within: line.all (leaf => leaf.kind.within1) = True):
    endsWithComment line ahead = endsOn line :=
  match line with
    | [] => byComputing
    | [leaf, ..earlier] =>
      match leaf.trivia.trailing.isSome with
        | True => byComputing
        | False =>
          rewrite skippedQuiet1 leaf earlier ahead (Bool.andLeft within),
              endsOnQuiet1 earlier [leaf, ..ahead] (Bool.andRight within)

--| Where rule 1 stops a comment on `leaf`, `older` the leaves before it,
--| newest first.
def stopsAt (leaf: Leaf) (older: List Leaf): Bool :=
  leaf.token.lineStart && (!leaf.trivia.leading.isEmpty || endsOn older)

--| The leaf `steps` back from `current` is where a walk may end: not a
--| comma or closer, the first leaf, or one rule 1 stops on.
def landsAt (steps: Nat) (current: Leaf) (behind: List Leaf): Bool := match steps, behind with
  | Zero, _ => !passable current || behind.isEmpty || stopsAt current behind
  | Succ more, [previous, ..earlier] => landsAt more previous earlier
  | Succ _, [] => False

--| Rule 1's walk ends on a leaf it may end on.
theorem walkLands ∀ (current: Leaf) (behind ahead: List Leaf) (steps: Nat)
    (within: current.kind.within1 = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True):
    ∃ (passed: Nat) => stepsBack current behind ahead steps = steps + passed ∧ landsAt passed current behind = True :=
  match behind with
    | [] => (0, arithmetic, Bool.orRight byComputing)
    | [previous, ..earlier] =>
      let passes: skipped current [previous, ..earlier] ahead = passable current :=
        skippedQuiet1 current [previous, ..earlier] ahead within
      let ends: endsWithComment [previous, ..earlier] [current, ..ahead] = endsOn [previous, ..earlier] :=
        endsOnQuiet1 [previous, ..earlier] [current, ..ahead] behindWithin
      match skips: passable current with
        | False => (0, rewrite passes then arithmetic, rewrite skips)
        | True =>
          match stops: current.token.lineStart
            && (!current.trivia.leading.isEmpty || endsWithComment [previous, ..earlier] [current, ..ahead]) with
            | True =>
              let stopsHere: stopsAt current [previous, ..earlier] = True := rewrite ends at stops then stops
              (0, rewrite passes then arithmetic, rewrite skips, stopsHere)
            | False =>
              let (passed, walked, lands) :=
                walkLands previous earlier
                  [current, ..ahead]
                  (Succ steps)
                  (Bool.andLeft behindWithin)
                  (Bool.andRight behindWithin)
              (Succ passed, rewrite passes, walked then arithmetic, lands)

--| A closer with a trailing comment is one rule 1 stops on, given the
--| leaves before it, newest first; a comma with one starts its line.
def homedLeaf (leaf: Leaf) (older: List Leaf): Bool :=
  leaf.trivia.trailing.isNone
    || ((!leaf.kind.isCloser || older.isEmpty || stopsAt leaf older)
      && (!(leaf.kind == Comma) || older.isEmpty || leaf.token.lineStart))

--| `homedLeaf` of every leaf, newest first.
def homedBehind: List Leaf → Bool
  | [] => True
  | [leaf, ..older] => homedLeaf leaf older && homedBehind older

theorem closerLands ∀ (leaf: Leaf) (rest: Bool)
    (lands: (!passable leaf || rest) = True):
    (!leaf.kind.isCloser || rest) = True :=
  match closer: leaf.kind.isCloser with
    | False => byComputing
    | True => rewrite Bool.orTrue at lands then lands

theorem commaLands ∀ (leaf: Leaf) (older: List Leaf)
    (lands: (!passable leaf || older.isEmpty || stopsAt leaf older) = True):
    (!(leaf.kind == Comma) || older.isEmpty || leaf.token.lineStart) = True :=
  match comma: leaf.kind == Comma with
    | False => byComputing
    | True =>
      match older.isEmpty with
        | True => byComputing
        | False => Bool.andLeft lands

--| Where a walk may end, a comment is homed.
theorem landsHomed ∀ (leaf: Leaf) (older: List Leaf)
    (lands: (!passable leaf || older.isEmpty || stopsAt leaf older) = True):
    homedLeaf leaf older = True :=
  Bool.orRight
    (Bool.andIntro (closerLands leaf (older.isEmpty || stopsAt leaf older) lands) (commaLands leaf older lands))

--| A comment rule 1 can't move is homed: on a comma that starts its line
--| or a leaf that is neither comma nor closer.
theorem fixedHomed ∀ (leaf: Leaf) (behind ahead: List Leaf)
    (within: leaf.kind.within1 = True)
    (fixed: movable leaf behind ahead = False):
    homedLeaf leaf behind = True :=
  let fixed1 := rewrite movableQuiet1 leaf behind ahead within at fixed then fixed
  let notCloser: leaf.kind.isCloser = False := Bool.orFalseRight _ _ fixed1
  let commaStarts := Bool.orFalseLeft _ _ fixed1
  let commaPart: (!(leaf.kind == Comma) || behind.isEmpty || leaf.token.lineStart) = True :=
    match comma: leaf.kind == Comma with
      | False => byComputing
      | True => Bool.orRight (Bool.notFalse _ commaStarts)
  Bool.orRight (Bool.andIntro (rewrite notCloser) commaPart)

--| A comment moved back over quiet leaves to where the walk ends keeps the
--| leaves homed.
theorem trailingAtHomed ∀ (behind: List Leaf) (steps: Nat) (comment: Comment) (current: Leaf)
    (homed: homedBehind behind = True)
    (quiet: quietFor steps behind = True)
    (lands: landsAt steps current behind = True):
    homedBehind (trailingAt behind steps comment) = True :=
  match steps, behind with
    | Succ Zero, [target, ..earlier] =>
      Bool.andIntro (landsHomed (target.withTrailing (Some comment)) earlier lands) (Bool.andRight homed)
    | Succ (Succ more), [leaf, ..earlier] =>
      Bool.andIntro
        (Bool.orLeft (Bool.andLeft (Bool.andRight quiet)))
        (trailingAtHomed earlier
          (Succ more)
          comment
          leaf
          (Bool.andRight homed)
          (Bool.andRight (Bool.andRight (Bool.andRight quiet)))
          lands)

--| Rule 1's result is homed, for leaves laid out as the lexer lays them
--| out, under slice 1's alphabet.
--|
--| Proof idea: by induction on the leaves left, keeping `homedBehind` of
--| the leaves settled: a comment rule 1 keeps or moves ends on a leaf its
--| walk may end on (`walkLands`), the leaves it passes have none
--| (`walkSteps`), and the leaves before the one it lands on don't change.
theorem homeFromHomed ∀ (behind rest: List Leaf) (pending: Bool)
    (clean: CleanFor behind pending)
    (laid: laidOut pending rest = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True)
    (restWithin: rest.all (leaf => leaf.kind.within1) = True)
    (homed: homedBehind behind = True):
    homedBehind ((homeFrom behind None rest).reverseOnto []) = True :=
  match rest with
    | [] => rewrite List.reverseReverse behind then homed
    | [leaf, ..after] =>
      let leafLaid := Bool.andLeft laid
      let leafPending := Bool.andLeft (Bool.andRight laid)
      let afterLaid := Bool.andRight (Bool.andRight laid)
      let within := Bool.andLeft restWithin
      let afterWithin := Bool.andRight restWithin
      let withLeaf: [leaf, ..behind].all (leaf => leaf.kind.within1) = True := rewrite within then behindWithin
      let kept := (later: Bool) (cleanLater: CleanFor [leaf, ..behind] later) (laidLater: laidOut later after
        = True) (homedLater: homedBehind [leaf, ..behind] = True) =>
        homeFromHomed [leaf, ..behind] after later cleanLater laidLater withLeaf afterWithin homedLater
      match trailing: leaf.trivia.trailing with
        | None =>
          kept False (cleanUntrailed leaf behind pending False clean leafLaid leafPending byComputing) afterLaid homed
        | Some comment =>
          let trailed := cleanTrailed leaf behind (ahead => byComputing)
          match fixed: movable leaf behind after with
            | False => kept True trailed afterLaid (Bool.andIntro (fixedHomed leaf behind after within fixed) homed)
            | True =>
              let (passed, walked, quiet) :=
                walkSteps leaf behind after 0 (clean leaf after leafLaid leafPending) within behindWithin
              let (landed, walkedToo, lands) := walkLands leaf behind after 0 within behindWithin
              let same: landed = passed := arithmetic [walked, walkedToo]
              let landsHere := rewrite same at lands then lands
              rewrite walked then
                match passed, quiet with
                  | Zero, _ =>
                    rewrite barsQuiet1 leaf behind after within then
                      kept True trailed afterLaid (Bool.andIntro (landsHomed leaf behind landsHere) homed)
                  | Succ more, Inl zero => cases
                  | Succ more, Inr (leadEmpty, leafPassable, quietBehind) =>
                    let moved := leaf.withTrailing None
                    let target := trailingAt behind (Succ more) comment
                    let movedWithin: [moved, ..target].all (leaf => leaf.kind.within1) = True :=
                      rewrite within then
                        withinOfTokens target behind (trailingAtTokens behind (Succ more) comment) behindWithin
                    let movedClean: CleanFor [moved, ..target] True := cleanTrailed moved target (ahead =>
                      movedEnds moved behind ahead
                        (Succ more)
                        comment
                        byComputing
                        leafPassable
                        within
                        behindWithin
                        quietBehind)
                    homeFromHomed
                      [moved, ..target]
                      after
                      True
                      movedClean
                      afterLaid
                      movedWithin
                      afterWithin
                      (trailingAtHomed behind (Succ more) comment leaf homed quietBehind landsHere)

-- From rule 1's result to rule N's: rules 2 to 5 take comments off commas
-- and `->`, and add own-line comments, so a closer rule 1 stops on still
-- stops, given that no comma that starts its line and no `->` comes just
-- before a comma or closer.

--| A comma or closer, by kind.
def passableKind (kind: Tok): Bool := kind == Comma || kind.isCloser

--| What may not follow `->`: a comma, a closer, or another `->`.
def arrowFollow (kind: Tok): Bool := passableKind kind || kind == Arrow

--| `plain` (spike K1) for slice 1's alphabet, from the second token on:
--| no `->` before a comma, closer or `->`, and no comma that starts its
--| line before a comma or closer.
def plainFrom: List Token → Bool
  | [first, second, ..rest] =>
    (!(first.kind == Arrow) || !arrowFollow second.kind)
      && (!(first.kind == Comma && first.lineStart) || !passableKind second.kind)
      && plainFrom [second, ..rest]
  | _ => True

--| `plain` for slice 1's alphabet: as `plainFrom`, and the first token is
--| no comma or closer. Every file that parses is `plain`.
def plain1 (tokens: List Token): Bool := match tokens with
  | [] => True
  | [first, .._] => !passableKind first.kind && plainFrom tokens

--| `plain1` read newest first.
def backOk: List Token → Bool
  | [newer, older, ..rest] =>
    (!(older.kind == Arrow) || !arrowFollow newer.kind)
      && (!(older.kind == Comma && older.lineStart) || !passableKind newer.kind)
      && backOk [older, ..rest]
  | [only] => !passableKind only.kind
  | [] => True

theorem plainBack ∀ (ahead: List Token) (newest: Token) (behind: List Token)
    (ok: backOk [newest, ..behind] = True)
    (plain: plainFrom [newest, ..ahead] = True):
    backOk (ahead.reverseOnto [newest, ..behind]) = True :=
  match ahead with
    | [] => ok
    | [next, ..rest] =>
      plainBack rest next
        [newest, ..behind]
        (Bool.andIntro (Bool.andLeft plain) (Bool.andIntro (Bool.andLeft (Bool.andRight plain)) ok))
        (Bool.andRight (Bool.andRight plain))

theorem plainReversed ∀ (tokens: List Token) (plain: plain1 tokens = True): backOk (tokens.reverseOnto []) = True :=
  match tokens with
    | [] => byComputing
    | [first, ..rest] => plainBack rest first [] (Bool.andLeft plain) (Bool.andRight plain)

--| How a pass may change a leaf's comments: take a trailing comment away,
--| keeping those of leaves other than commas and `->`, and keep a
--| closer's own-line comments.
def relatedLeaf (before after: Leaf): Bool :=
  (after.trivia.trailing.isNone || before.trivia.trailing.isSome)
    && (before.kind == Comma || before.kind == Arrow || before.trivia.trailing.isNone || after.trivia.trailing.isSome)
    && (!before.kind.isCloser || before.trivia.leading.isEmpty || !after.trivia.leading.isEmpty)

def related: List Leaf → List Leaf → Bool
  | [], [] => True
  | [before, ..befores], [after, ..afters] => relatedLeaf before after && related befores afters
  | _, _ => False

theorem headToken ∀ (before after: Leaf) (befores afters: List Leaf)
    (same: tokens [before, ..befores] = tokens [after, ..afters]):
    after.token = before.token :=
  (Eq.cong (list => list.head.getOrElse before.token) same).flipped

theorem tailTokens ∀ (before after: Leaf) (befores afters: List Leaf)
    (same: tokens [before, ..befores] = tokens [after, ..afters]):
    tokens befores = tokens afters :=
  Eq.cong (list => list.drop 1) same

--| A line that ends with a comment before a rule 2 to 5 pass still does
--| after it, seen from a comma or closer.
--|
--| Proof idea: by induction on the line, newest first. The comment the
--| line ends with is on a leaf the pass keeps it on: not a comma, which
--| would start its line before a comma or closer (or be the first token),
--| nor a `->` before one.
theorem endsTransfer ∀ (befores afters: List Leaf) (newer: Token)
    (same: tokens befores = tokens afters)
    (rel: related befores afters = True)
    (ok: backOk [newer, ..tokens befores] = True)
    (newerPassable: passableKind newer.kind = True)
    (homed: homedBehind befores = True)
    (ends: endsOn befores = True):
    endsOn afters = True :=
  match befores, afters with
    | [before, ..older], [after, ..olders] =>
      let kind := headToken before after older olders same
      match trailing: before.trivia.trailing with
        | Some comment =>
          match comma: before.kind == Comma with
            | True =>
              match older with
                | [] => Void.impossible (Bool.falseNotTrue (Bool.andRight (Bool.andRight ok)))
                | [first, ..rest] =>
                  let starts := Bool.andRight (Bool.andLeft homed)
                  let clause := rewrite starts, newerPassable at Bool.andLeft (Bool.andRight ok)
                  Void.impossible (Bool.falseNotTrue clause)
            | False =>
              match arrow: before.kind == Arrow with
                | True => Void.impossible (Bool.falseNotTrue (rewrite newerPassable at Bool.andLeft ok))
                | False => Bool.orLeft (Bool.andLeft (Bool.andRight (Bool.andLeft rel)))
        | None =>
          match older, olders with
            | [first, ..rest], [next, ..nexts] =>
              match passes: passable before with
                | True =>
                  let untrailed := Bool.andLeft (Bool.andLeft rel)
                  let later :=
                    endsTransfer
                      [first, ..rest]
                      [next, ..nexts]
                      before.token
                      (tailTokens before after [first, ..rest] [next, ..nexts] same)
                      (Bool.andRight rel)
                      (Bool.andRight (Bool.andRight ok))
                      passes
                      homed
                      ends
                  match after.trivia.trailing with
                    | None => rewrite kind, passes then later
            | [first, ..rest], [] => cases

theorem backOkTail ∀ (newer: Token) (older: List Token) (ok: backOk [newer, ..older] = True): backOk older = True :=
  match older with
    | [] => byComputing
    | [_, .._] => Bool.andRight (Bool.andRight ok)

--| A pass that changes comments only as `relatedLeaf` allows keeps the
--| leaves homed.
--|
--| Proof idea: by induction on the leaves, newest first. A trailing
--| comment after the pass was there before; a closer that held one keeps
--| its line start and own-line comments, and the line before it still ends
--| with a comment (`endsTransfer`); a comma that held one still starts its
--| line.
theorem homedTransfer ∀ (befores afters: List Leaf)
    (same: tokens befores = tokens afters)
    (rel: related befores afters = True)
    (ok: backOk (tokens befores) = True)
    (homed: homedBehind befores = True):
    homedBehind afters = True :=
  match befores, afters with
    | [], [] => byComputing
    | [before, ..older], [after, ..olders] =>
      let kind := headToken before after older olders same
      let sameOlder := tailTokens before after older olders same
      let rest :=
        homedTransfer older olders sameOlder
          (Bool.andRight rel)
          (backOkTail before.token (tokens older) ok)
          (Bool.andRight homed)
      let here: homedLeaf after olders = True := match trailing: after.trivia.trailing with
        | None => byComputing
        | Some comment =>
          match before.trivia.trailing with
            | Some kept =>
              let parts := Bool.andLeft homed
              let closerBefore := Bool.andLeft parts
              let commaBefore := Bool.andRight parts
              rewrite kind then
                match older, olders with
                  | [], [] => rewrite repeatedly [Bool.orTrue]
                  | [first, ..others], [next, ..nexts] =>
                    let closerPart: (!before.token.kind.isCloser
                      || ([next, ..nexts].isEmpty
                        || (before.token.lineStart && (!after.trivia.leading.isEmpty || endsOn [next, ..nexts]))))
                      = True :=
                      match closer: before.token.kind.isCloser with
                        | False => byComputing
                        | True =>
                          match before.trivia.leading with
                            | [] =>
                              Bool.andIntro
                                (Bool.andLeft closerBefore)
                                (Bool.orRight
                                  (endsTransfer
                                    [first, ..others]
                                    [next, ..nexts]
                                    before.token
                                    sameOlder
                                    (Bool.andRight rel)
                                    ok
                                    (Bool.orRight closer)
                                    (Bool.andRight homed)
                                    (Bool.andRight closerBefore)))
                            | [_, .._] =>
                              Bool.andIntro (Bool.andLeft closerBefore) (Bool.orLeft (Bool.andRight (Bool.andLeft rel)))
                    Bool.andIntro closerPart commaBefore
      Bool.andIntro here rest

theorem relatedReverseOnto ∀ (befores afters befores2 afters2: List Leaf)
    (rel: related befores afters = True)
    (rel2: related befores2 afters2 = True):
    related (befores.reverseOnto befores2) (afters.reverseOnto afters2) = True :=
  match befores, afters with
    | [], [] => rel2
    | [before, ..rest], [after, ..rests] =>
      relatedReverseOnto rest rests
        [before, ..befores2]
        [after, ..afters2]
        (Bool.andRight rel)
        (Bool.andIntro (Bool.andLeft rel) rel2)

--| A leaf whose trailing comment is kept and whose own-line comments are
--| kept or added to.
theorem relatedKeeping ∀ (leaf: Leaf) (trivia: Trivia)
    (trailing: trivia.trailing = leaf.trivia.trailing)
    (leading: (leaf.trivia.leading.isEmpty || !trivia.leading.isEmpty) = True):
    relatedLeaf leaf { leaf | trivia } = True :=
  let leadingPart := Bool.orRight [a := !leaf.kind.isCloser] leading
  match own: leaf.trivia.trailing with
    | None => rewrite trailing then Bool.andIntro (rewrite repeatedly [Bool.orTrue]) leadingPart
    | Some comment => rewrite trailing then Bool.andIntro (rewrite repeatedly [Bool.orTrue]) leadingPart

theorem appendConsNotEmpty ∀ (xs: List a) (y: a) (ys: List a): (xs ++ [y, ..ys]).isEmpty = False := match xs with
  | [] => byComputing
  | [_, .._] => byComputing

theorem receivedLeading ∀ (carried: Option Carried) (trivia: Trivia):
    (trivia.leading.isEmpty || !(carried.map (carry => carry.into trivia) |> .getOrElse trivia).leading.isEmpty)
      = True :=
  match trivia.leading with
    | [] => byComputing
    | [first, ..more] =>
      match carried with
        | None => byComputing
        | Some carry =>
          rewrite appendConsNotEmpty carry.comments
            { first | blankLines = Nat.max first.blankLines carry.blankLines }
            more

--| Rule 2 only takes comments off commas and adds own-line comments.
theorem commasRelated ∀ (doneBefore done: List Leaf) (carried: Option Carried) (rest: List Leaf) (end: Trivia)
    (rel: related doneBefore done = True):
    related (doneBefore.reverseOnto rest) (commasFrom done carried rest end).leaves = True :=
  match rest with
    | [] => relatedReverseOnto doneBefore done [] [] rel byComputing
    | [leaf, ..after] =>
      let receivedTrivia := carried.map (carry => carry.into leaf.trivia) |> .getOrElse leaf.trivia
      let received := { leaf | trivia = receivedTrivia }
      let receivedTrailing: receivedTrivia.trailing = leaf.trivia.trailing := match carried with
        | None => byComputing
        | Some carry =>
          match leaf.trivia.leading with
            | [] => byComputing
            | [_, .._] => byComputing
      let keep := relatedKeeping leaf receivedTrivia receivedTrailing (receivedLeading carried leaf.trivia)
      match commaCarries received.trivia with
        | None => commasRelated [leaf, ..doneBefore] [received, ..done] None after end (Bool.andIntro keep rel)
        | Some carry =>
          match comma: leaf.kind == Comma with
            | True =>
              let notCloser: leaf.kind.isCloser = False := rewrite DecEq.sound comma
              let emptied: relatedLeaf leaf { received | trivia = Trivia.empty } = True :=
                Bool.andIntro (Bool.orLeft comma) (Bool.orLeft (rewrite notCloser))
              commasRelated
                [leaf, ..doneBefore]
                [{ received | trivia = Trivia.empty }, ..done]
                (Some carry)
                after
                end
                (Bool.andIntro emptied rel)
            | False => commasRelated [leaf, ..doneBefore] [received, ..done] None after end (Bool.andIntro keep rel)

theorem relatedSelf ∀ (leaf: Leaf): relatedLeaf leaf leaf = True :=
  relatedKeeping leaf leaf.trivia byComputing
    (match leaf.trivia.leading with
      | [] => byComputing
      | [_, .._] => byComputing)

theorem relatedCleared ∀ (leaf: Leaf)
    (notCloser: leaf.kind.isCloser = False):
    relatedLeaf leaf (leaf.withLeading []) = True :=
  let leadingPart: (!leaf.kind.isCloser || leaf.trivia.leading.isEmpty || !([]: List Comment).isEmpty) = True :=
    Bool.orLeft (rewrite notCloser)
  match leaf.trivia.trailing with
    | None => Bool.andIntro (rewrite repeatedly [Bool.orTrue]) leadingPart
    | Some comment => Bool.andIntro (rewrite repeatedly [Bool.orTrue]) leadingPart

--| Rule 3 only takes comments off `->` and the own-line comments off the
--| token after it, which is no closer in a `plain` file.
theorem arrowsRelated ∀ (original current: Leaf) (rest: List Leaf)
    (rel: relatedLeaf original current = True)
    (kind: current.token = original.token)
    (plain: plainFrom (tokens [original, ..rest]) = True):
    related [original, ..rest] (arrowsFrom [] current rest) = True :=
  match rest with
    | [] => Bool.andIntro rel byComputing
    | [next, ..more] =>
      match moves: current.kind == Arrow && (!next.trivia.leading.isEmpty || current.trivia.trailing.isSome) with
        | True =>
          let moved := { current |
            trivia = { current.trivia |
              leading = current.trivia.leading
                ++ (current.trivia.trailing.map (comment => [comment.unspaced]) |> .getOrElse [])
                ++ next.trivia.leading,
              trailing = None
            }
          }
          let originalArrow: original.token.kind = Arrow :=
            Eq.trans (Eq.cong (token => token.kind) kind.flipped) (DecEq.sound (Bool.andLeft moves))
          let movedRelated: relatedLeaf original moved = True := rewrite originalArrow
          let follows := rewrite originalArrow at Bool.andLeft plain
          let notFollow := Bool.notTrue _ follows
          let notCloser: next.kind.isCloser = False := Bool.orFalseRight _ _ (Bool.orFalseLeft _ _ notFollow)
          rewrite arrowsFromOnto [moved] (next.withLeading []) more then
            Bool.andIntro movedRelated
              (arrowsRelated next
                (next.withLeading [])
                more
                (relatedCleared next notCloser)
                byComputing
                (Bool.andRight (Bool.andRight plain)))
        | False =>
          rewrite arrowsFromOnto [current] next more then
            Bool.andIntro rel
              (arrowsRelated next next more (relatedSelf next) byComputing (Bool.andRight (Bool.andRight plain)))

--| Rule 5 changes no comment's place.
theorem trimRelated ∀ (leaves: List Leaf):
    related leaves (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })) = True :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] =>
      let here: relatedLeaf leaf { leaf | trivia = leaf.trivia.trimmed } = True := cases
      Bool.andIntro here (trimRelated rest)

theorem tokensReversed ∀ (xs ys: List Leaf)
    (same: tokens xs = tokens ys):
    tokens (xs.reverseOnto []) = tokens (ys.reverseOnto []) :=
  rewrite tokensReverseOnto xs [], tokensReverseOnto ys [], same

theorem backOkOf ∀ (leaves: List Leaf) (original: List Token)
    (same: tokens leaves = original)
    (plain: plain1 original = True):
    backOk (tokens (leaves.reverseOnto [])) = True :=
  rewrite tokensReverseOnto leaves [], same then plainReversed original plain

theorem plainFromOf ∀ (original: List Token) (plain: plain1 original = True): plainFrom original = True :=
  match original with
    | [] => byComputing
    | [_, .._] => Bool.andRight plain

theorem arrowsRelatedAll ∀ (leaves: List Leaf)
    (plain: plainFrom (tokens leaves) = True):
    related leaves (arrows leaves) = True :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] => arrowsRelated first first rest (relatedSelf first) byComputing plain

--| Rule N's result is homed: every closer that keeps a trailing comment
--| starts its line, and has own-line comments or follows code ending with
--| a comment, looking back past commas and closers; every comma that keeps
--| one starts its line. For `plain` leaves laid out as the lexer lays
--| them out, under slice 1's alphabet (K1's `settledHomed`).
--|
--| Proof idea: rule 1's result is homed (`homeFromHomed`), and rules 2,
--| 3 and 5 only take trailing comments off commas and `->`, which in a
--| `plain` file no closer's line ends with, and keep closers' own-line
--| comments (`homedTransfer`); rule 4 does nothing.
theorem settledHomed ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True)
    (laid: laidOut False lexed.leaves = True)
    (plain: plain1 (tokens lexed.leaves) = True):
    homedBehind (lexed.settled.leaves.reverseOnto []) = True :=
  let homed := homeFrom [] None lexed.leaves
  let commas := commasFrom [] None homed lexed.end
  let arrowed := arrows commas.leaves
  let trimmed := arrowed.map (leaf => { leaf | trivia = leaf.trivia.trimmed })
  let leavesWithin := alphabet1Leaves lexed.leaves within
  let homedTokens: tokens homed = tokens lexed.leaves := homeFromTokens [] None lexed.leaves
  let commasTokens: tokens commas.leaves = tokens lexed.leaves :=
    Eq.trans (commasFromTokens [] None homed lexed.end) homedTokens
  let arrowedTokens: tokens arrowed = tokens lexed.leaves := Eq.trans (arrowsTokens commas.leaves) commasTokens
  let trimmedTokens1: tokens trimmed = tokens lexed.leaves := Eq.trans (trimmedTokens arrowed) arrowedTokens
  let homedFirst: homedBehind (homed.reverseOnto []) = True :=
    homeFromHomed [] lexed.leaves False
      (next ahead nextLaid nextPending => byComputing)
      laid
      byComputing
      leavesWithin
      byComputing
  let homedCommas: homedBehind (commas.leaves.reverseOnto []) = True :=
    homedTransfer
      (homed.reverseOnto [])
      (commas.leaves.reverseOnto [])
      (tokensReversed homed commas.leaves (Eq.trans homedTokens commasTokens.flipped))
      (relatedReverseOnto homed commas.leaves [] [] (commasRelated [] [] None homed lexed.end byComputing) byComputing)
      (backOkOf homed (tokens lexed.leaves) homedTokens plain)
      homedFirst
  let homedArrows: homedBehind (arrowed.reverseOnto []) = True :=
    homedTransfer
      (commas.leaves.reverseOnto [])
      (arrowed.reverseOnto [])
      (tokensReversed commas.leaves arrowed (Eq.trans commasTokens arrowedTokens.flipped))
      (relatedReverseOnto commas.leaves arrowed [] []
        (arrowsRelatedAll commas.leaves (rewrite commasTokens then plainFromOf (tokens lexed.leaves) plain))
        byComputing)
      (backOkOf commas.leaves (tokens lexed.leaves) commasTokens plain)
      homedCommas
  let arrowedWithin := withinOfTokens arrowed lexed.leaves (Eq.trans arrowedTokens byComputing) leavesWithin
  let quiet: letsFrom [] arrowed = arrowed := letsQuiet1 [] arrowed byComputing arrowedWithin
  rewrite quiet then
    homedTransfer
      (arrowed.reverseOnto [])
      (trimmed.reverseOnto [])
      (tokensReversed arrowed trimmed (Eq.trans arrowedTokens trimmedTokens1.flipped))
      (relatedReverseOnto arrowed trimmed [] [] (trimRelated arrowed) byComputing)
      (backOkOf arrowed (tokens lexed.leaves) arrowedTokens plain)
      homedArrows

-- Rule N applied to its own result changes nothing.

theorem homedSuffix ∀ (xs behind: List Leaf)
    (homed: homedBehind (xs.reverseOnto behind) = True):
    homedBehind behind = True :=
  match xs with
    | [] => homed
    | [x, ..rest] => Bool.andRight (homedSuffix rest [x, ..behind] homed)

--| A closer rule 1 stops on has its walk end at once.
theorem stepsZero ∀ (leaf: Leaf) (behind ahead: List Leaf)
    (within: leaf.kind.within1 = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True)
    (closer: leaf.kind.isCloser = True)
    (stops: (behind.isEmpty || stopsAt leaf behind) = True):
    stepsBack leaf behind ahead 0 = 0 :=
  match behind with
    | [] => byComputing
    | [previous, ..earlier] =>
      let passes: skipped leaf [previous, ..earlier] ahead = True :=
        rewrite skippedQuiet1 leaf [previous, ..earlier] ahead within then Bool.orRight closer
      rewrite passes, endsOnQuiet1 [previous, ..earlier] [leaf, ..ahead] behindWithin, stops

--| On homed leaves with bare commas rule 1 moves nothing.
theorem homeIdle ∀ (behind rest: List Leaf)
    (homed: homedBehind (rest.reverseOnto behind) = True)
    (bare: rest.all bareComma = True)
    (behindWithin: behind.all (leaf => leaf.kind.within1) = True)
    (within: rest.all (leaf => leaf.kind.within1) = True):
    homeFrom behind None rest = behind.reverseOnto rest :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let leafWithin := Bool.andLeft within
      let next :=
        homeIdle
          [leaf, ..behind]
          after
          homed
          (Bool.andRight bare)
          (rewrite leafWithin then behindWithin)
          (Bool.andRight within)
      match trailing: leaf.trivia.trailing with
        | None => next
        | Some comment =>
          match fixed: movable leaf behind after with
            | False => next
            | True =>
              let here := Bool.andLeft (homedSuffix after [leaf, ..behind] homed)
              let leafBare := Bool.andLeft bare
              let notComma: (leaf.kind == Comma) = False :=
                Bool.notTrue _ (rewrite Bool.andFalse at leafBare then leafBare)
              let closer: leaf.kind.isCloser = True :=
                rewrite movableQuiet1 leaf behind after leafWithin, notComma at fixed then fixed
              let stops := Bool.andLeft (rewrite trailing, closer at here then here)
              rewrite stepsZero leaf behind after leafWithin behindWithin closer stops,
                  barsQuiet1 leaf behind after leafWithin then
                next

--| With every comma bare rule 2 moves nothing.
theorem commasIdle ∀ (done rest: List Leaf) (end: Trivia)
    (bare: rest.all bareComma = True):
    commasFrom done None rest end = { leaves = done.reverseOnto rest, end } :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let next := commasIdle [leaf, ..done] after end (Bool.andRight bare)
      match carries: commaCarries leaf.trivia with
        | None => next
        | Some carry =>
          match comma: leaf.kind == Comma with
            | False => next
            | True =>
              let leafBare := Bool.andLeft bare
              let empty := rewrite Bool.orFalse at leafBare then leafBare
              match leaf.trivia.leading, leaf.trivia.trailing with
                | [], None => cases

--| With no comment after an `->` and no `->` before another, rule 3 moves
--| nothing.
theorem arrowsIdle ∀ (done: List Leaf) (current: Leaf) (rest: List Leaf)
    (bare: arrowsBare [current, ..rest] = True)
    (plain: plainFrom (tokens [current, ..rest]) = True):
    arrowsFrom done current rest = done.reverseOnto [current, ..rest] :=
  match rest with
    | [] => byComputing
    | [next, ..more] =>
      let later := arrowsIdle [current, ..done] next more (Bool.andRight bare) (Bool.andRight (Bool.andRight plain))
      match arrow: current.kind == Arrow with
        | False => later
        | True =>
          let follows := Bool.notTrue _ (Bool.andLeft plain)
          let notArrow: (next.kind == Arrow) = False := Bool.orFalseRight _ _ follows
          let clause := Bool.andLeft bare
          let empty: next.trivia.leading.isEmpty = True :=
            rewrite notArrow, Bool.orFalse at clause then Bool.andRight clause
          match current.trivia.trailing with
            | None => rewrite empty then later

theorem arrowsIdleAll ∀ (leaves: List Leaf)
    (bare: arrowsBare leaves = True)
    (plain: plainFrom (tokens leaves) = True):
    arrows leaves = leaves :=
  match leaves with
    | [] => byComputing
    | [first, ..rest] => arrowsIdle [] first rest bare plain

theorem commentTrimmedTwice ∀ (comment: Comment): comment.trimmed.trimmed = comment.trimmed :=
  rewrite trimEndTwice comment.text

theorem commentsTrimmedTwice ∀ (comments: List Comment):
    (comments.map Comment.trimmed).map Comment.trimmed = comments.map Comment.trimmed :=
  match comments with
    | [] => byComputing
    | [comment, ..rest] => rewrite commentTrimmedTwice comment, commentsTrimmedTwice rest

theorem triviaTrimmedTwice ∀ (trivia: Trivia): trivia.trimmed.trimmed = trivia.trimmed := match trivia.trailing with
  | None => rewrite commentsTrimmedTwice trivia.leading
  | Some comment => rewrite commentsTrimmedTwice trivia.leading, commentTrimmedTwice comment

theorem leavesTrimmedTwice ∀ (leaves: List Leaf):
    (leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed })).map (leaf => { leaf | trivia = leaf.trivia.trimmed })
      = leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed }) :=
  match leaves with
    | [] => byComputing
    | [leaf, ..rest] => rewrite triviaTrimmedTwice leaf.trivia, leavesTrimmedTwice rest

--| Applying rule N to its own result changes nothing, for `plain` leaves
--| laid out as the lexer lays them out, under slice 1's alphabet.
--|
--| Proof idea: rule N's result is homed with bare commas, so rule 1 moves
--| nothing (`homeIdle`); its commas are bare, so rule 2 moves nothing; no
--| `->` keeps a comment and none comes before another, so rule 3 moves
--| nothing; rule 4 does nothing in the alphabet, and trimming twice is
--| trimming once.
theorem settledIdempotent ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True)
    (laid: laidOut False lexed.leaves = True)
    (plain: plain1 (tokens lexed.leaves) = True):
    lexed.settled.settled = lexed.settled :=
  let settled := lexed.settled
  let bare := settledCommasBare lexed
  let settledWithin := alphabet1Leaves settled.leaves (settledAlphabet1 lexed within)
  let homeSame: homeFrom [] None settled.leaves = settled.leaves :=
    homeIdle [] settled.leaves (settledHomed lexed within laid plain) bare byComputing settledWithin
  let commasSame: commasFrom [] None settled.leaves settled.end = { leaves = settled.leaves, end = settled.end } :=
    commasIdle [] settled.leaves settled.end bare
  let plainSettled: plainFrom (tokens settled.leaves) = True :=
    rewrite settledKeepsTokens lexed then plainFromOf (tokens lexed.leaves) plain
  let arrowsSame: arrows settled.leaves = settled.leaves :=
    arrowsIdleAll settled.leaves (settledArrowsBare1 lexed within) plainSettled
  let letsSame: letsFrom [] settled.leaves = settled.leaves := letsQuiet1 [] settled.leaves byComputing settledWithin
  let reached: settled.settled
    = { leaves = settled.leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed }), end = settled.end.trimmed } :=
    rewrite homeSame, commasSame, arrowsSame, letsSame
  let commas := commasFrom [] None (homeFrom [] None lexed.leaves) lexed.end
  calc lexed.settled.settled
    _ = { leaves = settled.leaves.map (leaf => { leaf | trivia = leaf.trivia.trimmed }), end = settled.end.trimmed } :=
      reached
    _ = lexed.settled := rewrite leavesTrimmedTwice (letsFrom [] (arrows commas.leaves)), triviaTrimmedTwice commas.end

-- Rule N's result, written out again in any layout that starts a line at
-- each closer holding a comment, settles to itself (spike K1's
-- `settledAnyLayout`). The layouts are K1's `laidFrom` with `keeping`.

--| Whether the leaf is one rule 1 may leave a trailing comment on only
--| under its limits: a closer or a record update's `|` (K1).
def holder (leaf: Leaf) (behind ahead: List Leaf): Bool := leaf.kind != Comma && skipped leaf behind ahead

--| K1's `laidFrom`: the leaves as the lexer would read them from a text
--| with the same tokens and comments, a line break before each leaf whose
--| choice is `True` and wherever a comment forces one. A trailing comment
--| ends its line, so the lexer finds it on the last of the closers, commas
--| and bars that follow its token on that line. With `keeping`, every
--| `holder` with a trailing comment starts its line too.
def laidFrom (keeping: Bool) (behind: List Leaf) (choices: List Bool) (rest: List Leaf): List Leaf := match rest with
  | [] => behind.reverse
  | [leaf, ..after] =>
    let choice := choices.head.getOrElse False
    let later := choices.drop 1
    match behind with
      | [] => laidFrom keeping [leaf.startingLine True] later after
      | [previous, ..earlier] =>
        let quiet := leaf.trivia.leading.isEmpty && leaf.trivia.trailing.isNone
        let kept := keeping && leaf.trivia.trailing.isSome && holder leaf behind after
        match previous.trivia.trailing with
          | Some comment if quiet && !choice && skipped leaf behind after =>
            let carried := { leaf.startingLine False | trivia = { leaf.trivia | trailing = Some comment } }
            laidFrom keeping [carried, previous.withTrailing None, ..earlier] later after
          | trailing =>
            let lineStart := trailing.isSome || !leaf.trivia.leading.isEmpty || choice || kept
            laidFrom keeping [leaf.startingLine lineStart, ..behind] later after

--| The leaves written out again with K1's keeping layout.
def relaid (lexed: Lexed) (choices: List Bool): Lexed := { lexed | leaves = laidFrom True [] choices lexed.leaves }

--| `laidFrom True` under slice 1's alphabet, read forwards: `current` is
--| the leaf being laid, which may yet pass its trailing comment on.
def relayFrom (current: Leaf) (choices: List Bool) (rest: List Leaf): List Leaf := match rest with
  | [] => [current]
  | [leaf, ..after] =>
    let choice := choices.head.getOrElse False
    let later := choices.drop 1
    let quiet := leaf.trivia.leading.isEmpty && leaf.trivia.trailing.isNone
    let kept := leaf.trivia.trailing.isSome && (leaf.kind != Comma && passable leaf)
    match current.trivia.trailing with
      | Some comment if quiet && !choice && passable leaf =>
        let carried := { leaf.startingLine False | trivia = { leaf.trivia | trailing = Some comment } }
        [current.withTrailing None, ..relayFrom carried later after]
      | trailing =>
        let lineStart := trailing.isSome || !leaf.trivia.leading.isEmpty || choice || kept
        [current, ..relayFrom (leaf.startingLine lineStart) later after]

theorem laidFromOnto ∀ (done: List Leaf) (current: Leaf) (choices: List Bool) (rest: List Leaf)
    (within: rest.all (leaf => leaf.kind.within1) = True):
    laidFrom True [current, ..done] choices rest = done.reverseOnto (relayFrom current choices rest) :=
  match rest with
    | [] => byComputing
    | [leaf, ..after] =>
      let leafWithin := Bool.andLeft within
      let passes := skippedQuiet1 leaf [current, ..done] after leafWithin
      let quiet := leaf.trivia.leading.isEmpty && leaf.trivia.trailing.isNone
      let choice := choices.head.getOrElse False
      let later := choices.drop 1
      match current.trivia.trailing with
        | None =>
          let lineStart :=
            False
              || !leaf.trivia.leading.isEmpty
              || choice
              || (leaf.trivia.trailing.isSome && (leaf.kind != Comma && passable leaf))
          rewrite passes,
              laidFromOnto [current, ..done] (leaf.startingLine lineStart) later after (Bool.andRight within)
        | Some comment =>
          match quiet && !choice && passable leaf with
            | True =>
              let carried := { leaf.startingLine False | trivia = { leaf.trivia | trailing = Some comment } }
              rewrite passes,
                  laidFromOnto [current.withTrailing None, ..done] carried later after (Bool.andRight within)
            | False =>
              let lineStart :=
                True
                  || !leaf.trivia.leading.isEmpty
                  || choice
                  || (leaf.trivia.trailing.isSome && (leaf.kind != Comma && passable leaf))
              rewrite passes,
                  laidFromOnto [current, ..done] (leaf.startingLine lineStart) later after (Bool.andRight within)
