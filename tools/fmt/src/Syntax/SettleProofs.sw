--| Proofs about rule N (`Syntax/Settle.sw`, `Lexed.settled`) for slice 1 of the proved formatter
--| (docs/proposals/self-hosted-fmt-s1-sketch.md, ticket 15).

namespace Syntax.SettleProofs
import Std (Bool, Char, DecEq, Eq, List, Nat, Option, Text)
import Syntax (..)

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
