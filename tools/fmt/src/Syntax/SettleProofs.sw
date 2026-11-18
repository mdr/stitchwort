--| Proofs about rule N (`Syntax/Settle.sw`, `Lexed.settled`) for slice 1 of the proved formatter
--| (docs/proposals/self-hosted-fmt-s1-sketch.md, ticket 15).

namespace Syntax.SettleProofs
import Std (Bool, Char, Eq, List, Nat, Option, Text)
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
