-- The parser keeps the puzzle's promise (D2108): every character of the
-- input is one of the eight brackets. If `parseLines` reads `input` as
-- `lines`, the tokens of each line, written back as characters, are that
-- line of the input exactly: nothing dropped, added or changed. The
-- answers' theorems hold for every list of token lines, so they need
-- nothing more from the parser.

namespace Aoc.Year2021.Day10.Proofs
import Aoc.Year2021.Day10 (..)
import Std (Eq, Fail, List, Option, Result, Text, Void)

-- What `parseLines` reads is the input, line by line and character by
-- character.
theorem parseReadsLines (input: Text) (lines: List (List Token)) (parsed: Fail.toResult (() => parseLines input) = Ok lines):
    lines.map (tokens => tokens.map Token.char) = input.lines.map Text.toList :=
  let rows := rewrite Fail.toResultMap _ (input.lines.withIndex) at parsed in parsed
  let same := traverseMap _ (tokens => tokens.map Token.char) (row => row.snd.toList) (input.lines.withIndex) lines rows (entry tokens read => match entry with | (row, line) => lineRead row line tokens read)
  rewrite same in mapSndWithIndex Text.toList 0 input.lines

-- One line: its tokens are its characters.
theorem lineRead (row: Nat) (line: Text) (tokens: List Token)
    (read: Fail.toResult (() => line.toList.withIndex.map (((column, char)) =>
      Fail.need (tokenOf char) "line ${row + 1}, column ${column + 1}: expected a bracket, got '${char}'")) = Ok tokens):
    tokens.map Token.char = line.toList :=
  let chars := rewrite Fail.toResultMap _ (line.toList.withIndex) at read in read
  let same := traverseMap _ Token.char Pair.snd (line.toList.withIndex) tokens chars (entry token found => match entry with | (column, char) => charRead _ char token (rewrite Fail.toResultNeed _ (tokenOf char) at found in found))
  rewrite same, mapSndWithIndex (char => char) 0 line.toList in List.mapId line.toList

-- A character the parser reads as a token is that token's character.
theorem charRead (msg: Text) (char: Char) (token: Token) (found: Option.toResult (tokenOf char) msg = Ok token): token.char = char :=
  match e: tokenOf char with
    | None => Void.exfalso (Result.errNotOk _ token found)
    | Some read => rewrite <- Result.okInjective read token found in tokenOfChar char read e

-- `tokenOf` gives a token only for that token's character.
theorem tokenOfChar (char: Char) (token: Token) (h: tokenOf char = Some token): token.char = char :=
  match char with
    | '(' => rewrite <- Option.someInjective _ token h in rfl
    | '[' => rewrite <- Option.someInjective _ token h in rfl
    | '{' => rewrite <- Option.someInjective _ token h in rfl
    | '<' => rewrite <- Option.someInjective _ token h in rfl
    | ')' => rewrite <- Option.someInjective _ token h in rfl
    | ']' => rewrite <- Option.someInjective _ token h in rfl
    | '}' => rewrite <- Option.someInjective _ token h in rfl
    | '>' => rewrite <- Option.someInjective _ token h in rfl
    | _ => cases

-- A `traverse` that gave `Ok`, mapped: each value's `g` is its input's `h`.
theorem traverseMap (f: a → Result b e) (g: b → c) (h: a → c):
    (xs: List a) → (ys: List b) → Result.traverse xs f = Ok ys → ((x: a) → (y: b) → f x = Ok y → g y = h x) → ys.map g = xs.map h
  | Nil, ys, done, each => rewrite <- Result.okInjective Nil ys done in rfl
  | Cons x rest, ys, done, each =>
    Result.flatMapEqOk (f x) (y => Result.map (Result.traverse rest f) (Cons y)) ys (rewrite Result.traverseCons f x rest at done in done)
      (y first later =>
        match e: Result.traverse rest f with
          | Err m => Void.exfalso (Result.errNotOk m ys later)
          | Ok zs =>
            rewrite <- Result.okInjective (Cons y zs) ys later, each x y first, traverseMap f g h rest zs e each in rfl)

-- Numbering a list and dropping the numbers again changes nothing.
theorem mapSndWithIndex (f: a → c): (start: Nat) → (xs: List a) → (List.withIndexFrom start xs).map (entry => f entry.snd) = xs.map f
  | start, Nil => rfl
  | start, Cons x rest => rewrite mapSndWithIndex f (Succ start) rest in rfl
