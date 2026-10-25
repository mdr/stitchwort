-- `Ansi`: colour, bold and reverse video for a frame's lines, as ANSI
-- escape codes (docs/proposals/terminal-io.md §1). They're plain text, so
-- a frame can hold them and a test can `Ansi.strip` them off:
--
--   Terminal.draw ["You see a ${Ansi.colour Red "dragon"}."]
--   Ansi.strip (Ansi.bold "hi") = "hi"
--
-- Each one ends by switching off only what it switched on, so they nest:
-- `Ansi.bold (Ansi.colour Red "!")` is bold and red.

import Ansi.Colour (Black, Red, Green, Yellow, Blue, Magenta, Cyan, White)
import Ansi.Scan (Plain, AfterEscape, InSequence)

-- The eight standard colours. A terminal's theme decides the exact shades.
type Ansi.Colour: Type =
  | Black
  | Red
  | Green
  | Yellow
  | Blue
  | Magenta
  | Cyan
  | White

-- The colour's number in `ESC [3nm`.
def Ansi.colourNumber: Ansi.Colour → Nat
  | Black => 0
  | Red => 1
  | Green => 2
  | Yellow => 3
  | Blue => 4
  | Magenta => 5
  | Cyan => 6
  | White => 7

-- `text` in a colour, then the terminal's own colour again.
def Ansi.colour (colour: Ansi.Colour) (text: Text): Text := "\u{1b}[3${Ansi.colourNumber colour}m${text}\u{1b}[39m"

-- `text` in bold, then normal weight again.
def Ansi.bold (text: Text): Text := "\u{1b}[1m${text}\u{1b}[22m"

-- `text` in reverse video (the colours swapped), then normal again.
def Ansi.reverse (text: Text): Text := "\u{1b}[7m${text}\u{1b}[27m"

-- `text` without its escape codes: every `ESC [`, the parameter bytes after
-- it and its final character (`@` to `~`) are removed. Other text, and an
-- `ESC` not followed by `[`, are kept.
def Ansi.strip (text: Text): Text := Text.fromList (Ansi.stripChars Plain (Text.toList text))

-- Where `stripChars` is: in plain text, just after an `ESC`, or inside an
-- `ESC [` sequence.
type Ansi.Scan: Type =
  | Plain
  | AfterEscape
  | InSequence

def Ansi.stripChars (scan: Ansi.Scan): List Char → List Char
  | [] =>
    match scan with
      | AfterEscape => ['\u{1b}']
      | _ => []
  | [char, ..rest] =>
    match scan with
      | Plain => if char == '\u{1b}' then Ansi.stripChars AfterEscape rest else Cons char (Ansi.stripChars Plain rest)
      | AfterEscape =>
        if char == '[' then Ansi.stripChars InSequence rest
        else if char == '\u{1b}' then Cons '\u{1b}' (Ansi.stripChars AfterEscape rest)
        else Cons '\u{1b}' (Cons char (Ansi.stripChars Plain rest))
      | InSequence =>
        let code := Char.toNat char
        if 64 ≤ code && code ≤ 126 then Ansi.stripChars Plain rest else Ansi.stripChars InSequence rest

test "Ansi: colour" := Ansi.colour Red "@" == "\u{1b}[31m@\u{1b}[39m"
test "Ansi: each colour's number" :=
  List.map [Black, Red, Green, Yellow, Blue, Magenta, Cyan, White] Ansi.colourNumber == [0, 1, 2, 3, 4, 5, 6, 7]
test "Ansi: bold" := Ansi.bold "hi" == "\u{1b}[1mhi\u{1b}[22m"
test "Ansi: reverse" := Ansi.reverse "hi" == "\u{1b}[7mhi\u{1b}[27m"
test "Ansi: strip removes every code" := Ansi.strip "a ${Ansi.bold (Ansi.colour Green "b")} ${Ansi.reverse "c"}!" == "a b c!"
test "Ansi: strip keeps plain text" := Ansi.strip "plain [text]" == "plain [text]"
test "Ansi: strip keeps an ESC that starts no sequence" := Ansi.strip "a\u{1b}b\u{1b}" == "a\u{1b}b\u{1b}"
test "Ansi: strip drops a sequence cut off at the end" := Ansi.strip "a\u{1b}[3" == "a"
test "Ansi: strip removes cursor codes too" := Ansi.strip "\u{1b}[Hone\u{1b}[K\r\ntwo\u{1b}[J" == "one\r\ntwo"
