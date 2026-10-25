-- The four host operations a terminal handler is built on
-- (docs/proposals/terminal-io.md §4.2), used directly: `IO.console`,
-- `IO.keysMode`, `IO.readBytes` and `IO.write`. Checked with `IO.simulate`,
-- which says there's no terminal, ignores keys mode, gives the rest of the
-- input as UTF-8 in one read, and records each `write` as a payload. Piped,
-- `stitchwort run`, `run --reference` and the playground print the same
-- (crates/cli/tests/run_reference.rs, crates/web).

import Std (IO, Console, Char, Nat, Pair, Text)

def showBytes: Option (List Nat) → Text
  | None => "none"
  | Some bytes => Text.join (bytes.map Nat.toText) ','

def textOr: Option Text → Text
  | None => "none"
  | Some line => line

def yesNo (b: Bool): Text := if b then "yes" else "no"

def main(): {IO} () :=
  let console := IO.console()
  IO.print "terminals: ${yesNo console.inputIsTerminal} ${yesNo console.outputIsTerminal}"
  IO.print "size: ${console.columns.toText}x${console.rows.toText}"
  IO.keysMode True
  IO.write "drawn, "
  IO.write "no line ending"
  IO.keysMode False
  IO.print ""
  IO.print (textOr IO.readLine())
  IO.print (showBytes IO.readBytes())
  IO.print (showBytes IO.readBytes())
  IO.print (textOr IO.readLine())

def transcript (input: List Text): List Text := Pair.fst (IO.simulate input main)

test "what main does under IO.simulate" :=
  transcript ["first", "hé", "x"] == [
    "terminals: no no",
    "size: 0x0",
    "drawn, ",
    "no line ending",
    "",
    "first",
    "104,195,169,10,120,10",
    "none",
    "none"
  ]

test "with no input, readBytes gives None" :=
  transcript [] == ["terminals: no no", "size: 0x0", "drawn, ", "no line ending", "", "none", "none", "none", "none"]

-- `IO.simulate`'s clauses one at a time.

def console(): {IO} Console := IO.console()

test "console: no terminals, size unknown" :=
  let c := Pair.snd (IO.simulate ["a"] console)
  !c.inputIsTerminal && !c.outputIsTerminal && c.columns == 0 && c.rows == 0

def keysThenRead(): {IO} Option Text :=
  IO.keysMode True
  IO.keysMode False
  IO.readLine()

test "keysMode does nothing" :=
  IO.simulate ["a"] keysThenRead == MkPair [] (Some "a")

def bytesThenLine(): {IO} (Option (List Nat), Option Text, Text) :=
  let bytes := IO.readBytes()
  let line := IO.readLine()
  let rest := IO.readAll()
  (bytes, line, rest)

test "readBytes takes the rest of the input, each line ending in LF" :=
  Pair.snd (IO.simulate ["ab", ""] bytesThenLine) == (Some [97, 98, 10, 10], None, "")

def lineThenBytes(): {IO} (Option Text, Option (List Nat)) :=
  let line := IO.readLine()
  let bytes := IO.readBytes()
  (line, bytes)

test "readBytes after readLine takes what's left" :=
  Pair.snd (IO.simulate ["a", "b"] lineThenBytes) == (Some "a", Some [98, 10])

test "readBytes at the end is None" :=
  Pair.snd (IO.simulate ["a"] lineThenBytes) == (Some "a", None)

def writes(): {IO} () :=
  IO.write "a"
  IO.print "b"
  IO.write "c\nd"

test "write records one payload each, in order with print" :=
  Pair.fst (IO.simulate [] writes) == ["a", "b", "c\nd"]

-- `Char.utf8`

test "UTF-8 of one to four bytes" :=
  Char.utf8 'a' == [97] && Char.utf8 'é' == [195, 169] && Char.utf8 '€' == [226, 130, 172] && Char.utf8 '😀' == [240, 159, 152, 128]

test "UTF-8 at the edges of each length" :=
  Char.utf8 '\u{7F}' == [127] && Char.utf8 '\u{80}' == [194, 128] && Char.utf8 '\u{7FF}' == [223, 191] && Char.utf8 '\u{800}' == [224, 160, 128] && Char.utf8 '\u{FFFF}' == [239, 191, 191] && Char.utf8 '\u{10000}' == [240, 144, 128, 128] && Char.utf8 '\u{10FFFF}' == [244, 143, 191, 191]
