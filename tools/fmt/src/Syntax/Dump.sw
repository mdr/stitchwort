--| The token dump, in the form of `stitchwort dev tokens`
--| (`stitchwort_fmt::tidy::token_dump`): one line a token after comment placement, its
--| kind, its text quoted as Rust's `{:?}` quotes it, its column, whether it
--| starts its line, the blank lines before it, its own-line comments
--| (column, blank lines before, text) and its trailing comment; then a line
--| for the end of the file.

namespace Syntax
import Std (Bool, Char, List, Nat, Option, Text)

def Comment.dump (comment: Comment): Text := "${comment.column}:${comment.blankLines}:${quoted comment.text}"

def Trivia.dumpLeading (trivia: Trivia): Text := trivia.leading.map Comment.dump |> .joinWith " "

def Leaf.dump (leaf: Leaf): Text :=
  let token := leaf.token
  let trailing := leaf.trivia.trailing.map Comment.dump |> .getOrElse "none"
  "${token.kind.name} ${quoted token.text} col=${token.column} line_start=${rustBool token.lineStart} blank=${leaf.trivia.blankLines} leading=[${leaf.trivia.dumpLeading}] trailing=${trailing}\n"

--| `true` or `false`, as Rust writes a `bool`.
def rustBool (value: Bool): Text := if value then "true" else "false"

def Lexed.dump (lexed: Lexed): Text :=
  let lines := lexed.leaves.map Leaf.dump |> Text.concat
  "${lines}EOF blank=${lexed.end.blankLines} leading=[${lexed.end.dumpLeading}]\n"

-- Rust's `{:?}` for a `str`.

--| The text in double quotes, escaped as Rust's `Debug` escapes a `str`.
def quoted (text: Text): Text :=
  if text.all (char => 32 <= char.toNat && char.toNat < 127 && char != '"' && char != '\\') then "\"${text}\""
  else "\"${text.toList.map debugEscaped |> Text.concat}\""

--| One character as Rust's `Debug` for a `str` writes it.
def debugEscaped (char: Char): Text := match char with
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | _ =>
    let code := char.toNat
    if code == 0 then "\\0"
    else if code < 32 || code == 127 || (code >= 128 && escapedAbove code) then "\\u{${lowerHex code}}"
    else Text.fromList [char]

--| Whether Rust's `Debug` escapes a character above ASCII: those that
--| aren't printable (controls, format characters, separators, spaces other
--| than U+0020, private use) and those that extend a grapheme. An
--| approximation of Rust's tables, covering the blocks that turn up in
--| source text.
def escapedAbove (code: Nat): Bool :=
  within code 128 160
    || code == 173
    || within code 768 880
    || within code 1536 1542
    || code == 1564
    || code == 1757
    || code == 1807
    || code == 5760
    || code == 6158
    || within code 6832 6912
    || within code 7616 7680
    || within code 8192 8208
    || within code 8232 8240
    || within code 8287 8304
    || within code 8400 8448
    || code == 12288
    || within code 57344 63744
    || within code 65024 65040
    || within code 65056 65072
    || code == 65279
    || within code 65529 65532
    || within code 917504 918000

def within (code low high: Nat): Bool := low <= code && code < high

-- Numbers in hexadecimal.

def hexDigit (digit: Nat) (upper: Bool): Char :=
  let chars := if upper then "0123456789ABCDEF" else "0123456789abcdef"
  chars.getOr digit '0'

--| The digits of `n` in base 16 in front of `found`; `fuel` keeps it
--| structural, and `n + 1` is always enough.
def hexDigits (fuel n: Nat) (upper: Bool) (found: List Char): List Char := match fuel with
  | Zero => found
  | Succ more =>
    let digits := [hexDigit (n % 16) upper, ..found]
    if n < 16 then digits else hexDigits more (n / 16) upper digits

def lowerHex (n: Nat): Text := Text.fromList (hexDigits (n + 1) n False [])

def upperHex (n: Nat): Text := Text.fromList (hexDigits (n + 1) n True [])

-- How a lexical error names a character.

--| A character for a message: in backticks, or by its code point (at least
--| four digits) and name if it would show as nothing or as a plain space.
def shown (char: Char): Text := match invisibleName char.toNat with
  | Some name =>
    let code := upperHex char.toNat |> .padLeft 4 '0'
    if name.isEmpty then "U+${code}" else "U+${code} ${name}"
  | None => "`${Text.fromList [char]}`"

--| The Unicode name of a character that shows as nothing or as a space
--| (empty when the Rust lexer's table has none), as `crates/syntax`'s
--| `invisible` gives it.
def invisibleName (code: Nat): Option Text := match namedInvisible code with
  | Some name => Some name
  | None =>
    if within code 8289 8293
      || code == 1564
      || within code 8234 8239
      || within code 8294 8298
      || within code 65529 65532
      || code == 917505
      || within code 917536 917632
      || code < 32
      || within code 127 160 then
      Some ""
    else None

def namedInvisible (code: Nat): Option Text := match code with
  | 160 => Some "NO-BREAK SPACE"
  | 5760 => Some "OGHAM SPACE MARK"
  | 8192 => Some "EN QUAD"
  | 8193 => Some "EM QUAD"
  | 8194 => Some "EN SPACE"
  | 8195 => Some "EM SPACE"
  | 8196 => Some "THREE-PER-EM SPACE"
  | 8197 => Some "FOUR-PER-EM SPACE"
  | 8198 => Some "SIX-PER-EM SPACE"
  | 8199 => Some "FIGURE SPACE"
  | 8200 => Some "PUNCTUATION SPACE"
  | 8201 => Some "THIN SPACE"
  | 8202 => Some "HAIR SPACE"
  | 8239 => Some "NARROW NO-BREAK SPACE"
  | 8287 => Some "MEDIUM MATHEMATICAL SPACE"
  | 12288 => Some "IDEOGRAPHIC SPACE"
  | 173 => Some "SOFT HYPHEN"
  | 847 => Some "COMBINING GRAPHEME JOINER"
  | 6158 => Some "MONGOLIAN VOWEL SEPARATOR"
  | 8203 => Some "ZERO WIDTH SPACE"
  | 8204 => Some "ZERO WIDTH NON-JOINER"
  | 8205 => Some "ZERO WIDTH JOINER"
  | 8206 => Some "LEFT-TO-RIGHT MARK"
  | 8207 => Some "RIGHT-TO-LEFT MARK"
  | 8288 => Some "WORD JOINER"
  | 65279 => Some "ZERO WIDTH NO-BREAK SPACE (byte-order mark)"
  | 8232 => Some "LINE SEPARATOR"
  | 8233 => Some "PARAGRAPH SEPARATOR"
  | _ => None
