--| `printedHangs` from fewer facts (ticket 18h): of `DeclHangs`' facts, the tokens' trailing comments come from `sound`
--| and the name's kind and spelling from `within1`, so `printedHangs1` asks, beyond the four tree facts, only what
--| `DeclElements` names: no own-line comments above the `:` and the `:=`, and the type's and the value's element facts.
--|
--| Neither is a consequence of the tree facts. A `:` or `:=` may have comments above it in slice 1 (`def x\n  -- c\n
--| : T := a` formats as it stands), and so may the type's or the value's first token, where `ElHangs`' `wordStart`
--| is the wrong start: such a token starts a line of its own even where the element is entered mid-line (NOTES,
--| SW-4045).

namespace Fmt.DeclFactsProofs
import Std (Bool, Char, DecEq, Doc, Eq, List, Nat, Option, Result, Text, Void)
import Std.Doc.Proofs (IsComment, isLayout)
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Header, Lexed, Tok, Word, lex)
import Fmt (..)
import Fmt.HangProofs (ElHangs, TrailsComment, wordStart)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (
  lexKind,
  lexKindOfSpells,
  spellsNotComment,
  spellsNotLayout,
  spellsOfText1,
  spellsQuiet,
  wordQuiet
)
import Fmt.DeclHangProofs (BodyLays, DeclHangs, WordToken, atomDecl, atomDeclHangs, declStart, printedHangs)

-- Trailing comments, from `sound`.

--| Characters with no line break after the first have none after it either.
theorem freeTail ∀ (char: Char) (rest: List Char)
    (free: Text.containsChars ['\n'] [char, ..rest] = False):
    Text.containsChars ['\n'] rest = False :=
  match later: Text.containsChars ['\n'] rest with
    | True =>
      let found := Text.containsCharsCons ['\n'] char rest later
      (Bool.falseNotTrue (Eq.trans free.flipped found)).impossible
    | False => byComputing

--| Characters with no line break among them are each other than one.
theorem withoutNewline ∀ (chars: List Char)
    (free: Text.containsChars ['\n'] chars = False):
    chars.all (char => char != '\n') = True :=
  match chars with
    | [] => byComputing
    | [char, ..rest] =>
      let later := withoutNewline rest (freeTail char rest free)
      match equal: char == '\n' with
        | True =>
          let is: char = '\n' := DecEq.sound equal
          let found: Text.containsChars ['\n'] [char, ..rest] = True := rewrite is
          (Bool.falseNotTrue (Eq.trans free.flipped found)).impossible
        | False => later

--| Characters that start with `--` and have no line break are a comment's.
theorem dashed ∀ (chars: List Char)
    (starts: Text.startsWithChars ['-', '-'] chars = True)
    (free: Text.containsChars ['\n'] chars = False):
    ∃ (others: List Char) => chars = ['-', '-', ..others] ∧ others.all (char => char != '\n') = True :=
  match chars, starts with
    | [first, second, ..others], starts =>
      let whole := withoutNewline [first, second, ..others] free
      match one: Text.sameChar '-' first with
        | True =>
          match two: Text.sameChar '-' second with
            | True =>
              let isFirst: '-' = first := DecEq.sound (rewrite Text.sameCharEq '-' first at one then one)
              let isSecond: '-' = second := DecEq.sound (rewrite Text.sameCharEq '-' second at two then two)
              rewrite <- isFirst, <- isSecond then (others, byComputing, Bool.andRight (Bool.andRight whole))
    | [], never => cases
    | [_], never => cases

--| A comment as rule N leaves it is one the lexer reads as a comment, and no layout.
theorem commentIs ∀ (text: Text) (comment: commentText text = True): IsComment text ∧ isLayout text = False :=
  let starts: Text.startsWithChars ['-', '-'] text.toList = True := Bool.andLeft comment
  let free: Text.containsChars ['\n'] text.toList = False := Bool.notTrue _ (Bool.andLeft (Bool.andRight comment))
  (dashed text.toList starts free, commentNotLayout text comment)

--| A token whose trailing comment is as rule N leaves it trails one the lexer reads as a comment.
theorem trailsOfSound ∀ (word: Word) (sound: word.sound = True): TrailsComment word :=
  let after: afterSound word.comments.after = True := Bool.andRight (Bool.andRight sound)
  match word, after with
    | { text, comments = { above, after = Some comment, blankBefore } }, after => commentIs comment after
    | { text, comments = { above, after = None, blankBefore } }, _ => byComputing

-- The name, from `within1`.

--| A header's name, as `within1` spells it, is a plain token of the lexer's `Lower` kind.
theorem nameFacts ∀ (name: Word)
    (within: name.nameWithin1 = True):
    Fmt.HangProofs.Plain (lexKind name.text) ∧ WordToken name.text :=
  let spells := spellsOfText1 Lower name.text (Bool.andRight within)
  let (comma, closer) := spellsQuiet Lower name.text spells (wordQuiet Lower byComputing)
  (
    rewrite lexKindOfSpells Lower name.text spells then
      (byComputing, byComputing, byComputing, byComputing, byComputing, byComputing),
    (spellsNotComment Lower name.text spells, spellsNotLayout Lower name.text spells, closer, comma)
  )

-- The declaration.

--| What `printedHangs1` asks of a slice 1 declaration beyond the four tree facts: no own-line comments above the `:`
--| and the `:=`, the type's `ElHangs` at 4 and the value's `BodyLays`. Not a consequence of the tree facts: each
--| fails for some slice 1 declaration (NOTES, SW-4045).
def DeclElements (kinds: Text → Tok): Decl → Prop
  | Definition [] header (Assigned colonEq value) =>
    header.name.comments.above = []
      ∧ header.colon.above = []
      ∧ colonEq.above = []
      ∧ (∃ (trails: Bool) => ElHangs kinds
        (header.result.el (declStart.next header.colon.after.isSome 3))
        4
        4
        header.colon.after.isSome
        trails
        wordStart)
      ∧ BodyLays kinds value (declStart.next colonEq.after.isSome (4 + header.result.size)) colonEq.after.isSome
  | _ => False

--| `DeclHangs` from the tree facts and `DeclElements`: the trailing comments from `sound` (`trailsOfSound`), the
--| name's kind and spelling from `within1` (`nameFacts`).
theorem declHangsOf ∀ (decl: Decl)
    (within: decl.within1 = True)
    (sound: decl.sound = True)
    (elements: DeclElements lexKind decl):
    DeclHangs lexKind decl :=
  match decl, elements with
    | Definition [] header (Assigned colonEq value), (nameBare, colonBare, assignBare, typed, body) =>
      match header with
        | {
            exportKeyword = None,
            opaqueKeyword = None,
            kind = DefPlain,
            keyword,
            name,
            forallKeyword = None,
            params = [],
            colon,
            result,
            decreasingClause = None,
            unfoldingClause = None
          } =>
          let (plain, token) := nameFacts name (Bool.andLeft (Bool.andLeft within))
          let (keywordSound, rest) := (Bool.andLeft sound, Bool.andRight sound)
          let nameSound := Bool.andLeft rest
          let colonSound := Bool.andLeft (Bool.andRight rest)
          let assignSound := Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight rest)))
          (
            trailsOfSound (fixedWord "def" keyword) keywordSound,
            plain,
            token,
            nameBare,
            trailsOfSound name nameSound,
            colonBare,
            trailsOfSound (fixedWord ":" colon) colonSound,
            assignBare,
            trailsOfSound (fixedWord ":=" colonEq) assignSound,
            typed,
            body
          )

--| `printedHangs` from the four tree facts `printLexes1Tree` takes and `DeclElements`: the text the rules print for a
--| slice 1 declaration, at any width, lexes to leaves whose fold never breaks.
theorem printedHangs1 ∀ (decl: Decl) (doc: Doc) (width: Nat)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical1 = True)
    (elements: DeclElements lexKind decl)
    (shows: decl.doc1 = Some doc) (lexed: Lexed)
    (read: lex (Doc.print doc width) = Ok lexed):
    hangs lexed.leaves = True :=
  printedHangs decl doc width within shaped sound lexical (declHangsOf decl within sound elements) shows lexed read

--| `def d: A := b` meets `DeclElements`, so `printedHangs1` applies.
theorem atomDeclElements: DeclElements lexKind atomDecl :=
  let (_, _, _, _, _, _, _, _, _, typed, body) := atomDeclHangs
  (byComputing, byComputing, byComputing, typed, body)
