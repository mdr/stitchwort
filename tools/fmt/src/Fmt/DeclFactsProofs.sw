--| `printedHangs` from fewer facts (ticket 18h): of `DeclHangs`' facts, the tokens' trailing comments come from `sound`,
--| their own-line comments (above the name, the `:` and the `:=`, which the printer keeps there) too, and the name's
--| kind and spelling from `within1`, so `printedHangs1` asks, beyond the four tree facts, only what `DeclElements`
--| names: the type's and the value's element facts.
--|
--| Those are not a consequence of the tree facts: the type's or the value's first token may have comments above it,
--| and then `ElHangs`' `wordStart` is the wrong start: such a token starts a line of its own even where the element
--| is entered mid-line (NOTES, SW-4045).
--|
--| For a declaration whose type and value are quiet (`DeclQuiet`, `Expr.quiet1`), `DeclElements` follows
--| (`quietElements`, from `quietExprFacts` and the call hug's `quietHug`), so `printedHangs1Quiet` asks only the four
--| tree facts and that.

namespace Fmt.DeclFactsProofs
import Std (Bool, Char, DecEq, Doc, Eq, List, Nat, Option, Result, Text, Void)
import Std.Doc.Proofs (IsComment, isLayout)
import Syntax (BindingKind, Comments, Decl, DefBody, DefKind, Expr, Header, Lexed, Note, Tok, Word, lex)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.AppHangProofs (..)
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
import Fmt.DeclHangProofs (
  BodyLays,
  DeclHangs,
  OnLine,
  WordToken,
  atomDecl,
  atomDeclHangs,
  declStart,
  plainBody,
  printedHangs
)
import Fmt.ExprHangProofs (..)
import Fmt.QuietKeyProofs (quietExprFacts, quietKeys)

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

--| Own-line comments as rule N leaves them are ones the lexer reads as comments, and no layout.
theorem notesOfSound ∀ (notes: List Note) (sound: notesSound notes = True): NotesComment notes := match notes with
  | [] => byComputing
  | [note, ..rest] =>
    let (isComment, solid) := commentIs note.text (Bool.andLeft sound)
    (isComment, solid, notesOfSound rest (Bool.andRight sound))

--| A token whose trailing comment is as rule N leaves it trails one the lexer reads as a comment.
theorem trailsOfSound ∀ (word: Word) (sound: word.sound = True): TrailsComment word :=
  let after: afterSound word.comments.after = True := Bool.andRight (Bool.andRight sound)
  match word, after with
    | { text, comments = { above, after = Some comment, blankBefore } }, after => commentIs comment after
    | { text, comments = { above, after = None, blankBefore } }, _ => byComputing

--| A token that is sound has own-line comments the lexer reads as comments.
theorem notesOfWord ∀ (word: Word) (sound: word.sound = True): NotesComment word.comments.above :=
  notesOfSound word.comments.above (Bool.andLeft (Bool.andRight sound))

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

--| What `printedHangs1` asks of a slice 1 declaration beyond the four tree facts: the type's `ElHangs` at 4 and the
--| value's `BodyLays`. Not a consequence of the tree facts: each fails for some slice 1 declaration (NOTES, SW-4045).
--| Comments above the name, the `:` and the `:=` are no longer asked about: they come from `sound`.
def DeclElements (kinds: Text → Tok): Decl → Prop
  | Definition [] header (Assigned colonEq value) =>
    (∃ (trails: Bool) => ElHangs kinds
      (header.result.el (declStart.next header.colon.after.isSome 3))
      4
      4
      header.colon.after.isSome
      trails
      (startFor header.result.noted))
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
    | Definition [] header (Assigned colonEq value), (typed, body) =>
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
          let nameSound: name.sound = True := Bool.andLeft rest
          let colonSound: (fixedWord ":" colon).sound = True := Bool.andLeft (Bool.andRight rest)
          let assignSound: (fixedWord ":=" colonEq).sound = True :=
            Bool.andLeft (Bool.andRight (Bool.andRight (Bool.andRight rest)))
          (
            trailsOfSound (fixedWord "def" keyword) keywordSound,
            plain,
            token,
            notesOfWord name nameSound,
            trailsOfSound name nameSound,
            notesOfWord (fixedWord ":" colon) colonSound,
            trailsOfSound (fixedWord ":" colon) colonSound,
            notesOfWord (fixedWord ":=" colonEq) assignSound,
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
  (typed, body)

-- Quiet declarations.

--| A call value's hug, if it has one, hangs on the `:=`'s line.
def HugOnLine (kinds: Text → Tok) (value: Expr) (around: Around): Prop :=
  ∀ (open: Doc) => value.callHug { around | hoisted = True } = Some open → OnLine kinds open

--| A value with no `match` or `calc` is its element.
theorem plainBodyEl ∀ (value: Expr) (around: Around): plainBody value around = value.el around := match value with
  | Binding kind keyword params arrow body =>
    match kind with
      | BindsLambda => byComputing
      | BindsForall => byComputing
      | BindsExists => byComputing
  | _ => byComputing

-- Call hugs.

--| A call's hug (`appFrom`'s) hangs as its function's element, given its parts before the last spaced and the opened
--| last argument as a part after them.
theorem appFromHug ∀ (kinds: Text → Tok) (id keep: Nat) (between betweenFront: Bool) (headDoc: Doc) (front: List Doc)
    (lastDoc: Doc) (hug: Option Doc) (indent column: Nat) (middle fronted trails: Bool)
    (head: ElHangs kinds headDoc indent column False middle wordStart)
    (frontSpaced: SpacedParts kinds indent middle fronted front)
    (hugged: ∀ (opened: Doc) => hug = Some opened → PartHangs kinds opened indent fronted trails) (opened: Doc)
    (same: (appFrom id keep between betweenFront headDoc front lastDoc hug).hug = Some opened):
    ElHangs kinds opened indent column False trails wordStart :=
  match whole: keep == ([headDoc, ..front] ++ [lastDoc]).length, same with
    | True, never => cases
    | False, same =>
      match hug, hugged, same with
        | None, _, never => cases
        | Some open, hugged, same =>
          rewrite <- Option.someInjective same then
            elGapThen kinds
              (Flatten (spaced [headDoc, ..front]))
              (Doc.text " ")
              open
              indent
              column
              fronted
              trails
              (elFlatten kinds
                (spaced [headDoc, ..front])
                indent
                column
                False
                fronted
                (spacedHangs kinds headDoc front indent column middle fronted head frontSpaced))
              (Inr byComputing)
              (hugged open byComputing)

--| A call's hug (`appDocs`') hangs as its function's element, given its arguments' facts.
theorem appDocsHug ∀ (kinds: Text → Tok) (head argument: Expr) (rest: List Expr) (around: Around) (indent column: Nat)
    (headHangs: ElHangs kinds (head.el around) indent column False head.trails wordStart)
    (facts: ArgsHang kinds around.inArm head (around.at + head.size) [argument, ..rest]) (opened: Doc)
    (same: (appDocs head [argument, ..rest] around).hug = Some opened):
    ElHangs kinds opened indent column False (lastArg argument rest).trails wordStart :=
  let docs := argumentDocs around.inArm head (around.at + head.size) [argument, ..rest]
  let hug := (docs.snd.getOrElse (Nothing, None)).snd
  let trails := (lastArg argument rest).trails
  let (fronted, chain, _, hugs) := argumentDocsHang kinds around.inArm head (around.at + head.size) argument rest facts
  let frontSpaced: SpacedParts kinds indent head.trails fronted docs.fst :=
    chainedWeaker
      (before middle doc => Hangs kinds before middle doc)
      (before middle doc => PartHangs kinds doc indent before middle)
      head.trails
      fronted
      docs.fst
      (before middle doc hangs => elPart kinds doc indent before middle (hangs indent))
      chain
  let hugged: ∀ (open: Doc) => hug = Some open → PartHangs kinds open indent fronted trails := open hugSame =>
    elPart kinds open indent fronted trails (hugs open hugSame indent)
  let unfolded: (appFrom
    (around.at + 1)
    (keptFront head [argument, ..rest] + 1)
    (commentBetween head [argument, ..rest])
    (commentBetween head ([argument, ..rest].take (keptFront head [argument, ..rest])))
    (head.el around)
    docs.fst
    (docs.snd.getOrElse (Nothing, None)).fst
    hug).hug
    = Some opened :=
    rewrite <- Fmt.AppHangProofs.appDocsIs head [argument, ..rest] around then same
  appFromHug kinds _ _ _ _
    (head.el around)
    docs.fst _
    hug
    indent
    column
    head.trails
    fronted
    trails
    headHangs
    frontSpaced
    hugged
    opened
    unfolded

--| A quiet slice 1 call's hug hangs wherever it is laid.
theorem quietCallHug ∀ (head: Expr) (arguments: List Expr) (inside: Around) (indent column: Nat)
    (within: (App head arguments).within1 = True)
    (lexical: (App head arguments).lexical1 = True)
    (quiet: (App head arguments).quiet1 = True) (opened: Doc)
    (same: (App head arguments).callHug inside = Some opened):
    ∃ (trails: Bool) => ElHangs lexKind opened indent column False trails wordStart :=
  match arguments, quiet with
    | [argument, ..rest], quiet =>
      let headQuiet: head.quiet1 = True := Bool.andLeft quiet
      let headFacts := quietExprFacts head (Bool.andLeft within) (Bool.andLeft lexical) headQuiet
      let facts :=
        argsHang inside.inArm head
          (inside.at + head.size)
          [argument, ..rest]
          (quietTrails head headQuiet)
          (Bool.andRight within)
          (Bool.andRight lexical)
          (Bool.andRight quiet)
          quietKeys
      let headHangs: ElHangs lexKind (head.el inside) indent column False head.trails wordStart :=
        rewrite quietTrails head headQuiet then
          elUnheld lexKind
            (head.el inside)
            indent
            column
            inside.before
            False
            wordStart
            (hangsOf head headFacts inside indent column)
      (
        (lastArg argument rest).trails,
        appDocsHug lexKind head argument rest inside indent column headHangs facts opened same
      )

--| A quiet slice 1 value's hug, if it has one, hangs on the `:=`'s line.
theorem quietHug ∀ (value: Expr) (around: Around)
    (within: value.within1 = True)
    (lexical: value.lexical1 = True)
    (quiet: value.quiet1 = True):
    HugOnLine lexKind value around :=
  match value with
    | App head arguments => open same =>
      quietCallHug head arguments { around | hoisted = True } 0 0 within lexical quiet open same
    | _ => open never => cases

--| A quiet slice 1 value lays as a body, below the `:=` and on its line.
theorem quietBody ∀ (value: Expr) (around: Around)
    (within: value.within1 = True)
    (lexical: value.lexical1 = True)
    (quiet: value.quiet1 = True):
    BodyLays lexKind value around around.before :=
  let hangs := hangsOf value (quietExprFacts value within lexical quiet) around
  match around, hangs with
    | { before = False, hoisted, item, at, inArm }, hangs =>
      rewrite plainBodyEl value { before = False, hoisted, item, at, inArm }, quietNoted value quiet then
        (
          (False, hangs 2 2),
          _ _ => ((False, hangs 0 0), quietHug value { before = False, hoisted, item, at, inArm } within lexical quiet)
        )
    | { before = True, hoisted, item, at, inArm }, hangs =>
      rewrite plainBodyEl value { before = True, hoisted, item, at, inArm }, quietNoted value quiet then
        ((False, hangs 2 2), never => cases)

--| A declaration whose element facts follow from its tree's: its type and value have no own-line comments inside
--| (`Expr.quiet1`). Comments above the name, the `:` and the `:=` are allowed.
def DeclQuiet: Decl → Prop
  | Definition [] header (Assigned colonEq value) => header.result.quiet1 = True ∧ value.quiet1 = True
  | _ => False

--| A quiet slice 1 declaration meets `DeclElements`: its type's and value's facts from `quietExprFacts`.
theorem quietElements ∀ (decl: Decl)
    (within: decl.within1 = True)
    (lexical: decl.lexical1 = True)
    (quiet: DeclQuiet decl):
    DeclElements lexKind decl :=
  match decl, quiet with
    | Definition [] header (Assigned colonEq value), (typeQuiet, valueQuiet) =>
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
          let typeWithin: result.within1 = True := Bool.andRight (Bool.andLeft within)
          let valueWithin: value.within1 = True := Bool.andRight within
          let typeLexical: result.lexical1 = True := Bool.andLeft (Bool.andRight lexical)
          let valueLexical: value.lexical1 = True := Bool.andRight (Bool.andRight lexical)
          let typed :=
            hangsOf result
              (quietExprFacts result typeWithin typeLexical typeQuiet)
              (declStart.next colon.after.isSome 3)
          (
            (False, rewrite quietNoted result typeQuiet then typed 4 4),
            quietBody value (declStart.next colonEq.after.isSome (4 + result.size)) valueWithin valueLexical valueQuiet
          )

--| `printedHangs` for a quiet slice 1 declaration: the four tree facts, `DeclQuiet`, and nothing else.
theorem printedHangs1Quiet ∀ (decl: Decl) (doc: Doc) (width: Nat)
    (within: decl.within1 = True)
    (shaped: decl.shaped1 = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical1 = True)
    (quiet: DeclQuiet decl)
    (shows: decl.doc1 = Some doc) (lexed: Lexed)
    (read: lex (Doc.print doc width) = Ok lexed):
    hangs lexed.leaves = True :=
  printedHangs1 decl doc width within shaped sound lexical (quietElements decl within lexical quiet) shows lexed read

--| `def d: A := b` is quiet.
theorem atomDeclQuiet: DeclQuiet atomDecl := (byComputing, byComputing)

--| An own-line comment above a token.
def aboveComment: Comments := { above = [{ text = "-- c", blankBefore = False }], after = None, blankBefore = False }

--| `def d\n  -- c\n  : A := b`: a comment above the `:`.
def colonNotedDecl: Decl :=
  Definition []
    {
      exportKeyword = None,
      opaqueKeyword = None,
      kind = DefPlain,
      keyword = Comments.none,
      name = fixedWord "d" Comments.none,
      forallKeyword = None,
      params = [],
      colon = aboveComment,
      result = Atom Upper (fixedWord "A" Comments.none),
      decreasingClause = None,
      unfoldingClause = None
    }
    (Assigned Comments.none (Atom Lower (fixedWord "b" Comments.none)))

--| `def d: A\n  -- c\n  := b`: a comment above the `:=`.
def assignNotedDecl: Decl :=
  Definition []
    {
      exportKeyword = None,
      opaqueKeyword = None,
      kind = DefPlain,
      keyword = Comments.none,
      name = fixedWord "d" Comments.none,
      forallKeyword = None,
      params = [],
      colon = Comments.none,
      result = Atom Upper (fixedWord "A" Comments.none),
      decreasingClause = None,
      unfoldingClause = None
    }
    (Assigned aboveComment (Atom Lower (fixedWord "b" Comments.none)))

--| A comment above the `:` leaves a declaration quiet.
theorem colonNotedDeclQuiet: DeclQuiet colonNotedDecl := (byComputing, byComputing)

--| A comment above the `:=` leaves a declaration quiet.
theorem assignNotedDeclQuiet: DeclQuiet assignNotedDecl := (byComputing, byComputing)

--| `printedHangs1Quiet` applies to the declaration with a comment above its `:`: its four tree facts and `DeclQuiet`.
theorem colonNotedMeets: colonNotedDecl.within1 = True
      ∧ colonNotedDecl.shaped1 = True
      ∧ colonNotedDecl.sound = True
      ∧ colonNotedDecl.lexical1 = True
      ∧ DeclQuiet colonNotedDecl :=
  (byComputing, byComputing, byComputing, byComputing, colonNotedDeclQuiet)

--| `printedHangs1Quiet` applies to the declaration with a comment above its `:=`.
theorem assignNotedMeets: assignNotedDecl.within1 = True
      ∧ assignNotedDecl.shaped1 = True
      ∧ assignNotedDecl.sound = True
      ∧ assignNotedDecl.lexical1 = True
      ∧ DeclQuiet assignNotedDecl :=
  (byComputing, byComputing, byComputing, byComputing, assignNotedDeclQuiet)
