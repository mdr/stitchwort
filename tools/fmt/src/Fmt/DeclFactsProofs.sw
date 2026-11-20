--| `printedHangs` from fewer facts (ticket 18h): of `DeclHangs`' facts, the tokens' trailing comments come from `sound`,
--| their own-line comments (above the name, the `:` and the `:=`, which the printer keeps there) too, and the name's
--| kind and spelling from `within1`, so `printedHangs1` asks, beyond the four tree facts, only what `DeclElements`
--| names: the type's and the value's element facts.
--|
--| Those are not a consequence of the tree facts in general: inside the type or the value, a token after the first
--| may have comments above it or after it (NOTES, SW-4045, SW-4058).
--|
--| `Fmt.ElementsProofs` proves them for every slice 1 declaration.

namespace Fmt.DeclFactsProofs
import Std (Bool, Char, DecEq, Doc, Eq, List, Nat, Option, Result, Text, Void)
import Std.Doc.Proofs (IsComment, isLayout)
import Syntax (BindingKind, Comments, Decl, DefBody, DefKind, Expr, Header, InfixKind, Lexed, Note, Tok, Word, lex)
import Fmt (..)
import Fmt.HangProofs (..)
import Fmt.AppHangProofs (..)
import Fmt.SpellProofs (..)
import Fmt.TreeJoinProofs (
  lexKind,
  lexKindOfSpells,
  nameKinded,
  spellsNotComment,
  spellsNotLayout,
  spellsOfText1,
  spellsQuiet,
  wordQuiet
)
import Fmt.DeclHangProofs (BodyLays, DeclHangs, OnLine, WordToken, declStart, plainBody, printedHangs)
import Fmt.ExprHangProofs (..)

-- Trailing comments, from `sound`.

--| Characters that start with `--` and have no line break are a comment's.
theorem dashed ∀ (chars: List Char)
    (starts: Text.startsWithChars ['-', '-'] chars = True)
    (free: Text.containsChars ['\n'] chars = False):
    ∃ (others: List Char) => chars = ['-', '-', ..others] ∧ others.all (char => char != '\n') = True :=
  match chars, starts with
    | [first, second, ..others], starts =>
      let whole := Text.allNotLineBreak [first, second, ..others] free
      match one: Text.sameChar '-' first with
        | True =>
          match two: Text.sameChar '-' second with
            | True =>
              let isFirst: '-' = first := DecEq.sound (rewrite Text.sameCharEq '-' first at one then one)
              let isSecond: '-' = second := DecEq.sound (rewrite Text.sameCharEq '-' second at two then two)
              rewrite <- isFirst, <- isSecond then (others, byComputing, Bool.andRight (Bool.andRight whole))
    | [_], _ => cases

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

--| A header's name, as `within1` spells it, is a plain token of the lexer's `Lower` or `Upper` kind.
theorem nameFacts ∀ (name: Word)
    (within: name.nameWithin1 = True):
    Fmt.HangProofs.Plain (lexKind name.text) ∧ WordToken name.text :=
  let (kind, spells, quiet, isName) := nameKinded name within
  let (comma, closer) := spellsQuiet kind name.text spells quiet
  let kinded := lexKindOfSpells kind name.text spells
  match isName with
    | Inl same => (
      rewrite kinded, same then (byComputing, byComputing, byComputing, byComputing, byComputing, byComputing),
      (spellsNotComment kind name.text spells, spellsNotLayout kind name.text spells, closer, comma)
    )
    | Inr same => (
      rewrite kinded, same then (byComputing, byComputing, byComputing, byComputing, byComputing, byComputing),
      (spellsNotComment kind name.text spells, spellsNotLayout kind name.text spells, closer, comma)
    )

-- The declaration.

--| What `printedHangs1` asks of a slice 1 declaration beyond the four tree facts: the type's `ElHangs` at 4 and the
--| value's `BodyLays`, each from its first token's start (`startFor`): after its own-line comments, if it has any.
--| Comments above the name, the `:` and the `:=` are not asked about: they come from `sound`.
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
    (shaped: decl.shaped = True)
    (sound: decl.sound = True)
    (lexical: decl.lexical = True)
    (elements: DeclElements lexKind decl)
    (shows: decl.doc1 = Some doc) (lexed: Lexed)
    (read: lex (Doc.print doc width) = Ok lexed):
    hangs lexed.leaves = True :=
  printedHangs decl doc width within shaped sound lexical (declHangsOf decl within sound elements) shows lexed read

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
  let (fronted, chain, _, hugs) :=
    argumentDocsHang kinds around.inArm head
      (around.at + head.size)
      argument
      rest
      True
      (never => (Bool.trueNotFalse never).impossible)
      facts
  let frontSpaced: SpacedParts kinds indent head.trails fronted docs.fst :=
    chainedWeaker
      (ArgStep kinds True)
      (before middle doc => PartHangs kinds doc indent before middle)
      head.trails
      fronted
      docs.fst
      (before middle doc (noted, hangs, _) => partHangsFor kinds doc indent before middle noted (hangs indent))
      chain
  let hugged: ∀ (open: Doc) => hug = Some open → PartHangs kinds open indent fronted trails := open hugSame =>
    let (noted, hangs) := hugs open hugSame
    partHangsFor kinds open indent fronted trails noted (hangs indent)
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

-- Comments above the type's or the value's first token.

--| A slice 1 expression's first token is no closer.
theorem leadNotCloser ∀ (expr: Expr)
    (within: expr.within1 = True)
    (lexical: expr.lexical = True):
    isCloserText expr.lead.text = False :=
  match expr, within with
    | Atom kind word, within =>
      let (_, (_, _, closer, _)) := wordFacts kind word.text within
      closer
    | Paren _ _ _ | Tuple _ _ _ _ | ListOf _ _ _ _, _ => rewrite DecEq.sound (Bool.andLeft lexical)
    | App head _ | Infix InfixBinary head _ _ | Infix InfixArrow head _ _, within =>
      leadNotCloser head (Bool.andLeft within) (Bool.andLeft lexical)
    | Prefix operator _, within =>
      let (_, (_, _, closer, _)) := prefixToken operator.text (Bool.andRight within)
      closer
