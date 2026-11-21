--| Slice 1's formatter keeps comments (`CommentsKept`, `Fmt.Meaning`): `slice1KeepsComments`, beside `slice1Formats`.
--|
--| Both sides are read through the tree's words. The source's leaves after `settledBare` carry the words the parser
--| put in the tree (`bareSettles`, `parseCarriesSourceProved`), and P2 keeps every word (`declsWordsUncomma`). The
--| output's leaves after comment placement carry the words of `calmTop` of that tree (`printedSettle1`). `calm` and `calmTop`
--| change only blank-line flags: a closer's below its comments, and the file's first comment's above it, which are
--| the two `CommentsKept` leaves out (D3695).

namespace Fmt.CommentsKeptProof
import Std (Bool, Eq, List, Nat, Option, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Driver1 (..)
import Fmt.Accepts1 (formatAccepts1)
import Fmt.TopStatements (..)
import Fmt.PassProofs (commaKeepsComments, commaMap, declsWordsUncomma)
import Fmt.CalmProofs (..)
import Fmt.SettleOutputProofs (..)
import Fmt.OutputStatements (..)
import Fmt.Grammar1 (..)
import Syntax.SharedFacts (headerResultWithin)
import Syntax.SettleProofs (alphabet1, bareComma, settledCommasBare, sourcePlain1, tokens)
import Syntax.SettleOnceProofs (wordsOf, wordsOfComma, wordsOfDropF, wordsOfItem, wordsOfUnstarted)
import Syntax.SettleMarkProofs (..)
import Fmt.TriviaStatements (..)
import Fmt.StandsProofs (..)
import Syntax.SettleBareProofs (dropF)
import Syntax.ParseCarries (codeWords)
import Syntax.SettleSplitProofs (groupWordsConcat, groupsConcat)
import Syntax.ParseWalkOthers (parseCarriesSourceProved)

-- What a word holds of the comments, as the leaves' `commentViews` and `holders` read them.

def noteView (note: Note): CommentView := { text = note.text, ownLine = True, blankAbove = note.blankBefore }

def afterView (text: Text): CommentView := { text, ownLine = False, blankAbove = False }

def Comments.views (comments: Comments): List CommentView :=
  comments.above.map noteView ++ comments.after.toList.map afterView

def Word.holder (word: Word): Option Holder :=
  if word.comments.above.isEmpty && word.comments.after.isNone then None
  else
    Some {
      token = word.text,
      above = word.comments.above.length,
      trailing = word.comments.after.isSome,
      blankBelow = !word.comments.above.isEmpty && word.comments.blankBefore
    }

def wordsViews (words: List Word): List CommentView := words.flatMap (word => word.comments.views)

def wordsHolders (words: List Word): List Holder := (words.filterMap Word.holder).map Holder.forDocs

-- From leaves to words.

def commentNote (comment: Comment): Note := { text = comment.text, blankBefore = comment.blankLines > 0 }

def commentView (comment: Comment): CommentView :=
  { text = comment.text, ownLine = True, blankAbove = comment.blankLines > 0 }

theorem leadingViews ∀ (leading: List Comment): (leading.map commentNote).map noteView = leading.map commentView :=
  match leading with
    | [] => byComputing
    | [comment, ..rest] => Eq.cong (tail => [commentView comment, ..tail]) (leadingViews rest)

theorem triviaViews ∀ (trivia: Trivia): trivia.commentViews = trivia.comments.views := match trivia with
  | { leading, blankLines, trailing } =>
    match trailing with
      | None =>
        let same: leading.map commentView ++ [] = (leading.map commentNote).map noteView ++ [] :=
          rewrite leadingViews leading
        same
      | Some comment =>
        let tail: List CommentView := [afterView comment.text]
        let same: leading.map commentView ++ tail = (leading.map commentNote).map noteView ++ tail :=
          rewrite leadingViews leading
        same

theorem leafHolder ∀ (leaf: Leaf): leaf.holder = leaf.word.holder := match leaf with
  | { token, trivia = { leading, blankLines, trailing } } =>
    match leading with
      | [] => cases
      | [first, ..rest] =>
        let count: (rest.map (comment => ({ text = comment.text, blankBefore = comment.blankLines > 0 }: Note))).length
          = rest.length :=
          List.lengthMap rest (comment => ({ text = comment.text, blankBefore = comment.blankLines > 0 }: Note))
        match trailing with
          | None =>
            let same: Some {
              token = token.text,
              above = rest.length + 1,
              trailing = False,
              blankBelow = blankLines > 0
            }
              = Some {
                token = token.text,
                above = (rest.map (comment =>
                  ({ text = comment.text, blankBefore = comment.blankLines > 0 }: Note))).length
                  + 1,
                trailing = False,
                blankBelow = blankLines > 0
              } :=
              rewrite count
            same
          | Some comment =>
            let same: Some { token = token.text, above = rest.length + 1, trailing = True, blankBelow = blankLines > 0 }
              = Some {
                token = token.text,
                above = (rest.map (comment =>
                  ({ text = comment.text, blankBefore = comment.blankLines > 0 }: Note))).length
                  + 1,
                trailing = True,
                blankBelow = blankLines > 0
              } :=
              rewrite count
            same

theorem commaNoComments ∀ (leaf: Leaf)
    (bare: bareComma leaf = True)
    (comma: (leaf.token.kind == Comma) = True):
    leaf.trivia.commentViews = [] ∧ leaf.holder = None :=
  match leaf with
    | { token, trivia = { leading, blankLines, trailing } } =>
      match leading, trailing with
        | [], None => (byComputing, byComputing)
        | [], Some comment => cases
        | [first, ..rest], trailing => cases

--| A bare comma holds no comment, so dropping it from the words loses none.
theorem leavesWords ∀ (leaves: List Leaf)
    (bare: leaves.all bareComma = True):
    leaves.flatMap (leaf => leaf.trivia.commentViews) = wordsViews (wordsOf leaves)
      ∧ leaves.filterMap Leaf.holder = (wordsOf leaves).filterMap Word.holder :=
  match leaves with
    | [] => (byComputing, byComputing)
    | [leaf, ..rest] =>
      let (views, holders) := leavesWords rest (Bool.andRight bare)
      match comma: leaf.token.kind == Comma with
        | True =>
          let (noViews, noHolder) := commaNoComments leaf (Bool.andLeft bare) comma
          let viewsHere: [leaf, ..rest].flatMap (leaf => leaf.trivia.commentViews)
            = wordsViews (wordsOf [leaf, ..rest]) :=
            calc [leaf, ..rest].flatMap (leaf => leaf.trivia.commentViews)
              _ = leaf.trivia.commentViews ++ rest.flatMap (leaf => leaf.trivia.commentViews) := byComputing
              _ = rest.flatMap (leaf => leaf.trivia.commentViews) := rewrite noViews
              _ = wordsViews (wordsOf rest) := views
              _ = wordsViews (wordsOf [leaf, ..rest]) := rewrite wordsOfComma leaf rest comma
          let holdersHere: [leaf, ..rest].filterMap Leaf.holder = (wordsOf [leaf, ..rest]).filterMap Word.holder :=
            calc [leaf, ..rest].filterMap Leaf.holder
              _ = List.consSome leaf.holder (rest.filterMap Leaf.holder) := byComputing
              _ = rest.filterMap Leaf.holder := rewrite noHolder
              _ = (wordsOf rest).filterMap Word.holder := holders
              _ = (wordsOf [leaf, ..rest]).filterMap Word.holder := rewrite wordsOfComma leaf rest comma
          (viewsHere, holdersHere)
        | False =>
          let viewsHere: [leaf, ..rest].flatMap (leaf => leaf.trivia.commentViews)
            = wordsViews (wordsOf [leaf, ..rest]) :=
            calc [leaf, ..rest].flatMap (leaf => leaf.trivia.commentViews)
              _ = leaf.trivia.commentViews ++ rest.flatMap (leaf => leaf.trivia.commentViews) := byComputing
              _ = leaf.word.comments.views ++ wordsViews (wordsOf rest) := rewrite triviaViews leaf.trivia, views
              _ = wordsViews (wordsOf [leaf, ..rest]) := rewrite wordsOfItem leaf rest comma
          let holdersHere: [leaf, ..rest].filterMap Leaf.holder = (wordsOf [leaf, ..rest]).filterMap Word.holder :=
            calc [leaf, ..rest].filterMap Leaf.holder
              _ = List.consSome leaf.holder (rest.filterMap Leaf.holder) := byComputing
              _ = List.consSome leaf.word.holder ((wordsOf rest).filterMap Word.holder) :=
                rewrite leafHolder leaf, holders
              _ = (wordsOf [leaf, ..rest]).filterMap Word.holder := rewrite wordsOfItem leaf rest comma
          (viewsHere, holdersHere)

--| A lexed file's comments, read off its words and its end, when its commas hold none.
theorem lexedWords ∀ (lexed: Lexed)
    (bare: lexed.leaves.all bareComma = True):
    lexed.commentViews = wordsViews (wordsOf lexed.leaves) ++ lexed.end.comments.views
      ∧ lexed.holders.map Holder.forDocs = wordsHolders (wordsOf lexed.leaves) :=
  let (views, holders) := leavesWords lexed.leaves bare
  let viewsHere: lexed.commentViews = wordsViews (wordsOf lexed.leaves) ++ lexed.end.comments.views :=
    rewrite views, triviaViews lexed.end
  let holdersHere: lexed.holders.map Holder.forDocs = wordsHolders (wordsOf lexed.leaves) := rewrite holders
  (viewsHere, holdersHere)

-- `calm` keeps what `CommentsKept` reads of a word.

--| A word and its calmed word hold the same comments, and the same holder but for a closer's blank line below.
def Word.keeps (before after: Word): Prop :=
  before.comments.views = after.comments.views ∧ before.holder.map Holder.forDocs = after.holder.map Holder.forDocs

def AllKeep: List Word → List Word → Prop
  | [], [] => True
  | [before, ..more], [after, ..later] => before.keeps after ∧ AllKeep more later
  | _, _ => False

theorem keptKeeps ∀ (word: Word) (item closer: Bool)
    (closes: (!closer || isCloserText word.text) = True):
    word.keeps (word.kept item closer) :=
  match word with
    | { text, comments = { above, after, blankBefore } } =>
      match above with
        | [] => (byComputing, cases)
        | [first, ..rest] => (byComputing, cases)

theorem allKeepAppend ∀ (front later back after: List Word)
    (fronts: AllKeep front later)
    (backs: AllKeep back after):
    AllKeep (front ++ back) (later ++ after) :=
  match front, later, fronts with
    | [], [], _ => backs
    | [first, ..more], [second, ..others], (same, rest) => (same, allKeepAppend more others back after rest backs)

theorem consSomeForDocs ∀ (holder: Option Holder) (rest: List Holder):
    (List.consSome holder rest).map Holder.forDocs
      = List.consSome (holder.map Holder.forDocs) (rest.map Holder.forDocs) :=
  match holder with | None | Some _ => byComputing

theorem allKeepRead ∀ (before after: List Word)
    (keep: AllKeep before after):
    wordsViews before = wordsViews after ∧ wordsHolders before = wordsHolders after :=
  match before, after, keep with
    | [], [], _ => (byComputing, byComputing)
    | [first, ..more], [second, ..others], ((views, holder), rest) =>
      let (restViews, restHolders) := allKeepRead more others rest
      let viewsHere: wordsViews [first, ..more] = wordsViews [second, ..others] := calc wordsViews [first, ..more]
        _ = first.comments.views ++ wordsViews more := byComputing
        _ = second.comments.views ++ wordsViews others := rewrite views, restViews
        _ = wordsViews [second, ..others] := byComputing
      let holdersHere: wordsHolders [first, ..more] = wordsHolders [second, ..others] := calc wordsHolders
        [first, ..more]
        _ = (List.consSome first.holder (more.filterMap Word.holder)).map Holder.forDocs := byComputing
        _ = List.consSome (first.holder.map Holder.forDocs) (wordsHolders more) := consSomeForDocs _ _
        _ = List.consSome (second.holder.map Holder.forDocs) (wordsHolders others) := rewrite holder, restHolders
        _ = (List.consSome second.holder (others.filterMap Word.holder)).map Holder.forDocs :=
          (consSomeForDocs _ _).flipped
        _ = wordsHolders [second, ..others] := byComputing
      (viewsHere, holdersHere)

theorem itemsKeepAll ∀ (items: List Expr) (item: Bool)
    (within: allWithin1 items = True)
    (closed: allClosed items = True):
    AllKeep (itemsWords items) (itemsWords (calmAll item items)) :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      allKeepAppend first.words
        (first.calm item).words
        (itemsWords rest)
        (itemsWords (calmAll item rest))
        (wordsCalmKeep first item (Bool.andLeft within) (Bool.andLeft closed))
        (itemsKeepAll rest item (Bool.andRight within) (Bool.andRight closed))

theorem itemsKeepLead ∀ (items: List Expr)
    (within: allWithin1 items = True)
    (closed: allClosed items = True):
    AllKeep (itemsWords items) (itemsWords (calmLead items)) :=
  match items with
    | [] => byComputing
    | [first, ..rest] =>
      allKeepAppend first.words
        (first.calm False).words
        (itemsWords rest)
        (itemsWords (calmAll True rest))
        (wordsCalmKeep first False (Bool.andLeft within) (Bool.andLeft closed))
        (itemsKeepAll rest True (Bool.andRight within) (Bool.andRight closed))

theorem itemsKeepPick ∀ (plain: Bool) (items: List Expr)
    (within: allWithin1 items = True)
    (closed: allClosed items = True):
    AllKeep (itemsWords items) (itemsWords (pickItems plain items)) :=
  match plain with
    | True => itemsKeepLead items within closed
    | False => itemsKeepAll items True within closed

--| `calm` keeps every word's comments and holder, but a closer's blank line below its comments.
--|
--| Proof idea: induction on the expression, as `wordsCalm`; `keptKeeps` for each token `calm` touches, where a
--| bracket's closing word is a closer (`Expr.closed`).
theorem wordsCalmKeep ∀ (expr: Expr) (item: Bool)
    (within: expr.within1 = True)
    (closed: expr.closed = True):
    AllKeep expr.words (expr.calm item).words :=
  match expr with
    | Atom kind word => (keptKeeps word item False byComputing, byComputing)
    | Paren open inner close =>
      allKeepAppend
        [open, ..inner.words]
        [open.kept item False, ..(inner.calm False).words]
        [close]
        [close.kept False True]
        (keptKeeps open item False byComputing, wordsCalmKeep inner False within (Bool.andRight closed))
        (keptKeeps close False True (rewrite Bool.andLeft closed), byComputing)
    | Tuple open items comma close =>
      allKeepAppend
        [open, ..itemsWords items]
        [open.kept item False, ..itemsWords (calmAll True items)]
        [close]
        [close.kept False True]
        (keptKeeps open item False byComputing, itemsKeepAll items True within (Bool.andRight closed))
        (keptKeeps close False True (rewrite Bool.andLeft closed), byComputing)
    | ListOf open items comma close =>
      allKeepAppend
        [open, ..itemsWords items]
        [open.kept item False, ..itemsWords (calmItems items)]
        [close]
        [close.kept False True]
        (
          keptKeeps open item False byComputing,
          itemsKeepPick (items.all Expr.plainItem) items within (Bool.andRight closed)
        )
        (keptKeeps close False True (rewrite Bool.andLeft closed), byComputing)
    | App head arguments =>
      allKeepAppend head.words
        (head.calm item).words
        (itemsWords arguments)
        (itemsWords (calmAll False arguments))
        (wordsCalmKeep head item (Bool.andLeft within) (Bool.andLeft closed))
        (itemsKeepAll arguments False (Bool.andRight within) (Bool.andRight closed))
    | Infix kind left operator right =>
      match kind with
        | InfixBinary | InfixArrow =>
          allKeepAppend left.words
            (left.calm item).words
            [operator, ..right.words]
            [operator.kept False False, ..(right.calm False).words]
            (wordsCalmKeep left item (Bool.andLeft within) (Bool.andLeft closed))
            (
              keptKeeps operator False False byComputing,
              wordsCalmKeep right False (Bool.andLeft (Bool.andRight within)) (Bool.andRight closed)
            )
        | _ => cases
    | Prefix operator operand =>
      (keptKeeps operator item False byComputing, wordsCalmKeep operand False (Bool.andLeft within) closed)

--| A declaration's words, calmed, keep every comment and holder but a closer's blank line below.
theorem declCalmKeep ∀ (decl: Decl)
    (within: decl.within1 = True)
    (lexical: decl.lexical = True):
    AllKeep decl.words decl.calm.words :=
  match decl with
    | Definition [] header (Assigned colonEq value) =>
      let resultClosed := lexicalClosed header.result (Bool.andLeft (Bool.andRight lexical))
      let valueClosed := lexicalClosed value (Bool.andRight (Bool.andRight lexical))
      let headerWithin := Bool.andLeft within
      allKeepAppend
        [fixedWord "def" header.keyword, header.name, fixedWord ":" header.colon]
        [fixedWord "def" header.keyword, header.name.kept False False, fixedWord ":" (header.colon.kept False False)]
        (header.result.words ++ [fixedWord ":=" colonEq] ++ value.words)
        ((header.result.calm False).words ++ [fixedWord ":=" (colonEq.kept False False)] ++ (value.calm False).words)
        (
          (byComputing, byComputing),
          keptKeeps header.name False False byComputing,
          keptKeeps (fixedWord ":" header.colon) False False byComputing,
          byComputing
        )
        (allKeepAppend header.result.words
          (header.result.calm False).words
          ([fixedWord ":=" colonEq] ++ value.words)
          ([fixedWord ":=" (colonEq.kept False False)] ++ (value.calm False).words)
          (wordsCalmKeep header.result False (headerResultWithin header headerWithin) resultClosed)
          (
            keptKeeps (fixedWord ":=" colonEq) False False byComputing,
            wordsCalmKeep value False (Bool.andRight within) valueClosed
          ))

theorem declsCalmKeep ∀ (decls: List Decl)
    (within: decls.all Decl.within1 = True)
    (lexical: decls.all Decl.lexical = True):
    AllKeep (decls.map Decl.words).concat ((decls.map Decl.calm).map Decl.words).concat :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] =>
      allKeepAppend decl.words decl.calm.words
        (rest.map Decl.words).concat
        ((rest.map Decl.calm).map Decl.words).concat
        (declCalmKeep decl (Bool.andLeft within) (Bool.andLeft lexical))
        (declsCalmKeep rest (Bool.andRight within) (Bool.andRight lexical))

-- `calmTop`: the file's first comment loses its blank line above.

theorem toppedViews ∀ (comments: Comments) (rest: List CommentView):
    unheaded (comments.topped.views ++ rest) = unheaded (comments.views ++ rest) :=
  match comments with | { above, after, blankBefore } => cases above then byComputing

theorem toppedHolder ∀ (comments: Comments):
    (fixedWord "def" comments.topped).holder = (fixedWord "def" comments).holder :=
  match comments with | { above, after, blankBefore } => cases above then byComputing

--| A file's words whose first word's comments are topped read as before, but the first comment's blank line above.
theorem toppedWords ∀ (comments: Comments) (words: List Word) (end: List CommentView):
    unheaded (wordsViews [fixedWord "def" comments.topped, ..words] ++ end)
      = unheaded (wordsViews [fixedWord "def" comments, ..words] ++ end)
      ∧ wordsHolders [fixedWord "def" comments.topped, ..words] = wordsHolders [fixedWord "def" comments, ..words] :=
  let viewsHere: unheaded (wordsViews [fixedWord "def" comments.topped, ..words] ++ end)
    = unheaded (wordsViews [fixedWord "def" comments, ..words] ++ end) :=
    calc unheaded (wordsViews [fixedWord "def" comments.topped, ..words] ++ end)
      _ = unheaded ((comments.topped.views ++ wordsViews words) ++ end) := byComputing
      _ = unheaded (comments.topped.views ++ (wordsViews words ++ end)) :=
        rewrite List.appendAssoc comments.topped.views (wordsViews words) end
      _ = unheaded (comments.views ++ (wordsViews words ++ end)) := toppedViews comments (wordsViews words ++ end)
      _ = unheaded ((comments.views ++ wordsViews words) ++ end) :=
        rewrite List.appendAssoc comments.views (wordsViews words) end
      _ = unheaded (wordsViews [fixedWord "def" comments, ..words] ++ end) := byComputing
  let holdersHere: wordsHolders [fixedWord "def" comments.topped, ..words]
    = wordsHolders [fixedWord "def" comments, ..words] :=
    calc wordsHolders [fixedWord "def" comments.topped, ..words]
      _ = List.consSome ((fixedWord "def" comments.topped).holder.map Holder.forDocs) (wordsHolders words) :=
        consSomeForDocs _ _
      _ = List.consSome ((fixedWord "def" comments).holder.map Holder.forDocs) (wordsHolders words) :=
        rewrite toppedHolder comments
      _ = wordsHolders [fixedWord "def" comments, ..words] := (consSomeForDocs _ _).flipped
  (viewsHere, holdersHere)

--| What the file's comments read as, its words and its end.
def fileViews (file: SourceFile): List CommentView :=
  unheaded (wordsViews (file.decls.map Decl.words).concat ++ file.end.views)

def fileHolders (file: SourceFile): List Holder := wordsHolders (file.decls.map Decl.words).concat

theorem calmKeeps ∀ (file: SourceFile)
    (within: file.within1 = True)
    (lexical: file.lexical = True):
    fileViews file.calm = fileViews file ∧ fileHolders file.calm = fileHolders file :=
  let (views, holders) :=
    allKeepRead
      (file.decls.map Decl.words).concat
      ((file.decls.map Decl.calm).map Decl.words).concat
      (declsCalmKeep file.decls within lexical)
  (rewrite views then byComputing, holders.flipped)

--| `calmTop` keeps what `CommentsKept` reads of a file's words and end.
--|
--| Proof idea: `calm` keeps it word by word (`declsCalmKeep`); `calmTop` then tops the first declaration's `def`, or
--| the end if there is none, which changes only the first comment's blank line above (`toppedWords`).
theorem calmTopKeeps ∀ (file: SourceFile)
    (within: file.within1 = True)
    (lexical: file.lexical = True):
    fileViews file.calmTop = fileViews file ∧ fileHolders file.calmTop = fileHolders file :=
  match file with
    | { decls, end } =>
      match decls with
        | [] =>
          match end with
            | { above, after, blankBefore } =>
              match above with
                | [] => (byComputing, byComputing)
                | [first, ..more] => (byComputing, byComputing)
        | [Definition [] header (Assigned colonEq value), ..rest] =>
          let words: List Word :=
            ([header.name.kept False False, fixedWord ":" (header.colon.kept False False)]
              ++ (header.result.calm False).words
              ++ [fixedWord ":=" (colonEq.kept False False)]
              ++ (value.calm False).words)
              ++ ((rest.map Decl.calm).map Decl.words).concat
          let ending: Comments := { end | blankBefore = False }
          let (views, holders) := toppedWords header.keyword words ending.views
          let file: SourceFile := { decls = [Definition [] header (Assigned colonEq value), ..rest], end }
          let (calmViews, calmHolders) := calmKeeps file within lexical
          let viewsHere: fileViews file.calmTop = fileViews file := calc fileViews file.calmTop
            _ = fileViews file.calm := views
            _ = fileViews file := calmViews
          let holdersHere: fileHolders file.calmTop = fileHolders file := calc fileHolders file.calmTop
            _ = fileHolders file.calm := holders
            _ = fileHolders file := calmHolders
          (viewsHere, holdersHere)
        | _ => cases

-- The two sides.

--| The source's leaves after `settledBare` hold the comments of the words of the tree the driver prints: the parser
--| carries the leaves' words to the tree (`parseCarriesSourceProved`), `settledOnce` has `settledBare`'s words
--| (`bareSettles`), and P2 keeps every word and the end.
theorem sourceComments ∀ (source: Text) (lexed: Lexed) (parsed: SourceFile)
    (lexes: lex source = Ok lexed)
    (leaves: leavesWithin1 lexed.leaves = True)
    (parses: parseFile lexed.settledOnce = Ok parsed)
    (within: parsed.within1 = True):
    unheaded lexed.settledBare.commentViews = fileViews parsed.tidy1
      ∧ lexed.settledBare.holders.map Holder.forDocs = fileHolders parsed.tidy1 :=
  let alphabet := Bool.andLeft leaves
  let plain := Bool.andRight leaves
  let (words, fileEnd) := parseCarriesSourceProved source lexed parsed lexes alphabet plain parses within
  let joined: (parsed.decls.map Decl.words).concat = codeWords lexed.settledOnce.leaves :=
    rewrite words then
      Eq.trans (groupWordsConcat (groupsOf lexed.settledOnce.leaves)) (rewrite groupsConcat lexed.settledOnce.leaves)
  let (leavesEq, endEq) := bareSettles lexed alphabet plain
  let dropped := dropF [] lexed.settledOnce.leaves
  let bareWords: wordsOf lexed.settledOnce.leaves = wordsOf lexed.settledBare.leaves := calc wordsOf
      lexed.settledOnce.leaves
    _ = wordsOf dropped := (wordsOfDropF [] lexed.settledOnce.leaves).flipped
    _ = wordsOf (dropped.map Leaf.unstarted) := (wordsOfUnstarted dropped).flipped
    _ = wordsOf (lexed.settledBare.leaves.map Leaf.unstarted) := rewrite leavesEq
    _ = wordsOf lexed.settledBare.leaves := wordsOfUnstarted lexed.settledBare.leaves
  let (tidyWords, tidyEnd) := commaKeepsComments parsed within
  let tidied: (parsed.tidy1.decls.map Decl.words).concat = wordsOf lexed.settledBare.leaves :=
    calc (parsed.tidy1.decls.map Decl.words).concat
      _ = (parsed.withoutTrailingCommas.decls.map Decl.words).concat := rewrite tidyComma1 parsed within
      _ = (parsed.decls.map Decl.words).concat := rewrite tidyWords
      _ = wordsOf lexed.settledOnce.leaves := joined
      _ = wordsOf lexed.settledBare.leaves := bareWords
  let ended: parsed.tidy1.end = lexed.settledBare.end.comments := calc parsed.tidy1.end
    _ = parsed.withoutTrailingCommas.end := rewrite tidyComma1 parsed within
    _ = parsed.end := tidyEnd
    _ = lexed.settledOnce.end.comments := fileEnd
    _ = lexed.settledBare.end.comments := rewrite endEq
  let (views, holders) :=
    lexedWords lexed.settledBare (settledCommasBare { lexed | leaves = withoutLastCommas [] lexed.leaves })
  let viewsHere: unheaded lexed.settledBare.commentViews = fileViews parsed.tidy1 := calc unheaded
      lexed.settledBare.commentViews
    _ = unheaded (wordsViews (wordsOf lexed.settledBare.leaves) ++ lexed.settledBare.end.comments.views) :=
      rewrite views
    _ = unheaded (wordsViews (parsed.tidy1.decls.map Decl.words).concat ++ parsed.tidy1.end.views) :=
      rewrite tidied, ended
    _ = fileViews parsed.tidy1 := byComputing
  let holdersHere: lexed.settledBare.holders.map Holder.forDocs = fileHolders parsed.tidy1 :=
    calc lexed.settledBare.holders.map Holder.forDocs
      _ = wordsHolders (wordsOf lexed.settledBare.leaves) := holders
      _ = wordsHolders (parsed.tidy1.decls.map Decl.words).concat := rewrite tidied
      _ = fileHolders parsed.tidy1 := byComputing
  (viewsHere, holdersHere)

--| The output's leaves after comment placement hold the comments of the words of `calmTop` of the printed tree
--| (`printedSettle1`).
theorem outputComments ∀ (file: SourceFile)
    (facts: TreeFacts file)
    (declsUnreturned: file.decls.all Decl.unreturned = True)
    (unreturned: file.unreturned = True):
    unheaded file.lexed.settled.commentViews = fileViews file.calmTop
      ∧ file.lexed.settled.holders.map Holder.forDocs = fileHolders file.calmTop :=
  let (within, shaped, settled, lexical, commaFree) := facts
  let declsSettled: file.decls.all Decl.settled = True := Bool.andLeft settled
  let hung: file.hung = True :=
    declsAll file.decls
      (decl => hangs decl.leaves)
      within
      shaped
      declsSettled
      lexical
      declsUnreturned
      (decl w s t l u => (declHangs1 decl w s t l u).left)
  let stood: file.stood = True :=
    declsAll file.decls Decl.stands within shaped declsSettled lexical declsUnreturned (decl w s t l u =>
      (declHangs1 decl w s t l u).right u)
  let (words, ends) := printedSettle1 file within shaped settled lexical hung stood unreturned
  let settledLeaves := file.lexed.settled.leaves
  let joined: wordsOf settledLeaves = (file.calmTop.decls.map Decl.words).concat := calc wordsOf settledLeaves
    _ = codeWords (groupsOf settledLeaves).concat := rewrite groupsConcat settledLeaves
    _ = ((groupsOf settledLeaves).map codeWords).concat := (groupWordsConcat (groupsOf settledLeaves)).flipped
    _ = (file.calmTop.decls.map Decl.words).concat := rewrite words
  let (views, holders) := lexedWords file.lexed.settled (settledCommasBare file.lexed)
  let viewsHere: unheaded file.lexed.settled.commentViews = fileViews file.calmTop := calc unheaded
      file.lexed.settled.commentViews
    _ = unheaded (wordsViews (wordsOf settledLeaves) ++ file.lexed.settled.end.comments.views) := rewrite views
    _ = unheaded (wordsViews (file.calmTop.decls.map Decl.words).concat ++ file.calmTop.end.views) :=
      rewrite joined, ends
    _ = fileViews file.calmTop := byComputing
  let holdersHere: file.lexed.settled.holders.map Holder.forDocs = fileHolders file.calmTop :=
    calc file.lexed.settled.holders.map Holder.forDocs
      _ = wordsHolders (wordsOf settledLeaves) := holders
      _ = wordsHolders (file.calmTop.decls.map Decl.words).concat := rewrite joined
      _ = fileHolders file.calmTop := byComputing
  (viewsHere, holdersHere)

-- The theorems.

--| **Comments kept.** If slice 1's driver formats `source` to `out`, the comments of `out` are those of `source`
--| (`CommentsKept`): each comment's text, in order, own-line or trailing, on the same token, with the blank lines
--| that decide a doc.
--|
--| Proof idea: both sides read as the comments of words: the source's (`sourceComments`) those of the tree the
--| driver prints, the output's (`outputComments`) those of its `calmTop`, which keeps all `CommentsKept` reads
--| (`calmTopKeeps`).
theorem formatKeepsComments1 ∀ (source out: Text) (lexed lexedOut: Lexed)
    (formats: formatWithin1 source = Ok out)
    (lexes: lex source = Ok lexed)
    (lexesOut: lex out = Ok lexedOut):
    CommentsKept lexed lexedOut :=
  let (lexedD, parsed, accepted) := formatsOf source out formats
  let (lexesD, leaves, parses, within, outIs) := accepted
  let (facts, lexOut, _) := printedOf source out lexedD parsed accepted
  let file := parsed.tidy1
  let sameIn: lexedD = lexed := Result.okInjective (Eq.trans lexesD.flipped lexes)
  let printedLexes: lex file.printed1 = Ok lexedOut := rewrite outIs at lexesOut then lexesOut
  let sameOut: file.lexed = lexedOut := Result.okInjective (Eq.trans lexOut.flipped printedLexes)
  let (sourceViews, sourceHolders) := sourceComments source lexedD parsed lexesD leaves parses within
  let unreturned := tidiedUnreturned1 source lexedD parsed lexesD leaves parses within
  let declsUnreturned := tidiedDeclsUnreturned1 source lexedD parsed lexesD leaves parses within
  let (outViews, outHolders) := outputComments file facts declsUnreturned unreturned
  let (fileWithin, _, _, fileLexical, _) := facts
  let (topViews, topHolders) := calmTopKeeps file fileWithin fileLexical
  let viewsKept: unheaded lexedD.settledBare.commentViews = unheaded file.lexed.settled.commentViews := calc unheaded
      lexedD.settledBare.commentViews
    _ = fileViews file := sourceViews
    _ = fileViews file.calmTop := topViews.flipped
    _ = unheaded file.lexed.settled.commentViews := outViews.flipped
  let holdersKept: lexedD.settledBare.holders.map Holder.forDocs = file.lexed.settled.holders.map Holder.forDocs :=
    calc lexedD.settledBare.holders.map Holder.forDocs
      _ = fileHolders file := sourceHolders
      _ = fileHolders file.calmTop := topHolders.flipped
      _ = file.lexed.settled.holders.map Holder.forDocs := outHolders.flipped
  rewrite <- sameIn, <- sameOut then (viewsKept, holdersKept)

--| **Slice 1 keeps comments (D3695).** For every source in slice 1's grammar, the formatter succeeds, giving `out`;
--| both lex; and `out` keeps the comments of `source` (`CommentsKept`). A companion to `slice1Formats`, with its one
--| hypothesis.
theorem slice1KeepsComments ∀ (source: Text)
    (inGrammar: inGrammar1 source = True):
    ∃ (out: Text) (lexed lexedOut: Lexed) => formatWithin1 source = Ok out
      ∧ lex source = Ok lexed
      ∧ lex out = Ok lexedOut
      ∧ CommentsKept lexed lexedOut :=
  let (out, formats) := formatAccepts1 source inGrammar
  let (lexed, parsed, accepted) := formatsOf source out formats
  let (lexes, _, _, _, outIs) := accepted
  let (_, lexOut, _) := printedOf source out lexed parsed accepted
  let lexesOut: lex out = Ok parsed.tidy1.lexed := rewrite outIs then lexOut
  (
    out,
    lexed,
    parsed.tidy1.lexed,
    formats,
    lexes,
    lexesOut,
    formatKeepsComments1 source out lexed parsed.tidy1.lexed formats lexes lexesOut
  )

--| `slice1KeepsComments`' hypothesis holds of `witnessSource`, with comments above, after and at the end of
--| declarations.
theorem witnessKeepsComments: ∃ (out: Text) (lexed lexedOut: Lexed) => formatWithin1 witnessSource = Ok out
      ∧ lex witnessSource = Ok lexed
      ∧ lex out = Ok lexedOut
      ∧ CommentsKept lexed lexedOut :=
  slice1KeepsComments witnessSource witnessInGrammar
