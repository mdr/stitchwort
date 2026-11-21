# Glossary of the slice 1 formatter proof

For a reader who knows what a code formatter does and how a proof assistant reads, but has not seen this
code. The proof is about `tools/fmt`, a formatter for Stitchwort written in Stitchwort, and its top theorems are
in [`src/Fmt/TopStatements.sw`](src/Fmt/TopStatements.sw) and [`src/Fmt/Accepts1.sw`](src/Fmt/Accepts1.sw).
[`PROOF-MAP.md`](PROOF-MAP.md) shows how the pieces fit; this page says what the words mean.

How to read an entry: the plain meaning first, then **Defined** with the definition's name and `file:line`
(paths are under `tools/fmt/src/`; Std's are under `crates/elab/src/std/`), then an example where one helps.
Names ending in `1` belong to slice 1 only; the unnumbered ones serve every slice. Many properties are
`Bool` tests on the tree, so a theorem says `x.hung = True`, not `Hung x`. The definitions were read, not
guessed from their names; `dev/check-glossary.sh` checks that each `file:line` still holds its name.

Contents: [The pipeline](#the-pipeline) · [Source text and trees](#source-text-and-trees) ·
[Comments](#comments) · [Layout and the line rule](#layout-and-the-line-rule) ·
[Properties of a tree](#properties-of-a-tree) · [The printer's documents](#the-printers-documents) ·
[What the printed text says](#what-the-printed-text-says) · [The parser, run twice](#the-parser-run-twice) ·
[Walks and traversals](#walks-and-traversals) · [Project codes](#project-codes)

## The pipeline

**Slice.** One step of the plan that grows the proved formatter by language features. Slice 1 is files of
`def name: Type := value` with no parameters, where type and value are names, numerals, brackets, tuples,
lists, calls, `-`, `!`, `¬`, binary operators and `->`, with comments and blank lines anywhere. Later slices
(`Slice2.sw` to `Slice6a.sw`) add binders, blocks, patterns, records and more. A slice is exactly its Scope
definitions: the grammar, the driver, its gate `within1` and the token alphabet. **Defined:** the grammar in
`inGrammar1` (Fmt/Grammar1.sw:158), the driver in `formatWithin1` (Fmt/Driver1.sw:98), the gate in `Expr.within1`
(Fmt/Slice1.sw:37).

**Grammar (`inGrammar1`).** The sources slice 1 must format: the language's own lexer and parser read them,
every token is in slice 1's alphabet, and the tree has only slice 1's forms. It says nothing about layout or
where comments sit. **Defined:** `inGrammar1` (Fmt/Grammar1.sw:158). The grammar is fixed; the proof makes the
driver accept more, never the grammar smaller (D3687).

**Driver (`formatWithin1`).** The formatter's entry point for slice 1: lex the source, refuse it if a test
fails, parse, refuse a tree outside `within1`, tidy, print. **Defined:** `formatWithin1` (Fmt/Driver1.sw:98),
with the tests in `leavesWithin1` (Fmt/Driver1.sw:30).
Example: `formatWithin1 witnessSource = Ok witnessOut` is `witnessFormats` (Fmt/TopStatements.sw:551).

**Alphabet (`alphabet1`) and `within1`.** `alphabet1` says every token of the source is one of slice 1's token
kinds. `within1` says the tree built from them has only slice 1's forms and spellings; it is the driver's gate
and is a little stronger than the grammar (`grammar1`). **Defined:** `alphabet1` (Syntax/SettleProofs.sw:330),
`Expr.within1` (Fmt/Slice1.sw:37).

**Tidy passes (P1 to P4).** Four rewrites of the tree, run after parsing, as in the Rust formatter: P1 puts a
`∀` after a theorem's name, P2 drops a comma before a closer, P3 drops redundant round brackets, P4 merges
adjacent parameters of one type. In slice 1 only P2 changes anything. **Defined:** `SourceFile.tidy1`
(Fmt/Driver1.sw:22), the passes in Fmt/Passes.sw; `tidyIs1` (Fmt/TopStatements.sw:147) says P1, P3 and P4 are the
identity there.

**Printer, rules, document.** The *rules* (Fmt/Rules.sw) turn a tidied declaration into a layout *document*
(`Doc`, from Std: text, line breaks, groups and the like); Std's printer then lays the document out at the
formatter's width. The proofs reason about the document, not about the printer's algorithm.
**Defined:** Fmt/Rules.sw (whole file); `Decl.leaves` (Fmt/OutputStatements.sw:33) is the declaration's printed
text lexed again.

**Two runs.** Idempotence compares the formatter's first run on a source with its second run on the first run's
output. The second run lexes the printed text, places comments, parses and prints again; much of the proof is
showing the second run sees the same tree as the first printed. Not to be confused with the *two-run parser
facts* (see [The parser, run twice](#the-parser-run-twice)).

**Top theorems.** `formatAccepts1` (every source of the grammar is formatted), `formatKeepsProgram1` (the
output parses to the same program), `formatIdempotent1` (formatting the output changes nothing), and
`slice1Formats`, which joins the three in one statement about the language's own lexer and parser.
**Defined:** `formatAccepts1` (Fmt/Accepts1.sw:26), `formatKeepsProgram1` (Fmt/TopStatements.sw:379),
`formatIdempotent1` (Fmt/TopStatements.sw:409), `slice1Formats` (Fmt/TopStatements.sw:483). `slice1KeepsComments`
(Fmt/CommentsKeptProof.sw:603) is a fourth statement beside them: no comment is lost or moved to where it
doesn't belong.

**Twin (the harness).** The comparison harness `fmt-twin` (`task fmt:twin`), which runs this formatter and the Rust one on
the same files and compares answers stage by stage. A "twin" check is a test against Rust, not a proof. (In the two-run parser lemmas "twin" means the second run's
copy of a value; see Alike (trees).)
**Defined:** `dev/fmt-twin` (the repo's `dev/`), the stages in Fmt/Twin.sw:1.

**Stock take.** `docs/reviews/SW-4078-slice1-stock-take.md`, the review that listed what slice 1 still needed
to prove. Comments cite its rows ("the stock take's row 10", "U6") as the origin of a statement.

## Source text and trees

**Leaf.** A token with its comments: the lexer's output unit. **Defined:** `Leaf = { token, trivia }`
(Syntax/Tree.sw:18). A **token** is a kind, its text, its column and whether it starts its line
(Syntax/Token.sw:300). A file lexes to a **`Lexed`**: its leaves plus the comments after the last token
(Syntax/Token.sw:304). "Leaves" in a theorem usually means this list, or `Decl.leaves`, the leaves of a
declaration's own printed text.

**Trivia.** What surrounds a token besides spaces: own-line comments before it, blank lines before its line, and
a comment after it on its line. **Defined:** `Trivia` (Syntax/Token.sw:289).

**Word.** The tree's token: its text and its `Comments`. The tree keeps nothing of columns, line starts or
blank-line counts beyond a flag. **Defined:** `Word` (Syntax/Expr.sw:33), `Comments = { above, after,
blankBefore }` (Syntax/Expr.sw:30). A fixed token such as `:=` is held as its comments only and made a word on
demand by `fixedWord` (Fmt/Rules.sw:90). Example: in `f x -- note`, the word `x` has `after = Some "-- note"`.

**Words of a tree.** `Expr.words` / `Decl.words` list a tree's tokens in order, with no commas (the tree
doesn't keep them). Comparing leaves to words is how the proofs say "the printed text has the tree's comments
where they belong". **Defined:** `Expr.words` (Fmt/Rules.sw:162), `Decl.words` (Fmt/Predicates.sw:38); `Expr.kinds`
(Fmt/Kinds.sw:40) lists kinds with commas in.

**Item.** A leaf as the parser reads it: with whether it is glued to the previous token, its bracket depth and
the line's indentation. **Defined:** `Item` (Syntax/Parser.sw:30).

**Glued.** A token with no space or line break before it, so the lexer reads it as touching the previous one
(`-1` against `- 1`). The printer says which words touch (`Touches`); the lexer says which are glued; the proof
connects them. **Defined:** the `glued` field of `Item` (Syntax/Parser.sw:30), `printedSpacing1` (Fmt/SpacingProofs.sw:402),
`Spacing = Free | Glued | Apart` (Fmt/OutputStatements.sw:49).

**Last comma.** A comma before a closing bracket (`[1, 2,]`). The tree has none; P2 deletes it. Comment
placement runs first with the last commas left in "bare" (their comments moved first) so that its answer
matches Rust's (see `settledOnce`). **Defined:** `withBareLastCommas` (Syntax/Settle.sw:359).

**`calmTop` and `meaning`.** `meaning` is a file's tree with each freedom the formatter has set to one spelling
and every comment gone: two files are "the same program" when their meanings are equal. `calmTop` is a tree as
the second run will parse it: blank-line flags that nothing prints are cleared (see Calm), and the first thing
in the file loses its blank line. **Defined:** `SourceFile.meaning` (Fmt/Meaning.sw:98), `SourceFile.calmTop`
(Fmt/OutputStatements.sw:178).

**Printed text (`printed1`).** The text the file loop prints for a tree. **Defined:** `SourceFile.printed1`
(Fmt/Slice1.sw:289). `SourceFile.lexed` (Fmt/OutputStatements.sw:148) writes out, as leaves, what the lexer
will read back from it.

## Comments

**Comment placement** (formerly "rule N"). The first thing the driver does after lexing: it moves each comment to
the token it belongs to, in five steps that run in this order, so the same program has one placement however
the author wrote it. After it: (1) no comma, closer or record update's `|` keeps a trailing comment unless
moving it would pass other comments; (2) no comma holds any comment; (3) no `->` holds a trailing comment, and
comments after it come before it; (4) an expression `let`'s `:=` has no trailing comment; (5) no comment's text
ends in a space. Its Rust twin is `place_comments`. **Defined:** `Lexed.settled` (Syntax/Settle.sw:289) with the
steps below; "settled" in a name means "after comment placement". Example: in `(a, b) -- c` the lexer gives
the comment to `)`, and placement takes it back to `b`.

- **Back-walk** (formerly "rule 1"): a trailing comment after closers, commas or a record update's `|` is moved
  back to the code before them. **Defined:** `homeFrom` (Syntax/Settle.sw:164).
- **Comma carry** (formerly "rule 2"): a comma's comments go to the token after it. **Defined:** `commasFrom`
  (Syntax/Settle.sw:203).
- **Arrow lift** (formerly "rule 3"): comments after `->` go before it. **Defined:** `arrowsFrom`
  (Syntax/Settle.sw:216).
- **Let lift** (formerly "rule 4"): a comment ending a `let`'s `:=` line goes before the `:=`. **Defined:**
  `letsFrom` (Syntax/Settle.sw:258). Under slice 1's alphabet there is no `let`, so it does nothing.
- **Trim** (formerly "rule 5"): a comment's text loses its trailing spaces. **Defined:** `Comment.trimmed`
  (Syntax/Settle.sw:270).

**Settled (`settled`).** A tree property: its comments are where comment placement leaves them. A closer's trailing
comment must be homed (below), no `->` holds a comment, and every comment's text is clean (`commentText`:
starts `--`, no line break, no trailing space). **Defined:** `Decl.settled` (Fmt/Predicates.sw:69),
`commentText` (Fmt/Predicates.sw:65). `Lexed.settled` is the function, `Decl.settled` the property.

**`settledOnce`, `settledBare`.** What the driver actually parses: comment placement run once on a source
whose last commas have been made bare (`settledWith True`). `settledOnce` and the plain `settled` agree when a
file has no last comma, which the printer's output never has. **Defined:** `Lexed.settledOnce`
(Syntax/Settle.sw:372), `Lexed.settledWith` (Syntax/Settle.sw:281). `settledOnceNone` (Syntax/SettleBareProofs.sw:1747).

**Homed.** A comment is homed when comment placement would leave it where it is: a closer holds a trailing
comment only if it has own-line comments above it, or the code before it (closers aside) ends its line with a
comment. **Defined:** `homedBack` (Fmt/Predicates.sw:50), `Expr.homed` (Fmt/ElementsHomed.sw:25),
`Word.homedAfter` (Fmt/ElementsHomed.sw:21).

**Trails, noted.** A word *trails* if a comment follows it on its line; it is *noted* if own-line comments are
above it. `Expr.trails` asks whether a comment ends the expression's line, reading from the back past closers
(`trailsBack`). **Defined:** `Word.trails` (Fmt/Rules.sw:92), `Word.noted` (Fmt/Rules.sw:94), `trailsBack` (Fmt/Rules.sw:317).

**Quiet.** Four unrelated words share this name. (a) A *word* is quiet when it has no comment and no blank line
above it: `Word.quiet` (Fmt/ExprHangProofs.sw:32); an *expression* is quiet when all its words are
(`Expr.quiet`, Fmt/ExprHangProofs.sw:38), *edge-quiet* when only the first and last token may have comments
(`Expr.edgeQuiet`, Fmt/OneLineStatements.sw:33). (b) A *token kind* is quiet when it is not a comma or closer:
`Quiet` (Fmt/TreeJoinProofs.sw:73). (c) A printer *seam* is quiet when any comment waiting there really is a
comment: `Quiet` (Fmt/TouchSteps.sw:37). (d) The parser's *modes* are quiet when no guard, `calc` or `rewrite` rule
is in force, so only a line start ends a reading: `Quiet` (Syntax/ReadBackLine.sw:29).

**Stands.** The printed leaves have the tree's comments where the tree says: each word's own-line comments and
blank-line flag, a trailing comment on the word's leaf or *owed* on to a closer or comma after it on the same
line, none misplaced. It is what comment placement reads on the output. `stood` is the words as printed (`calm`'s,
minus the first `def`'s own-line comments). **Defined:** `stands` (Fmt/TriviaStatements.sw:37), `Decl.stands`
(Fmt/TriviaStatements.sw:72), `Decl.stood` (Fmt/TriviaStatements.sw:67); proved of slice 1 by `printedStands1`
(Fmt/StandsProofs.sw:1468).

**Owed.** In `stands`, a trailing comment of a word already passed, which the lexer hasn't yet seen because
closers and commas follow the word on its line. `tucked` (Fmt/TriviaStatements.sw:16) says a comma or closer can
stand on such a line.

**Unreturned.** A comment's text ends in no carriage return and no space. The lexer strips both, so every
lexed comment is unreturned; the printed tree's comments must be. **Defined:** `Note.unreturned`
(Fmt/SettleOutputProofs.sw:592), `SourceFile.unreturned` (Fmt/SettleOutputProofs.sw:595).

**Note.** A comment on its own line above a token (`Syntax.Note`); "own-line comment" and "note" mean the same.

**Auto-placed.** A list starting `[auto Ord …]` reads as an implicit parameter where a full expression starts
(a declaration's type or value, a bracket's inside, an item, an arrow's right side), so a parsed tree has none
there. **Defined:** `Expr.autoPlaced` (Syntax/AutoPlaced.sw:30).

**Comments kept.** The formatter keeps every comment's text and the place it belongs, up to the blank lines the
printer sets by rule. **Defined:** `CommentsKept` (Fmt/Meaning.sw:299), proved for slice 1 by
`slice1KeepsComments` (Fmt/CommentsKeptProof.sw:603).

## Layout and the line rule

**Hangs.** A declaration's printed leaves keep *the line rule*: the parser's rule for when a line may start at a
column. A leaf that starts a line is right of the block column in force; a closer that starts a line is left of
the column its bracket's current item started at; no comma starts a line, nor the leaf after `->`; a `:` that
starts one is right of column 0. If this fails, the output would re-parse as different statements.
**Defined:** `hangs` (Fmt/Predicates.sw:346), the step in `HangState.step` (Fmt/Predicates.sw:314). Example: in
`def x: T := f\n  a` the `a` is right of the `:=`'s block column, so it hangs.

**HangState.** What `hangs` carries while it walks the leaves: the open brackets' block columns (innermost
first), the type's or value's column, whether the next leaf starts an item, whether it must not start a line
(after `->`). **Defined:** `HangState` (Fmt/Predicates.sw:281).

**Hung.** The file-level form of Hangs: every declaration's printed leaves keep the line rule
(`SourceFile.hung`, Fmt/OutputStatements.sw:154). "Read back over hung lines" is the parser reading such leaves
(Syntax/ReadBackHung.sw). The many `…Hang…` names (`HangsFor`, `ItemHangs`, `DeclHangs`) are the printer's side:
"this element, laid by the rules, ends up satisfying the line rule". **Defined:** `DeclHangs`
(Fmt/DeclHangProofs.sw:825), `printedHangs1` (Fmt/DeclFactsProofs.sw:152).

**Element.** In the printer proofs, a node of the tree that is laid out as one unit: an atom, a bracket, a
call's argument, an operator chain. `DeclElements` says every element of a declaration's type and value meets
its hang facts; the proof is an induction over the expression (`AnyFacts`). **Defined:** `DeclElements`
(Fmt/DeclFactsProofs.sw:95), `declElements1` (Fmt/ElementsProofs.sw:1228).

**Lays.** From a given place and trace, every way a document may print puts its words where the predicate
`next` lists them. It does not follow the printer's modes: a `Line` may be a space or a break wherever it
stands, so a theorem about `Lays` holds at every width. **Defined:** `Doc.Proofs.Lays` (crates/elab/src/std/Doc/Lays.sw:123);
`Fmt/LaysKinds.sw` checks it by computing, for a continuation that holds everywhere.

**Place, carry, mark, floor.** Std's printer position: at a line start (`AtStart`), after words (`Mid`), after
a break that follows a waiting comment (`Broken`), or with a trailing comment waiting (`Held`). It carries the
*comment floor* (the least indentation of lines up to the next code, after an own-line comment) and *marks* (the
opener's indentation, remembered for a closer comments put on a line of its own). **Defined:** `Doc.Proofs.Place`
(crates/elab/src/std/Doc/Places.sw:56), `Mark` and `CloserLine` constructors (crates/elab/src/std/Doc/Doc.sw:97).

**Led.** An element with own-line comments above its first token: those comments start the line, and the
first token starts the line after them. **Defined:** `Led` (Fmt/ElementsApp.sw:20), `LedAt` (Fmt/ElementsKeys.sw:381).

**Seat, Seated.** Where an element may start: at a line start at a given column, mid-line, or after a waiting
comment only if the code before ends its line with one. **Defined:** `Seated` (Fmt/HangProofs.sw:695).

**Around.** What a rule needs to know of where a token or element stands: whether the code before ends its
line with a comment, whether its first token's own-line comments are printed by an enclosing element (*hoisted*),
and so on. **Defined:** `Around` (Fmt/Rules.sw:62).

**Hug.** A call's last argument opening downwards from the call's line (`f (` … `)`): the call document carries
a second form, the hug. **Defined:** `Applied = { doc, hug }` (Fmt/Rules.sw:651).

## Properties of a tree

These are the facts a printed tree is shown to have before the layout proofs start. The bundle is `TreeFacts`
(Fmt/TopStatements.sw:193): `within1`, `shaped`, `settled`, `lexical`, `commaFree`.

**Shaped.** The tree is one the parser can give: a call's head is an atom, a bracket or a negative numeral; its
arguments atoms, brackets or signs on them; operands of an infix sit at their ladder levels (a right operand of
a left-nesting chain one level up); a tuple has two items or more. **Defined:** `Expr.shaped` (Fmt/Predicates.sw:190).

**Lexical.** Each word's text lexes as exactly one token of its kind, a bracket's word is its bracket, and an
operator's text is in the operator table. **Defined:** `Expr.lexical` (Fmt/Predicates.sw:226).

**Sound.** A word's text is not layout and its comments are as comment placement leaves them (so the printer can
write it). **Defined:** `Word.sound` (Fmt/SpellProofs.sw:213).

**Comma-free.** The tree has no last comma: P2 has run. **Defined:** `commaFree` (member of `TreeFacts`;
`commaSame1`, Fmt/TopStatements.sw:108, says P2 changes nothing on such a tree).

**Calm.** A tree with only the blank-line flags the rules read: the flag below a word's comments is kept above
an item or below comments that aren't a closer's, and cleared otherwise. `calm` changes flags only, so the
printed text and the `meaning` are unchanged. **Defined:** `Expr.calm` (Fmt/Predicates.sw:89),
`Comments.kept` (Fmt/Predicates.sw:81), `SourceFile.calm` (Fmt/Predicates.sw:129); `calmPrints`
(Fmt/CalmProofs.sw) and `calmTopMeans` (Fmt/CalmTopProofs.sw:242), `calmTopPrints` (Fmt/CalmTopProofs.sw:292).

**Alike.** Two words are alike when they have the same text, same trailing comment and same own-line comment
texts; they may differ in blank-line flags. Used to say `calm` changes nothing the rules read. **Defined:**
`Word.alike` (Fmt/CalmProofs.sw:19). (Parser-side "alike" trees: see
[The parser, run twice](#the-parser-run-twice).)

**Kept.** Two unrelated words. In the printer, `Comments.kept`/`Word.kept` keep the blank-line flags the rules
read (Fmt/Predicates.sw:81). In the parser walk, `Kept read expr` says a parser function gave a tree of the
grammar with the words of the items it read, their kinds, `within1`, and that it is placed (`Kept`, Syntax/ParseKept.sw:61).

**Carried.** Two unrelated words. In comment placement, `Carried` is the own-line comments a comma carries to the
next token plus its blank lines (Syntax/Settle.sw:183). In the parser walk, `Carried` is the spec `Kept` is
built from: the tree has the words of the items read (Syntax/ParseCarries.sw:1).

**Shapes, plain.** `sourcePlain1` is the driver's test on a source's tokens: no `->` before a comma, closer or
`->`; no comma starting a line except a last comma; the first token no comma or closer. `plain1` is the same
for a settled output (no comma ever starts a line). **Defined:** `sourcePlain1` (Syntax/SettleProofs.sw:1595),
`plain1` (Syntax/SettleProofs.sw:1252). A *shape* (`SourceFile.shapes`, Fmt/SourcePlainProofs.sw:126) is the
kind of token for these tests.

**Call head, call argument.** Which expressions may stand as a call's head or argument, including a `-` glued
to a numeral (`-1 n` is one atom applied). **Defined:** `Expr.callHead` (Fmt/Predicates.sw:163),
`Expr.callArgument` (Fmt/Predicates.sw:170).

## The printer's documents

The rules' documents are proved to have properties by "triples" over Std's relations: from every position
satisfying `pre`, the document may print and leave a position satisfying `post`.

**Spells.** A document `Spells` a list of texts when every option of each choice has those words (`Uniform`), its
closers and trailing comments are of the kinds the rules write (`Marked`), and its words are the texts.
`Expr.spelt`/`Decl.spelt` are the texts the rules print for a tree. **Defined:** `Spells` (Fmt/SpellProofs.sw:26),
`Expr.spelt` (Fmt/SpellProofs.sw:375); Std's `Uniform` and `Marked` in crates/elab/src/std/Doc/Words.sw (lines
306 and 757). Proved of slice 1 by `printedSpells` (Fmt/SpellProofs.sw:1597).

**Joins, Follows.** `Joins` says what the printer puts next to what: each printed piece may stand after the one
before. `Follows kinds word next` is the caller's relation: `word` still lexes as itself before `next`. A
`Passes` triple takes an edge satisfying `pre` to one satisfying `post`. **Defined:** `Doc.Proofs.Joins`
(crates/elab/src/std/Doc/Joins.sw:116), `Follows` (Fmt/PrintLexProofs.sw:45), `Passes` (Fmt/JoinProofs.sw:200);
proved by `printLexes1` (Fmt/JoinProofs.sw:2294).

**Touches, Seam.** Which printed words touch the piece before them (no space or break between). A *seam* is
where the printer is: at a line start, after pieces on the line, or with a trailing comment waiting.
**Defined:** `Doc.Proofs.Seam` (crates/elab/src/std/Doc/Touches.sw:48); the rules' triples `Steps`
(Fmt/TouchSteps.sw:109), with `Fits` (Fmt/TouchSteps.sw:48) asking a seam admits the next word's spacing.

**Told.** What a document says of its words whatever layout prints it: whether each word starts its line, follows
words on it, or may do either, and whether each blank leaves a blank line. `Spot` is where the printer may be
when telling. **Defined:** `Doc.tell` (crates/elab/src/std/Doc/Told.sw:157); the rules' side in
Fmt/ToldWordProofs.sw and Fmt/ToldDeclProofs.sw; `Refines` (Fmt/ToldDeclProofs.sw:29).

**Trace, events.** The printer's own account of where it puts each word: a word and the column its line starts at,
if it starts one. `hangs` over the leaves equals a fold over the trace (`Tracks`, Fmt/PrintHangProofs.sw:176).

**Heard (Hears).** The lexer's reading of the printed events, written as a fold (`hearAll`) and shown to agree with
the lexer proofs' layout fold `Laid.lay` over the same pieces. **Defined:** `hearAll` (Fmt/HearProofs.sw:147), `Hears` (Fmt/HearProofs.sw:157).

**Laid, Piece.** The lexer proofs' model of printed text: a `Piece` is a gap, a break, a remark (comment) or a
code token; `Laid` is the state of the layout folded over pieces. **Defined:** `Piece` (Syntax/LexProofs.sw:402),
`Laid` (Syntax/LexProofs.sw:440), `laidOf` (Fmt/PrintHangProofs.sw:160).

## What the printed text says

The three claims the proof must show about the formatter's output, each derived from the layers above:

**Lexes back.** The printed text lexes to the leaves `SourceFile.lexed` writes out (`printedFileLexes1`,
Fmt/FileLexProofs.sw:1044): tokens have the right spelling and kinds (`printedTokens1`, Fmt/TokenProofs.sw:175),
glued as the printer touches them (`printedSpacing1`), comments on the leaves `stands` says.

**Settles back.** Comment placement on those leaves gives back the tree's words (`printedSettle1`,
Fmt/SettleOutputProofs.sw:1627): the back-walk (see `homeStands`, Fmt/SettleOutputProofs.sw:320) walks each owed
comment back to its word and the other steps find nothing to do. Comment placement is *not* idle on the output
(`outputNotIdle`, Fmt/OutputStatements.sw:290), which is why this is a theorem.

**Reads back.** The parser on those settled leaves gives `calmTop` of the printed tree. It is proved per
declaration group (`readsBackDecl1`, Fmt/TopReadBack.sw:54) from the over-many-lines read-back
(`readsBackHung`, Syntax/ReadBackHungTop.sw:148) and the split of printed items into slots
(`printedSplit1`, Fmt/GroupSlots.sw:926), then per file (`readsBackFile1`, Fmt/TopReadBack.sw:254).

**Spelt.** An expression is *spelt* by a list of items when the items are the node's tokens in order, each
carrying the node's word, a comma between two bracket items and none after the last. It links the tree to
what the parser reads. **Defined:** `Spelt` (Syntax/ReadBackLine.sw:156), `SlotMatch` (Fmt/SpeltSlots.sw:41).
Not the same as `Spells` (a document's words).

**Group.** One declaration's leaves, as the file-level parser splits them. **Defined:** `PrintedGroup`
(Fmt/GroupFacts.sw:44), `GroupSplit` (Fmt/GroupFacts.sw:25).

**Formats1, Printed1, TreeFacts.** The bundles of facts the top theorems pass between steps: `Formats1` is what
`formatWithin1 source = Ok out` tells (lexes, leaves pass, parses, within, `out` is the tidied tree printed);
`TreeFacts` the five tree properties; `Printed1` those facts on the tree the driver prints, plus that the
output lexes and parses. **Defined:** `Formats1` (Fmt/TopStatements.sw:121), `TreeFacts` (Fmt/TopStatements.sw:193), `Printed1`
(Fmt/TopStatements.sw:348).

## The parser, run twice

The source and the formatter's output differ only in comments, blank lines and layout. The proof shows the
language's parser reads them to trees that differ only in comments, with the *same function* on both.

**Two-run, follows.** For each parser function `f`, the lemma `followsF` says: called with *alike* arguments
(items equal once their comments are blanked), `f` follows itself, giving alike results or the same failure.
**Defined:** the relations and the pattern in Syntax/FollowsBase.sw:1; knots tied in Syntax/FollowsParse.sw;
`Follows*.sw` has one lemma per parser function. (The name `Follows` also names a printer relation; see Joins.)

**Alike (trees).** Equal once their comments are blanked. `AllAlike` is the list form for words.
**Defined:** `ExprsAlike` (Syntax/FollowsBase.sw:86: the two trees are equal once walked with `blankPure`), `WordsAlike`
(Syntax/FollowsBase.sw:84), and the same for patterns, groups, declarations and so on; `SameCode` (Syntax/DeafProofs.sw:15)
is the relation on items (equal once stripped of trivia). In a two-run lemma the second run's value is named with
`Twin`: `xTwin` is the value the second run computes, `selfTwin` the second run's recursive call.

**Deaf.** A parser function is deaf to comments when it gives the same answer on items and on the same items
with their comments stripped. `deafOfStripped` turns such a fact into one about two runs. The look-aheads and
the lowering's checks are deaf, so they agree on both runs. **Defined:** `Leaf.stripped`
(Syntax/DeafProofs.sw:11), `deafOfStripped` (Syntax/DeafProofs.sw:1046), `stopsDeaf`, `loweringDeaf` and the rest
of that file.

**Blanks.** Blanking a tree's comments (`walk blankPure`) commutes with a traversal step: the step fails the same
way or finishes with the result blanked. `meaning` is built on it. **Defined:** `Blanks` (Fmt/TraverseFail.sw:17),
`blankPure` (Fmt/BlankProofs.sw:333); `meaningBlanksFirst` (Fmt/BlankProofs.sw:364).

**Honest.** Std's `Parse.Honest total at`: a parser mark's offset and remaining input are consistent with the
whole input. The lexer proofs need it to chain steps. **Defined:** `Parse.Honest` (crates/elab/src/std/Parse/Reads.sw:46).

**Parser's walk (carried walk).** The proof that every parser function on slice 1's path gives a tree with the
words of the items it read: `Kept` for each function from atoms up to a declaration. It lives in
Syntax/ParseKept.sw (atoms to `append_expr`), Syntax/ParseCarriesLadder.sw (the levels above),
Syntax/ParseCarriesDecl.sw (declarations), Syntax/ParseCarriesFile.sw (files) and Syntax/ParseWalk*.sw (shapes
and the parsers outside slice 1, which are only shown to give trees *outside* the slice, `Out`).

## Walks and traversals

**Traversal (`Traverse`) and `walk`.** The shared traversal of the tree (Syntax/Traverse.sw) takes *steps* that
may fail; the passes and `meaning` are traversals with different steps. `walk` is a pure copy of it, arm for arm,
with steps that cannot fail (`Pure`). Two families of lemma, one theorem per function: `…Ok` (the traversal
finishes with the walk's result when the steps agree, `Agrees`) and `…Twice` (walking with `s` then `m` is walking
with `m`, `Keeps`). **Defined:** `Pure` (Fmt/Walk.sw:22), `Agrees` (Fmt/Walk.sw:458), `Keeps` (Fmt/Walk.sw:471).
This is unrelated to *the parser's walk* above and the *back-walk* of comment placement; all three are walks
over different things.

**Seq-N lemmas.** `seqN` in Fmt/Walk.sw run N finished computations in order; the proofs of the `…Ok` family were
generated from them, one call per arm.

## Project codes

Descriptions cite tickets and plan labels; their meaning:

- **SW-N** — a board ticket (`board/`); **D-N** — a numbered decision of Matt's (`board/`, `docs/`);
  a name like "ticket 18g" or "F3 of SW-4042" is a piece of a plan in `docs/reviews/`.
- **K1** — "spike K1", the early experiment on comment placement and the parked last comma
  (`docs/proposals/self-hosted-fmt-s1-sketch.md`); `settledHomed` is "K1's" statement.
- **P1 to P4** — the four tidy passes (above).
- **U6, row 10** — rows of the stock take's list.
- **Slice 1, 2, 3, 4a …** — see Slice.
