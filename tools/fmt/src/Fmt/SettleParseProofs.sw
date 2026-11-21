--| Comment placement keeps the parse (SW-4129; item 7 of docs/reviews/SW-4120-grammar1.md). Slice 1's grammar parses the
--| lexer's own leaves (`parseFile lexed`); the driver parses them after comment placement (`parseFile lexed.settledOnce`). So
--| the acceptance theorem needs: a source whose own parse is a slice 1 tree also parses after comment placement, to the same
--| tree with its comments where comment placement puts them (`settledParses1`).
--|
--| Why it holds: comment placement moves comments between leaves and never a token (`settledOnceTokens`), and the parser reads a
--| leaf's comments only to copy them into the tree's words (`Leaf.word`, `Trivia.comments`, and a binder's `bare`,
--| none of which any test of the parser reads). Its every decision is
--| taken on the tokens: kinds, texts, columns and line starts (`items`, `groupsOf`, `fileRefusal`, the parser's
--| look-aheads). So two leaf lists with the same tokens parse alike, up to the comments in the tree.
--|
--| What is proved here: the file's layer, from that fact for one declaration group (`groupKeepsTokens1`). The
--| groups are cut by the tokens (`splitTokens`), the file is refused or not by its first token, and the groups'
--| declarations are parsed one at a time, each with the same `Seen` on both sides since both are definitions.
--| `groupKeepsTokens1` itself comes from `groupKeepsTokens`, the two-run walk of the parser (`Syntax.FollowsParse`),
--| with slice 1's grammar and the lowering error read off the blanked tree (`grammar1Deaf`, `loweringDeaf`).

namespace Fmt.SettleParseProofs
import Std (Bool, Eq, Fail, List, Nat, Option, Parse, Result, Text)
import Syntax (..)
import Fmt (..)
import Fmt.Grammar1 (..)
import Fmt.Walk (..)
import Fmt.BlankProofs (blankPure, blankAgrees)
import Fmt.SettleOutputProofs (groupTokens, splitTokens)
import Syntax.SettleProofs (alphabet1, plain1, sourcePlainOfPlain, tokens)
import Syntax.GoodItemProofs (settledOnceTokens)
import Syntax.ParseCarries (codeWords)
import Syntax.ParseWalkOthers (parseCarriesSourceProved)
import Syntax.DeafProofs (grammar1Deaf, loweringDeaf)
import Syntax.FollowsParse (declarationKeepsTokens)

-- One group.

--| What `parseGroups` runs on one group's leaves.
def groupRun (seen: Seen) (group: List Leaf): Result Decl Parse.Failure := Parse.run (items group) (() =>
  let decl := declaration seen
  decl)

--| The parser reads one declaration group's comments only into the tree: a group that parses parses as well with
--| the same tokens and any comments, to the same declaration with its comments blanked. For any declaration, not
--| only slice 1's: it is the two-run walk of the whole parser (`Syntax.FollowsParse.declarationKeepsTokens`).
--| The hypothesis `same` includes each token's column and `lineStart`, so a change that moves a token to another
--| line is outside it. The twin's `Group.bare` flag is not known equal to the first run's, since the parser reads
--| comments to set it.
theorem groupKeepsTokens ∀ (seen: Seen) (group other: List Leaf) (decl: Decl)
    (same: tokens group = tokens other)
    (runs: groupRun seen group = Ok decl):
    ∃ (twin: Decl) => groupRun seen other = Ok twin ∧ twin.walk blankPure = decl.walk blankPure :=
  declarationKeepsTokens seen group other decl same runs

--| The parser reads one declaration group's comments only into the tree: a group whose declaration is slice 1's
--| parses as well with the same tokens and any comments, to the same declaration with its comments blanked, with
--| the same lowering error (none, for slice 1's trees).
--|
--| Slice 1's grammar and the lowering error are read off the blanked tree (`grammar1Deaf`, `loweringDeaf`), which
--| `groupKeepsTokens` says is the same on both sides.
theorem groupKeepsTokens1 ∀ (seen: Seen) (group other: List Leaf) (decl: Decl)
    (same: tokens group = tokens other)
    (runs: groupRun seen group = Ok decl)
    (grammar: decl.grammar1 = True):
    ∃ (twin: Decl) => groupRun seen other = Ok twin
      ∧ twin.walk blankPure = decl.walk blankPure
      ∧ twin.grammar1 = True
      ∧ twin.loweringError = decl.loweringError :=
  let (twin, twinRuns, alike) := groupKeepsTokens seen group other decl same runs
  let twinGrammar: twin.grammar1 = True := calc twin.grammar1
    _ = (twin.walk blankPure).grammar1 := grammar1Deaf twin
    _ = (decl.walk blankPure).grammar1 := rewrite alike
    _ = decl.grammar1 := Eq.flipped (grammar1Deaf decl)
    _ = True := grammar
  let twinLowered: twin.loweringError = decl.loweringError := calc twin.loweringError
    _ = (twin.walk blankPure).loweringError := loweringDeaf twin
    _ = (decl.walk blankPure).loweringError := rewrite alike
    _ = decl.loweringError := Eq.flipped (loweringDeaf decl)
  (twin, twinRuns, alike, twinGrammar, twinLowered)

-- The file.

theorem parseGroupsStep ∀ (seen: Seen) (group: List Leaf) (rest: List (List Leaf)) (found: List Decl):
    parseGroups seen [group, ..rest] found = groupRan seen rest found (groupRun seen group) :=
  byComputing

--| Every slice 1 declaration is a definition, which a file's `Seen` counts as a declaration.
theorem seenAfter1 ∀ (seen: Seen) (decl: Decl)
    (grammar: decl.grammar1 = True):
    seen.after decl = { seen | hasDecls = True } :=
  match decl with | Definition _ _ _ => byComputing

theorem walkDeclsMap ∀ (p: Pure) (decls: List Decl): walkDecls p decls = decls.map (decl => decl.walk p) :=
  match decls with
    | [] => byComputing
    | [decl, ..rest] => rewrite walkDeclsMap p rest

theorem walkDeclsReverse ∀ (p: Pure) (decls: List Decl): walkDecls p decls.reverse = (walkDecls p decls).reverse :=
  calc walkDecls p decls.reverse
    _ = decls.reverse.map (decl => decl.walk p) := walkDeclsMap p decls.reverse
    _ = (decls.map (decl => decl.walk p)).reverse := List.mapReverse decls (decl => decl.walk p)
    _ = (walkDecls p decls).reverse := rewrite walkDeclsMap p decls

theorem reversedCons ∀ (decl: Decl) (found more: List Decl):
    [decl, ..found].reverse ++ more = found.reverse ++ [decl, ..more] :=
  calc [decl, ..found].reverse ++ more
    _ = (found.reverse ++ [decl]) ++ more := rewrite List.reverseCons decl found
    _ = found.reverse ++ [decl, ..more] := List.appendAssoc found.reverse [decl] more

--| What `parseGroups` gives starts with the declarations already found.
theorem groupsPrefix ∀ (seen: Seen) (groups: List (List Leaf)) (found decls: List Decl)
    (runs: parseGroups seen groups found = Ok decls):
    ∃ (more: List Decl) => decls = found.reverse ++ more :=
  match groups with
    | [] =>
      let done: (Ok found.reverse: Result (List Decl) Text) = Ok decls := runs
      let isDecls: found.reverse = decls := Result.okInjective done
      ([], rewrite <- isDecls then Eq.flipped (List.appendNil found.reverse))
    | [group, ..rest] =>
      let stepped: groupRan seen rest found (groupRun seen group) = Ok decls :=
        rewrite <- parseGroupsStep seen group rest found then runs
      match ran: groupRun seen group with
        | Ok decl =>
          match lowered: decl.loweringError with
            | None =>
              let later: parseGroups (seen.after decl) rest [decl, ..found] = Ok decls := stepped
              let (more, starts) := groupsPrefix (seen.after decl) rest [decl, ..found] decls later
              ([decl, ..more], rewrite starts then reversedCons decl found more)

--| The groups' declarations, parsed from groups with the same tokens and with found declarations alike up to
--| comments: alike up to comments, and slice 1's.
--|
--| Proof idea: by induction on the groups. Each group's declaration is in the result (`groupsPrefix`), so it is
--| slice 1's, and `groupKeepsTokens1` parses its twin, with no lowering error and the same `Seen` after it.
theorem groupsKeepTokens1 ∀ (seen: Seen) (groups others: List (List Leaf)) (found founds decls: List Decl)
    (same: groupTokens groups = groupTokens others)
    (sameFound: walkDecls blankPure founds = walkDecls blankPure found)
    (foundsGrammar: founds.all Decl.grammar1 = True)
    (runs: parseGroups seen groups found = Ok decls)
    (grammar: decls.all Decl.grammar1 = True):
    ∃ (twins: List Decl) => parseGroups seen others founds = Ok twins
      ∧ walkDecls blankPure twins = walkDecls blankPure decls
      ∧ twins.all Decl.grammar1 = True :=
  match groups, others with
    | [], [] =>
      let done: (Ok found.reverse: Result (List Decl) Text) = Ok decls := runs
      let isDecls: found.reverse = decls := Result.okInjective done
      let alike: walkDecls blankPure founds.reverse = walkDecls blankPure decls := calc walkDecls blankPure
          founds.reverse
        _ = (walkDecls blankPure founds).reverse := walkDeclsReverse blankPure founds
        _ = (walkDecls blankPure found).reverse := rewrite sameFound
        _ = walkDecls blankPure found.reverse := Eq.flipped (walkDeclsReverse blankPure found)
        _ = walkDecls blankPure decls := rewrite isDecls
      (founds.reverse, byComputing, alike, List.allReverseTrue Decl.grammar1 founds foundsGrammar)
    | [group, ..rest], [other, ..later] =>
      let headSame: tokens group = tokens other := Eq.cong (all => all.headOr (tokens group)) same
      let tailSame: groupTokens rest = groupTokens later := Eq.cong (all => all.drop 1) same
      let stepped: groupRan seen rest found (groupRun seen group) = Ok decls :=
        rewrite <- parseGroupsStep seen group rest found then runs
      match ran: groupRun seen group with
        | Ok decl =>
          match lowered: decl.loweringError with
            | None =>
              let next: parseGroups (seen.after decl) rest [decl, ..found] = Ok decls := stepped
              let (more, starts) := groupsPrefix (seen.after decl) rest [decl, ..found] decls next
              let split: (found.reverse ++ [decl, ..more]).all Decl.grammar1 = True :=
                rewrite <- reversedCons decl found more, <- starts then grammar
              let declGrammar: decl.grammar1 = True :=
                Bool.andLeft (List.allAppendRightTrue Decl.grammar1 found.reverse [decl, ..more] split)
              let (twin, twinRuns, twinAlike, twinGrammar, twinLowered) :=
                groupKeepsTokens1 seen group other decl headSame ran declGrammar
              let seenSame: seen.after twin = seen.after decl :=
                rewrite seenAfter1 seen twin twinGrammar, seenAfter1 seen decl declGrammar
              let foundAlike: walkDecls blankPure [twin, ..founds] = walkDecls blankPure [decl, ..found] :=
                rewrite twinAlike, sameFound
              let (twins, twinsRun, twinsAlike, twinsGrammar) :=
                groupsKeepTokens1
                  (seen.after decl)
                  rest
                  later
                  [decl, ..found]
                  [twin, ..founds]
                  decls
                  tailSame
                  foundAlike
                  (Bool.andIntro twinGrammar foundsGrammar)
                  next
                  grammar
              let twinNone: twin.loweringError = None := rewrite twinLowered then lowered
              let otherStep: groupRan seen later founds (groupRun seen other) = Ok twins :=
                rewrite twinRuns, twinNone, seenSame then twinsRun
              (twins, rewrite parseGroupsStep seen other later founds then otherStep, twinsAlike, twinsGrammar)

theorem refusalTokens ∀ (leaves others: List Leaf)
    (same: tokens leaves = tokens others):
    fileRefusal leaves = fileRefusal others :=
  match leaves, others with
    | [], [] => byComputing
    | [first, .._], [twin, .._] =>
      let headSame: first.token = twin.token := Eq.cong (all => all.headOr first.token) same
      rewrite headSame

theorem parseFileGroups1 ∀ (lexed: Lexed)
    (none: fileRefusal lexed.leaves = None):
    parseFile lexed = fileEnd lexed (parseGroups Seen.start (groupsOf lexed.leaves) []) :=
  rewrite none

def bareFile (decls: List Decl): SourceFile := { decls, end = Comments.none }

theorem withoutCommentsWalk ∀ (file: SourceFile): file.withoutComments = bareFile (walkDecls blankPure file.decls) :=
  Eq.cong bareFile (applyDeclsWalk blankSteps blankPure blankAgrees file.decls)

--| The parser's file layer: leaves with the same tokens as leaves whose file is slice 1's parse to a file alike up
--| to comments, and slice 1's, given `groupKeepsTokens1`.
theorem parseKeepsTokens1 ∀ (lexed other: Lexed) (file: SourceFile)
    (same: tokens lexed.leaves = tokens other.leaves)
    (parses: parseFile lexed = Ok file)
    (grammar: file.grammar1 = True):
    ∃ (twin: SourceFile) => parseFile other = Ok twin
      ∧ twin.withoutComments = file.withoutComments
      ∧ twin.grammar1 = True :=
  let refusal: fileRefusal lexed.leaves = fileRefusal other.leaves := refusalTokens lexed.leaves other.leaves same
  let groupsSame: groupTokens (groupsOf lexed.leaves) = groupTokens (groupsOf other.leaves) :=
    splitTokens Splitter.start [] [] [] [] lexed.leaves other.leaves same byComputing byComputing
  match refused: fileRefusal lexed.leaves with
    | None =>
      let grouped: fileEnd lexed (parseGroups Seen.start (groupsOf lexed.leaves) []) = Ok file :=
        rewrite <- parseFileGroups1 lexed refused then parses
      match ranGroups: parseGroups Seen.start (groupsOf lexed.leaves) [] with
        | Ok decls =>
          let built: (Ok { decls, end = lexed.end.comments }: Result SourceFile Text) = Ok file := grouped
          let isFile: { decls, end = lexed.end.comments } = file := Result.okInjective built
          let declsGrammar: decls.all Decl.grammar1 = True := rewrite <- isFile at grammar then grammar
          let (twins, twinsRun, twinsAlike, twinsGrammar) :=
            groupsKeepTokens1 Seen.start
              (groupsOf lexed.leaves)
              (groupsOf other.leaves)
              []
              []
              decls
              groupsSame
              byComputing
              byComputing
              ranGroups
              declsGrammar
          let otherNone: fileRefusal other.leaves = None := rewrite <- refusal then refused
          let twin: SourceFile := { decls = twins, end = other.end.comments }
          let twinParses: parseFile other = Ok twin := rewrite parseFileGroups1 other otherNone, twinsRun
          let alike: twin.withoutComments = file.withoutComments := calc twin.withoutComments
            _ = bareFile (walkDecls blankPure twins) := withoutCommentsWalk twin
            _ = bareFile (walkDecls blankPure decls) := Eq.cong bareFile twinsAlike
            _ = ({ decls, end = lexed.end.comments }: SourceFile).withoutComments :=
              Eq.flipped (withoutCommentsWalk { decls, end = lexed.end.comments })
            _ = file.withoutComments := rewrite isFile
          (twin, twinParses, alike, twinsGrammar)

-- Comment placement.

--| `settledParses1` for leaves whose tokens comment placement keeps.
theorem settledParsesKept1 ∀ (lexed: Lexed) (file: SourceFile)
    (parses: parseFile lexed = Ok file)
    (grammar: file.grammar1 = True)
    (kept: tokens lexed.settledOnce.leaves = tokens lexed.leaves):
    ∃ (settled: SourceFile) => parseFile lexed.settledOnce = Ok settled
      ∧ settled.withoutComments = file.withoutComments
      ∧ settled.grammar1 = True :=
  parseKeepsTokens1 lexed lexed.settledOnce file (Eq.flipped kept) parses grammar

--| Comment placement keeps the parse: leaves whose own parse is a slice 1 tree parse after comment placement (as the driver parses them)
--| to a slice 1 tree that is the same but for comments. Comment placement keeps every token (`settledOnceTokens`): a closer
--| after a last comma that starts its line is read as starting it inside comment placement's walk, not marked in its token.
theorem settledParses1 ∀ (lexed: Lexed) (file: SourceFile)
    (parses: parseFile lexed = Ok file)
    (grammar: file.grammar1 = True):
    ∃ (settled: SourceFile) => parseFile lexed.settledOnce = Ok settled
      ∧ settled.withoutComments = file.withoutComments
      ∧ settled.grammar1 = True :=
  settledParsesKept1 lexed file parses grammar (settledOnceTokens lexed)

--| Comment placement keeps the parse of every source of slice 1's grammar: the source's own parse is a slice 1 tree, and the
--| leaves the driver parses (after comment placement) parse to a slice 1 tree that is the same but for comments.
theorem settledParsesGrammar1 ∀ (source: Text) (lexed: Lexed) (file: SourceFile)
    (lexes: lex source = Ok lexed)
    (alphabet: lexed.leaves.all (leaf => leaf.token.kind.alphabet1) = True)
    (parses: parseFile lexed = Ok file)
    (grammar: file.grammar1 = True):
    ∃ (settled: SourceFile) => parseFile lexed.settledOnce = Ok settled
      ∧ settled.withoutComments = file.withoutComments
      ∧ settled.grammar1 = True :=
  settledParses1 lexed file parses grammar

-- Closed examples (D3684).

--| What `settledParses1` says of one source, as a test: lexed, parsed to a slice 1 tree; and parsed after comment placement to a
--| slice 1 tree with the same blanked declarations.
def settlesOn (source: Text): Bool := match lex source with
  | Err _ => False
  | Ok lexed =>
    match parseFile lexed, parseFile lexed.settledOnce with
      | Ok file, Ok settled => file.grammar1 && settled.grammar1 && settled.withoutComments == file.withoutComments
      | _, _ => False

--| The driver's hypotheses on one source: the leaf tests, and `within1` of the tree after comment placement.
def placedOn (source: Text): Bool := match lex source with
  | Err _ => False
  | Ok lexed =>
    alphabet1 lexed.leaves
      && plain1 (tokens lexed.leaves)
      && match parseFile lexed.settledOnce with
        | Ok settled => settled.within1
        | Err _ => False

theorem placedOnExample: placedOn
        "-- top\ndef d: A -> -- arrow\n  B := g [ -- open\n    a, -- first\n    -- above\n    b, -- last\n  ] -- close\n\ndef e: C := (-1 + f x, y) -- end\n-- last\n"
      = True :=
  byComputing

--| Comments in every kind of place, which comment placement moves: after a comma, on a closer, after `->`, above a token.
theorem settlesOnExample: settlesOn
        "-- top\ndef d: A -> -- arrow\n  B := g [ -- open\n    a, -- first\n    -- above\n    b, -- last\n  ] -- close\n\ndef e: C := (-1 + f x, y) -- end\n-- last\n"
      = True :=
  byComputing

def ownLineCommaKeeps (source: Text): Bool := match lex source with
  | Err _ => False
  | Ok lexed =>
    match parseFile lexed, parseFile lexed.settledOnce with
      | Ok file, Ok settled => settled.withoutComments == file.withoutComments
      | _, _ => False

theorem ownLineCommaKeepsExample: ownLineCommaKeeps "def d: A := [a\n  , ]\n" = True := byComputing

--| What `groupKeepsTokens1` says of each group of one source and its settled twin, as a test: the hypotheses (the
--| same tokens, the group parses to a slice 1 declaration) and the conclusion.
def groupsKeepOn (source: Text): Bool := match lex source with
  | Err _ => False
  | Ok lexed => groupPairsKeep (groupsOf lexed.leaves) (groupsOf lexed.settledOnce.leaves)

def groupPairsKeep: List (List Leaf) → List (List Leaf) → Bool
  | [], [] => True
  | [group, ..rest], [other, ..later] =>
    groupPairsKeep rest later
      && tokens group == tokens other
      && match groupRun Seen.start group, groupRun Seen.start other with
        | Ok decl, Ok twin =>
          decl.grammar1
            && twin.grammar1
            && twin.walk blankPure == decl.walk blankPure
            && twin.loweringError == decl.loweringError
        | _, _ => False
  | _, _ => False

theorem groupsKeepOnExample: groupsKeepOn
        "-- top\ndef d: A -> -- arrow\n  B := g [ -- open\n    a, -- first\n    -- above\n    b, -- last\n  ] -- close\n\ndef e: C := (-1 + f x, y) -- end\n-- last\n"
      = True :=
  byComputing

--| A test on one source: it parses to a slice 1 tree whose every declaration has no
--| lowering error.
def lowersOn (source: Text): Bool := match lex source with
  | Err _ => False
  | Ok lexed =>
    match parseFile lexed with
      | Ok file => file.grammar1 && file.decls.all (decl => decl.loweringError == None)
      | Err _ => False

theorem declLowers1Example: lowersOn
        "-- top\ndef d: A -> -- arrow\n  B := g [ -- open\n    a, -- first\n    -- above\n    b, -- last\n  ] -- close\n\ndef e: C := (-1 + f x, y) -- end\n-- last\n"
      = True :=
  byComputing
