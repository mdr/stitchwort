/- SW-4537 batch B (the syntax side): seven drawn slice 1 theorems in Lean 4 (core and Std only).
   Counted theorems follow a `-- sample:` line; everything else is uncounted support
   (cut-down definitions, and lemmas the Stitchwort proof names, as axioms).
   Check: nix shell nixpkgs#lean4 -c lean BatchB.lean -/

/-! ## settle 3: `homeStands` (Fmt/SettleOutputProofs.sw) -/
namespace HomeStands

/-- Cut down from `Syntax.Tok`: one word kind, the comma, one closer, and `|` (outside slice 1). -/
inductive Tok
  | Lower | Comma | RParen | Pipe
  deriving DecidableEq

def Tok.isCloser : Tok → Bool
  | .RParen => true
  | _ => false

/-- Cut down from `Fmt/Slice1.sw`: `|` is the one kind here outside slice 1. -/
def Tok.within1 : Tok → Bool
  | .Pipe => false
  | _ => true

structure Comment where
  text : String
  column : Nat
  blankLines : Nat
  deriving DecidableEq

structure Trivia where
  leading : List Comment
  blankLines : Nat
  trailing : Option Comment
  deriving DecidableEq

structure Token where
  kind : Tok
  text : String
  column : Nat
  lineStart : Bool
  deriving DecidableEq

structure Leaf where
  token : Token
  trivia : Trivia
  deriving DecidableEq

structure Note where
  text : String
  blankBefore : Bool
  deriving DecidableEq

structure Comments where
  above : List Note
  after : Option String
  blankBefore : Bool
  deriving DecidableEq

structure Word where
  text : String
  comments : Comments
  deriving DecidableEq

def Leaf.kind (leaf : Leaf) : Tok := leaf.token.kind

def Leaf.withTrailing (leaf : Leaf) (trailing : Option Comment) : Leaf :=
  { leaf with trivia := { leaf.trivia with trailing } }

def Leaf.withLeading (leaf : Leaf) (leading : List Comment) : Leaf :=
  { leaf with trivia := { leaf.trivia with leading } }

def Comment.unspaced (comment : Comment) : Comment := { comment with blankLines := 0 }

def Leaf.word (leaf : Leaf) : Word :=
  { text := leaf.token.text,
    comments := { above := leaf.trivia.leading.map fun c => { text := c.text, blankBefore := c.blankLines > 0 },
                  after := leaf.trivia.trailing.map (·.text),
                  blankBefore := leaf.trivia.blankLines > 0 } }

def Word.trails (word : Word) : Bool := word.comments.after.isSome
def Word.noted (word : Word) : Bool := !word.comments.above.isEmpty
def isCloserText (text : String) : Bool := text == ")" || text == "]" || text == "}"

def trailsBack : List Word → Bool
  | [] => false
  | word :: rest => word.trails || (isCloserText word.text && trailsBack rest)

def homedBack : List Word → Bool
  | [] => true
  | word :: earlier =>
    (!(isCloserText word.text && word.trails) || earlier.isEmpty || word.noted || trailsBack earlier)
      && homedBack earlier

def Leaf.headedAs (leaf : Leaf) (word : Word) : Bool :=
  leaf.token.text == word.text
    && leaf.word.comments.above == word.comments.above
    && leaf.word.comments.blankBefore == word.comments.blankBefore

def tucked (owed : Option String) (leaf : Leaf) : Option (Option String) :=
  match owed, leaf.trivia.trailing with
  | none, none => some none
  | none, some _ => none
  | some _, none => if leaf.token.lineStart then none else some owed
  | some text, some comment => if leaf.token.lineStart || !(comment.text == text) then none else some none

def stands (owed : Option String) (words : List Word) : List Leaf → Bool
  | [] => words.isEmpty && owed.isNone
  | leaf :: rest =>
    if leaf.kind == .Comma then
      leaf.trivia.leading.isEmpty && leaf.trivia.blankLines == 0
        && (match tucked owed leaf with
          | none => false
          | some still => stands still words rest)
    else
      match words with
      | [] => false
      | word :: later =>
        leaf.headedAs word
          && (match owed, word.comments.after with
            | some _, some _ => false
            | some _, none =>
              leaf.kind.isCloser
                && (match tucked owed leaf with
                  | none => false
                  | some still => stands still later rest)
            | none, none => leaf.trivia.trailing.isNone && stands none later rest
            | none, some text =>
              (!leaf.kind.isCloser || leaf.token.lineStart)
                && (match leaf.trivia.trailing with
                  | none => stands (some text) later rest
                  | some comment => comment.text == text && stands none later rest))

def passable (leaf : Leaf) : Bool := leaf.kind == .Comma || leaf.kind.isCloser

def endsOn : List Leaf → Bool
  | [] => false
  | leaf :: earlier =>
    if leaf.trivia.trailing.isSome then true
    else if earlier.isEmpty || !passable leaf then false
    else endsOn earlier

def stopsAt (leaf : Leaf) (older : List Leaf) : Bool :=
  leaf.token.lineStart && (!leaf.trivia.leading.isEmpty || endsOn older)

def chainTo : Nat → List Leaf → Bool
  | 1, target :: older => !passable target || older.isEmpty || stopsAt target older
  | more + 2, leaf :: earlier => passable leaf && !leaf.token.lineStart && chainTo (more + 1) earlier
  | _, _ => false

def trailingAt : List Leaf → Nat → Comment → List Leaf
  | leaf :: earlier, 1, comment => leaf.withTrailing (some comment) :: earlier
  | leaf :: earlier, more + 2, comment => leaf :: trailingAt earlier (more + 1) comment
  | behind, _, _ => behind

def tokens (leaves : List Leaf) : List Token := leaves.map (·.token)

/- Rule 1's `movable`, `stepsBack` and `barBelow` look at record-update bars (`recordBar`), which slice 1 never
   reaches; the proof uses them only through `movableQuiet1`, `chainSteps`, `landedHere` and `barsQuiet1`, so they
   are opaque here. -/
opaque movable : Leaf → List Leaf → List Leaf → Bool
opaque stepsBack : Bool → Leaf → List Leaf → List Leaf → Nat → Nat
opaque barBelow : Leaf → List Leaf → List Leaf → Bool

def homeFrom (bareLast : Bool) (behind : List Leaf) (bumped : Option Comment) : List Leaf → List Leaf
  | [] => behind.reverse
  | leaf :: after =>
    let leaf := (bumped.map fun comment => leaf.withLeading (comment :: leaf.trivia.leading)).getD leaf
    match leaf.trivia.trailing with
    | some comment =>
      if movable leaf behind after then
        match stepsBack bareLast leaf behind after 0 with
        | 0 =>
          if barBelow leaf behind after then
            homeFrom bareLast (leaf.withTrailing none :: behind) (some comment.unspaced) after
          else homeFrom bareLast (leaf :: behind) none after
        | steps => homeFrom bareLast (leaf.withTrailing none :: trailingAt behind steps comment) none after
      else homeFrom bareLast (leaf :: behind) none after
    | none => homeFrom bareLast (leaf :: behind) none after

def Leaf.agrees (leaf : Leaf) : Bool := leaf.kind.isCloser == isCloserText leaf.token.text

def Leaf.fits (leaf : Leaf) (word : Word) : Bool :=
  leaf.headedAs word && leaf.trivia.trailing.map (·.text) == word.comments.after && leaf.agrees

def Leaf.bare (leaf : Leaf) : Bool := leaf.trivia.trailing.isNone && leaf.trivia.leading.isEmpty

def matched : List Leaf → List Word → Bool
  | [], done => done.isEmpty
  | leaf :: earlier, done =>
    if leaf.kind == .Comma then !done.isEmpty && leaf.bare && matched earlier done
    else
      match done with
      | [] => false
      | word :: older => leaf.fits word && matched earlier older

def lands (leaf : Leaf) (earlier : List Leaf) : Bool := !passable leaf || earlier.isEmpty || stopsAt leaf earlier

def owing (text : String) : List Leaf → List Word → Bool
  | [], _ => false
  | leaf :: earlier, done =>
    if leaf.kind == .Comma then leaf.bare && !leaf.token.lineStart && owing text earlier done
    else
      match done with
      | [] => false
      | word :: older =>
        if word.comments.after == some text then
          leaf.trivia.trailing.isNone && leaf.headedAs word && leaf.agrees && lands leaf earlier
            && matched earlier older
        else leaf.kind.isCloser && !leaf.token.lineStart && leaf.fits word && owing text earlier older

def held (owed : Option String) (behind : List Leaf) (done : List Word) : Bool :=
  match owed with
  | none => matched behind done
  | some text => owing text behind done

def notCommaFirst : List Leaf → Bool
  | [] => true
  | leaf :: _ => !(leaf.kind == .Comma)

def kindWithin (leaf : Leaf) : Bool := leaf.kind.within1

axiom movableQuiet1 (leaf : Leaf) (behind ahead : List Leaf) (within : leaf.kind.within1 = true) :
    movable leaf behind ahead = ((leaf.kind == .Comma && !leaf.token.lineStart) || leaf.kind.isCloser)

axiom barsQuiet1 (leaf : Leaf) (behind ahead : List Leaf) (within : leaf.kind.within1 = true) :
    barBelow leaf behind ahead = false

axiom chainSteps (current : Leaf) (behind ahead : List Leaf) (steps acc : Nat)
    (within : current.kind.within1 = true) (behindWithin : behind.all (·.kind.within1) = true)
    (passes : passable current = true) (notStart : current.token.lineStart = false)
    (chain : chainTo steps behind = true) :
    stepsBack false current behind ahead acc = acc + steps

axiom landedHere (leaf : Leaf) (older ahead : List Leaf) (steps : Nat)
    (within : leaf.kind.within1 = true) (olderWithin : older.all (·.kind.within1) = true)
    (lands : (!passable leaf || older.isEmpty || stopsAt leaf older) = true) :
    stepsBack false leaf older ahead steps = steps

axiom withinOfTokens (xs ys : List Leaf) (same : tokens xs = tokens ys)
    (within : ys.all (·.kind.within1) = true) : xs.all (·.kind.within1) = true

axiom trailingAtTokens (behind : List Leaf) (steps : Nat) (comment : Comment) :
    tokens (trailingAt behind steps comment) = tokens behind

axiom owingNonEmpty (text : String) (behind : List Leaf) (done : List Word)
    (owes : owing text behind done = true) : (!done.isEmpty) = true

axiom homedReverseOnto (xs ys : List Word) (homed : homedBack (xs.reverseAux ys) = true) : homedBack ys = true

axiom landing (leaf : Leaf) (word : Word) (behind : List Leaf) (done : List Word)
    (notComma : (leaf.kind == .Comma) = false) (headed : leaf.headedAs word = true)
    (agrees : leaf.agrees = true) (trails : word.comments.after.isSome = true)
    (open_ : (!leaf.kind.isCloser || leaf.token.lineStart) = true)
    (m : matched behind done = true) (homed : homedBack (word :: done) = true) :
    lands leaf behind = true

axiom owingPlaced (text : String) (behind : List Leaf) (done : List Word) (comment : Comment)
    (owes : owing text behind done = true) (named : comment.text = text) :
    ∃ steps, chainTo (steps + 1) behind = true ∧ matched (trailingAt behind (steps + 1) comment) done = true

-- sample: homeStands
theorem homeStands (owed : Option String) (behind rest : List Leaf) (done words : List Word)
    (standing : stands owed words rest = true)
    (state : held owed behind done = true)
    (lead : (!done.isEmpty || notCommaFirst rest) = true)
    (homed : homedBack (words.reverseAux done) = true)
    (behindWithin : behind.all kindWithin = true)
    (within : rest.all kindWithin = true)
    (agree : rest.all Leaf.agrees = true) :
    matched (homeFrom false behind none rest).reverse (words.reverseAux done) = true := by
  induction rest generalizing owed behind done words with
  | nil => cases owed <;> cases words <;> simp_all [stands, homeFrom, held]
  | cons leaf after ih =>
    simp only [List.all_cons, Bool.and_eq_true] at within agree
    have pushed : (leaf :: behind).all kindWithin = true := by simp_all [kindWithin]
    -- a moved comment's target keeps its tokens, so stays within slice 1
    have target : ∀ steps comment,
        (leaf.withTrailing none :: trailingAt behind steps comment).all kindWithin = true := by
      intro steps comment
      have := withinOfTokens _ behind (trailingAtTokens behind steps comment) behindWithin
      simp_all [kindWithin, Leaf.withTrailing, Leaf.kind]
    by_cases comma : leaf.kind = .Comma
    · have filled : (!done.isEmpty) = true := by
        cases owed with
        | none => simpa [notCommaFirst, comma] using lead
        | some text => exact owingNonEmpty text behind done state
      simp only [stands, comma, beq_self_eq_true, ite_true, Bool.and_eq_true] at standing
      obtain ⟨⟨leading, -⟩, tuck⟩ := standing
      rcases owed with _ | text <;> rcases trailing : leaf.trivia.trailing with _ | comment <;>
        simp only [tucked, trailing, Bool.false_eq_true] at tuck
      · -- nothing owed, nothing held
        simp only [homeFrom, trailing, Option.map_none, Option.getD_none]
        exact ih none _ done words tuck (by simp_all [held, matched, Leaf.bare]) (by simp [filled])
          homed pushed within.2 agree.2
      · -- a comment owed, carried past the comma
        cases start : leaf.token.lineStart <;> simp [start] at tuck
        simp only [homeFrom, trailing, Option.map_none, Option.getD_none]
        exact ih (some text) _ done words tuck (by simp_all [held, owing, Leaf.bare])
          (by simp [filled]) homed pushed within.2 agree.2
      · -- the comma holds the owed comment: it walks back to its word
        cases start : leaf.token.lineStart <;> by_cases named : comment.text = text <;>
          simp [start, named] at tuck
        obtain ⟨steps, chain, placed⟩ := owingPlaced text behind done comment state named
        have walked := chainSteps leaf behind after (steps + 1) 0 within.1 behindWithin
          (by simp [passable, comma]) start chain
        simp only [homeFrom, trailing, Option.map_none, Option.getD_none,
          movableQuiet1 leaf behind after within.1, comma, start, walked, Nat.zero_add]
        refine ih none _ done words tuck ?_ (by simp [filled]) homed (target _ _) within.2 agree.2
        simp [held, matched, Leaf.kind, Leaf.bare, Leaf.withTrailing,
          show leaf.token.kind = _ from comma, filled, leading, placed]
    · obtain _ | ⟨word, later⟩ := words
      · simp [stands, comma] at standing
      simp only [stands, comma, beq_iff_eq, ite_false, Bool.and_eq_true] at standing
      obtain ⟨headed, clause⟩ := standing
      have fitted : ∀ moved : Leaf, moved.token = leaf.token →
          moved.trivia.leading = leaf.trivia.leading →
          moved.trivia.blankLines = leaf.trivia.blankLines →
          moved.trivia.trailing.map (·.text) = word.comments.after → moved.fits word = true := by
        intro moved token leading blank after
        simp_all [Leaf.fits, Leaf.headedAs, Leaf.word, Leaf.agrees, Leaf.kind]
      rcases owed with _ | text <;> rcases afterIs : word.comments.after with _ | text' <;>
        simp only [afterIs] at clause
      · -- nothing owed, no comment on the word
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at clause
        simp only [homeFrom, clause.1, Option.map_none, Option.getD_none]
        exact ih none _ (word :: done) later clause.2
          (by simp_all [held, matched]) (by simp) homed pushed within.2 agree.2
      · -- the word's own comment: on the leaf, or owed on
        simp only [Bool.and_eq_true] at clause
        obtain ⟨open_, tuck⟩ := clause
        have landsHere := landing leaf word behind done (by simpa using comma) headed agree.1
          (by simp [afterIs]) open_ state (homedReverseOnto later (word :: done) homed)
        rcases trailing : leaf.trivia.trailing with _ | comment <;> simp only [trailing] at tuck
        · simp only [homeFrom, trailing, Option.map_none, Option.getD_none]
          exact ih (some text') _ (word :: done) later tuck
            (by simp_all [held, owing]) (by simp) homed pushed within.2 agree.2
        · simp only [Bool.and_eq_true, beq_iff_eq] at tuck
          have kept := ih none (leaf :: behind) (word :: done) later tuck.2
            (by simp_all [held, matched]) (by simp) homed pushed within.2 agree.2
          simp only [homeFrom, trailing, Option.map_none, Option.getD_none]
          split
          · rw [landedHere leaf behind after 0 within.1 behindWithin landsHere,
              barsQuiet1 leaf behind after within.1]
            exact kept
          · exact kept
      · -- an earlier word's comment owed: the leaf is a closer carrying it
        simp only [Bool.and_eq_true] at clause
        obtain ⟨closer, tuck⟩ := clause
        rcases trailing : leaf.trivia.trailing with _ | comment <;>
          cases start : leaf.token.lineStart <;> simp [tucked, trailing, start] at tuck
        · simp only [homeFrom, trailing, Option.map_none, Option.getD_none]
          exact ih (some text) _ (word :: done) later tuck
            (by simp_all [held, owing]) (by simp) homed pushed within.2 agree.2
        · by_cases named : comment.text = text <;> simp [named] at tuck
          obtain ⟨steps, chain, placed⟩ := owingPlaced text behind done comment state named
          have walked := chainSteps leaf behind after (steps + 1) 0 within.1 behindWithin
            (by simp [passable, closer]) start chain
          simp only [homeFrom, trailing, Option.map_none, Option.getD_none,
            movableQuiet1 leaf behind after within.1, closer, walked, Nat.zero_add, Bool.or_true]
          refine ih none _ (word :: done) later tuck ?_ (by simp) homed (target _ _)
            within.2 agree.2
          have moved :=
            fitted (leaf.withTrailing none) rfl rfl rfl (by simp [Leaf.withTrailing, afterIs])
          dsimp only [Leaf.withTrailing] at moved ⊢
          simp [held, matched, Leaf.kind, show leaf.token.kind ≠ .Comma from comma, moved, placed]
      · simp at clause

end HomeStands

/-! ## settle 2: `settledHomed` (Syntax/SettleProofs.sw) -/
namespace SettledHomed

/- The proof chains lemmas about rule N's passes, so the passes and most predicates are opaque; only what it
   computes with is defined: `tokens`, the empty cases of `homedBehind`, `related` and `walkClean`, and
   `Lexed.settled`. -/
axiom Tok : Type
axiom Tok.within1 : Tok → Bool
axiom Comment : Type
axiom Carried : Type

noncomputable section

/-- Cut down from `Syntax.Token`: `text` and `column` dropped. -/
structure Token where
  kind : Tok
  lineStart : Bool

/-- Cut down from `Syntax.Trivia`: `blankLines` dropped. -/
structure Trivia where
  leading : List Comment
  trailing : Option Comment

structure Leaf where
  token : Token
  trivia : Trivia

structure Lexed where
  leaves : List Leaf
  «end» : Trivia

def Leaf.kind (leaf : Leaf) : Tok := leaf.token.kind
def tokens (leaves : List Leaf) : List Token := leaves.map (·.token)

axiom homedLeaf : Leaf → List Leaf → Bool
def homedBehind : List Leaf → Bool
  | [] => true
  | leaf :: older => homedLeaf leaf older && homedBehind older

axiom relatedLeaf : Leaf → Leaf → Bool
def related : List Leaf → List Leaf → Bool
  | [], [] => true
  | before :: befores, after :: afters => relatedLeaf before after && related befores afters
  | _, _ => false

axiom skipped : Leaf → List Leaf → List Leaf → Bool
axiom endsWithComment : List Leaf → List Leaf → Bool
def walkClean (current : Leaf) (behind ahead : List Leaf) : Bool :=
  match behind with
  | [] => true
  | previous :: earlier =>
    if !skipped current behind ahead then true
    else if current.token.lineStart
      && (!current.trivia.leading.isEmpty || endsWithComment behind (current :: ahead)) then true
    else current.trivia.leading.isEmpty && previous.trivia.trailing.isNone
      && walkClean previous earlier (current :: ahead)

def CleanFor (behind : List Leaf) (pending : Bool) : Prop :=
  ∀ (next : Leaf) (ahead : List Leaf), (next.trivia.leading.isEmpty || next.token.lineStart) = true →
    (!pending || next.token.lineStart) = true → walkClean next behind ahead = true

axiom alphabet1 : List Leaf → Bool
axiom laidOut : Bool → List Leaf → Bool
axiom plain1 : List Token → Bool
axiom plainFrom : List Token → Bool
axiom backOk : List Token → Bool
axiom homeFrom : Bool → List Leaf → Option Comment → List Leaf → List Leaf
axiom commasFrom : List Leaf → Option Carried → List Leaf → Trivia → Lexed
axiom arrows : List Leaf → List Leaf
axiom letsFrom : List Leaf → List Leaf → List Leaf
axiom Trivia.trimmed : Trivia → Trivia

def Lexed.settledWith (lexed : Lexed) (bareLast : Bool) : Lexed :=
  let homed := homeFrom bareLast [] none lexed.leaves
  let commas := commasFrom [] none homed lexed.end
  let leaves := letsFrom [] (arrows commas.leaves)
  { leaves := leaves.map fun leaf => { leaf with trivia := leaf.trivia.trimmed }, «end» := commas.end.trimmed }

def Lexed.settled (lexed : Lexed) : Lexed := lexed.settledWith false

axiom alphabet1Leaves (leaves : List Leaf) (within : alphabet1 leaves = true) :
    leaves.all (·.kind.within1) = true
axiom homeFromTokens (bareLast : Bool) (behind : List Leaf) (bumped : Option Comment) (rest : List Leaf) :
    tokens (homeFrom bareLast behind bumped rest) = tokens (behind.reverseAux rest)
axiom commasFromTokens (done : List Leaf) (carried : Option Carried) (rest : List Leaf) (e : Trivia) :
    tokens (commasFrom done carried rest e).leaves = tokens (done.reverseAux rest)
axiom arrowsTokens (leaves : List Leaf) : tokens (arrows leaves) = tokens leaves
axiom trimmedTokens (leaves : List Leaf) :
    tokens (leaves.map fun leaf => { leaf with trivia := leaf.trivia.trimmed }) = tokens leaves
axiom homeFromHomed (behind rest : List Leaf) (pending : Bool) (clean : CleanFor behind pending)
    (laid : laidOut pending rest = true) (behindWithin : behind.all (·.kind.within1) = true)
    (restWithin : rest.all (·.kind.within1) = true) (homed : homedBehind behind = true) :
    homedBehind ((homeFrom false behind none rest).reverseAux []) = true
axiom homedTransfer (befores afters : List Leaf) (same : tokens befores = tokens afters)
    (rel : related befores afters = true) (ok : backOk (tokens befores) = true)
    (homed : homedBehind befores = true) : homedBehind afters = true
axiom tokensReversed (xs ys : List Leaf) (same : tokens xs = tokens ys) :
    tokens (xs.reverseAux []) = tokens (ys.reverseAux [])
axiom relatedReverseOnto (befores afters befores2 afters2 : List Leaf) (rel : related befores afters = true)
    (rel2 : related befores2 afters2 = true) :
    related (befores.reverseAux befores2) (afters.reverseAux afters2) = true
axiom commasRelated (doneBefore done : List Leaf) (carried : Option Carried) (rest : List Leaf) (e : Trivia)
    (rel : related doneBefore done = true) :
    related (doneBefore.reverseAux rest) (commasFrom done carried rest e).leaves = true
axiom backOkOf (leaves : List Leaf) (original : List Token) (same : tokens leaves = original)
    (plain : plain1 original = true) : backOk (tokens (leaves.reverseAux [])) = true
axiom arrowsRelatedAll (leaves : List Leaf) (plain : plainFrom (tokens leaves) = true) :
    related leaves (arrows leaves) = true
axiom plainFromOf (original : List Token) (plain : plain1 original = true) : plainFrom original = true
axiom withinOfTokens (xs ys : List Leaf) (same : tokens xs = tokens ys)
    (within : ys.all (·.kind.within1) = true) : xs.all (·.kind.within1) = true
axiom letsQuiet1 (behind rest : List Leaf) (behindWithin : behind.all (·.kind.within1) = true)
    (restWithin : rest.all (·.kind.within1) = true) : letsFrom behind rest = behind.reverseAux rest
axiom trimRelated (leaves : List Leaf) :
    related leaves (leaves.map fun leaf => { leaf with trivia := leaf.trivia.trimmed }) = true

-- sample: settledHomed
theorem settledHomed (lexed : Lexed) (within : alphabet1 lexed.leaves = true)
    (laid : laidOut false lexed.leaves = true) (plain : plain1 (tokens lexed.leaves) = true) :
    homedBehind (lexed.settled.leaves.reverseAux []) = true := by
  have leavesWithin := alphabet1Leaves lexed.leaves within
  let homed := homeFrom false [] none lexed.leaves
  let commas := commasFrom [] none homed lexed.end
  let arrowed := arrows commas.leaves
  have homedTokens : tokens homed = tokens lexed.leaves := homeFromTokens false [] none lexed.leaves
  have commasTokens : tokens commas.leaves = tokens lexed.leaves :=
    (commasFromTokens [] none homed lexed.end).trans homedTokens
  have arrowedTokens : tokens arrowed = tokens lexed.leaves := (arrowsTokens _).trans commasTokens
  have homed1 : homedBehind (homed.reverseAux []) = true :=
    homeFromHomed [] lexed.leaves false (fun _ _ _ _ => rfl) laid rfl leavesWithin rfl
  have homed2 : homedBehind (commas.leaves.reverseAux []) = true :=
    homedTransfer _ _ (tokensReversed _ _ (homedTokens.trans commasTokens.symm))
      (relatedReverseOnto _ _ [] [] (commasRelated [] [] none homed lexed.end rfl) rfl)
      (backOkOf _ _ homedTokens plain) homed1
  have homed3 : homedBehind (arrowed.reverseAux []) = true :=
    homedTransfer _ _ (tokensReversed _ _ (commasTokens.trans arrowedTokens.symm))
      (relatedReverseOnto _ _ [] [] (arrowsRelatedAll _ (commasTokens ▸ plainFromOf _ plain)) rfl)
      (backOkOf _ _ commasTokens plain) homed2
  have quiet : letsFrom [] arrowed = arrowed :=
    letsQuiet1 [] arrowed rfl (withinOfTokens arrowed lexed.leaves arrowedTokens leavesWithin)
  dsimp only [Lexed.settled, Lexed.settledWith]
  rw [quiet]
  exact homedTransfer _ _ (tokensReversed _ _ (trimmedTokens arrowed).symm)
    (relatedReverseOnto _ _ [] [] (trimRelated arrowed) rfl) (backOkOf _ _ arrowedTokens plain)
    homed3

end

end SettledHomed

/-! ## settle 1: `endsQuietJoin` (Fmt/SettleOutputProofs.sw) -/
namespace EndsQuietJoin

axiom Word : Type
/-- Opaque: `operatorTok word.text == Some Arrow`, which the proof never looks into. -/
axiom arrowText : Word → Bool

noncomputable def endsQuiet : List Word → Bool
  | [] => false
  | [word] => !arrowText word
  | _ :: rest => endsQuiet rest

-- sample: endsQuietJoin
theorem endsQuietJoin (xs ys : List Word) (quiet : endsQuiet ys = true) :
    endsQuiet (xs ++ ys) = true := by
  induction xs with
  | nil => exact quiet
  | cons x rest ih => cases rest <;> cases ys <;> simp_all [endsQuiet]

end EndsQuietJoin

/-! ## lexer 2: `headerResult1` (Fmt/SourcePlainProofs.sw) -/
namespace HeaderResult1

axiom Comments : Type
axiom Word : Type
axiom Word.text : Word → String
axiom Group : Type
axiom Expr : Type
axiom Expr.grammar1 : Expr → Bool
axiom isName1 : String → Bool

inductive DefKind
  | DefPlain | DefTheorem | DefInstance

structure Header where
  exportKeyword : Option Comments
  opaqueKeyword : Option Comments
  kind : DefKind
  keyword : Comments
  name : Word
  forallKeyword : Option Word
  params : List Group
  colon : Comments
  result : Expr
  decreasingClause : Option (Comments × Expr)
  unfoldingClause : Option (Comments × List Word)

noncomputable def Header.grammar1 : Header → Bool
  | ⟨none, none, .DefPlain, _, name, none, [], _, result, none, none⟩ => isName1 name.text && result.grammar1
  | _ => false

-- sample: headerResult1
theorem headerResult1 (header : Header) (grammar : header.grammar1 = true) :
    header.result.grammar1 = true := by
  unfold Header.grammar1 at grammar
  split at grammar <;> simp_all

end HeaderResult1

/-! ## lexer 3: `plainOfShapes` (Fmt/SourcePlainProofs.sw) -/
namespace PlainOfShapes

/-- Cut down from `Syntax.Tok`, keeping a kind of each shape. -/
inductive Tok
  | Lower | Comma | Arrow | RParen | LParen
  deriving DecidableEq

inductive PlainShape
  | ShapeComma | ShapeArrow | ShapeCloser | ShapeOther | ShapeNonItem
open PlainShape

def Tok.shape : Tok → PlainShape
  | .Comma => ShapeComma
  | .LParen => ShapeNonItem
  | .Arrow => ShapeArrow
  | .RParen => ShapeCloser
  | .Lower => ShapeOther

def Tok.isCloser : Tok → Bool
  | .RParen => true
  | _ => false

/-- Cut down from `Syntax.Token`: `text` and `column` dropped. -/
structure Token where
  kind : Tok
  lineStart : Bool

def tokenShapes (toks : List Token) : List PlainShape := toks.map (·.kind.shape)

def PlainShape.isItem : PlainShape → Bool
  | ShapeComma | ShapeNonItem => false
  | _ => true

def shapeStep (item : Bool) (prev next : PlainShape) : Bool :=
  match prev, next with
  | ShapeArrow, ShapeComma | ShapeArrow, ShapeCloser | ShapeArrow, ShapeArrow => false
  | ShapeComma, ShapeComma => false
  | ShapeComma, ShapeCloser => item
  | _, _ => true

def shapesFrom (item : Bool) (prev : PlainShape) : List PlainShape → Bool
  | [] => true
  | next :: rest => shapeStep item prev next && shapesFrom prev.isItem next rest

def passableKind (kind : Tok) : Bool := kind == .Comma || kind.isCloser
def arrowFollow (kind : Tok) : Bool := passableKind kind || kind == .Arrow

/-- Opaque: whether a token ends an item; the proof uses it only through `itemOfShape`. -/
opaque itemKind : Tok → Bool

def sourcePlainFrom (item : Bool) : List Token → Bool
  | first :: second :: rest =>
    (!(first.kind == .Arrow) || !arrowFollow second.kind)
      && (!(first.kind == .Comma && first.lineStart) || !passableKind second.kind || (second.kind.isCloser && item))
      && sourcePlainFrom (itemKind first.kind) (second :: rest)
  | _ => true

axiom itemOfShape (kind : Tok) : kind.shape.isItem = itemKind kind

axiom clauseArrow (flag : Bool) (first second : Token)
    (ok : shapeStep flag first.kind.shape second.kind.shape = true) :
    (!(first.kind == .Arrow) || !arrowFollow second.kind) = true

axiom clauseComma (flag : Bool) (first second : Token)
    (ok : shapeStep flag first.kind.shape second.kind.shape = true) :
    (!(first.kind == .Comma && first.lineStart) || !passableKind second.kind || (second.kind.isCloser && flag)) = true

-- sample: plainOfShapes
theorem plainOfShapes (flag : Bool) (first : Token) (rest : List Token)
    (runs : shapesFrom flag first.kind.shape (tokenShapes rest) = true) :
    sourcePlainFrom flag (first :: rest) = true := by
  induction rest generalizing flag first with
  | nil => simp [sourcePlainFrom]
  | cons second more ih =>
    simp only [tokenShapes, List.map_cons, shapesFrom, Bool.and_eq_true] at runs
    simp only [sourcePlainFrom, clauseArrow flag first second runs.1,
      clauseComma flag first second runs.1, ← itemOfShape, ih _ second runs.2, Bool.and_self]

end PlainOfShapes

/-! ## tree 1: `argumentMinusDeaf` (Syntax/DeafProofs.sw) -/
namespace ArgumentMinusDeaf

/-- Cut down from `Syntax.Tok`. -/
inductive Tok
  | Lower | Minus | Bang
  deriving DecidableEq

axiom Comment : Type

/-- Cut down from `Syntax.Token`: `text`, `column` and `lineStart` dropped. -/
structure Token where
  kind : Tok

/-- Cut down from `Syntax.Trivia`: `blankLines` dropped. -/
structure Trivia where
  leading : List Comment
  trailing : Option Comment

def Trivia.empty : Trivia := { leading := [], trailing := none }

structure Leaf where
  token : Token
  trivia : Trivia

/-- Cut down from `Syntax.Item`: `afterDot`, `index`, `depth` and `lineIndent` dropped. -/
structure Item where
  leaf : Leaf
  glued : Bool
  afterOperand : Bool

def Item.kind (item : Item) : Tok := item.leaf.token.kind
def Leaf.stripped (leaf : Leaf) : Leaf := { leaf with trivia := Trivia.empty }
def Item.stripped (item : Item) : Item := { item with leaf := item.leaf.stripped }

/-- Opaque: the proof uses it only through `argumentPrefixDeaf`. -/
opaque argumentPrefix : List Item → Bool

def argumentMinus : List Item → Bool
  | sign :: rest => sign.kind == .Minus && argumentPrefix (sign :: rest)
  | [] => false

axiom argumentPrefixDeaf (items : List Item) : argumentPrefix items = argumentPrefix (items.map Item.stripped)

-- sample: argumentMinusDeaf
theorem argumentMinusDeaf (items : List Item) :
    argumentMinus items = argumentMinus (items.map Item.stripped) := by
  cases items with
  | nil => rfl
  | cons a more =>
    simp [argumentMinus, Item.kind, Item.stripped, Leaf.stripped, argumentPrefixDeaf (a :: more)]

end ArgumentMinusDeaf

/-! ## tree 2: `walkAttributesAlike` (Syntax/FollowsDecl.sw) -/
namespace WalkAttributesAlike

axiom Attributes : Type
axiom blankAttributes : Attributes → Attributes

/-- std's `List.All2`, as an inductive (Batteries' and Mathlib's `List.Forall₂`; core has none). -/
inductive Forall₂ (r : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ r [] []
  | cons {x y xs ys} : r x y → Forall₂ r xs ys → Forall₂ r (x :: xs) (y :: ys)

/-- Cut down from `Fmt.Pure`: the walk's other six functions dropped. -/
structure Pure where
  attributes : Attributes → Attributes

noncomputable def blankPure : Pure := { attributes := blankAttributes }

def walkAttributes (on : Pure) : List Attributes → List Attributes
  | [] => []
  | first :: rest => on.attributes first :: walkAttributes on rest

def AttributeGroupAlike (attributes twin : Attributes) : Prop := blankAttributes attributes = blankAttributes twin

-- mathlib: List.Forall₂ from Batteries or Mathlib instead of the local inductive (support only), 0 counted lines
-- sample: walkAttributesAlike
theorem walkAttributesAlike (items twins : List Attributes)
    (alike : Forall₂ AttributeGroupAlike items twins) :
    walkAttributes blankPure items = walkAttributes blankPure twins := by
  induction alike with
  | nil => rfl
  | cons head _ ih => simp_all [walkAttributes, blankPure, AttributeGroupAlike]

end WalkAttributesAlike
