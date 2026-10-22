-- Day 2, which templates `allTemplatesForRange` lists: exactly those that fit
-- in the digits of the range's end (`templateFits` and `fittingTemplateListed`);
-- every id of the range that is a block written two or more times has its
-- template listed (`writtenIdTemplateListed`), so the sum over the templates
-- misses no id; and no template is listed twice (`templatesDistinct`).
-- Kept apart from the program, so `stitchwort run Aoc.Day02.main` doesn't
-- check it.

namespace Aoc.Day02.Proofs
import Aoc.Common (..)
import Aoc.Common.Proofs (..)
import Aoc.Day02 (..)
import Aoc.Day02.Spec (..)
import Std (And, Bool, Decidable, DecEq, Each, Eq, List, Nat, Or, Void)
import Std.Each (each, require)

-- A template fits a range when it is a block of one or more digits written
-- two or more times, with no more digits than the range's end has.
def Fits (range: Range) (template: RepetitionTemplate): Prop :=
  And (1 <= template.blockLength)
    (And (2 <= template.copies)
      (template.blockLength * template.copies <= List.length (Nat.digits range.to)))

-- The template of `blockLength` and `copies` if it fits in `size` digits,
-- otherwise nothing.
def keptIfFits (size: Nat) (blockLength: Nat) (copies: Nat): List RepetitionTemplate :=
  if Nat.leq (blockLength * copies) size then [{ blockLength, copies }] else []

-- The program is a loop over block lengths with a loop over copies inside,
-- keeping the templates that fit: as lists, a `flatMap` of a `flatMap` of
-- "this template if it fits, else nothing". (Compare `templatesSum` in
-- Repeated.sw, which does the same for sums.)
theorem templatesAsGrid (range: Range):
    allTemplatesForRange range
      = List.flatMap (List.between 1 (List.length (Nat.digits range.to))) (blockLength =>
          List.flatMap (List.between 2 (List.length (Nat.digits range.to))) (copies =>
            if Nat.leq (blockLength * copies) (List.length (Nat.digits range.to))
            then [{ blockLength, copies }] else [])) :=
  let size := List.length (Nat.digits range.to)
  -- The program after it has chosen the block length (and the copies).
  let fitting: Nat -> Nat -> {Each} RepetitionTemplate := k n =>
    require (k * n <= size)
    { blockLength = k, copies = n }
  let withCopies: Nat -> {Each} RepetitionTemplate := k => fitting k (each (List.between 2 size))
  calc allTemplatesForRange range
    -- Choosing a block length: one collection per block length.
    _ = List.flatMap (List.between 1 size) (k => Each.collect (u => withCopies k))
        := Each.collectEach withCopies (List.between 1 size)
    _ = List.flatMap (List.between 1 size) (k =>
          List.flatMap (List.between 2 size) (n => keptIfFits size k n))
        := Eq.cong List.concat (List.mapCong (k => Each.collect (u => withCopies k)) (k =>
             List.flatMap (List.between 2 size) (n => keptIfFits size k n))
             (List.between 1 size) (k =>
             calc Each.collect (u => withCopies k)
               -- Choosing the copies: one collection per number of copies.
               _ = List.flatMap (List.between 2 size) (n => Each.collect (u => fitting k n))
                   := Each.collectEach (fitting k) (List.between 2 size)
               -- `require` keeps the template if it fits.
               _ = List.flatMap (List.between 2 size) (n => keptIfFits size k n)
                   := Eq.cong List.concat (List.mapCong (n => Each.collect (u => fitting k n)) (n =>
                        keptIfFits size k n)
                        (List.between 2 size) (n =>
                        Eq.trans (Each.collectRequire (u => ({ blockLength = k, copies = n }: RepetitionTemplate)) (k * n <= size))
                          (Eq.cong (b => if b then [({ blockLength = k, copies = n }: RepetitionTemplate)] else []) (Bool.decTrueToBool (Nat.leq (k * n) size)))))))

-- Membership (1): a listed template fits.
theorem templateFits (range: Range) (template: RepetitionTemplate)
    (listed: List.Mem template (allTemplatesForRange range)): Fits range template :=
  let size := List.length (Nat.digits range.to)
  -- It came from some block length in `1..size`,
  List.anyElim (blockLength => List.Mem template (List.flatMap (List.between 2 size) (copyCount =>
      keptIfFits size blockLength copyCount)))
    (Fits range template) (List.between 1 size)
    (List.memFlatMapElim (blockLength => List.flatMap (List.between 2 size) (copyCount =>
      keptIfFits size blockLength copyCount)) template (List.between 1 size)
      (rewrite templatesAsGrid range at listed))
    (blockLength lengthChosen fromBlockLength =>
      -- and from some number of copies in `2..size`,
      List.anyElim (copyCount => List.Mem template (keptIfFits size blockLength copyCount))
        (Fits range template) (List.between 2 size)
        (List.memFlatMapElim (copyCount => keptIfFits size blockLength copyCount)
          template (List.between 2 size) fromBlockLength)
        (copyCount copyCountChosen fromCopyCount =>
          -- where it was kept: the block fits in the digits.
          match room: Nat.leq (blockLength * copyCount) size with
            | True =>
              match fromCopyCount with
                | Inl same =>
                  rewrite <- same in
                  match List.memBetween lengthChosen, List.memBetween copyCountChosen with
                    | Both oneLe _, Both twoLe _ => Both oneLe (Both twoLe room)
                | Inr none => Void.exfalso none
            | False => Void.exfalso fromCopyCount))

-- Two small facts about the product: a block is no longer than the block
-- written `copies` times, and the number of copies is no more than the block
-- length times itself.
theorem blockLengthLeProduct (blockLength: Nat) (copies: Nat) (atLeastOne: 1 <= copies): blockLength <= blockLength * copies :=
  Nat.leMulPos blockLength copies atLeastOne

theorem copiesLeProduct (blockLength: Nat) (copies: Nat) (atLeastOne: 1 <= blockLength): copies <= blockLength * copies :=
  Nat.leCongRight copies (copies * blockLength) (blockLength * copies) (Nat.mulComm copies blockLength)
    (Nat.leMulPos copies blockLength atLeastOne)

-- A template is its block length and its number of copies.
theorem templateEta (template: RepetitionTemplate):
    ({ blockLength = template.blockLength, copies = template.copies }: RepetitionTemplate) = template :=
  match template with
    | { blockLength, copies } => rfl

-- Membership (2): a template that fits is listed.
theorem fittingTemplateListed (range: Range) (template: RepetitionTemplate)
    (fits: Fits range template): List.Mem template (allTemplatesForRange range) :=
  let size := List.length (Nat.digits range.to)
  match fits with
    | Both blockNotEmpty (Both writtenTwice room) =>
      -- It is the template of its block length, in the loop over `1..size`,
      rewrite templatesAsGrid range in
      List.memFlatMapIntro (blockLength => List.flatMap (List.between 2 size) (copies => keptIfFits size blockLength copies))
        template.blockLength template (List.between 1 size)
        (List.memBetweenIntro template.blockLength 1 size blockNotEmpty
          (omega [blockLengthLeProduct template.blockLength template.copies omega]))
        -- and of its number of copies, in the loop over `2..size`,
        (List.memFlatMapIntro (copies => keptIfFits size template.blockLength copies) template.copies template (List.between 2 size)
          (List.memBetweenIntro template.copies 2 size writtenTwice
            (omega [copiesLeProduct template.blockLength template.copies blockNotEmpty]))
          -- where it fits, so it is kept.
          (rewrite room in Inl (templateEta template)))

-- If an id's digits are a block of `blockLength` digits written `copies`
-- (two or more) times, then those blocks fill all of the id's digits.
theorem writtenAsFillsDigits (digits: List Nat) (hasDigits: 1 <= List.length digits)
    (blockLength: Nat) (copies: Nat) (written: writtenAs digits blockLength copies = True) (atLeastTwo: 2 <= copies):
    blockLength * copies = List.length digits :=
  -- The digits are the first `blockLength` digits, `copies` times over,
  let same: List.concat (List.replicate copies (List.take blockLength digits)) = digits := DecEq.sound (List.concat (List.replicate copies (List.take blockLength digits))) digits written
  -- so their count is `copies` times the count of the first `blockLength` digits.
  let counted: copies * List.length (List.take blockLength digits) = List.length digits :=
    Eq.trans (Eq.sym (List.lengthConcatReplicate (List.take blockLength digits) copies)) (Eq.cong List.length same)
  match room: Nat.leq blockLength (List.length digits) with
    -- There are `blockLength` digits to take, so that is how many the first block has.
    | True =>
      calc blockLength * copies
        _ = copies * blockLength := Nat.mulComm blockLength copies
        _ = copies * List.length (List.take blockLength digits) := rewrite List.lengthTake blockLength digits room
        _ = List.length digits := counted
    -- Taking more digits than there are takes all of them: then `copies`
    -- times as many digits as there are would be as many as there are,
    -- which two or more copies can't be.
    | False =>
      let takesAll := List.takeAll blockLength digits omega
      let sameCount: copies * List.length digits = List.length digits := rewrite takesAll at counted
      let twiceLe: List.length digits + List.length digits <= List.length digits :=
        calc List.length digits + List.length digits
          _ = List.length digits * 2 := Eq.trans (Eq.cong (t => List.length digits + t) (Eq.sym (Nat.mulOne (List.length digits)))) (Eq.sym (Nat.mulSucc (List.length digits) 1))
          _ = 2 * List.length digits := Nat.mulComm (List.length digits) 2
          _ <= copies * List.length digits := Nat.leMulRight 2 copies (List.length digits) atLeastTwo
          _ = List.length digits := sameCount
      Void.exfalso omega

-- Coverage: every invalid id in the range has its template listed. If `x` is
-- in the range and its digits are a block of `blockLength` digits written
-- `copies` (two or more) times, the template of that block length and that
-- many copies is in `allTemplatesForRange`.
theorem writtenIdTemplateListed (range: Range) (x: Nat) (inRange: List.Mem x range.ids)
    (blockLength: Nat) (copies: Nat) (written: writtenAs (Nat.digits x) blockLength copies = True) (atLeastTwo: 2 <= copies):
    List.Mem ({ blockLength, copies }: RepetitionTemplate) (allTemplatesForRange range) :=
  -- An x in the range is at most the range's end,
  let notAfterEnd: x <= range.to :=
    match List.memRangeFrom x range.size range.from inRange with
      | Both afterStart beforeEnd => rangeEnd range.from range.to x afterStart beforeEnd
  -- so it has no more digits than the end does.
  let fewerDigits: List.length (Nat.digits x) <= List.length (Nat.digits range.to) := Nat.digitsLengthMono x range.to notAfterEnd
  -- The blocks fill the digits,
  let filled: blockLength * copies = List.length (Nat.digits x) :=
    writtenAsFillsDigits (Nat.digits x) (Nat.digitsNonEmpty x) blockLength copies written atLeastTwo
  -- so the block has a digit (or the x would have none)
  let blockNotEmpty: 1 <= blockLength :=
    match blockLength with
      | Zero   => omega [Nat.digitsNonEmpty x]
      | Succ k => rfl
  fittingTemplateListed range { blockLength, copies }
    (Both blockNotEmpty (Both atLeastTwo omega))

-- What `keptIfFits` gives is at most one template, and it is that of its arguments.
theorem keptIfFitsDistinct (size: Nat) (blockLength: Nat) (copies: Nat): List.Distinct (keptIfFits size blockLength copies) :=
  match Nat.leq (blockLength * copies) size with
    | True  => Both (listed => listed) Trivial
    | False => Trivial

theorem keptIfFitsIsTemplate (size: Nat) (blockLength: Nat) (copies: Nat) (template: RepetitionTemplate)
    (kept: List.Mem template (keptIfFits size blockLength copies)): And (template.blockLength = blockLength) (template.copies = copies) :=
  match Nat.leq (blockLength * copies) size with
    | True =>
      match kept with
        | Inl same => rewrite <- same in Both rfl rfl
        | Inr none => Void.exfalso none
    | False => Void.exfalso kept

-- No duplicates: the list holds each template once. Templates from
-- different block lengths differ in `blockLength`, and within one block
-- length, in `copies`.
theorem templatesDistinct (range: Range): List.Distinct (allTemplatesForRange range) :=
  let size := List.length (Nat.digits range.to)
  rewrite templatesAsGrid range in
  List.distinctFlatMap (blockLength => List.flatMap (List.between 2 size) (copyCount => keptIfFits size blockLength copyCount))
    (template => template.blockLength) (List.between 1 size) (List.distinctBetween 1 size)
    (blockLength _ =>
      List.distinctFlatMap (copyCount => keptIfFits size blockLength copyCount) (template => template.copies)
        (List.between 2 size) (List.distinctBetween 2 size)
        (copyCount _ => keptIfFitsDistinct size blockLength copyCount)
        (copyCount _ template kept => match keptIfFitsIsTemplate size blockLength copyCount template kept with
                                       | Both _ sameCopies => sameCopies))
    (blockLength _ template listed =>
      List.anyElim (copyCount => List.Mem template (keptIfFits size blockLength copyCount)) (template.blockLength = blockLength)
        (List.between 2 size) (List.memFlatMapElim (copyCount => keptIfFits size blockLength copyCount) template (List.between 2 size) listed)
        (copyCount _ kept => match keptIfFitsIsTemplate size blockLength copyCount template kept with
                              | Both sameBlockLength _ => sameBlockLength))
