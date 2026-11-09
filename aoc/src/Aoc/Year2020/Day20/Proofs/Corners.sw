--| Part 1: the program's corners are the spec's, in order, so its product
--| is the spec's answer and the only one.

namespace Aoc.Year2020.Day20.Proofs
import Aoc.Year2020.Day20 (..)
import Aoc.Year2020.Day20 (Spec)
import Std (Bool, DecEq, Eq, Iff, List, Nat, Void)

theorem edgesPixels (image: Image): image.edges.map (.pixels) = Spec.edges image := rfl

theorem fitsIff (edge: Edge) (other: Edge): edge.fits other = True ↔ Spec.Fit edge.pixels other.pixels := {
  forward = fits => Bool.orElim fits (same => Inl (DecEq.sound same)) (reversed => Inr (DecEq.sound reversed)),
  backward = fit =>
    match fit with
      | Inl same => Bool.orLeft (rewrite same in DecEq.refl other.pixels)
      | Inr reversed => Bool.orRight (rewrite reversed in DecEq.refl other.pixels.reverse)
}

theorem matchesIff (jigsaw: Jigsaw) (tile: Tile) (edge: Edge): jigsaw.matches tile edge = True ↔ Spec.Matched jigsaw tile edge.pixels := {
  forward = matched =>
    List.anyTrueElim jigsaw.tiles _ _ matched (other member both =>
      List.anyTrueElim other.image.edges edge.fits _ (Bool.andRight both) (otherEdge onEdge fits =>
        Witness other (Both member (Both (DecEq.neTrue (Bool.andLeft both))
          (Witness otherEdge.pixels (Both (List.memMap _ otherEdge onEdge (.pixels)) ((fitsIff edge otherEdge).forward fits))))))),
  backward = matched =>
    match matched with
      | Witness other (Both member (Both different (Witness pixels (Both onEdge fit)))) =>
        match List.memMapElim (.pixels) pixels other.image.edges onEdge with
          | Witness otherEdge (Both onOther same) =>
            List.anyOfMem jigsaw.tiles _ other
              (Bool.andIntro (DecEq.trueOfNe different)
                (List.anyOfMem other.image.edges edge.fits otherEdge ((fitsIff edge otherEdge).backward (rewrite same in fit)) onOther))
              member
}

theorem cornerIff (jigsaw: Jigsaw) (tile: Tile): (jigsaw.matchedEdges tile == 2) = True ↔ Spec.Corner jigsaw tile :=
  let counted := List.countWithIff (pixels => jigsaw.matches tile { pixels }) (pixels => matchesIff jigsaw tile { pixels }) (Spec.edges tile.image) 2
  {
    forward = two => counted.backward (Eq.sym (DecEq.sound two)),
    backward = corner => rewrite <- counted.forward corner in DecEq.refl 2
  }

theorem keptFilter [p: a → Prop] (decide: a → Bool) (decides: (item: a) → decide item = True ↔ p item):
    (items: List a) → (kept: List a) → Spec.Kept p items kept ↔ kept = items.filter decide
  | [], kept => { forward = none => none, backward = none => none }
  | [item, ..rest], kept =>
    let later := keptFilter decide decides rest
    match decided: decide item with
      | True =>
        let holds := (decides item).forward decided
        {
          forward = found =>
            match found with
              | Inl (Both yes (Witness others (Both more same))) => rewrite same, (later others).forward more in rfl
              | Inr (Both no more) => Void.exfalso (no holds),
          backward = same => Inl (Both holds (Witness (rest.filter decide) (Both ((later (rest.filter decide)).backward rfl) same)))
        }
      | False =>
        let fails: ¬p item := holds => Bool.falseNotTrue (Eq.trans (Eq.sym decided) ((decides item).backward holds))
        {
          forward = found =>
            match found with
              | Inl (Both yes more) => Void.exfalso (fails yes)
              | Inr (Both no more) => (later kept).forward more,
          backward = same => Inr (Both fails ((later kept).backward same))
        }

theorem part1Exactly (jigsaw: Jigsaw) (answer: Nat): Spec.Part1 jigsaw answer ↔ answer = jigsaw.cornerProduct :=
  let kept := keptFilter (tile => jigsaw.matchedEdges tile == 2) (cornerIff jigsaw) jigsaw.tiles
  {
    forward = part1 =>
      match part1 with
        | Witness corners (Both found product) => rewrite (kept corners).forward found at product in product,
    backward = same => Witness jigsaw.corners (Both ((kept jigsaw.corners).backward rfl) same)
  }
