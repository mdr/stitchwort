--| Part 1 proved: the graph's edges are the rules read backwards, so a walk
--| out from shiny gold's holders is a chain of bags each directly inside the
--| next, and breadth-first search (std's, proved there) finds exactly the
--| colours that can eventually contain a shiny gold bag.

namespace Aoc.Year2020.Day07.Proofs
import Aoc.Year2020.Day07 (..)
import Aoc.Year2020.Day07 (Spec)
import Std (Bool, DecEq, Eq, Exists, Graph, List, Map, Pair)

--| A colour's holders are the colours whose rules list it.
theorem holderDirectly (rules: List Rule) (inner: Colour) (holder: Colour):
    (holder ∈ holdersIn (holdersIndex rules) inner) ↔ Spec.Directly rules holder inner := {
  forward = found =>
    let (Witness pair (Both kept same)) := List.memMapElim Pair.snd holder _ (rewrite holdersInIndex rules inner at found in found)
    let (Both listed matching) := List.memFilter _ _ kept
    List.anyElim (rule => pair ∈ rule.insides) (Spec.Directly rules holder inner) rules (List.memFlatMapElim .insides pair rules listed)
      (rule member inRule =>
        let (Witness content (Both inContents made)) := List.memMapElim (content => (content.colour, rule.colour)) pair rule.contents inRule
        let ruleColour: rule.colour = holder := rewrite <- same, <- made in rfl
        let contentColour: content.colour = inner := Eq.sym (Map.Spec.sameKeySound inner content.colour (rewrite <- made at matching in matching))
        Witness content
          (Both (List.memFlatMapIntro .contents rule content _ (List.memFilterIntro rules _ member (rewrite ruleColour in DecEq.refl holder)) inContents)
            contentColour)),
  backward = directly =>
    let (Witness content (Both inContents contentColour)) := directly
    List.anyElim (rule => content ∈ rule.contents) (holder ∈ holdersIn (holdersIndex rules) inner) _ (List.memFlatMapElim .contents content _ inContents)
      (rule kept inRule =>
        let (Both member isHolder) := List.memFilter _ _ kept
        let ruleColour: rule.colour = holder := DecEq.sound isHolder
        let pair := (content.colour, rule.colour)
        let inInsides: pair ∈ rule.insides := List.memMap rule.contents content inRule (content => (content.colour, rule.colour))
        let matching: Map.Spec.sameKey inner pair.fst = True := rewrite Map.Spec.sameKeyDecide inner pair.fst, contentColour in DecEq.refl inner
        rewrite holdersInIndex rules inner, <- ruleColour in
          List.memMap _ pair (List.memFilterIntro _ _ (List.memFlatMapIntro .insides rule pair rules member inInsides) matching) Pair.snd)
}

theorem edgeDirectly (rules: Rules) (inner: Colour) (holder: Colour) (weight: Nat) (edge: (holder, weight) ∈ rules.graph.edges inner):
    Spec.Directly rules.all holder inner ∧ weight = 1 :=
  let (Witness listed (Both found same)) := List.memMapElim (holder => (holder, 1)) (holder, weight) _ edge
  Both ((holderDirectly rules.all inner holder).forward (rewrite <- Eq.cong Pair.fst same in found)) (Eq.sym (Eq.cong Pair.snd same))

theorem directlyEdge (rules: Rules) (inner: Colour) (holder: Colour) (directly: Spec.Directly rules.all holder inner):
    (holder, 1) ∈ rules.graph.edges inner :=
  List.memMap _ holder ((holderDirectly rules.all inner holder).backward directly) (holder => (holder, 1))

theorem walkOutward (rules: Rules): (start: Colour) → (path: List (Colour, Nat)) → (finish: Colour) → rules.graph.Walk start path finish →
    Spec.Outward rules.all start (path.map Pair.fst) finish
  | start, [], finish, walked => walked
  | start, [(next, weight), ..rest], finish, Both edge later =>
    Both (And.left (edgeDirectly rules start next weight edge)) (walkOutward rules next rest finish later)

theorem outwardWalk (rules: Rules): (start: Colour) → (bags: List Colour) → (finish: Colour) → Spec.Outward rules.all start bags finish →
    rules.graph.Walk start (bags.map (bag => (bag, 1))) finish
  | start, [], finish, outward => outward
  | start, [next, ..rest], finish, Both directly later => Both (directlyEdge rules start next directly) (outwardWalk rules next rest finish later)

--| A source of the search is a direct holder.
theorem sourceDirectly (rules: Rules) (inner: Colour) (source: Colour) (start: Nat)
    (member: (source, start) ∈ ((rules.graph.edges inner).map Pair.fst).map (source => (source, 0))):
    Spec.Directly rules.all source inner :=
  let (Witness first (Both inFirsts same)) := List.memMapElim (source => (source, 0)) (source, start) _ member
  let (Witness edge (Both inEdges made)) := List.memMapElim Pair.fst first _ inFirsts
  match edge with
    | (holder, weight) =>
      rewrite <- Eq.cong Pair.fst same, <- made in And.left (edgeDirectly rules inner holder weight inEdges)

--| The colours the search finds are exactly those that can eventually
--| contain `inner`.
theorem outsideCanContain (rules: Rules) (inner: Colour) (colour: Colour):
    ((rules.outside inner).contains colour = True) ↔ Spec.CanContain rules.all colour inner :=
  let graph := rules.graph
  let sources := (graph.edges inner).map Pair.fst
  let unit: (state: Colour) → (next: Colour) → (weight: Nat) → (next, weight) ∈ graph.edges state → weight = 1 :=
    state next weight edge => And.right (edgeDirectly rules state next weight edge)
  let (Both found complete) := Graph.breadthFirstShortest graph sources unit
  {
    forward = there =>
      let (Witness cost got) := Map.getOfContains _ colour there
      let (Witness source (Witness start (Witness path (Both member (Both walked costs))))) := found colour cost got
      Witness source (Witness (path.map Pair.fst) (Both (sourceDirectly rules inner source start member) (walkOutward rules source path colour walked))),
    backward = can =>
      let (Witness holder (Witness bags (Both directly outward))) := can
      let member: (holder, 0) ∈ sources.map (source => (source, 0)) :=
        List.memMap sources holder (List.memMap _ (holder, 1) (directlyEdge rules inner holder directly) Pair.fst) (source => (source, 0))
      let (Witness cost (Both got bound)) := complete holder 0 member _ colour (outwardWalk rules holder bags colour outward)
      Map.containsOfGet _ colour cost got
  }

--| Part 1 is the number of colours that can eventually contain a shiny
--| gold bag, for any rules.
theorem part1Rules (rules: Rules): Spec.Part1 rules.all (solvePart1 rules) :=
  let outside := rules.outside shinyGold
  Witness outside.keys
    (Both (Map.keysDistinct outside)
      (Both (colour => {
        forward = listed => (outsideCanContain rules shinyGold colour).forward ((Map.memKeys outside colour).forward listed),
        backward = can => (Map.memKeys outside colour).backward ((outsideCanContain rules shinyGold colour).backward can)
      })
        (Eq.sym (Map.lengthKeys outside))))
