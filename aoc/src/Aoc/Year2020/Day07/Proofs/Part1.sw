--| Part 1 proved: the graph's edges are the rules read backwards, so a walk
--| out from shiny gold's holders is a chain of bags each directly inside the
--| next, and `Graph.reachable` (std's, proved there) finds exactly the
--| colours that can eventually contain a shiny gold bag.

namespace Aoc.Year2020.Day07.Proofs
import Aoc.Year2020.Day07 (..)
import Aoc.Year2020.Day07 (Spec)
import Std (Bool, DecEq, Eq, Exists, Graph, List, Map, Pair, Set)

theorem holdersInIndex ∀ (rules: Rules) (colour: Colour):
    rules.holders.of colour = ((rules.all.flatMap .holdings).filter (pair => Map.Spec.sameKey colour pair.inside)).map .holder :=
  rewrite Map.getGroupBy .inside colour (rules.all.flatMap .holdings) in
    match List.filter (rules.all.flatMap .holdings) (pair => Map.Spec.sameKey colour pair.inside) with
      | [] => rfl
      | [first, ..rest] => rfl

--| Every holder is the colour of a rule.
theorem holderListed ∀ (rules: List Rule) (colour: Colour) (holder: Colour) (found: holder ∈ ({ all = rules }: Rules).holders.of colour):
    holder ∈ rules.map .colour :=
  let (Witness pair (Both kept same)) := List.memMapElim .holder holder _ (rewrite holdersInIndex { all = rules } colour at found in found)
  let (Both listed matching) := List.memFilter _ _ kept
  List.anyElim (rule => pair ∈ rule.holdings) (holder ∈ rules.map .colour) rules (List.memFlatMapElim .holdings pair rules listed)
    (rule member inRule =>
      let (Witness content (Both inContents made)) := List.memMapElim (content => { inside = content.colour, holder = rule.colour }) pair rule.contents inRule
      rewrite <- same, <- made in List.memMap rules rule member .colour)

--| A colour's holders are the colours whose rules list it.
theorem holderDirectly ∀ (rules: Rules) (inner: Colour) (holder: Colour):
    (holder ∈ rules.holders.of inner) ↔ Spec.Directly rules.all holder inner := {
  forward = found =>
    let (Witness pair (Both kept same)) := List.memMapElim .holder holder _ (rewrite holdersInIndex rules inner at found in found)
    let (Both listed matching) := List.memFilter _ _ kept
    List.anyElim (rule => pair ∈ rule.holdings) (Spec.Directly rules.all holder inner) rules.all (List.memFlatMapElim .holdings pair rules.all listed)
      (rule member inRule =>
        let (Witness content (Both inContents made)) := List.memMapElim (content => { inside = content.colour, holder = rule.colour }) pair rule.contents inRule
        let ruleColour: rule.colour = holder := rewrite <- same, <- made in rfl
        let contentColour: content.colour = inner := Eq.sym (Map.Spec.sameKeySound inner content.colour (rewrite <- made at matching in matching))
        Witness content
          (Both (List.memFlatMapIntro .contents rule content _ (List.memFilterIntro rules.all _ member (rewrite ruleColour in DecEq.refl holder)) inContents)
            contentColour)),
  backward = directly =>
    let (Witness content (Both inContents contentColour)) := directly
    List.anyElim (rule => content ∈ rule.contents) (holder ∈ rules.holders.of inner) _ (List.memFlatMapElim .contents content _ inContents)
      (rule kept inRule =>
        let (Both member isHolder) := List.memFilter _ _ kept
        let ruleColour: rule.colour = holder := isHolder.read
        let pair: Holding := { inside = content.colour, holder = rule.colour }
        let inInsides: pair ∈ rule.holdings := List.memMap rule.contents content inRule (content => { inside = content.colour, holder = rule.colour })
        let matching: Map.Spec.sameKey inner pair.inside = True := rewrite Map.Spec.sameKeyDecide inner pair.inside, contentColour in DecEq.refl inner
        rewrite holdersInIndex rules inner, <- ruleColour in
          List.memMap _ pair (List.memFilterIntro _ _ (List.memFlatMapIntro .holdings rule pair rules.all member inInsides) matching) .holder)
}

--| The graph's edges out of a bag are its holders, each at cost 1, when the
--| holder has a rule.
theorem graphEdge ∀ (rules: Rules) (inner: Colour) (holder: Colour) (weight: Nat):
    ((holder, weight) ∈ rules.graph.edges inner) ↔ (((holder, weight) ∈ (rules.holders.of inner).map (next => (next, 1))) ∧ (holder ∈ rules.all.map .colour)) :=
  Graph.fromEdgesEdge (colour => (rules.holders.of colour).map (next => (next, 1))) (rules.all.map .colour) inner holder weight

theorem edgeDirectly ∀ (rules: Rules) (inner: Colour) (holder: Colour) (weight: Nat) (edge: (holder, weight) ∈ rules.graph.edges inner):
    Spec.Directly rules.all holder inner ∧ weight = 1 :=
  let (Both raw listed) := (graphEdge rules inner holder weight).forward edge
  let (Witness found (Both inHolders same)) := List.memMapElim (holder => (holder, 1)) (holder, weight) _ raw
  Both ((holderDirectly rules inner holder).forward (rewrite <- Eq.cong Pair.fst same in inHolders)) (Eq.sym (Eq.cong Pair.snd same))

theorem directlyEdge ∀ (rules: Rules) (inner: Colour) (holder: Colour) (directly: Spec.Directly rules.all holder inner):
    (holder, 1) ∈ rules.graph.edges inner :=
  let held := (holderDirectly rules inner holder).backward directly
  (graphEdge rules inner holder 1).backward
    (Both (List.memMap _ holder held (holder => (holder, 1))) (holderListed rules.all inner holder held))

theorem walkOutward ∀ (rules: Rules) (start: Colour) (path: List (Colour, Nat)) (finish: Colour) (walked: rules.graph.Walk start path finish):
    Spec.Outward rules.all start (path.map Pair.fst) finish := match path, walked with
      | [], walked => walked
      | [(next, weight), ..rest], Both edge later =>
        Both (And.left (edgeDirectly rules start next weight edge)) (walkOutward rules next rest finish later)

theorem outwardWalk ∀ (rules: Rules) (start: Colour) (bags: List Colour) (finish: Colour) (outward: Spec.Outward rules.all start bags finish):
    rules.graph.Walk start (bags.map (bag => (bag, 1))) finish := match bags, outward with
      | [], outward => outward
      | [next, ..rest], Both directly later => Both (directlyEdge rules start next directly) (outwardWalk rules next rest finish later)

--| A source of the search is a direct holder.
theorem sourceDirectly ∀ (rules: Rules) (inner: Colour) (source: Colour)
    (member: source ∈ (rules.graph.edges inner).map Pair.fst): Spec.Directly rules.all source inner :=
  let (Witness edge (Both inEdges made)) := List.memMapElim Pair.fst source _ member
  match edge with
    | (holder, weight) => rewrite <- made in And.left (edgeDirectly rules inner holder weight inEdges)

--| The colours the search finds are exactly those that can eventually
--| contain `inner`.
theorem outsideCanContain ∀ (rules: Rules) (inner: Colour) (colour: Colour):
    ((rules.outside inner).contains colour = True) ↔ Spec.CanContain rules.all colour inner :=
  let graph := rules.graph
  let sources := (graph.edges inner).map Pair.fst
  {
    forward = there =>
      let (Witness source (Witness path (Both member walked))) := (Graph.reachableIff graph sources colour).forward there
      Witness source (Witness (path.map Pair.fst) (Both (sourceDirectly rules inner source member) (walkOutward rules source path colour walked))),
    backward = can =>
      let (Witness holder (Witness bags (Both directly outward))) := can
      (Graph.reachableIff graph sources colour).backward
        (Witness holder (Witness (bags.map (bag => (bag, 1)))
          (Both (List.memMap _ (holder, 1) (directlyEdge rules inner holder directly) Pair.fst) (outwardWalk rules holder bags colour outward))))
  }

--| Part 1 is the number of colours that can eventually contain a shiny
--| gold bag, for any rules.
theorem part1Rules ∀ (rules: Rules): Spec.Part1 rules.all (solvePart1 rules) :=
  let outside := rules.outside shinyGold
  Witness outside.toList
    (Both (Map.keysDistinct outside.items)
      (Both (colour => {
        forward = listed => (outsideCanContain rules shinyGold colour).forward ((Set.memToList outside colour).forward listed),
        backward = can => (Set.memToList outside colour).backward ((outsideCanContain rules shinyGold colour).backward can)
      })
        (Eq.sym (Map.lengthKeys outside.items))))
