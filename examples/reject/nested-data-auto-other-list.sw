-- expect-error: E-AUTO-STUCK
-- A membership in some other list doesn't make a packet smaller than
-- `Packets items`: `auto` finds no size lemma that fits, and says the goal,
-- as it computes, mentions a helper generated for `Packet.size`.
import Std (List, Nat, Unit)

type Packet: Type =
  | Number (value: Nat)
  | Packets (items: List Packet)

theorem memberSmaller (q: Packet) (items: List Packet) [auto lt: Packet.size q < Packet.size (Packets items)]: Unit := ()

theorem elsewhere (q: Packet) (items: List Packet) (others: List Packet) (h: List.Mem q others): Unit := memberSmaller q items
