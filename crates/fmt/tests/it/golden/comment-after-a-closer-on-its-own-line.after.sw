-- A comment after a closer that starts its own line belongs to the last
-- item (rule N): in a list that breaks, it ends the last item's line.
def long: List Nat := [1000000000000, 2000000000000, 3000000000000, 4000000000000, 5000000000000, 6000000000000,
  7000000000000, 8000000000000, 9000000000000] -- after the closer

def call: Nat := ffffffffffffffffffffffffffffff (
  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb -- after the closer
)

-- In one that fits, it follows the closer, as before.
def short: List Nat := [1, 2] -- after the closer
