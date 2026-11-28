namespace Probe.N

-- Which loop Probe.RunTail runs (0 three-field, 1 state machine, 2 cursor, 4 Seq, 5 origin and
-- offset, otherwise the cells loop), and how many values it reads.
def which: Nat := 4

def n: Nat := 20000
