-- A definition `Plain`, used twice.
namespace N

def Plain (n: Nat): Nat := n

def twice (n: Nat): Nat := Plain (Plain n)
