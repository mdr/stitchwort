-- A procedure in a namespace Day doesn't use.
namespace Another

import Base (Token)

def decU: Decidable Token := Yes MkToken
