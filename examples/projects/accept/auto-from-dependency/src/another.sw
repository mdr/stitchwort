-- A procedure in a namespace Day doesn't use.
namespace Another

import Base (Token)

instance decU: Decidable Token := Yes MkToken
