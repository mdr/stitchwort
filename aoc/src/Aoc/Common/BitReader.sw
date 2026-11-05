--| A stream of bits read from the front, field by field: the bits not yet
--| read, and operations that read a field of a given width and give back
--| the reader for what follows it. For formats that run fields of
--| different widths together (2021 day 16). Its proofs are in
--| `Aoc.Common.Proofs` (Proofs/BitReader.sw).

namespace Aoc.Common
import Std (Bool, List, Nat, Option)

--| The bits of a stream that haven't been read yet.
type BitReader = { unread: List Bool }

--| A reader at the start of `bits`.
def BitReader.of (bits: Bits): BitReader := { unread = bits.bits }

--| How many bits are left to read.
def BitReader.length (reader: BitReader): Nat := reader.unread.length

--| The next `width` bits, and the reader after them; none if fewer are left.
def BitReader.read (reader: BitReader) (width: Nat): Option (Bits, BitReader) :=
  let field := reader.unread.take width
  if field.length == width then Some ({ bits = field }, { unread = reader.unread.drop width }) else None

--| The number spelt by the next `width` bits, and the reader after them.
def BitReader.readNumber (reader: BitReader) (width: Nat): Option (Nat, BitReader) :=
  reader.read width |> match some | Some (field, rest) => (field.value, rest)

--| The next bit, and the reader after it; none if none is left.
def BitReader.readBit: BitReader → Option (Bool, BitReader)
  | { unread = [] } => None
  | { unread = [bit, ..rest] } => Some (bit, { unread = rest })
