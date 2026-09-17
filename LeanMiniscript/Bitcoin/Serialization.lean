import Lean

namespace LeanMiniscript.Bitcoin

/-- Fixed-width unsigned little-endian serialization. Callers use bounded
    transaction fields; this helper encodes the low `width` bytes. -/
def unsignedLE : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, value => UInt8.ofNat value :: unsignedLE width (value / 256)

/-- Bitcoin CompactSize, for lengths representable by uint64. -/
def compactSize (value : Nat) : List UInt8 :=
  if value < 253 then [UInt8.ofNat value]
  else if value ≤ 65535 then 0xfd :: unsignedLE 2 value
  else if value ≤ 4294967295 then 0xfe :: unsignedLE 4 value
  else 0xff :: unsignedLE 8 value

def serializeByteVector (bytes : ByteArray) : ByteArray :=
  ⟨(compactSize bytes.size).toArray⟩ ++ bytes

/-- Serialize the entire transaction-input witness, in wire order. This
    includes the item count and each item's CompactSize length prefix. -/
def serializeWitness (items : List ByteArray) : ByteArray :=
  items.foldl (fun bytes item => bytes ++ serializeByteVector item)
    ⟨(compactSize items.length).toArray⟩

end LeanMiniscript.Bitcoin
