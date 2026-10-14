import LeanMiniscript.Psbt.Fields

namespace LeanMiniscript.Psbt

private def bytes (values : List Nat) : ByteArray :=
  ⟨values.toArray.map UInt8.ofNat⟩

private def source : KeySource :=
  { fingerprint := bytes [0xde, 0xad, 0xbe, 0xef]
    path := [44, 0x80000000, 1] }

private def tapSource : TapKeySource :=
  { leafHashes := [bytes (List.replicate 32 0x11), bytes (List.replicate 32 0x22)]
    source }

private def tree : List TapTreeLeaf :=
  [{ depth := 0, leafVersion := 0xc0, script := bytes [0x51] }]

private def keySourceRoundTrip : Bool :=
  match decodeKeySource "input" KeyType.inBip32Derivation (encodeKeySource source) with
  | .ok got => decide (got = source)
  | .error _ => false

private def tapKeySourceRoundTrip : Bool :=
  match decodeTapKeySource "input" KeyType.inTapBip32Derivation
      (encodeTapKeySource tapSource) with
  | .ok got => decide (got = tapSource)
  | .error _ => false

private def tapTreeRoundTrip : Bool :=
  match decodeTapTree (encodeTapTree tree) with
  | .ok got => decide (got = tree)
  | .error _ => false

example : keySourceRoundTrip = true := by
  native_decide

example : tapKeySourceRoundTrip = true := by
  native_decide

example : tapTreeRoundTrip = true := by
  native_decide

end LeanMiniscript.Psbt
