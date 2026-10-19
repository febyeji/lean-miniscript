import LeanHash160
import LeanMiniscript.Bitcoin.Serialization

namespace LeanMiniscript.Bitcoin.ScriptBytes

/-- Length-prefixed push for descriptor keys and scriptSig items. Callers
provide payloads smaller than 65536 bytes. -/
def pushData (data : ByteArray) : ByteArray :=
  if data.size < 76 then ⟨#[UInt8.ofNat data.size]⟩ ++ data
  else if data.size < 256 then ⟨#[0x4c, UInt8.ofNat data.size]⟩ ++ data
  else ⟨#[0x4d] ++ (unsignedLE 2 data.size).toArray⟩ ++ data

/-- P2SH output committing to a redeem script. -/
def p2sh (script : ByteArray) : ByteArray :=
  ⟨#[0xa9, 0x14]⟩ ++ LeanHash160.hash160 script ++ ⟨#[0x87]⟩

/-- P2WSH output committing to a witness script. -/
def p2wsh (script : ByteArray) : ByteArray :=
  ⟨#[0x00, 0x20]⟩ ++ LeanHash160.SHA256.hash script

/-- P2PKH output or BIP143 scriptCode for a 20-byte public-key hash. -/
def p2pkh (keyHash : ByteArray) : ByteArray :=
  ⟨#[0x76, 0xa9, 0x14]⟩ ++ keyHash ++ ⟨#[0x88, 0xac]⟩

/-- P2WPKH output for a 20-byte public-key hash. -/
def p2wpkh (keyHash : ByteArray) : ByteArray :=
  ⟨#[0x00, 0x14]⟩ ++ keyHash

end LeanMiniscript.Bitcoin.ScriptBytes
