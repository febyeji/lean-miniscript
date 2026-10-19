import LeanMiniscript.TestSupport.Hex
import LeanMiniscript.Psbt.Fields
import LeanMiniscript.Psbt.Fixtures
import LeanMiniscript.Bitcoin.Base64

namespace LeanMiniscript.Psbt.CodecExamples

open LeanMiniscript.Bitcoin LeanMiniscript.Psbt LeanMiniscript.Psbt.Fixtures

/-! Official BIP174, BIP370 and BIP371 parser vectors. Valid vectors must
parse, re-serialize to the identical bytes and match their Base64 form;
invalid vectors must be rejected. -/

open LeanMiniscript.TestSupport (hex)

private def rejected (vectors : List (String × String × String)) : Bool :=
  vectors.all fun (_, bytes, encoded) =>
    (Psbt.parse (hex bytes)).toBool == false && (Psbt.parseBase64 encoded).toBool == false

private def accepted (vectors : List (String × String × String)) : Bool :=
  vectors.all fun (_, bytes, encoded) =>
    match Psbt.parse (hex bytes), Psbt.parseBase64 encoded with
    | .ok psbt, .ok fromText => psbt.serialize == hex bytes && psbt.toBase64 == encoded &&
        fromText == psbt
    | _, _ => false

example : (bip174Invalid.length, bip370Invalid.length, bip371Invalid.length) = (20, 24, 11) := by
  decide
example : (bip174Valid.length, bip174SignerFailures.length, bip370Valid.length,
    bip371Valid.length) = (10, 4, 14, 6) := by decide

example : rejected bip174Invalid = true := by native_decide
example : rejected bip370Invalid = true := by native_decide
example : rejected bip371Invalid = true := by native_decide

example : accepted bip174Valid = true := by native_decide
example : accepted bip174SignerFailures = true := by native_decide
example : accepted bip370Valid = true := by native_decide
example : accepted bip371Valid = true := by native_decide
-- Every role-vector PSBT also round-trips; the extracted transaction is not a PSBT.
example : accepted (bip174Roles.eraseIdx 7) = true := by native_decide
example : (match Psbt.parse (hex bip174Roles[7]!.2.1) with
    | .error .magic => true
    | _ => false) = true := by native_decide

-- Invalid Base64 forms of the BIP174 invalid vectors still decode to their hex.
example : bip174Invalid.all (fun (_, bytes, encoded) =>
    Base64.decode encoded == some (hex bytes)) = true := by native_decide

-- Specific BIP rule behind selected invalid vectors.
private def errorOf (vectors : List (String × String × String)) (index : Nat) : Option PsbtError :=
  match Psbt.parse (hex vectors[index]!.2.1) with
  | .ok _ => none
  | .error error => some error

example : errorOf bip174Invalid 4 = some (.duplicateKey (hex "00")) := by native_decide
example : errorOf bip174Invalid 2 =
    some (.invalidUnsignedTransaction "scriptSig must be empty") := by native_decide
example : errorOf bip370Invalid 0 = some (.excludedField "global" 0) := by native_decide
example : errorOf bip370Invalid 14 = some (.missingField "global" 4) := by native_decide
example : errorOf bip371Invalid 1 =
    some (.invalidValue "input" 19 "signature must be 64 or 65 bytes") := by native_decide
example : errorOf bip371Invalid 9 =
    some (.invalidKey "input" 21 "invalid control block size") := by native_decide

-- The sighash-type vector is rejected by framing before typed decoding; its
-- `0x03` key with key data is also rejected by the input decoder itself.
example : (decodeInput 0 [⟨hex "0300", hex "01000000"⟩]).toBool = false := by native_decide
example : (decodeInput 0 [⟨hex "03", hex "01000000"⟩]).toBool = true := by native_decide

-- Non-canonical CompactSize key lengths are rejected.
example : (decodeMap [0xfd, 0x01, 0x00, 0x00, 0x00]).toBool = false := by native_decide
example : (match decodeMap [0x01, 0x00, 0x00, 0x00] with
    | .ok (map, rest) => map == [⟨hex "00", ByteArray.empty⟩] && rest.isEmpty
    | .error _ => false) = true := by native_decide

/-! BIP370 lock time determination vectors. -/

private def locktimeOf (bytes : String) : Option (Option Nat) :=
  match Psbt.parse (hex bytes) >>= Psbt.decode with
  | .ok decoded => some ((determineLocktime decoded.global.fallbackLocktime decoded.inputs).map
      UInt32.toNat)
  | .error _ => none

example : bip370Locktimes.length = 10 := by decide
example : bip370Locktimes.all (fun (_, bytes, encoded, expected) =>
    locktimeOf bytes == some expected && Base64.decode encoded == some (hex bytes)) = true := by
  native_decide

-- Version-2 PSBTs build their unsigned transaction with the determined lock
-- time; incompatible lock time types have none.
example : bip370Locktimes.all (fun (_, bytes, _, expected) =>
    match Psbt.parse (hex bytes) >>= Psbt.decode with
    | .ok decoded => match decoded.unsignedTransaction, expected with
      | .ok tx, some locktime => tx.locktime.toNat == locktime
      | .error _, none => true
      | _, _ => false
    | .error _ => false) = true := by native_decide

end LeanMiniscript.Psbt.CodecExamples
