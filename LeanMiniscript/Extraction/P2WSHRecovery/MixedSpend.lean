import LeanMiniscript.Extraction.P2WSHRecovery.MixedMaterial
import LeanMiniscript.Extraction.CoreFixtureExecution
import LeanMiniscript.Miniscript.CompileConcreteProofs
import Init.Internal.Order.While

/-! A signed BIP143 spend of `and_v(v:sha256(H),c:pk_k(K))`. -/

namespace LeanMiniscript.Extraction.P2WSHRecovery.MixedSpend

open LeanMiniscript.Bitcoin LeanMiniscript.Miniscript LeanMiniscript.Script

def key : PubKey := .ofBytes ⟨#[
    0x02, 0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0, 0x62,
    0x95, 0xce, 0x87, 0x0b, 0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28,
    0xd9, 0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8, 0x17, 0x98]⟩

def opening : ByteArray := ⟨Array.replicate 32 0⟩
private def alternate : ByteArray := ⟨Array.replicate 32 1⟩
def lock : HashLock := .sha256 ⟨⟨#[
    0x66, 0x68, 0x7a, 0xad, 0xf8, 0x62, 0xbd, 0x77, 0x6c, 0x8f, 0xc1, 0x8b,
    0x8e, 0x9f, 0x8e, 0x20, 0x08, 0x97, 0x14, 0x85, 0x6e, 0xe2, 0x33, 0xb3,
    0x90, 0x2a, 0x59, 0x1d, 0x0d, 0x5f, 0x29, 0x25]⟩⟩

def sane : SaneFragment .p2wsh :=
  (checkSane .p2wsh (guardedKey lock key)).toOption.get (by decide)

def script : ByteArray :=
  (serializeScript (compile sane.checked.fragment)).toOption.get (by decide)

def output := ScriptBytes.p2wsh script

/-- Low-S DER signature followed by SIGHASH_ALL for input 0 of the 100,000 sat fixture. -/
def signature : ByteArray := ⟨#[
    0x30, 0x45, 0x02, 0x21, 0x00, 0x83, 0xb1, 0xf0, 0xb0, 0x0f, 0x49, 0xca,
    0x75, 0xde, 0xa8, 0xd4, 0xc9, 0xc8, 0x0b, 0xad, 0x02, 0x37, 0xd8, 0x41,
    0x5f, 0x05, 0x93, 0xb0, 0x93, 0xc7, 0xe6, 0x78, 0xbb, 0xbe, 0x1a, 0xdd,
    0xe2, 0x02, 0x20, 0x31, 0x43, 0x31, 0xa6, 0x58, 0x54, 0xd8, 0xdf, 0x0b,
    0xdb, 0xd0, 0x2a, 0x12, 0x38, 0x51, 0x19, 0x73, 0xe8, 0xd3, 0x67, 0xf3,
    0x48, 0x0a, 0xeb, 0xde, 0x75, 0xb9, 0x81, 0xde, 0xcf, 0x49, 0xaf, 0x01]⟩

def context : TxContext :=
  { version := 1, sequence := 0xffffffff, locktime := 0, sigVersion := .witnessV0,
    sigHash := ⟨#[
      0x57, 0xdc, 0xa7, 0x29, 0x0f, 0x52, 0xc9, 0x0d, 0xa2, 0x55, 0xde, 0x17,
      0x4d, 0xec, 0x52, 0x84, 0x22, 0xb2, 0x90, 0xa8, 0xe8, 0xd3, 0x42, 0x2e,
      0x01, 0xc8, 0x43, 0x2c, 0x30, 0x29, 0xe3, 0xcf]⟩ }

def flags : CoreVerificationFlags :=
  { witness := true, p2sh := true, cleanStack := true,
    script := { derSig := true, lowS := true, witnessPubKeyType := true } }

def oracle : CryptoOracle := CryptoOracle.pureLeanSchnorr fun sig pub digest =>
  sig.size != 0 && ECDSA.verify (sig.extract 0 (sig.size - 1)) pub digest

private def digest : HashLock → ByteArray → ByteArray
  | .sha256 _ => oracle.sha256
  | .hash256 _ => oracle.hash256
  | .ripemd160 _ => oracle.ripemd160
  | .hash160 _ => oracle.hash160

def env : SatEnv where
  signatureFor k := if k.bytes = key.bytes then some signature else none
  preimageFor
    | .sha256 h => if h.bytes = lock.expected then some opening else none
    | _ => none
  nonPreimageFor target := if digest target opening = target.expected then alternate else opening
  txCtx := context

-- Express the hash library's padding loop as the bounded sequence of zero
-- bytes before the length field. This lets the kernel evaluate the test vectors.
private def padZeros (bytes : ByteArray) : Nat → ByteArray
  | 0 => bytes
  | n + 1 => padZeros (bytes.push 0) n

private abbrev padStep (_ : Unit) (b : ByteArray) : Id (ForInStep ByteArray) :=
  if b.size % 64 != 56 then pure (.yield (b.push 0)) else pure (.done b)

private theorem padSteps (b : ByteArray) (n : Nat)
    (endsAt : (b.size + n) % 64 = 56) (bound : n < 64) :
    forIn (m := Id) ({} : Lean.Loop) b padStep = padZeros b n := by
  change Lean.Loop.forIn _ _ _ = _
  induction n generalizing b with
  | zero =>
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp only [Nat.add_zero] at endsAt
    simp [padStep, endsAt, padZeros, pure, bind]
  | succ n ih =>
    rw [Lean.Loop.forIn_eq_of_monadTail]
    have more : b.size % 64 ≠ 56 := by omega
    simp [padStep, more, pure, bind, padZeros]
    exact ih (b.push 0) (by rw [ByteArray.size_push]; omega) (by omega)

private theorem padLoop (b : ByteArray) :
    forIn (m := Id) ({} : Lean.Loop) b padStep =
      padZeros b ((120 - b.size % 64) % 64) :=
  padSteps b _ (by omega) (by omega)

private theorem digest_eq (refines : oracle.RefinesModel) (target : HashLock) (b : ByteArray) :
    target.digest b = digest target b := by
  cases target
  · exact (refines.1 b).symm
  · exact (refines.2.1 b).symm
  · exact (refines.2.2.1 b).symm
  · exact (refines.2.2.2.1 b).symm

private theorem digests_ne (target : HashLock) : digest target opening ≠ digest target alternate := by
  cases target <;>
    simp only [digest, oracle, CryptoOracle.pureLeanSchnorr, CryptoOracle.pureLeanHashes,
      LeanHash160.hash160, LeanHash160.RIPEMD160.hash, LeanHash160.SHA256.hash,
      LeanHash160.Internal.padMessage, padLoop] <;> decide +kernel

private theorem opening_digest : oracle.sha256 opening = lock.expected := by
  simp only [oracle, CryptoOracle.pureLeanSchnorr, CryptoOracle.pureLeanHashes,
    LeanHash160.SHA256.hash, LeanHash160.Internal.padMessage, padLoop]
  decide +kernel

private theorem signature_valid : oracle.checkSig signature key.bytes context.sigHash = true := by
  decide +kernel

theorem sound (refines : oracle.RefinesModel) : env.Sound := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k sig found
    simp [env] at found
    obtain ⟨same, rfl⟩ := found
    change checkSig signature k.bytes context.sigHash = true
    rw [same, ← refines.2.2.2.2.1]
    exact signature_valid
  · intro k
    change checkSig falseElement k.bytes context.sigHash = false
    rw [← refines.2.2.2.2.1]
    rfl
  · intro target item found
    cases target with
    | sha256 h =>
      simp [env] at found
      obtain ⟨same, rfl⟩ := found
      exact ⟨rfl, (refines.1 opening).symm.trans (opening_digest.trans same.symm)⟩
    | _ => contradiction
  · intro target
    change target.Mismatches (if digest target opening = target.expected then alternate else opening)
    split <;> rename_i h
    · exact ⟨rfl, by rw [digest_eq refines, ← h]; exact (digests_ne target).symm⟩
    · exact ⟨rfl, by rwa [digest_eq refines]⟩

theorem run (refines : oracle.RefinesModel) :
    CompiledScriptRun .p2wsh env flags context (fun _ _ => oracle) script := by
  refine ⟨rfl, by decide, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, sound refines, ?_, rfl, refines⟩
  intro k sig found
  simp [env] at found
  obtain ⟨same, rfl⟩ := found
  rw [same]
  rfl

private theorem serialized (refines : oracle.RefinesModel) :
    CompiledScriptBytes sane.checked.fragment script := by
  refine ⟨rfl, fun data => ?_⟩
  rw [← refines.2.2.2.1]
  exact concreteKeyHash_size (.ofBytes data)

private theorem spend : CompiledScriptSpend .p2wsh script output [script] := by
  refine ⟨rfl, rfl, ?_⟩
  simp only [LeanHash160.SHA256.hash, LeanHash160.Internal.padMessage, padLoop]
  decide +kernel

private theorem images (refines : oracle.RefinesModel) :
    ∀ item ∈ [signature, opening], Script.hash160 item ≠ Script.hash160 key.bytes := by
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rw [← refines.2.2.2.1, ← refines.2.2.2.1]
  rcases member with rfl | rfl <;>
    simp only [oracle, CryptoOracle.pureLeanSchnorr, CryptoOracle.pureLeanHashes,
      LeanHash160.hash160, LeanHash160.RIPEMD160.hash, LeanHash160.SHA256.hash,
      LeanHash160.Internal.padMessage, padLoop] <;> decide +kernel

/-- The generated mixed witness is eligible, satisfies both local recovery
    premises, and is accepted by the Core verifier for this witness program. -/
theorem accepted (refines : oracle.RefinesModel) (keyPath : CoreKeyPathChecker) :
    satisfyFinal sane.checked.fragment env = some [signature, opening] ∧
    ThirdPartyWitness sane.checked.fragment env.txCtx [signature, opening] [signature, opening] ∧
    LocalHashSlotRecovery sane.checked.fragment env [signature, opening] ∧
    LocalPreimageSignatureDisjoint sane.checked.fragment env flags.script [signature, opening] ∧
    coreVerifyScript flags context (fun _ _ => oracle) keyPath ByteArray.empty output
      [signature, opening, script] = .ok () :=
  guardedKey_accepted_separated sane (lock := lock) (key := key) rfl keyPath
    (serialized refines) spend (run refines) rfl rfl (by decide) (by decide) (images refines)

private def fixture := coreFixtureTransaction ByteArray.empty output 100000

#guard (witnessV0SignatureHash fixture.spend fixture.inputIndex script fixture.amount 1).toOption ==
  some context.sigHash

private def verifyWitness (witness : Witness) :=
  verifyScriptWith (executeCoreFixtureScript fixture flags) flags
    (fun _ _ _ => .error .witnessProgramMismatch) ByteArray.empty output (witness ++ [script])

#guard (verifyWitness [signature, opening]).toOption.isSome
#guard (verifyWitness [opening, opening]).toOption.isNone
#guard (verifyWitness [signature, alternate]).toOption.isNone

end LeanMiniscript.Extraction.P2WSHRecovery.MixedSpend
