import LeanMiniscript.Extraction.BitcoinCoreScriptExecution
import LeanMiniscript.Extraction.BitcoinCoreWitness

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

private def pushOnlyLoop (bytes : ByteArray) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, offset =>
      if offset ≥ bytes.size then true
      else match readCoreRawInstruction bytes offset with
        | .error _ => false
        | .ok instruction => instruction.opcode.toNat ≤ 0x60 &&
            pushOnlyLoop bytes fuel instruction.nextOffset

/-- Core IsPushOnly includes OP_RESERVED and rejects malformed pushes. -/
def coreScriptIsPushOnly (bytes : ByteArray) : Bool :=
  pushOnlyLoop bytes (bytes.size + 1) 0

/-- P2SH requires this exact 23-byte template, including the direct push length. -/
def coreScriptIsP2SH (bytes : ByteArray) : Bool :=
  bytes.size == 23 && bytes[0]! == 0xa9 && bytes[1]! == 0x14 && bytes[22]! == 0x87

private def requireTruthy (stack : Stack) : Except CoreVerificationError Unit :=
  match stack with
  | [] => .error (.script .evalFalse)
  | top :: _ => if castToBool top then .ok () else .error (.script .evalFalse)

/-- Core VerifyScript ordering for scriptSig/scriptPubKey, native witness,
P2SH redemption, nested witness, CLEANSTACK and unexpected witness data.
CLEANSTACK enables P2SH and WITNESS as the upstream fixture harness does. -/
def verifyCoreScripts (execute : CoreScriptExecutor) (verifyWitness : CoreWitnessVerifier)
    (flags : CoreVerificationFlags) (scriptSig scriptPubKey : ByteArray)
    (witness : List ByteArray) : Except CoreVerificationError Unit := do
  let p2sh := flags.p2sh || flags.cleanStack
  let useWitness := flags.witness || flags.cleanStack
  if flags.sigPushOnly && !coreScriptIsPushOnly scriptSig then throw .sigPushOnly
  let sigStack ← execute { scriptBytes := scriptSig }
  let initial ← execute { scriptBytes := scriptPubKey, stack := sigStack }
  requireTruthy initial
  let mut stack := initial
  let mut hadWitness := false
  if useWitness then
    if let some (version, program) := decodeCoreWitnessProgram? scriptPubKey then
      hadWitness := true
      if scriptSig.size != 0 then throw .witnessMalleated
      verifyWitness witness version program false
      stack := [trueElement]
  if p2sh && coreScriptIsP2SH scriptPubKey then
    if !coreScriptIsPushOnly scriptSig then throw .sigPushOnly
    match sigStack with
    | [] => throw (.script .evalFalse)
    | redeemScript :: arguments =>
        stack ← execute { scriptBytes := redeemScript, stack := arguments }
        requireTruthy stack
        if useWitness then
          if let some (version, program) := decodeCoreWitnessProgram? redeemScript then
            hadWitness := true
            if scriptSig != coreSignaturePush redeemScript then throw .witnessMalleatedP2SH
            verifyWitness witness version program true
            stack := [trueElement]
  if flags.cleanStack && stack.length != 1 then throw (.script .cleanStack)
  if useWitness && !hadWitness && !witness.isEmpty then throw .witnessUnexpected
  return ()

end LeanMiniscript.Extraction
