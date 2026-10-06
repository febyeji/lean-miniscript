import LeanMiniscript.Extraction.BitcoinCoreVerificationTypes
import LeanMiniscript.Extraction.BitcoinCoreRawScript
import LeanMiniscript.Bitcoin.TaprootControlBlock

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script LeanMiniscript.Bitcoin

/-- Core's exact native witness-program byte shape: a version opcode followed
by a direct push of between 2 and 40 bytes. -/
def decodeCoreWitnessProgram? (bytes : ByteArray) : Option (Nat × ByteArray) := do
  if bytes.size < 4 || bytes.size > 42 then none
  else
    let opcode := bytes[0]!.toNat
    let version ← if opcode = 0 then some 0
      else if 0x51 ≤ opcode && opcode ≤ 0x60 then some (opcode - 0x50)
      else none
    if bytes[1]!.toNat + 2 != bytes.size then none
    else some (version, bytes.extract 2 bytes.size)

private def isCoreOpSuccess (byte : Nat) : Bool :=
  byte == 80 || byte == 98 ||
  (126 ≤ byte && byte ≤ 129) || (131 ≤ byte && byte ≤ 134) ||
  (137 ≤ byte && byte ≤ 138) || (141 ≤ byte && byte ≤ 142) ||
  (149 ≤ byte && byte ≤ 153) || (187 ≤ byte && byte ≤ 254)

/-- Locate an OP_SUCCESS instruction before validating initial witness stack
limits. Pushed bytes are skipped; a truncated push encountered first fails. -/
private def scanCoreOpSuccess (bytes : ByteArray) :
    Nat → Nat → Except CoreVerificationError Bool
  | 0, _ => .error (.script .badOpcode)
  | fuel + 1, offset => do
      if offset ≥ bytes.size then return false
      let instruction ← (readCoreRawInstruction bytes offset).mapError .script
      if isCoreOpSuccess instruction.opcode.toNat then return true
      scanCoreOpSuccess bytes fuel instruction.nextOffset

/-- A full source-order OP_SUCCESS scan; success overrides subsequent malformed
bytes and stack limits, as required by ExecuteWitnessScript. -/
def coreTapscriptHasOpSuccess (bytes : ByteArray) : Except CoreVerificationError Bool :=
  scanCoreOpSuccess bytes (bytes.size + 1) 0

private def acceptWitnessStack : Stack → Except CoreVerificationError Unit
  | [top] => if castToBool top then .ok () else .error (.script .evalFalse)
  | _ => .error (.script .cleanStack)

/-- Witness-v0 and Tapscript share element-size and cleanstack checks. Only
Tapscript limits the initial element count before executing its first opcode. -/
def executeCoreWitnessScript (execute : CoreScriptExecutor)
    (flags : CoreVerificationFlags) (request : CoreScriptExecutionRequest) :
    Except CoreVerificationError Unit := do
  if request.sigVersion = .tapscript then
    if ← coreTapscriptHasOpSuccess request.scriptBytes then
      if flags.discourageOpSuccess then throw .discourageOpSuccess
      return ()
    if request.stack.length > maxStackSize then throw (.script .stackSize)
  if request.stack.any (fun item => item.size > maxScriptElementSize) then
    throw (.script .pushSize)
  acceptWitnessStack (← execute request)

private def coreControlError : TaprootControlError → CoreVerificationError
  | .controlSize => .taprootWrongControlSize
  | _ => .witnessProgramMismatch

/-- Verify the program selected by VerifyScript, retaining Bitcoin Core's
native/wrapped distinction and witness error precedence. The executor supplies
transaction-backed Script signatures; key-path verification is a separate
callback. Wire-order witnesses are reversed only when entering Script. -/
def verifyCoreWitnessProgram (execute : CoreScriptExecutor)
    (flags : CoreVerificationFlags) (witness : List ByteArray)
    (version : Nat) (program : ByteArray) (isP2SH : Bool)
    (checkKeyPath : CoreKeyPathChecker :=
      fun _ _ _ => .error (.unsupported "Taproot key-path verifier")) :
    Except CoreVerificationError Unit := do
  if version = 0 then
    if program.size = 32 then
      match witness.reverse with
      | [] => throw .witnessProgramWitnessEmpty
      | script :: arguments =>
          if (LeanHash160.SHA256.hash script).data != program.data then
            throw .witnessProgramMismatch
          executeCoreWitnessScript execute flags {
            scriptBytes := script, stack := arguments, sigVersion := .witnessV0 }
    else if program.size = 20 then
      if witness.length != 2 then throw .witnessProgramMismatch
      executeCoreWitnessScript execute flags {
        scriptBytes := ⟨#[0x76, 0xa9, 0x14]⟩ ++ program ++ ⟨#[0x88, 0xac]⟩
        stack := witness.reverse
        sigVersion := .witnessV0 }
    else throw .witnessProgramWrongLength
  else if version = 1 && program.size = 32 && !isP2SH then
    if !flags.taproot then return ()
    let reversed := witness.reverse
    if reversed.isEmpty then throw .witnessProgramWitnessEmpty
    let (remaining, annex) := match reversed with
      | last :: next :: rest =>
          if last.size > 0 && last[0]! == 0x50 then (next :: rest, some last)
          else (reversed, none)
      | _ => (reversed, none)
    match remaining with
    | [] => throw .witnessProgramWitnessEmpty
    | [signature] => checkKeyPath signature program annex
    | control :: script :: arguments =>
        let commitment ← (verifyTaprootControlBlock program script control).mapError coreControlError
        if commitment.leafVersion = 0xc0 then
          executeCoreWitnessScript execute flags {
            scriptBytes := script
            stack := arguments
            sigVersion := .tapscript
            validationWeight := (serializeWitness witness).size + 50
            annex := annex
            tapleafHash := some commitment.leafHash
            leafVersion := commitment.leafVersion }
        else if flags.discourageUpgradableTaprootVersion then
          throw .discourageUpgradableTaprootVersion
        else return ()
  else if !isP2SH && version = 1 && program.data == #[0x4e, 0x73] then
    -- The pinned Core revision recognizes native pay-to-anchor programs.
    return ()
  else if flags.discourageUpgradableWitnessProgram then
    throw .discourageUpgradableWitnessProgram
  else return ()

end LeanMiniscript.Extraction
