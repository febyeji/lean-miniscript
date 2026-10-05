import LeanMiniscript.Extraction.BitcoinCoreVerification

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-- BASE and witness-v0 reject an oversized source before parsing or execution. -/
theorem executeCoreScript_scriptSize (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracleForScript : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest)
    (legacy : (request.sigVersion != .tapscript) = true)
    (large : request.scriptBytes.size > 10000) :
    executeCoreScript flags ctx oracleForScript request = .error (.script .scriptSize) := by
  simp [executeCoreScript, legacy, large]

/-- SIGPUSHONLY runs before either script and every witness callback. -/
theorem verifyCoreScripts_sigPushOnly (execute : CoreScriptExecutor)
    (verifyWitness : CoreWitnessVerifier) (flags : CoreVerificationFlags)
    (scriptSig scriptPubKey : ByteArray) (witness : List ByteArray)
    (enabled : flags.sigPushOnly = true) (rejected : coreScriptIsPushOnly scriptSig = false) :
    verifyCoreScripts execute verifyWitness flags scriptSig scriptPubKey witness =
      .error .sigPushOnly := by
  simp [verifyCoreScripts, enabled, rejected]
  rfl

/-- A reached scriptSig error precedes pubkey and witness evaluation. -/
theorem verifyCoreScripts_scriptSigFailure (execute : CoreScriptExecutor)
    (verifyWitness : CoreWitnessVerifier) (flags : CoreVerificationFlags)
    (scriptSig scriptPubKey : ByteArray) (witness : List ByteArray)
    (allowed : (flags.sigPushOnly && !coreScriptIsPushOnly scriptSig) = false)
    (error : CoreVerificationError)
    (failed : execute { scriptBytes := scriptSig } = .error error) :
    verifyCoreScripts execute verifyWitness flags scriptSig scriptPubKey witness =
      .error error := by
  simp [verifyCoreScripts, allowed, failed, bind, Except.bind]

/-- A scriptPubKey error is preserved before P2SH, CLEANSTACK or witness handling. -/
theorem verifyCoreScripts_scriptPubKeyFailure (execute : CoreScriptExecutor)
    (verifyWitness : CoreWitnessVerifier) (flags : CoreVerificationFlags)
    (scriptSig scriptPubKey : ByteArray) (witness : List ByteArray)
    (allowed : (flags.sigPushOnly && !coreScriptIsPushOnly scriptSig) = false)
    (stack : Stack) (error : CoreVerificationError)
    (sigDone : execute { scriptBytes := scriptSig } = .ok stack)
    (failed : execute { scriptBytes := scriptPubKey, stack := stack } = .error error) :
    verifyCoreScripts execute verifyWitness flags scriptSig scriptPubKey witness =
      .error error := by
  simp [verifyCoreScripts, allowed, sigDone, failed, bind, Except.bind]

end LeanMiniscript.Extraction
