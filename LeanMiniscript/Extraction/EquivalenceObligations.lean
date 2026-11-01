import LeanMiniscript.Extraction.BitcoinCoreExecutionProofs

/-!
# Opcode equivalence obligations

One theorem per (opcode, signature version): Core's `coreRawStep` and the typed
`runtimeStep` agree on that opcode for all flags, oracles, and states.
`scripts/equivalence_obligations.lean` counts the pairs without a proof.
-/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script
open CoreScriptExecution

/-- Core's raw step and the typed step give the same state or error. The typed
step uses the oracle for the script code after the last OP_CODESEPARATOR. -/
def OpcodeAgreement (opcode : Opcode) (version : SignatureVersion) : Prop :=
  ∀ (flags : CoreVerificationFlags) (ctx : TxContext)
    (oracles : SignatureVersion → ByteArray → CryptoOracle)
    (request : CoreScriptExecutionRequest) (state : CoreRawState)
    (instruction : CoreRawInstruction),
    request.sigVersion = version →
    instruction.Encodes (.op opcode) →
    (coreRawStep flags ctx oracles request state instruction).map CoreRawState.runtime =
      (runtimeStep
        (oracles version (request.scriptBytes.extract state.codeSeparatorOffset
          request.scriptBytes.size))
        (.op opcode) state.runtime flags.script
        (instructionContext ctx request state)).mapError .script

set_option maxHeartbeats 2000000 in
theorem opcodeAgreement_tapscript (opcode : Opcode)
    (timelock : opcode ≠ .OP_CHECKLOCKTIMEVERIFY ∧ opcode ≠ .OP_CHECKSEQUENCEVERIFY) :
    OpcodeAgreement opcode .tapscript := by
  intro flags ctx oracles request state instruction version encoded
  obtain ⟨byte, payload⟩ := encoded
  cases opcode <;> simp at timelock <;>
    simp +decide [coreRawStep, byte, payload, version,
      opcodeByte, opcodeFromByte?, coreLegacyDisabledOpcode, maxScriptElementSize,
      removeSignatures, bind, Except.bind, Except.mapError, Except.map,
      pure, Except.pure]
  all_goals split <;> split <;> simp_all <;> (subst_vars; rfl)

namespace OpcodeAgreement

/- TODO(equivalence): the remaining pairs are false for the current typed step.
- `.base`, `.witnessV0`: Core fails with `opCount` past 201 operations, and
  under `.base` CONST_SCRIPTCODE and FindAndDelete change the result.
- CLTV and CSV: Core runs them as OP_NOP when their flag is off. -/

theorem OP_NOP_tapscript : OpcodeAgreement .OP_NOP .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NOP1_tapscript : OpcodeAgreement .OP_NOP1 .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NOP4_tapscript : OpcodeAgreement .OP_NOP4 .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NOP5_tapscript : OpcodeAgreement .OP_NOP5 .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NOP6_tapscript : OpcodeAgreement .OP_NOP6 .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NOP7_tapscript : OpcodeAgreement .OP_NOP7 .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NOP8_tapscript : OpcodeAgreement .OP_NOP8 .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NOP9_tapscript : OpcodeAgreement .OP_NOP9 .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NOP10_tapscript : OpcodeAgreement .OP_NOP10 .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_RETURN_tapscript : OpcodeAgreement .OP_RETURN .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_IF_tapscript : OpcodeAgreement .OP_IF .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NOTIF_tapscript : OpcodeAgreement .OP_NOTIF .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_ELSE_tapscript : OpcodeAgreement .OP_ELSE .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_ENDIF_tapscript : OpcodeAgreement .OP_ENDIF .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_2DROP_tapscript : OpcodeAgreement .OP_2DROP .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_2DUP_tapscript : OpcodeAgreement .OP_2DUP .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_3DUP_tapscript : OpcodeAgreement .OP_3DUP .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_2OVER_tapscript : OpcodeAgreement .OP_2OVER .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_2ROT_tapscript : OpcodeAgreement .OP_2ROT .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_2SWAP_tapscript : OpcodeAgreement .OP_2SWAP .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_IFDUP_tapscript : OpcodeAgreement .OP_IFDUP .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_DEPTH_tapscript : OpcodeAgreement .OP_DEPTH .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_DROP_tapscript : OpcodeAgreement .OP_DROP .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_DUP_tapscript : OpcodeAgreement .OP_DUP .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NIP_tapscript : OpcodeAgreement .OP_NIP .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_OVER_tapscript : OpcodeAgreement .OP_OVER .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_PICK_tapscript : OpcodeAgreement .OP_PICK .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_ROLL_tapscript : OpcodeAgreement .OP_ROLL .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_ROT_tapscript : OpcodeAgreement .OP_ROT .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_SWAP_tapscript : OpcodeAgreement .OP_SWAP .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_TUCK_tapscript : OpcodeAgreement .OP_TUCK .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_TOALTSTACK_tapscript : OpcodeAgreement .OP_TOALTSTACK .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_FROMALTSTACK_tapscript : OpcodeAgreement .OP_FROMALTSTACK .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_1ADD_tapscript : OpcodeAgreement .OP_1ADD .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_1SUB_tapscript : OpcodeAgreement .OP_1SUB .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NEGATE_tapscript : OpcodeAgreement .OP_NEGATE .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_ABS_tapscript : OpcodeAgreement .OP_ABS .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_ADD_tapscript : OpcodeAgreement .OP_ADD .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_SUB_tapscript : OpcodeAgreement .OP_SUB .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_BOOLAND_tapscript : OpcodeAgreement .OP_BOOLAND .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_BOOLOR_tapscript : OpcodeAgreement .OP_BOOLOR .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NOT_tapscript : OpcodeAgreement .OP_NOT .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_0NOTEQUAL_tapscript : OpcodeAgreement .OP_0NOTEQUAL .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_EQUAL_tapscript : OpcodeAgreement .OP_EQUAL .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_EQUALVERIFY_tapscript : OpcodeAgreement .OP_EQUALVERIFY .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NUMEQUAL_tapscript : OpcodeAgreement .OP_NUMEQUAL .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NUMEQUALVERIFY_tapscript : OpcodeAgreement .OP_NUMEQUALVERIFY .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_NUMNOTEQUAL_tapscript : OpcodeAgreement .OP_NUMNOTEQUAL .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_LESSTHAN_tapscript : OpcodeAgreement .OP_LESSTHAN .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_GREATERTHAN_tapscript : OpcodeAgreement .OP_GREATERTHAN .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_LESSTHANOREQUAL_tapscript : OpcodeAgreement .OP_LESSTHANOREQUAL .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_GREATERTHANOREQUAL_tapscript : OpcodeAgreement .OP_GREATERTHANOREQUAL .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_MIN_tapscript : OpcodeAgreement .OP_MIN .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_MAX_tapscript : OpcodeAgreement .OP_MAX .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_WITHIN_tapscript : OpcodeAgreement .OP_WITHIN .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_SHA256_tapscript : OpcodeAgreement .OP_SHA256 .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_HASH256_tapscript : OpcodeAgreement .OP_HASH256 .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_RIPEMD160_tapscript : OpcodeAgreement .OP_RIPEMD160 .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_HASH160_tapscript : OpcodeAgreement .OP_HASH160 .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_CHECKSIG_tapscript : OpcodeAgreement .OP_CHECKSIG .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_CHECKSIGVERIFY_tapscript : OpcodeAgreement .OP_CHECKSIGVERIFY .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_CHECKSIGADD_tapscript : OpcodeAgreement .OP_CHECKSIGADD .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_CHECKMULTISIG_tapscript : OpcodeAgreement .OP_CHECKMULTISIG .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_CHECKMULTISIGVERIFY_tapscript : OpcodeAgreement .OP_CHECKMULTISIGVERIFY .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_VERIFY_tapscript : OpcodeAgreement .OP_VERIFY .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

theorem OP_SIZE_tapscript : OpcodeAgreement .OP_SIZE .tapscript :=
  opcodeAgreement_tapscript _ (by decide)

end OpcodeAgreement

/-- One equivalence obligation and the theorem expected to discharge it. -/
structure EquivalenceObligation where
  opcode : Opcode
  version : SignatureVersion
  theoremName : Lean.Name

/-- Every `Opcode` × `SignatureVersion`, each naming the theorem that should
prove `OpcodeAgreement opcode version`. -/
def equivalenceObligations : List EquivalenceObligation := [
  ⟨.OP_NOP, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP_base⟩,
  ⟨.OP_NOP, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP_witnessV0⟩,
  ⟨.OP_NOP, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP_tapscript⟩,
  ⟨.OP_NOP1, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP1_base⟩,
  ⟨.OP_NOP1, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP1_witnessV0⟩,
  ⟨.OP_NOP1, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP1_tapscript⟩,
  ⟨.OP_NOP4, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP4_base⟩,
  ⟨.OP_NOP4, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP4_witnessV0⟩,
  ⟨.OP_NOP4, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP4_tapscript⟩,
  ⟨.OP_NOP5, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP5_base⟩,
  ⟨.OP_NOP5, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP5_witnessV0⟩,
  ⟨.OP_NOP5, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP5_tapscript⟩,
  ⟨.OP_NOP6, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP6_base⟩,
  ⟨.OP_NOP6, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP6_witnessV0⟩,
  ⟨.OP_NOP6, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP6_tapscript⟩,
  ⟨.OP_NOP7, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP7_base⟩,
  ⟨.OP_NOP7, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP7_witnessV0⟩,
  ⟨.OP_NOP7, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP7_tapscript⟩,
  ⟨.OP_NOP8, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP8_base⟩,
  ⟨.OP_NOP8, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP8_witnessV0⟩,
  ⟨.OP_NOP8, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP8_tapscript⟩,
  ⟨.OP_NOP9, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP9_base⟩,
  ⟨.OP_NOP9, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP9_witnessV0⟩,
  ⟨.OP_NOP9, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP9_tapscript⟩,
  ⟨.OP_NOP10, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP10_base⟩,
  ⟨.OP_NOP10, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP10_witnessV0⟩,
  ⟨.OP_NOP10, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOP10_tapscript⟩,
  ⟨.OP_RETURN, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_RETURN_base⟩,
  ⟨.OP_RETURN, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_RETURN_witnessV0⟩,
  ⟨.OP_RETURN, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_RETURN_tapscript⟩,
  ⟨.OP_IF, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_IF_base⟩,
  ⟨.OP_IF, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_IF_witnessV0⟩,
  ⟨.OP_IF, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_IF_tapscript⟩,
  ⟨.OP_NOTIF, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOTIF_base⟩,
  ⟨.OP_NOTIF, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOTIF_witnessV0⟩,
  ⟨.OP_NOTIF, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOTIF_tapscript⟩,
  ⟨.OP_ELSE, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ELSE_base⟩,
  ⟨.OP_ELSE, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ELSE_witnessV0⟩,
  ⟨.OP_ELSE, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ELSE_tapscript⟩,
  ⟨.OP_ENDIF, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ENDIF_base⟩,
  ⟨.OP_ENDIF, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ENDIF_witnessV0⟩,
  ⟨.OP_ENDIF, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ENDIF_tapscript⟩,
  ⟨.OP_2DROP, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2DROP_base⟩,
  ⟨.OP_2DROP, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2DROP_witnessV0⟩,
  ⟨.OP_2DROP, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2DROP_tapscript⟩,
  ⟨.OP_2DUP, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2DUP_base⟩,
  ⟨.OP_2DUP, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2DUP_witnessV0⟩,
  ⟨.OP_2DUP, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2DUP_tapscript⟩,
  ⟨.OP_3DUP, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_3DUP_base⟩,
  ⟨.OP_3DUP, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_3DUP_witnessV0⟩,
  ⟨.OP_3DUP, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_3DUP_tapscript⟩,
  ⟨.OP_2OVER, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2OVER_base⟩,
  ⟨.OP_2OVER, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2OVER_witnessV0⟩,
  ⟨.OP_2OVER, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2OVER_tapscript⟩,
  ⟨.OP_2ROT, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2ROT_base⟩,
  ⟨.OP_2ROT, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2ROT_witnessV0⟩,
  ⟨.OP_2ROT, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2ROT_tapscript⟩,
  ⟨.OP_2SWAP, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2SWAP_base⟩,
  ⟨.OP_2SWAP, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2SWAP_witnessV0⟩,
  ⟨.OP_2SWAP, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_2SWAP_tapscript⟩,
  ⟨.OP_IFDUP, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_IFDUP_base⟩,
  ⟨.OP_IFDUP, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_IFDUP_witnessV0⟩,
  ⟨.OP_IFDUP, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_IFDUP_tapscript⟩,
  ⟨.OP_DEPTH, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_DEPTH_base⟩,
  ⟨.OP_DEPTH, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_DEPTH_witnessV0⟩,
  ⟨.OP_DEPTH, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_DEPTH_tapscript⟩,
  ⟨.OP_DROP, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_DROP_base⟩,
  ⟨.OP_DROP, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_DROP_witnessV0⟩,
  ⟨.OP_DROP, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_DROP_tapscript⟩,
  ⟨.OP_DUP, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_DUP_base⟩,
  ⟨.OP_DUP, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_DUP_witnessV0⟩,
  ⟨.OP_DUP, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_DUP_tapscript⟩,
  ⟨.OP_NIP, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NIP_base⟩,
  ⟨.OP_NIP, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NIP_witnessV0⟩,
  ⟨.OP_NIP, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NIP_tapscript⟩,
  ⟨.OP_OVER, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_OVER_base⟩,
  ⟨.OP_OVER, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_OVER_witnessV0⟩,
  ⟨.OP_OVER, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_OVER_tapscript⟩,
  ⟨.OP_PICK, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_PICK_base⟩,
  ⟨.OP_PICK, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_PICK_witnessV0⟩,
  ⟨.OP_PICK, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_PICK_tapscript⟩,
  ⟨.OP_ROLL, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ROLL_base⟩,
  ⟨.OP_ROLL, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ROLL_witnessV0⟩,
  ⟨.OP_ROLL, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ROLL_tapscript⟩,
  ⟨.OP_ROT, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ROT_base⟩,
  ⟨.OP_ROT, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ROT_witnessV0⟩,
  ⟨.OP_ROT, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ROT_tapscript⟩,
  ⟨.OP_SWAP, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_SWAP_base⟩,
  ⟨.OP_SWAP, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_SWAP_witnessV0⟩,
  ⟨.OP_SWAP, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_SWAP_tapscript⟩,
  ⟨.OP_TUCK, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_TUCK_base⟩,
  ⟨.OP_TUCK, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_TUCK_witnessV0⟩,
  ⟨.OP_TUCK, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_TUCK_tapscript⟩,
  ⟨.OP_TOALTSTACK, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_TOALTSTACK_base⟩,
  ⟨.OP_TOALTSTACK, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_TOALTSTACK_witnessV0⟩,
  ⟨.OP_TOALTSTACK, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_TOALTSTACK_tapscript⟩,
  ⟨.OP_FROMALTSTACK, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_FROMALTSTACK_base⟩,
  ⟨.OP_FROMALTSTACK, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_FROMALTSTACK_witnessV0⟩,
  ⟨.OP_FROMALTSTACK, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_FROMALTSTACK_tapscript⟩,
  ⟨.OP_1ADD, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_1ADD_base⟩,
  ⟨.OP_1ADD, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_1ADD_witnessV0⟩,
  ⟨.OP_1ADD, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_1ADD_tapscript⟩,
  ⟨.OP_1SUB, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_1SUB_base⟩,
  ⟨.OP_1SUB, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_1SUB_witnessV0⟩,
  ⟨.OP_1SUB, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_1SUB_tapscript⟩,
  ⟨.OP_NEGATE, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NEGATE_base⟩,
  ⟨.OP_NEGATE, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NEGATE_witnessV0⟩,
  ⟨.OP_NEGATE, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NEGATE_tapscript⟩,
  ⟨.OP_ABS, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ABS_base⟩,
  ⟨.OP_ABS, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ABS_witnessV0⟩,
  ⟨.OP_ABS, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ABS_tapscript⟩,
  ⟨.OP_ADD, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ADD_base⟩,
  ⟨.OP_ADD, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ADD_witnessV0⟩,
  ⟨.OP_ADD, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_ADD_tapscript⟩,
  ⟨.OP_SUB, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_SUB_base⟩,
  ⟨.OP_SUB, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_SUB_witnessV0⟩,
  ⟨.OP_SUB, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_SUB_tapscript⟩,
  ⟨.OP_BOOLAND, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_BOOLAND_base⟩,
  ⟨.OP_BOOLAND, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_BOOLAND_witnessV0⟩,
  ⟨.OP_BOOLAND, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_BOOLAND_tapscript⟩,
  ⟨.OP_BOOLOR, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_BOOLOR_base⟩,
  ⟨.OP_BOOLOR, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_BOOLOR_witnessV0⟩,
  ⟨.OP_BOOLOR, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_BOOLOR_tapscript⟩,
  ⟨.OP_NOT, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOT_base⟩,
  ⟨.OP_NOT, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOT_witnessV0⟩,
  ⟨.OP_NOT, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NOT_tapscript⟩,
  ⟨.OP_0NOTEQUAL, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_0NOTEQUAL_base⟩,
  ⟨.OP_0NOTEQUAL, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_0NOTEQUAL_witnessV0⟩,
  ⟨.OP_0NOTEQUAL, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_0NOTEQUAL_tapscript⟩,
  ⟨.OP_EQUAL, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_EQUAL_base⟩,
  ⟨.OP_EQUAL, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_EQUAL_witnessV0⟩,
  ⟨.OP_EQUAL, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_EQUAL_tapscript⟩,
  ⟨.OP_EQUALVERIFY, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_EQUALVERIFY_base⟩,
  ⟨.OP_EQUALVERIFY, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_EQUALVERIFY_witnessV0⟩,
  ⟨.OP_EQUALVERIFY, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_EQUALVERIFY_tapscript⟩,
  ⟨.OP_NUMEQUAL, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NUMEQUAL_base⟩,
  ⟨.OP_NUMEQUAL, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NUMEQUAL_witnessV0⟩,
  ⟨.OP_NUMEQUAL, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NUMEQUAL_tapscript⟩,
  ⟨.OP_NUMEQUALVERIFY, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NUMEQUALVERIFY_base⟩,
  ⟨.OP_NUMEQUALVERIFY, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NUMEQUALVERIFY_witnessV0⟩,
  ⟨.OP_NUMEQUALVERIFY, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NUMEQUALVERIFY_tapscript⟩,
  ⟨.OP_NUMNOTEQUAL, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NUMNOTEQUAL_base⟩,
  ⟨.OP_NUMNOTEQUAL, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NUMNOTEQUAL_witnessV0⟩,
  ⟨.OP_NUMNOTEQUAL, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_NUMNOTEQUAL_tapscript⟩,
  ⟨.OP_LESSTHAN, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_LESSTHAN_base⟩,
  ⟨.OP_LESSTHAN, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_LESSTHAN_witnessV0⟩,
  ⟨.OP_LESSTHAN, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_LESSTHAN_tapscript⟩,
  ⟨.OP_GREATERTHAN, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_GREATERTHAN_base⟩,
  ⟨.OP_GREATERTHAN, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_GREATERTHAN_witnessV0⟩,
  ⟨.OP_GREATERTHAN, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_GREATERTHAN_tapscript⟩,
  ⟨.OP_LESSTHANOREQUAL, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_LESSTHANOREQUAL_base⟩,
  ⟨.OP_LESSTHANOREQUAL, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_LESSTHANOREQUAL_witnessV0⟩,
  ⟨.OP_LESSTHANOREQUAL, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_LESSTHANOREQUAL_tapscript⟩,
  ⟨.OP_GREATERTHANOREQUAL, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_GREATERTHANOREQUAL_base⟩,
  ⟨.OP_GREATERTHANOREQUAL, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_GREATERTHANOREQUAL_witnessV0⟩,
  ⟨.OP_GREATERTHANOREQUAL, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_GREATERTHANOREQUAL_tapscript⟩,
  ⟨.OP_MIN, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_MIN_base⟩,
  ⟨.OP_MIN, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_MIN_witnessV0⟩,
  ⟨.OP_MIN, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_MIN_tapscript⟩,
  ⟨.OP_MAX, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_MAX_base⟩,
  ⟨.OP_MAX, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_MAX_witnessV0⟩,
  ⟨.OP_MAX, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_MAX_tapscript⟩,
  ⟨.OP_WITHIN, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_WITHIN_base⟩,
  ⟨.OP_WITHIN, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_WITHIN_witnessV0⟩,
  ⟨.OP_WITHIN, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_WITHIN_tapscript⟩,
  ⟨.OP_SHA256, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_SHA256_base⟩,
  ⟨.OP_SHA256, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_SHA256_witnessV0⟩,
  ⟨.OP_SHA256, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_SHA256_tapscript⟩,
  ⟨.OP_HASH256, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_HASH256_base⟩,
  ⟨.OP_HASH256, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_HASH256_witnessV0⟩,
  ⟨.OP_HASH256, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_HASH256_tapscript⟩,
  ⟨.OP_RIPEMD160, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_RIPEMD160_base⟩,
  ⟨.OP_RIPEMD160, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_RIPEMD160_witnessV0⟩,
  ⟨.OP_RIPEMD160, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_RIPEMD160_tapscript⟩,
  ⟨.OP_HASH160, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_HASH160_base⟩,
  ⟨.OP_HASH160, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_HASH160_witnessV0⟩,
  ⟨.OP_HASH160, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_HASH160_tapscript⟩,
  ⟨.OP_CHECKSIG, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKSIG_base⟩,
  ⟨.OP_CHECKSIG, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKSIG_witnessV0⟩,
  ⟨.OP_CHECKSIG, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKSIG_tapscript⟩,
  ⟨.OP_CHECKSIGVERIFY, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKSIGVERIFY_base⟩,
  ⟨.OP_CHECKSIGVERIFY, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKSIGVERIFY_witnessV0⟩,
  ⟨.OP_CHECKSIGVERIFY, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKSIGVERIFY_tapscript⟩,
  ⟨.OP_CHECKSIGADD, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKSIGADD_base⟩,
  ⟨.OP_CHECKSIGADD, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKSIGADD_witnessV0⟩,
  ⟨.OP_CHECKSIGADD, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKSIGADD_tapscript⟩,
  ⟨.OP_CHECKMULTISIG, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKMULTISIG_base⟩,
  ⟨.OP_CHECKMULTISIG, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKMULTISIG_witnessV0⟩,
  ⟨.OP_CHECKMULTISIG, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKMULTISIG_tapscript⟩,
  ⟨.OP_CHECKMULTISIGVERIFY, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKMULTISIGVERIFY_base⟩,
  ⟨.OP_CHECKMULTISIGVERIFY, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKMULTISIGVERIFY_witnessV0⟩,
  ⟨.OP_CHECKMULTISIGVERIFY, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKMULTISIGVERIFY_tapscript⟩,
  ⟨.OP_CHECKSEQUENCEVERIFY, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKSEQUENCEVERIFY_base⟩,
  ⟨.OP_CHECKSEQUENCEVERIFY, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKSEQUENCEVERIFY_witnessV0⟩,
  ⟨.OP_CHECKSEQUENCEVERIFY, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKSEQUENCEVERIFY_tapscript⟩,
  ⟨.OP_CHECKLOCKTIMEVERIFY, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKLOCKTIMEVERIFY_base⟩,
  ⟨.OP_CHECKLOCKTIMEVERIFY, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKLOCKTIMEVERIFY_witnessV0⟩,
  ⟨.OP_CHECKLOCKTIMEVERIFY, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_CHECKLOCKTIMEVERIFY_tapscript⟩,
  ⟨.OP_VERIFY, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_VERIFY_base⟩,
  ⟨.OP_VERIFY, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_VERIFY_witnessV0⟩,
  ⟨.OP_VERIFY, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_VERIFY_tapscript⟩,
  ⟨.OP_SIZE, .base, `LeanMiniscript.Extraction.OpcodeAgreement.OP_SIZE_base⟩,
  ⟨.OP_SIZE, .witnessV0, `LeanMiniscript.Extraction.OpcodeAgreement.OP_SIZE_witnessV0⟩,
  ⟨.OP_SIZE, .tapscript, `LeanMiniscript.Extraction.OpcodeAgreement.OP_SIZE_tapscript⟩
]

end LeanMiniscript.Extraction
