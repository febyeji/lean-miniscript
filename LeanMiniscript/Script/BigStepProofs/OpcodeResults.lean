import LeanMiniscript.Script.BigStep
import LeanMiniscript.Script.BigStepProofs.Totality

namespace LeanMiniscript.Script

/-!
# Big-step proofs: opcode results

Characterizations of the result of individual stack, arithmetic, NOP,
signature, and alt-stack opcodes, plus small concrete conditional examples.
-/

theorem Eval.done {stack altStack : Stack} {flags : ScriptFlags} {ctx : TxContext} :
    Eval [] stack altStack flags ctx (.success stack altStack) :=
  .empty stack altStack flags ctx

/-- NIP removes precisely the second item for every pair of byte vectors. -/
theorem Eval.nip_result (top discarded : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_NIP] (top :: discarded :: stack) altStack flags ctx result ↔
      result = .success (top :: stack) altStack := by
  have canonical : Eval [.op .OP_NIP] (top :: discarded :: stack) altStack flags ctx
      (.success (top :: stack) altStack) :=
    .nip top discarded stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With zero or one main-stack item, NIP terminates before any suffix. -/
theorem Eval.nip_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 2)
    (evaluated : Eval (.op .OP_NIP :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_NIP 2 script stack altStack flags ctx rfl short)

/-- 2DROP removes precisely the top two items for every pair of byte vectors. -/
theorem Eval.twoDrop_result (top discarded : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_2DROP] (top :: discarded :: stack) altStack flags ctx result ↔
      result = .success stack altStack := by
  have canonical : Eval [.op .OP_2DROP] (top :: discarded :: stack) altStack flags ctx
      (.success stack altStack) :=
    .twoDrop top discarded stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With zero or one main-stack item, 2DROP terminates before any suffix. -/
theorem Eval.twoDrop_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 2)
    (evaluated : Eval (.op .OP_2DROP :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_2DROP 2 script stack altStack flags ctx rfl short)

/-- 2DUP copies the top pair in order above the unchanged original stack. -/
theorem Eval.twoDup_result (top below : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_2DUP] (top :: below :: stack) altStack flags ctx result ↔
      result = .success (top :: below :: top :: below :: stack) altStack := by
  have canonical : Eval [.op .OP_2DUP] (top :: below :: stack) altStack flags ctx
      (.success (top :: below :: top :: below :: stack) altStack) :=
    .twoDup top below stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With zero or one main-stack item, 2DUP terminates before any suffix. -/
theorem Eval.twoDup_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 2)
    (evaluated : Eval (.op .OP_2DUP :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_2DUP 2 script stack altStack flags ctx rfl short)

/-- 3DUP copies the top three items in order above the unchanged original stack. -/
theorem Eval.threeDup_result (top second third : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_3DUP] (top :: second :: third :: stack) altStack flags ctx result ↔
      result = .success (top :: second :: third :: top :: second :: third :: stack) altStack := by
  have canonical : Eval [.op .OP_3DUP] (top :: second :: third :: stack) altStack flags ctx
      (.success (top :: second :: third :: top :: second :: third :: stack) altStack) :=
    .threeDup top second third stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With fewer than three main-stack items, 3DUP terminates before any suffix. -/
theorem Eval.threeDup_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 3)
    (evaluated : Eval (.op .OP_3DUP :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_3DUP 3 script stack altStack flags ctx rfl short)

/-- 2OVER copies the third and fourth items above the unchanged original stack. -/
theorem Eval.twoOver_result (top second third fourth : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_2OVER] (top :: second :: third :: fourth :: stack) altStack flags ctx result ↔
      result = .success (third :: fourth :: top :: second :: third :: fourth :: stack) altStack := by
  have canonical : Eval [.op .OP_2OVER] (top :: second :: third :: fourth :: stack) altStack flags ctx
      (.success (third :: fourth :: top :: second :: third :: fourth :: stack) altStack) :=
    .twoOver top second third fourth stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With fewer than four main-stack items, 2OVER terminates before any suffix. -/
theorem Eval.twoOver_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 4)
    (evaluated : Eval (.op .OP_2OVER :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_2OVER 4 script stack altStack flags ctx rfl short)

/-- OVER copies precisely the second item above the unchanged original stack. -/
theorem Eval.over_result (top below : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_OVER] (top :: below :: stack) altStack flags ctx result ↔
      result = .success (below :: top :: below :: stack) altStack := by
  have canonical : Eval [.op .OP_OVER] (top :: below :: stack) altStack flags ctx
      (.success (below :: top :: below :: stack) altStack) :=
    .over top below stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With zero or one main-stack item, OVER terminates before any suffix. -/
theorem Eval.over_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 2)
    (evaluated : Eval (.op .OP_OVER :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_OVER 2 script stack altStack flags ctx rfl short)

/-- TUCK inserts an exact copy of the top item beneath the original top two. -/
theorem Eval.tuck_result (top below : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_TUCK] (top :: below :: stack) altStack flags ctx result ↔
      result = .success (top :: below :: top :: stack) altStack := by
  have canonical : Eval [.op .OP_TUCK] (top :: below :: stack) altStack flags ctx
      (.success (top :: below :: top :: stack) altStack) :=
    .tuck top below stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With zero or one main-stack item, TUCK terminates before any suffix. -/
theorem Eval.tuck_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 2)
    (evaluated : Eval (.op .OP_TUCK :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_TUCK 2 script stack altStack flags ctx rfl short)

/-- ROT moves the third item to the top, preserving the lower stack and raw bytes. -/
theorem Eval.rot_result (top second third : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_ROT] (top :: second :: third :: stack) altStack flags ctx result ↔
      result = .success (third :: top :: second :: stack) altStack := by
  have canonical : Eval [.op .OP_ROT] (top :: second :: third :: stack) altStack flags ctx
      (.success (third :: top :: second :: stack) altStack) :=
    .rot top second third stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With fewer than three main-stack items, ROT terminates before any suffix. -/
theorem Eval.rot_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 3)
    (evaluated : Eval (.op .OP_ROT :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_ROT 3 script stack altStack flags ctx rfl short)

/-- 2ROT moves the fifth and sixth items to the top, preserving the lower stack and raw bytes. -/
theorem Eval.twoRot_result (top second third fourth fifth sixth : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_2ROT] (top :: second :: third :: fourth :: fifth :: sixth :: stack) altStack flags ctx result ↔
      result = .success (fifth :: sixth :: top :: second :: third :: fourth :: stack) altStack := by
  have canonical : Eval [.op .OP_2ROT] (top :: second :: third :: fourth :: fifth :: sixth :: stack) altStack flags ctx
      (.success (fifth :: sixth :: top :: second :: third :: fourth :: stack) altStack) :=
    .twoRot top second third fourth fifth sixth stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With fewer than six main-stack items, 2ROT terminates before any suffix. -/
theorem Eval.twoRot_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 6)
    (evaluated : Eval (.op .OP_2ROT :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_2ROT 6 script stack altStack flags ctx rfl short)

/-- 2SWAP exchanges the top two pairs, preserving the lower stack and raw bytes. -/
theorem Eval.twoSwap_result (top second third fourth : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_2SWAP] (top :: second :: third :: fourth :: stack) altStack flags ctx result ↔
      result = .success (third :: fourth :: top :: second :: stack) altStack := by
  have canonical : Eval [.op .OP_2SWAP] (top :: second :: third :: fourth :: stack) altStack flags ctx
      (.success (third :: fourth :: top :: second :: stack) altStack) :=
    .twoSwap top second third fourth stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- With fewer than four main-stack items, 2SWAP terminates before any suffix. -/
theorem Eval.twoSwap_underflow_result {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (short : stack.length < 4)
    (evaluated : Eval (.op .OP_2SWAP :: script) stack altStack flags ctx result) :
    result = .failure .stackUnderflow :=
  evaluated.result_unique (.stack_underflow .OP_2SWAP 4 script stack altStack flags ctx rfl short)

/-- An allowed upgradeable NOP preserves the suffix relation and both stacks. -/
theorem Eval.upgradeableNop_cons (opcode : Opcode) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (allowed : flags.discourageUpgradableNops = false) (result : ExecResult) :
    Eval (.op opcode :: script) stack altStack flags ctx result ↔
      Eval script stack altStack flags ctx result := by
  constructor
  · intro evaluated
    rcases Eval.exists_result script stack altStack flags ctx with ⟨nextResult, next⟩
    have same := evaluated.result_unique
      (.upgradeableNop opcode script stack altStack flags ctx nextResult
        upgradeable allowed next)
    cases same
    exact next
  · exact .upgradeableNop opcode script stack altStack flags ctx result upgradeable allowed

/-- An allowed upgradeable NOP has the exact unchanged-stack result. -/
theorem Eval.upgradeableNop_result (opcode : Opcode)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (allowed : flags.discourageUpgradableNops = false) (result : ExecResult) :
    Eval [.op opcode] stack altStack flags ctx result ↔
      result = .success stack altStack := by
  have canonical : Eval [.op opcode] stack altStack flags ctx (.success stack altStack) :=
    .upgradeableNop opcode [] stack altStack flags ctx _ upgradeable allowed .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- A discouraged upgradeable NOP terminates before its suffix. -/
theorem Eval.upgradeableNop_failure_result (opcode : Opcode) (script : Script)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (upgradeable : opcode.isUpgradeableNop = true)
    (discouraged : flags.discourageUpgradableNops = true) (result : ExecResult) :
    Eval (.op opcode :: script) stack altStack flags ctx result ↔
      result = .failure .discourageUpgradableNops := by
  have canonical : Eval (.op opcode :: script) stack altStack flags ctx
      (.failure .discourageUpgradableNops) :=
    .upgradeableNop_discouraged opcode script stack altStack flags ctx upgradeable discouraged
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Active RETURN determines the terminal result for every stack and suffix. -/
theorem Eval.opReturn_result (script : Script) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult) :
    Eval (.op .OP_RETURN :: script) stack altStack flags ctx result ↔
      result = .failure .opReturn := by
  have canonical : Eval (.op .OP_RETURN :: script) stack altStack flags ctx
      (.failure .opReturn) := .opReturn script stack altStack flags ctx
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- A decoded in-range index determines the exact OP_PICK result. -/
theorem Eval.pick_result (operand top : StackElement) (index : Nat)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeStackIndex flags operand (top :: stack).length = .ok index)
    (result : ExecResult) :
    Eval [.op .OP_PICK] (operand :: top :: stack) altStack flags ctx result ↔
      result = .success ((top :: stack)[index]?.getD ByteArray.empty ::
        (top :: stack)) altStack := by
  have canonical : Eval [.op .OP_PICK] (operand :: top :: stack) altStack flags ctx
      (.success ((top :: stack)[index]?.getD ByteArray.empty ::
        (top :: stack)) altStack) :=
    .pick operand top index stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- A decoded in-range index determines the exact OP_ROLL result. -/
theorem Eval.roll_result (operand top : StackElement) (index : Nat)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeStackIndex flags operand (top :: stack).length = .ok index)
    (result : ExecResult) :
    Eval [.op .OP_ROLL] (operand :: top :: stack) altStack flags ctx result ↔
      result = .success ((top :: stack)[index]?.getD ByteArray.empty ::
        (top :: stack).eraseIdx index) altStack := by
  have canonical : Eval [.op .OP_ROLL] (operand :: top :: stack) altStack flags ctx
      (.success ((top :: stack)[index]?.getD ByteArray.empty ::
        (top :: stack).eraseIdx index) altStack) :=
    .roll operand top index stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- DEPTH has this exact relational result for every main/alternate stack. -/
theorem Eval.depth_result (stack altStack : Stack) (flags : ScriptFlags)
    (ctx : TxContext) (result : ExecResult) :
    Eval [.op .OP_DEPTH] stack altStack flags ctx result ↔
      result = .success (scriptNat stack.length :: stack) altStack := by
  have canonical : Eval [.op .OP_DEPTH] stack altStack flags ctx
      (.success (scriptNat stack.length :: stack) altStack) :=
    .depth stack altStack [] flags ctx _ .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Successful OP_1ADD decoding determines its exact relational result. -/
theorem Eval.oneAdd_result (operand : StackElement) (value : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .ok value) (result : ExecResult) :
    Eval [.op .OP_1ADD] (operand :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (value + 1) :: stack) altStack := by
  have canonical : Eval [.op .OP_1ADD] (operand :: stack) altStack flags ctx
      (.success (scriptNum (value + 1) :: stack) altStack) :=
    .oneAdd operand value stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Successful OP_1SUB decoding determines its exact relational result. -/
theorem Eval.oneSub_result (operand : StackElement) (value : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .ok value) (result : ExecResult) :
    Eval [.op .OP_1SUB] (operand :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (value - 1) :: stack) altStack := by
  have canonical : Eval [.op .OP_1SUB] (operand :: stack) altStack flags ctx
      (.success (scriptNum (value - 1) :: stack) altStack) :=
    .oneSub operand value stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Successful OP_NEGATE decoding determines its exact relational result. -/
theorem Eval.negate_result (operand : StackElement) (value : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .ok value) (result : ExecResult) :
    Eval [.op .OP_NEGATE] (operand :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (-value) :: stack) altStack := by
  have canonical : Eval [.op .OP_NEGATE] (operand :: stack) altStack flags ctx
      (.success (scriptNum (-value) :: stack) altStack) :=
    .negate operand value stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Successful OP_ABS decoding determines its exact relational result. -/
theorem Eval.abs_result (operand : StackElement) (value : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .ok value) (result : ExecResult) :
    Eval [.op .OP_ABS] (operand :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (if value < 0 then -value else value) :: stack) altStack := by
  have canonical : Eval [.op .OP_ABS] (operand :: stack) altStack flags ctx
      (.success (scriptNum (if value < 0 then -value else value) :: stack) altStack) :=
    .abs operand value stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_SUB operands determine its exact relational result. -/
theorem Eval.sub_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_SUB] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (b - a) :: stack) altStack := by
  have canonical : Eval [.op .OP_SUB] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (scriptNum (b - a) :: stack) altStack) :=
    .sub aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_MIN operands determine its exact relational result. -/
theorem Eval.min_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_MIN] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (Min.min b a) :: stack) altStack := by
  have canonical : Eval [.op .OP_MIN] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (scriptNum (Min.min b a) :: stack) altStack) :=
    .min aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_MAX operands determine its exact relational result. -/
theorem Eval.max_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_MAX] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (scriptNum (Max.max b a) :: stack) altStack := by
  have canonical : Eval [.op .OP_MAX] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (scriptNum (Max.max b a) :: stack) altStack) :=
    .max aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_NUMNOTEQUAL operands determine its exact relational result. -/
theorem Eval.numNotEqual_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_NUMNOTEQUAL] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (decide (a ≠ b)) :: stack) altStack := by
  have canonical : Eval [.op .OP_NUMNOTEQUAL] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (boolToElement (decide (a ≠ b)) :: stack) altStack) :=
    .numNotEqual aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_LESSTHAN operands determine its exact relational result. -/
theorem Eval.lessThan_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_LESSTHAN] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (decide (b < a)) :: stack) altStack := by
  have canonical : Eval [.op .OP_LESSTHAN] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (boolToElement (decide (b < a)) :: stack) altStack) :=
    .lessThan aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_GREATERTHAN operands determine its exact relational result. -/
theorem Eval.greaterThan_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_GREATERTHAN] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (decide (b > a)) :: stack) altStack := by
  have canonical : Eval [.op .OP_GREATERTHAN] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (boolToElement (decide (b > a)) :: stack) altStack) :=
    .greaterThan aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_LESSTHANOREQUAL operands determine its exact relational result. -/
theorem Eval.lessThanOrEqual_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_LESSTHANOREQUAL] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (decide (b ≤ a)) :: stack) altStack := by
  have canonical : Eval [.op .OP_LESSTHANOREQUAL] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (boolToElement (decide (b ≤ a)) :: stack) altStack) :=
    .lessThanOrEqual aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Decoded OP_GREATERTHANOREQUAL operands determine its exact relational result. -/
theorem Eval.greaterThanOrEqual_result (aBytes bBytes : StackElement) (a b : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeBinaryScriptNums flags aBytes bBytes = .ok (a, b))
    (result : ExecResult) :
    Eval [.op .OP_GREATERTHANOREQUAL] (aBytes :: bBytes :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (decide (b ≥ a)) :: stack) altStack := by
  have canonical : Eval [.op .OP_GREATERTHANOREQUAL] (aBytes :: bBytes :: stack) altStack flags ctx
      (.success (boolToElement (decide (b ≥ a)) :: stack) altStack) :=
    .greaterThanOrEqual aBytes bBytes a b stack [] altStack flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Successful NOT decoding determines its exact relational result. -/
theorem Eval.not_result (operand : StackElement) (value : Int)
    (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .ok value) (result : ExecResult) :
    Eval [.op .OP_NOT] (operand :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (value == 0) :: stack) altStack := by
  have canonical : Eval [.op .OP_NOT] (operand :: stack) altStack flags ctx
      (.success (boolToElement (value == 0) :: stack) altStack) :=
    .op_not operand value stack altStack [] flags ctx _ decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Any relational execution after a NOT decoder error has that exact failure. -/
theorem Eval.notScriptNumFailure_result
    {operand : StackElement} {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {error : ScriptError} {result : ExecResult}
    (decoded : decodeScriptNum operand flags.minimalData maxArithmeticScriptNumBytes =
      .error error)
    (evaluated : Eval (.op .OP_NOT :: script) (operand :: stack) altStack flags ctx result) :
    result = .failure error :=
  evaluated.result_unique
    (.not_scriptnum_failure operand stack script altStack flags ctx error decoded)

/-- Decoded WITHIN operands determine the exact relational stack result. -/
theorem Eval.within_result (upperBytes lowerBytes valueBytes : StackElement)
    (upper lower value : Int) (stack altStack : Stack) (flags : ScriptFlags) (ctx : TxContext)
    (decoded : decodeWithinScriptNums flags upperBytes lowerBytes valueBytes = .ok (upper, lower, value))
    (result : ExecResult) :
    Eval [.op .OP_WITHIN] (upperBytes :: lowerBytes :: valueBytes :: stack) altStack flags ctx result ↔
      result = .success (boolToElement (decide (lower ≤ value ∧ value < upper)) :: stack) altStack := by
  have canonical : Eval [.op .OP_WITHIN] (upperBytes :: lowerBytes :: valueBytes :: stack)
      altStack flags ctx (.success (boolToElement (decide (lower ≤ value ∧ value < upper)) :: stack)
        altStack) :=
    .within upperBytes lowerBytes valueBytes upper lower value stack altStack [] flags ctx _
      decoded .done
  constructor
  · intro evaluated
    exact evaluated.result_unique canonical
  · intro equal
    subst result
    exact canonical

/-- Every relational execution after a WITHIN decoding error has that failure. -/
theorem Eval.withinScriptNumFailure_result
    {upperBytes lowerBytes valueBytes : StackElement} {stack altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {error : ScriptError} {result : ExecResult}
    (decoded : decodeWithinScriptNums flags upperBytes lowerBytes valueBytes = .error error)
    (evaluated : Eval (.op .OP_WITHIN :: script) (upperBytes :: lowerBytes :: valueBytes :: stack)
      altStack flags ctx result) :
    result = .failure error :=
  evaluated.result_unique
    (.within_scriptnum_failure upperBytes lowerBytes valueBytes stack script altStack flags ctx
      error decoded)

theorem Eval.pushDataNext
    {data : StackElement} {rest : Script} {stack altStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (next : Eval rest (data :: stack) altStack flags ctx result) :
    Eval (.pushData data :: rest) stack altStack flags ctx result :=
  .pushData data rest stack altStack flags ctx result next

theorem Eval.checksigTrue
    {pubkey sig : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .ok true)
    (next : Eval script (trueElement :: rest) altStack flags ctx result) :
    Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest) altStack flags ctx result :=
  .checksig_success pubkey sig rest script altStack flags ctx result checked next

theorem Eval.checksigFalse
    {pubkey sig : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    {result : ExecResult}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .ok false)
    (next : Eval script (falseElement :: rest) altStack flags ctx result) :
    Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest) altStack flags ctx result :=
  .checksig_failure pubkey sig rest script altStack flags ctx result checked next

/-- Rejected nonempty ECDSA signatures terminate at the checked boundary. -/
theorem Eval.checksigNullFail
    {pubkey sig : StackElement} {rest : Stack} {script : Script}
    {altStack : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (checked : checkSigWithEncoding checkSig checkSchnorrSig flags ctx sig pubkey = .error .sigNullFail) :
    Eval (.op .OP_CHECKSIG :: script) (pubkey :: sig :: rest) altStack flags ctx (.failure .sigNullFail) :=
  .checksig_encoding_failure pubkey sig rest script altStack flags ctx .sigNullFail checked

theorem Eval.verifyTrue
    {top : StackElement} {rest : Stack} {script : Script} {altStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (truthy : castToBool top = true)
    (next : Eval script rest altStack flags ctx result) :
    Eval (.op .OP_VERIFY :: script) (top :: rest) altStack flags ctx result :=
  .verify_success top rest script altStack flags ctx result truthy next

theorem Eval.verifyFalse
    {top : StackElement} {rest : Stack} {script : Script} {altStack : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (falsey : castToBool top = false) :
    Eval (.op .OP_VERIFY :: script) (top :: rest) altStack flags ctx
      (.failure .verify) :=
  .verify_failure top rest script altStack flags ctx falsey

theorem Eval.toAltStackNext
    {x : StackElement} {rest altStack : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (next : Eval script rest (x :: altStack) flags ctx result) :
    Eval (.op .OP_TOALTSTACK :: script) (x :: rest) altStack flags ctx result :=
  .toAltStack x rest altStack script flags ctx result next

theorem Eval.fromAltStackNext
    {x : StackElement} {stack altRest : Stack} {script : Script}
    {flags : ScriptFlags} {ctx : TxContext} {result : ExecResult}
    (next : Eval script (x :: stack) altRest flags ctx result) :
    Eval (.op .OP_FROMALTSTACK :: script) stack (x :: altRest) flags ctx result :=
  .fromAltStack x stack altRest script flags ctx result next

/-- A concrete non-minimal truthy IF argument fails when the active signature
    version requires MINIMALIF. -/
theorem nonMinimalTruthy_if_else_minimalif_failure
    (rest altStack : Stack) (thenBranch elseBranch after : Script)
    (flags : ScriptFlags) (ctx : TxContext)
    (nonMinimal : ¬ minimalIfSatisfied flags ctx.sigVersion
      nonMinimalTruthyElement) :
    Eval (.op .OP_IF ::
          (thenBranch ++ (.op .OP_ELSE ::
            elseBranch ++ .op .OP_ENDIF :: after)))
      (nonMinimalTruthyElement :: rest) altStack flags ctx
      (.failure (minimalIfError ctx.sigVersion)) := by
  exact Eval.if_minimalif_failure nonMinimalTruthyElement rest altStack
    (thenBranch ++ (.op .OP_ELSE :: elseBranch ++ .op .OP_ENDIF :: after))
    flags ctx nonMinimal

/-- When the active signature-version rules admit it, the same concrete
    non-minimal truthy IF argument selects the true branch. -/
theorem nonMinimalTruthy_if_else_relaxed_true
    (rest altStack : Stack) (script : Script) (frame : ConditionalFrame)
    (flags : ScriptFlags) (ctx : TxContext) (result : ExecResult)
    (minimal : minimalIfSatisfied flags ctx.sigVersion
      nonMinimalTruthyElement)
    (hSplit : splitConditional script = some frame)
    (hSelected : Eval (frame.select true) rest altStack flags ctx result) :
    Eval (.op .OP_IF :: script) (nonMinimalTruthyElement :: rest)
      altStack flags ctx result := by
  apply Eval.if_execute nonMinimalTruthyElement rest altStack script frame
    flags ctx result hSplit minimal
  simpa [nonMinimalTruthyElement_truthy] using hSelected

/-- Moving a stack element to the alt stack and immediately back preserves both
    stacks. -/
theorem toAltStack_fromAltStack_roundtrip
    (x : StackElement) (stack altStack : Stack)
    (flags : ScriptFlags) (ctx : TxContext) :
    Eval [.op .OP_TOALTSTACK, .op .OP_FROMALTSTACK]
      (x :: stack) altStack flags ctx (.success (x :: stack) altStack) := by
  exact Eval.toAltStack x stack altStack [.op .OP_FROMALTSTACK] flags ctx _
    (Eval.fromAltStack x stack altStack [] flags ctx _
      (Eval.empty (x :: stack) altStack flags ctx))

end LeanMiniscript.Script
