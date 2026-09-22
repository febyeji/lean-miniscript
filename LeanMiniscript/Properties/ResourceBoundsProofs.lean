import LeanMiniscript.Miniscript.CompileConcreteProofs
import LeanMiniscript.Miniscript.Sane
import LeanMiniscript.Properties.ResourceBounds
import LeanMiniscript.Script.RuntimeStackBounds

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

private inductive ElementSerializationShape where
  | op (opcode : Opcode)
  | pushData (size : Except SerializationError Nat)
  | pushNum (value : Int)

private def elementSerializationShape : ScriptElement → ElementSerializationShape
  | .op opcode => .op opcode
  | .pushData data => .pushData ((serializePushData data).map ByteArray.size)
  | .pushNum value => .pushNum value

private def elementShapeSize : ElementSerializationShape → Except SerializationError Nat
  | .op _ => .ok 1
  | .pushData size => size
  | .pushNum value => (serializePushNum value).map ByteArray.size

private def scriptSerializationShape (script : Script) : List ElementSerializationShape :=
  script.map elementSerializationShape

private def serializationShapeSize :
    List ElementSerializationShape → Except SerializationError Nat
  | [] => .ok 0
  | shape :: rest => do
      let elementSize ← elementShapeSize shape
      let restSize ← serializationShapeSize rest
      pure (elementSize + restSize)

private theorem serializeElement_size (element : ScriptElement) :
    (serializeElement element).map ByteArray.size =
      elementShapeSize (elementSerializationShape element) := by
  cases element <;> rfl

private theorem serializeScript_size (script : Script) :
    (serializeScript script).map ByteArray.size =
      serializationShapeSize (scriptSerializationShape script) := by
  induction script with
  | nil => rfl
  | cons element script ih =>
      simp only [serializeScript, scriptSerializationShape, List.map_cons,
        serializationShapeSize]
      cases serialized : serializeElement element with
      | error error =>
          have sizeError : elementShapeSize (elementSerializationShape element) =
              .error error := by
            rw [← serializeElement_size element, serialized]
            rfl
          rw [sizeError]
          rfl
      | ok bytes =>
          have sizeOk : elementShapeSize (elementSerializationShape element) =
              .ok bytes.size := by
            rw [← serializeElement_size element, serialized]
            rfl
          rw [sizeOk]
          cases restSerialized : serializeScript script with
          | error error =>
              have restError :
                  serializationShapeSize (scriptSerializationShape script) =
                    .error error := by
                rw [← ih, restSerialized]
                rfl
              change serializationShapeSize
                (List.map elementSerializationShape script) =
                  .error error at restError
              rw [restError]
              rfl
          | ok restBytes =>
              have restOk :
                  serializationShapeSize (scriptSerializationShape script) =
                    .ok restBytes.size := by
                rw [← ih, restSerialized]
                rfl
              change serializationShapeSize
                (List.map elementSerializationShape script) =
                  .ok restBytes.size at restOk
              rw [restOk]
              change Except.ok (bytes ++ restBytes).size =
                Except.ok (bytes.size + restBytes.size)
              rw [ByteArray.size_append]

private theorem serializedScriptSize_eq_shape (script : Script) :
    LeanMiniscript.Script.serializedScriptSize script =
      serializationShapeSize (scriptSerializationShape script) := by
  unfold LeanMiniscript.Script.serializedScriptSize
  exact serializeScript_size script

private def verifyShapeReplacement? :
    ElementSerializationShape → Option ElementSerializationShape
  | .op .OP_EQUAL => some (.op .OP_EQUALVERIFY)
  | .op .OP_CHECKSIG => some (.op .OP_CHECKSIGVERIFY)
  | .op .OP_CHECKMULTISIG => some (.op .OP_CHECKMULTISIGVERIFY)
  | .op .OP_NUMEQUAL => some (.op .OP_NUMEQUALVERIFY)
  | _ => none

private def compileVerifyShape
    (shapes : List ElementSerializationShape) : List ElementSerializationShape :=
  match shapes.reverse with
  | [] => [.op .OP_VERIFY]
  | last :: reversedPrefix =>
      match verifyShapeReplacement? last with
      | some replacement => (replacement :: reversedPrefix).reverse
      | none => (.op .OP_VERIFY :: last :: reversedPrefix).reverse

private theorem compileVerify_shape (script : Script) :
    scriptSerializationShape (compileVerify script) =
      compileVerifyShape (scriptSerializationShape script) := by
  simp only [scriptSerializationShape, compileVerify, compileVerifyShape]
  generalize reversedEq : script.reverse = reversed
  have mappedReverse :
      (List.map elementSerializationShape script).reverse =
        List.map elementSerializationShape reversed := by
    rw [← List.map_reverse, reversedEq]
  rw [mappedReverse]
  cases reversed with
  | nil => simp [elementSerializationShape]
  | cons last reversedPrefix =>
      cases last with
      | op opcode => cases opcode <;>
          simp [elementSerializationShape, verifyReplacement?,
            verifyShapeReplacement?, List.map_reverse]
      | pushData data =>
          simp [elementSerializationShape, verifyReplacement?,
            verifyShapeReplacement?, List.map_reverse]
      | pushNum value =>
          simp [elementSerializationShape, verifyReplacement?,
            verifyShapeReplacement?, List.map_reverse]

private theorem serializePushData_size_twenty (data : ByteArray)
    (size : data.size = 20) :
    (serializePushData data).map ByteArray.size = .ok 21 := by
  simp only [serializePushData, size]
  change
    (do
      let lengthPrefix ← pushDataPrefix data.size
      pure (⟨(lengthPrefix ++ data.data.toList).toArray⟩ : ByteArray)).map
        ByteArray.size = .ok 21
  simp only [pushDataPrefix, size, Nat.reduceLT, ↓reduceIte]
  change
    Except.ok (ByteArray.size
      (⟨([UInt8.ofNat 20] ++ data.data.toList).toArray⟩ : ByteArray)) =
      Except.ok 21
  congr 1
  simp only [ByteArray.size, List.size_toArray, List.length_append,
    List.length_singleton, Array.length_toList]
  have dataSize : data.data.size = 20 := size
  omega

mutual
  private theorem compileWithKeyHash_shape_eq
      (leftKeyHash rightKeyHash : PubKey → Hash160)
      (leftSize : ∀ key, (leftKeyHash key).size = 20)
      (rightSize : ∀ key, (rightKeyHash key).size = 20)
      (fragment : CoreFragment) :
      scriptSerializationShape (compileWithKeyHash leftKeyHash fragment) =
        scriptSerializationShape (compileWithKeyHash rightKeyHash fragment) := by
    cases fragment with
    | zero | one | pk_k | older | after | sha256 | hash256 | ripemd160 |
        hash160 | multi | multi_a => rfl
    | pk_h key =>
        simp only [compileWithKeyHash, scriptSerializationShape, List.map_cons,
          List.map_nil, elementSerializationShape]
        rw [serializePushData_size_twenty _ (leftSize key),
          serializePushData_size_twenty _ (rightSize key)]
    | and_v x y | and_b x y | or_b x y | or_c x y | or_d x y | or_i x y =>
        have xEq := compileWithKeyHash_shape_eq leftKeyHash rightKeyHash
          leftSize rightSize x
        have yEq := compileWithKeyHash_shape_eq leftKeyHash rightKeyHash
          leftSize rightSize y
        unfold scriptSerializationShape at xEq yEq
        simp only [compileWithKeyHash, scriptSerializationShape, List.map_append,
          List.map_cons, List.map_nil]
        rw [xEq, yEq]
    | andor x y z =>
        have xEq := compileWithKeyHash_shape_eq leftKeyHash rightKeyHash
          leftSize rightSize x
        have yEq := compileWithKeyHash_shape_eq leftKeyHash rightKeyHash
          leftSize rightSize y
        have zEq := compileWithKeyHash_shape_eq leftKeyHash rightKeyHash
          leftSize rightSize z
        unfold scriptSerializationShape at xEq yEq zEq
        simp only [compileWithKeyHash, scriptSerializationShape, List.map_append,
          List.map_cons, List.map_nil]
        rw [xEq, yEq, zEq]
    | a x | s x | c x | d x | j x | n x =>
        have xEq := compileWithKeyHash_shape_eq leftKeyHash rightKeyHash
          leftSize rightSize x
        unfold scriptSerializationShape at xEq
        simp only [compileWithKeyHash, scriptSerializationShape, List.map_append,
          List.map_cons, List.map_nil]
        rw [xEq]
    | v x =>
        simp only [compileWithKeyHash]
        rw [compileVerify_shape, compileVerify_shape,
          compileWithKeyHash_shape_eq leftKeyHash rightKeyHash leftSize rightSize x]
    | thresh k fragments =>
        have fragmentsEq := compileThreshWithKeyHash_shape_eq leftKeyHash
          rightKeyHash leftSize rightSize fragments
        unfold scriptSerializationShape at fragmentsEq
        simp only [compileWithKeyHash, scriptSerializationShape, List.map_append,
          List.map_cons, List.map_nil]
        rw [fragmentsEq]

  private theorem compileThreshWithKeyHash_shape_eq
      (leftKeyHash rightKeyHash : PubKey → Hash160)
      (leftSize : ∀ key, (leftKeyHash key).size = 20)
      (rightSize : ∀ key, (rightKeyHash key).size = 20)
      (fragments : List CoreFragment) :
      scriptSerializationShape
          (compileThreshWithKeyHash leftKeyHash fragments) =
        scriptSerializationShape
          (compileThreshWithKeyHash rightKeyHash fragments) := by
    cases fragments with
    | nil => rfl
    | cons fragment fragments =>
        have fragmentEq := compileWithKeyHash_shape_eq leftKeyHash rightKeyHash
          leftSize rightSize fragment
        have fragmentsEq := compileThreshTailWithKeyHash_shape_eq leftKeyHash
          rightKeyHash leftSize rightSize fragments
        unfold scriptSerializationShape at fragmentEq fragmentsEq
        simp only [compileThreshWithKeyHash, scriptSerializationShape,
          List.map_append]
        rw [fragmentEq, fragmentsEq]

  private theorem compileThreshTailWithKeyHash_shape_eq
      (leftKeyHash rightKeyHash : PubKey → Hash160)
      (leftSize : ∀ key, (leftKeyHash key).size = 20)
      (rightSize : ∀ key, (rightKeyHash key).size = 20)
      (fragments : List CoreFragment) :
      scriptSerializationShape
          (compileThreshTailWithKeyHash leftKeyHash fragments) =
        scriptSerializationShape
          (compileThreshTailWithKeyHash rightKeyHash fragments) := by
    cases fragments with
    | nil => rfl
    | cons fragment fragments =>
        have fragmentEq := compileWithKeyHash_shape_eq leftKeyHash rightKeyHash
          leftSize rightSize fragment
        have fragmentsEq := compileThreshTailWithKeyHash_shape_eq leftKeyHash
          rightKeyHash leftSize rightSize fragments
        unfold scriptSerializationShape at fragmentEq fragmentsEq
        simp only [compileThreshTailWithKeyHash, scriptSerializationShape,
          List.map_append, List.map_cons, List.map_nil]
        rw [fragmentEq, fragmentsEq]
end

/-- A 20-byte key-HASH160 resolver gives every compiled fragment the exact
    serialized size used by executable resource analysis. -/
theorem resourceSerializedScriptSize_eq_compileWithKeyHash
    (keyHash : PubKey → Hash160)
    (keyHashSize : ∀ key, (keyHash key).size = 20)
    (fragment : CoreFragment) :
    resourceSerializedScriptSize fragment =
      LeanMiniscript.Script.serializedScriptSize
        (compileWithKeyHash keyHash fragment) := by
  unfold resourceSerializedScriptSize compileForResourceAnalysis
  rw [serializedScriptSize_eq_shape, serializedScriptSize_eq_shape]
  apply congrArg serializationShapeSize
  apply compileWithKeyHash_shape_eq
  · intro key
    rfl
  · exact keyHashSize

/-- Concrete HASH160 compilation has the exact serialized size used by
    executable resource analysis. -/
theorem resourceSerializedScriptSize_eq_compileConcrete
    (fragment : CoreFragment) :
    resourceSerializedScriptSize fragment =
      LeanMiniscript.Script.serializedScriptSize
        (compileConcrete fragment) :=
  resourceSerializedScriptSize_eq_compileWithKeyHash concreteKeyHash
    concreteKeyHash_size fragment

end LeanMiniscript.Properties

namespace LeanMiniscript.Miniscript.SaneFragment

open LeanMiniscript.Properties
open LeanMiniscript.Script

/-- A sane fragment's resource certificate applies to the serialized output
    of the executable concrete compiler. -/
theorem compileConcrete_scriptSizeWithinLimit
    {ctx : ScriptContext} (sane : SaneFragment ctx) :
    ∃ size,
      LeanMiniscript.Script.serializedScriptSize
          (compileConcrete sane.checked.fragment) = .ok size ∧
        scriptSizeWithinContextLimit ctx size = true := by
  have resourceLimits := sane.withinResourceLimits
  unfold WithinResourceLimits resourceLimitsSatisfied at resourceLimits
  have compiledLimit :
      compiledScriptSizeWithinLimit ctx sane.checked.fragment = true :=
    (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp resourceLimits).1).1
  cases sizeResult : resourceSerializedScriptSize sane.checked.fragment with
  | error error =>
      simp [compiledScriptSizeWithinLimit, sizeResult] at compiledLimit
  | ok size =>
      refine ⟨size, ?_, ?_⟩
      · rw [← resourceSerializedScriptSize_eq_compileConcrete]
        exact sizeResult
      · simpa [compiledScriptSizeWithinLimit, sizeResult] using compiledLimit

end LeanMiniscript.Miniscript.SaneFragment

namespace LeanMiniscript.Properties

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

/-- Every successfully executed compiled core fragment satisfies the
    conservative combined-stack bound. The general Script theorem makes
    context validity and typing unnecessary for this particular bound. -/
theorem compile_stackGrowth
    {fragment : CoreFragment} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (evaluated : Eval (compile fragment) stack alt flags ctx (.success finalStack finalAlt)) :
    finalStack.length + finalAlt.length ≤
      stack.length + alt.length + scriptElementCount fragment :=
  evaluated.stackGrowth

/-- Discharge the existing resource contract without weakening its statement. -/
theorem resourceBoundsSound : ResourceBoundsSound := by
  intro ctx fragment ty stack alt finalStack finalAlt flags txCtx _ evaluated
  exact compile_stackGrowth evaluated

/-- Surface compilation inherits the core bound through desugaring. -/
theorem compileSurface_stackGrowth
    {fragment : SurfaceFragment} {stack alt finalStack finalAlt : Stack}
    {flags : ScriptFlags} {ctx : TxContext}
    (evaluated : Eval (compileSurface fragment) stack alt flags ctx
      (.success finalStack finalAlt)) :
    finalStack.length + finalAlt.length ≤
      stack.length + alt.length + scriptElementCount (desugar fragment) :=
  compile_stackGrowth evaluated

/-- The compiled instruction count also bounds every reachable intermediate
    combined stack, before runtime stack-size checks are applied. -/
theorem compile_prefix_stackBound
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {fragment : CoreFragment} {visited : Script} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix (compile fragment))
    (budget : before.stack.length + before.altStack.length + scriptElementCount fragment ≤ maxStackSize) :
    after.stack.length + after.altStack.length ≤ maxStackSize :=
  reached.stackBound agreement isPrefix budget

/-- Surface prefix bounds use the instruction count of the desugared core. -/
theorem compileSurface_prefix_stackBound
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {fragment : SurfaceFragment} {visited : Script} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix (compileSurface fragment))
    (budget : before.stack.length + before.altStack.length +
      scriptElementCount (desugar fragment) ≤ maxStackSize) :
    after.stack.length + after.altStack.length ≤ maxStackSize :=
  reached.stackBound agreement isPrefix budget

/-- The fragment-specific allowance is never weaker than the earlier compiled
    instruction-count allowance. -/
theorem maxStackGrowth_le_scriptElementCount (fragment : CoreFragment) :
    maxStackGrowth fragment ≤ scriptElementCount fragment :=
  stackGrowthAllowance_le_length (compile fragment)

/-- The static fragment allowance bounds every reachable compiled prefix. -/
theorem compile_prefix_maxStackGrowth
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {fragment : CoreFragment} {visited : Script} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix (compile fragment))
    (budget : before.stack.length + before.altStack.length +
      maxStackGrowth fragment ≤ maxStackSize) :
    after.stack.length + after.altStack.length ≤ maxStackSize :=
  reached.stackBoundAllowance agreement isPrefix budget

/-- Surface compilation inherits the fragment-specific allowance through
    desugaring. -/
theorem compileSurface_prefix_maxStackGrowth
    {oracle : CryptoOracle} (agreement : oracle.RefinesModel)
    {fragment : SurfaceFragment} {visited : Script} {before after : RuntimeState}
    {flags : ScriptFlags} {ctx : TxContext}
    (reached : RuntimePrefix oracle flags ctx visited before after)
    (isPrefix : visited.IsPrefix (compileSurface fragment))
    (budget : before.stack.length + before.altStack.length +
      maxStackGrowth (desugar fragment) ≤ maxStackSize) :
    after.stack.length + after.altStack.length ≤ maxStackSize :=
  reached.stackBoundAllowance agreement isPrefix budget

end LeanMiniscript.Properties
