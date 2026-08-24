import LeanMiniscript.Script.BigStep

namespace LeanMiniscript.Script

/-!
# BIP 65 and BIP 68/112 timelock fixtures

These examples exercise the Bitcoin Core v31.1 transaction-context conditions
modeled by `OP_CHECKLOCKTIMEVERIFY` and `OP_CHECKSEQUENCEVERIFY`. The operand
remains on the top-first stack after either opcode succeeds.
-/

private def timelockFlags : ScriptFlags := {}

private def timelockTx (version : Int) (locktime sequence : Nat) : TxContext where
  version := version
  locktime := locktime
  sequence := sequence
  sigHash := ⟨#[]⟩

/-! ## BIP 65: absolute locktime -/

/-- Height-based locktimes compare within the height class. -/
example : Eval [.op .OP_CHECKLOCKTIMEVERIFY] [scriptNum 100] []
    timelockFlags (timelockTx 2 200 0)
    (.success [scriptNum 100] []) := by
  apply Eval.checklocktimeverify_success (n := 100)
  · rfl
  · omega
  · native_decide
  · exact Eval.done

/-- The threshold itself is the first timestamp-based locktime. -/
example : Eval [.op .OP_CHECKLOCKTIMEVERIFY] [scriptNum 500000000] []
    timelockFlags (timelockTx 2 500000100 0)
    (.success [scriptNum 500000000] []) := by
  apply Eval.checklocktimeverify_success (n := 500000000)
  · rfl
  · omega
  · native_decide
  · exact Eval.done

/-- A height operand cannot be compared with a timestamp transaction. -/
example : Eval [.op .OP_CHECKLOCKTIMEVERIFY] [scriptNum 499999999] []
    timelockFlags (timelockTx 2 500000000 0)
    (.failure .checkLockTimeVerify) := by
  apply Eval.checklocktimeverify_failure (n := 499999999)
  · rfl
  · omega
  · native_decide

/-- A timestamp operand cannot be compared with a height transaction. -/
example : Eval [.op .OP_CHECKLOCKTIMEVERIFY] [scriptNum 500000000] []
    timelockFlags (timelockTx 2 499999999 0)
    (.failure .checkLockTimeVerify) := by
  apply Eval.checklocktimeverify_failure (n := 500000000)
  · rfl
  · omega
  · native_decide

/-- Matching classes still require the transaction locktime to be adequate. -/
example : Eval [.op .OP_CHECKLOCKTIMEVERIFY] [scriptNum 201] []
    timelockFlags (timelockTx 2 200 0)
    (.failure .checkLockTimeVerify) := by
  apply Eval.checklocktimeverify_failure (n := 201)
  · rfl
  · omega
  · native_decide

/-- A final current-input sequence disables CLTV even when the value matches. -/
example : Eval [.op .OP_CHECKLOCKTIMEVERIFY] [scriptNum 100] []
    timelockFlags (timelockTx 2 200 sequenceFinal)
    (.failure .checkLockTimeVerify) := by
  apply Eval.checklocktimeverify_failure (n := 100)
  · rfl
  · omega
  · native_decide

/-! ## BIP 68/112: relative locktime -/

/-- An operand disable bit makes CSV a NOP before version or input checks. -/
example : Eval [.op .OP_CHECKSEQUENCEVERIFY]
    [scriptNum sequenceLocktimeDisableFlag] []
    timelockFlags (timelockTx 1 0 sequenceFinal)
    (.success [scriptNum sequenceLocktimeDisableFlag] []) := by
  apply Eval.checksequenceverify_success (n := sequenceLocktimeDisableFlag)
  · rfl
  · omega
  · native_decide
  · exact Eval.done

/-- Active height-based relative locktimes compare their low 16 bits. -/
example : Eval [.op .OP_CHECKSEQUENCEVERIFY] [scriptNum 9] []
    timelockFlags (timelockTx 2 0 10)
    (.success [scriptNum 9] []) := by
  apply Eval.checksequenceverify_success (n := 9)
  · rfl
  · omega
  · native_decide
  · exact Eval.done

/-- Equal type bits permit time-based relative-locktime comparison. -/
example : Eval [.op .OP_CHECKSEQUENCEVERIFY]
    [scriptNum (sequenceLocktimeTypeFlag + 9)] []
    timelockFlags (timelockTx 2 0 (sequenceLocktimeTypeFlag + 10))
    (.success [scriptNum (sequenceLocktimeTypeFlag + 9)] []) := by
  apply Eval.checksequenceverify_success (n := sequenceLocktimeTypeFlag + 9)
  · rfl
  · omega
  · native_decide
  · exact Eval.done

/-- An active CSV operand requires transaction version 2 or later. -/
example : Eval [.op .OP_CHECKSEQUENCEVERIFY] [scriptNum 9] []
    timelockFlags (timelockTx 1 0 10)
    (.failure .checkSequenceVerify) := by
  apply Eval.checksequenceverify_failure (n := 9)
  · rfl
  · omega
  · native_decide

/-- The current input cannot disable BIP 68 relative-locktime semantics. -/
example : Eval [.op .OP_CHECKSEQUENCEVERIFY] [scriptNum 9] []
    timelockFlags
      (timelockTx 2 0 (sequenceLocktimeDisableFlag + 10))
    (.failure .checkSequenceVerify) := by
  apply Eval.checksequenceverify_failure (n := 9)
  · rfl
  · omega
  · native_decide

/-- Height and time relative-locktime types cannot be mixed. -/
example : Eval [.op .OP_CHECKSEQUENCEVERIFY]
    [scriptNum (sequenceLocktimeTypeFlag + 1)] []
    timelockFlags (timelockTx 2 0 10)
    (.failure .checkSequenceVerify) := by
  apply Eval.checksequenceverify_failure (n := sequenceLocktimeTypeFlag + 1)
  · rfl
  · omega
  · native_decide

/-- Matching types still require an adequate masked relative-locktime value. -/
example : Eval [.op .OP_CHECKSEQUENCEVERIFY] [scriptNum 11] []
    timelockFlags (timelockTx 2 0 10)
    (.failure .checkSequenceVerify) := by
  apply Eval.checksequenceverify_failure (n := 11)
  · rfl
  · omega
  · native_decide

/-- Bits outside the type flag and low 16-bit value mask are ignored. -/
example : Eval [.op .OP_CHECKSEQUENCEVERIFY] [scriptNum 65546] []
    timelockFlags (timelockTx 2 0 131082)
    (.success [scriptNum 65546] []) := by
  apply Eval.checksequenceverify_success (n := 65546)
  · rfl
  · omega
  · native_decide
  · exact Eval.done

/-! ## Local result uniqueness -/

/-- A context-invalid CLTV execution cannot also return a successful stack. -/
example : ¬ ∃ main alt,
    Eval [.op .OP_CHECKLOCKTIMEVERIFY] [scriptNum 100] []
      timelockFlags (timelockTx 2 200 sequenceFinal) (.success main alt) := by
  rintro ⟨main, alt, evaluated⟩
  have impossible := Eval.checkLockTimeVerifyFailure_result
    (value := 100) (decoded := by rfl) (nonnegative := by omega)
    (unsatisfied := by native_decide) evaluated
  cases impossible

/-- A context-invalid CSV execution cannot also return a successful stack. -/
example : ¬ ∃ main alt,
    Eval [.op .OP_CHECKSEQUENCEVERIFY] [scriptNum 9] []
      timelockFlags (timelockTx 1 0 10) (.success main alt) := by
  rintro ⟨main, alt, evaluated⟩
  have impossible := Eval.checkSequenceVerifyFailure_result
    (value := 9) (decoded := by rfl) (nonnegative := by omega)
    (unsatisfied := by native_decide) evaluated
  cases impossible

end LeanMiniscript.Script
