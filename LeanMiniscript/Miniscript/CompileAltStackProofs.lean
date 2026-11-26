import LeanMiniscript.Miniscript.TypeSoundnessProofs.SuccessShapes

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# Alternate-stack independence of compiled Miniscript

Successful compiled execution preserves the incoming alternate stack and
permits replacing it without changing the main-stack result. The proof follows
the existing BIP 379 compilation relation, including threshold child lists and
optimized VERIFY. The guarantee applies to raw fragments.
-/

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

/-- Successful main-stack behavior is independent of the complete incoming
alternate stack; the final alternate stack is that same incoming stack. -/
def AltStackIndependent (script : Script) : Prop :=
  ∀ (input alt output outAlt : Stack) (flags : ScriptFlags) (ctx : TxContext),
    Eval script input alt flags ctx (.success output outAlt) →
    outAlt = alt ∧ ∀ replacement : Stack,
      Eval script input replacement flags ctx (.success output replacement)

private def AltFreeAtom (element : ScriptElement) : Prop :=
  NonConditional element ∧ element ≠ .op .OP_TOALTSTACK ∧ element ≠ .op .OP_FROMALTSTACK

private def branchOpcode (negative : Bool) : Opcode := if negative then .OP_NOTIF else .OP_IF

private theorem alt_nil : AltStackIndependent [] := by
  intro input alt output outAlt flags ctx run
  cases run
  exact ⟨rfl, fun _ => Eval.done⟩

private theorem alt_atom {element : ScriptElement} (safe : AltFreeAtom element) :
    AltStackIndependent [element] := by
  intro input alt output outAlt flags ctx run
  generalize resultEq : ExecResult.success output outAlt = result at run
  cases run <;> simp_all [AltFreeAtom, NonConditional] <;> try grind [Eval]
  case within =>
    rename_i upperBytes lowerBytes valueBytes upper lower value rest decoded final
    cases resultEq
    cases final
    exact ⟨rfl, fun replacement => by
      simpa using Eval.within upperBytes lowerBytes valueBytes upper lower value
        rest replacement [] flags ctx _ decoded Eval.done⟩

private theorem alt_append {left right : Script}
    (balanced : BalancedControlFlow left) (leftSafe : AltStackIndependent left)
    (rightSafe : AltStackIndependent right) :
    AltStackIndependent (left ++ right) := by
  intro input alt output outAlt flags ctx run
  obtain ⟨mid, midAlt, runL, runR⟩ := LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success balanced run
  obtain ⟨rfl, changeL⟩ := leftSafe _ _ _ _ _ _ runL
  obtain ⟨rfl, changeR⟩ := rightSafe _ _ _ _ _ _ runR
  exact ⟨rfl, fun replacement => Eval.append (changeL replacement) (changeR replacement)⟩

private theorem alt_conditional {script : Script} {frame : ConditionalFrame}
    (negative : Bool) (split : splitConditional script = some frame)
    (selectedSafe : ∀ chosen, AltStackIndependent (frame.select chosen)) :
    AltStackIndependent (.op (branchOpcode negative) :: script) := by
  intro input alt output outAlt flags ctx run
  cases negative
  · change Eval (.op .OP_IF :: script) _ _ _ _ _ at run
    generalize resultEq : ExecResult.success output outAlt = result at run
    cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
    case if_execute =>
      rename_i selector rest actual splitActual minimal selected
      cases resultEq
      rw [split] at splitActual
      cases splitActual
      obtain ⟨eq, transfer⟩ := selectedSafe (castToBool selector) _ _ _ _ _ _ selected
      exact ⟨eq, fun replacement => Eval.if_execute selector rest replacement script frame flags ctx _
        split minimal (transfer replacement)⟩
    case if_unbalanced =>
      rename_i selector rest selectedResult splitNone minimal selected
      rw [split] at splitNone
      contradiction
    all_goals cases resultEq
  · change Eval (.op .OP_NOTIF :: script) _ _ _ _ _ at run
    generalize resultEq : ExecResult.success output outAlt = result at run
    cases run <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
    case notif_execute =>
      rename_i selector rest actual splitActual minimal selected
      cases resultEq
      rw [split] at splitActual
      cases splitActual
      obtain ⟨eq, transfer⟩ := selectedSafe (!castToBool selector) _ _ _ _ _ _ selected
      exact ⟨eq, fun replacement => Eval.notif_execute selector rest replacement script frame flags ctx _
        split minimal (transfer replacement)⟩
    case notif_unbalanced =>
      rename_i selector rest selectedResult splitNone minimal selected
      rw [split] at splitNone
      contradiction
    all_goals cases resultEq

private theorem alt_single {body : Script} (negative : Bool)
    (balanced : BalancedControlFlow body) (safe : AltStackIndependent body) :
    AltStackIndependent ([.op (branchOpcode negative)] ++ body ++ [.op .OP_ENDIF]) := by
  apply alt_conditional negative
    (frame := { branches := [body], after := [] })
    (by simpa using splitConditional_balanced_ifThen balanced (suffix := []))
  intro chosen
  cases chosen
  · simpa [ConditionalFrame.select, selectConditionalBranches] using alt_nil
  · simpa [ConditionalFrame.select, selectConditionalBranches] using safe

private theorem alt_branch {left right : Script} (negative : Bool)
    (leftBalanced : BalancedControlFlow left) (rightBalanced : BalancedControlFlow right)
    (leftSafe : AltStackIndependent left) (rightSafe : AltStackIndependent right) :
    AltStackIndependent ([.op (branchOpcode negative)] ++ left ++ [.op .OP_ELSE] ++ right ++ [.op .OP_ENDIF]) := by
  apply alt_conditional negative
    (frame := { branches := [left, right], after := [] })
    (by simpa using splitConditional_balanced_ifElse leftBalanced rightBalanced (suffix := []))
  intro chosen
  cases chosen
  · simpa [ConditionalFrame.select, selectConditionalBranches] using rightSafe
  · simpa [ConditionalFrame.select, selectConditionalBranches] using leftSafe

private theorem alt_scope {body : Script} (balanced : BalancedControlFlow body) (safe : AltStackIndependent body) :
    AltStackIndependent ([.op .OP_TOALTSTACK] ++ body ++ [.op .OP_FROMALTSTACK]) := by
  intro input alt output outAlt flags ctx run
  have combined : Eval (.op .OP_TOALTSTACK :: (body ++ [.op .OP_FROMALTSTACK]))
      input alt flags ctx (.success output outAlt) := by simpa [List.append_assoc] using run
  generalize resultEq : ExecResult.success output outAlt = result at combined
  cases combined <;> try { simp_all only [Opcode.isUpgradeableNop, Bool.false_eq_true]; done }
  case toAltStack =>
    rename_i saved tail next
    cases resultEq
    obtain ⟨mid, midAlt, runBody, restore⟩ :=
      LeanMiniscript.Miniscript.Eval.splitBalancedAppend_success balanced next
    obtain ⟨rfl, transfer⟩ := safe _ _ _ _ _ _ runBody
    have canonical : Eval [.op .OP_FROMALTSTACK] mid (saved :: alt) flags ctx
        (.success (saved :: mid) alt) := Eval.fromAltStackNext Eval.done
    have eq := Eval.result_unique restore canonical
    cases eq
    refine ⟨rfl, fun replacement => ?_⟩
    apply Eval.toAltStackNext
    exact Eval.append (transfer (saved :: replacement)) (Eval.fromAltStackNext Eval.done)
  all_goals cases resultEq

private theorem alt_verify {body : Script} (balanced : BalancedControlFlow body) (safe : AltStackIndependent body) :
    AltStackIndependent (compileVerify body) := by
  intro input alt output outAlt flags ctx run
  have unfused := LeanMiniscript.Miniscript.Eval.compileVerify_success_inverse balanced run
  have verifySafe : AltStackIndependent [.op .OP_VERIFY] := alt_atom (by simp [AltFreeAtom, NonConditional])
  obtain ⟨eq, transfer⟩ := alt_append balanced safe verifySafe _ _ _ _ _ _ unfused
  exact ⟨eq, fun replacement => Eval.compileVerify_success balanced (transfer replacement)⟩

private theorem alt_atoms {script : Script}
    (safe : ∀ element ∈ script, AltFreeAtom element) : AltStackIndependent script := by
  induction script with
  | nil => exact alt_nil
  | cons element tail ih =>
    exact alt_append (.atom (safe element (by simp)).1)
      (alt_atom (safe element (by simp))) (ih (fun x h => safe x (by simp [h])))

private theorem alt_keyPushes (keys : List PubKey) : AltStackIndependent (compileKeyPushes keys) := by
  induction keys with
  | nil => exact alt_nil
  | cons key keys ih =>
    exact alt_append (.atom (by trivial)) (alt_atom (by simp [AltFreeAtom, NonConditional])) ih

private theorem keyPushes_balanced (keys : List PubKey) : BalancedControlFlow (compileKeyPushes keys) := by
  induction keys with
  | nil => exact .nil
  | cons key keys ih => exact .append (.atom (by trivial)) ih

private theorem alt_checkSigAddTail (keys : List PubKey) :
    AltStackIndependent (compileCheckSigAddTail keys) := by
  induction keys with
  | nil => exact alt_nil
  | cons key keys ih =>
    apply alt_append
      (BalancedControlFlow.ofAllNonConditional (by simp [AllNonConditional, NonConditional]))
      (alt_atoms (by simp [AltFreeAtom, NonConditional])) ih

private theorem alt_checkSigAdd (keys : List PubKey) : AltStackIndependent (compileCheckSigAdd keys) := by
  cases keys with
  | nil => exact alt_atom (by simp [AltFreeAtom, NonConditional])
  | cons key keys =>
    exact alt_append
      (BalancedControlFlow.ofAllNonConditional (by simp [AllNonConditional, NonConditional]))
      (alt_atoms (by simp [AltFreeAtom, NonConditional])) (alt_checkSigAddTail keys)

mutual

/-- Every conforming compiler derivation scopes its alternate-stack accesses.
The property includes successful-execution transfer, beyond preservation alone. -/
theorem Bip379Compilation.altStackIndependent
    {keyHash : PubKey → Hash160} {fragment : CoreFragment} {script : Script}
    (conforms : Bip379Compilation keyHash fragment script) : AltStackIndependent script := by
  cases conforms with
  | zero | one | pkK | pkH | older | after | sha256 | hash256 | ripemd160 | hash160 =>
      exact alt_atoms (by simp [AltFreeAtom, NonConditional])
  | andV x y => exact alt_append x.balancedControlFlow x.altStackIndependent y.altStackIndependent
  | andB x y =>
      exact alt_append (.append x.balancedControlFlow y.balancedControlFlow)
        (alt_append x.balancedControlFlow x.altStackIndependent y.altStackIndependent)
        (alt_atom (by simp [AltFreeAtom, NonConditional]))
  | orB x y =>
      exact alt_append (.append x.balancedControlFlow y.balancedControlFlow)
        (alt_append x.balancedControlFlow x.altStackIndependent y.altStackIndependent)
        (alt_atom (by simp [AltFreeAtom, NonConditional]))
  | orC x y =>
      simpa [branchOpcode, List.append_assoc] using alt_append x.balancedControlFlow
        x.altStackIndependent (alt_single true y.balancedControlFlow y.altStackIndependent)
  | orD x y =>
      have prefixSafe : AltStackIndependent [.op .OP_IFDUP] :=
        alt_atom (by simp [AltFreeAtom, NonConditional])
      simpa [branchOpcode, List.append_assoc] using alt_append x.balancedControlFlow
        x.altStackIndependent (alt_append (.atom (by trivial)) prefixSafe
          (alt_single true y.balancedControlFlow y.altStackIndependent))
  | orI x y =>
      exact alt_branch false x.balancedControlFlow y.balancedControlFlow
        x.altStackIndependent y.altStackIndependent
  | andor x y z =>
      simpa [branchOpcode, List.append_assoc] using alt_append x.balancedControlFlow
        x.altStackIndependent (alt_branch true z.balancedControlFlow y.balancedControlFlow
          z.altStackIndependent y.altStackIndependent)
  | a child => exact alt_scope child.balancedControlFlow child.altStackIndependent
  | s child =>
      exact alt_append (.atom (by trivial))
        (alt_atom (by simp [AltFreeAtom, NonConditional])) child.altStackIndependent
  | c child =>
      exact alt_append child.balancedControlFlow child.altStackIndependent
        (alt_atom (by simp [AltFreeAtom, NonConditional]))
  | v child verified =>
      rw [verified.eq_compileVerify]
      exact alt_verify child.balancedControlFlow child.altStackIndependent
  | d child =>
      have prefixSafe : AltStackIndependent [.op .OP_DUP] :=
        alt_atom (by simp [AltFreeAtom, NonConditional])
      simpa [branchOpcode, List.append_assoc] using alt_append (.atom (by trivial)) prefixSafe
        (alt_single false child.balancedControlFlow child.altStackIndependent)
  | j child =>
      have prefixSafe : AltStackIndependent [.op .OP_SIZE, .op .OP_0NOTEQUAL] :=
        alt_atoms (by simp [AltFreeAtom, NonConditional])
      simpa [branchOpcode, List.append_assoc] using alt_append
        (BalancedControlFlow.ofAllNonConditional (by simp [AllNonConditional, NonConditional])) prefixSafe
        (alt_single false child.balancedControlFlow child.altStackIndependent)
  | n child =>
      exact alt_append child.balancedControlFlow child.altStackIndependent
        (alt_atom (by simp [AltFreeAtom, NonConditional]))
  | thresh children =>
      exact alt_append children.balancedControlFlow children.altStackIndependent
        (alt_atoms (by simp [AltFreeAtom, NonConditional]))
  | @multi k keys keyScript keysConform =>
      rw [keysConform.eq_compileKeyPushes]
      have keyBalanced := keyPushes_balanced keys
      exact alt_append (.append (.atom (by trivial)) keyBalanced)
        (alt_append (.atom (by trivial))
          (alt_atom (by simp [AltFreeAtom, NonConditional])) (alt_keyPushes _))
        (alt_atoms (by simp [AltFreeAtom, NonConditional]))
  | multiA k keys =>
      rw [keys.eq_compileCheckSigAdd]
      exact alt_append (compileCheckSigAdd_balancedControlFlow _) (alt_checkSigAdd _)
        (alt_atoms (by simp [AltFreeAtom, NonConditional]))

/-- Threshold compilation sequences one first child with its arithmetic tail. -/
theorem Bip379ThreshCompilation.altStackIndependent
    {keyHash : PubKey → Hash160} {fragments : List CoreFragment} {script : Script}
    (conforms : Bip379ThreshCompilation keyHash fragments script) : AltStackIndependent script := by
  cases conforms with
  | nil => exact alt_nil
  | cons first tail =>
      exact alt_append first.balancedControlFlow first.altStackIndependent tail.altStackIndependent

/-- Each threshold-tail ADD operates only on the main stack. -/
theorem Bip379ThreshTailCompilation.altStackIndependent
    {keyHash : PubKey → Hash160} {fragments : List CoreFragment} {script : Script}
    (conforms : Bip379ThreshTailCompilation keyHash fragments script) : AltStackIndependent script := by
  cases conforms with
  | nil => exact alt_nil
  | cons first tail =>
      exact alt_append (.append first.balancedControlFlow (.atom (by trivial)))
        (alt_append first.balancedControlFlow first.altStackIndependent
          (alt_atom (by simp [AltFreeAtom, NonConditional])))
        tail.altStackIndependent

end

/-- Alternate-stack independence holds for every raw fragment and key-hash
resolver, including nested thresholds and optimized VERIFY wrappers. -/
theorem compileWithKeyHash_altStackIndependent (keyHash : PubKey → Hash160) (fragment : CoreFragment) :
    AltStackIndependent (compileWithKeyHash keyHash fragment) :=
  (compileWithKeyHash_conforms keyHash fragment).altStackIndependent

/-- The model compiler preserves and permits replacing any incoming alternate stack. -/
theorem compile_altStackIndependent (fragment : CoreFragment) : AltStackIndependent (compile fragment) :=
  compileWithKeyHash_altStackIndependent modelKeyHash fragment

/-- Transfer a successful compiled run to any alternate stack, preserving the
exact main-stack result, flags and transaction context. -/
theorem Eval.compile_replace_altStack {fragment : CoreFragment}
    {input alt output outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compile fragment) input alt flags ctx (.success output outAlt)) (replacement : Stack) :
    outAlt = alt ∧ Eval (compile fragment) input replacement flags ctx (.success output replacement) := by
  obtain ⟨preserved, transfer⟩ := compile_altStackIndependent fragment _ _ _ _ _ _ run
  exact ⟨preserved, transfer replacement⟩

/-- Remove an arbitrary preserved alternate-stack suffix from a successful run. -/
theorem Eval.compile_remove_altStack_suffix {fragment : CoreFragment}
    {input output own suffix : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compile fragment) input (own ++ suffix) flags ctx (.success output (own ++ suffix))) :
    Eval (compile fragment) input own flags ctx (.success output own) :=
  (Eval.compile_replace_altStack run own).2

/-- A compiled child can run with an empty alternate stack even when the
original run was surrounded by a wrapper's saved items. -/
theorem Eval.compile_erase_altStack {fragment : CoreFragment}
    {input alt output outAlt : Stack} {flags : ScriptFlags} {ctx : TxContext}
    (run : Eval (compile fragment) input alt flags ctx (.success output outAlt)) :
    Eval (compile fragment) input [] flags ctx (.success output []) :=
  (Eval.compile_replace_altStack run []).2

end LeanMiniscript.Miniscript
