import LeanMiniscript.Script.Syntax

namespace LeanMiniscript.Script

/-!
Conditional selection for the modeled opcode subset. The reference is Bitcoin
Core v31.1, commit 9be056a8a72b624dae9623b2f7bded92c2a21c91,
`src/script/interpreter.cpp` (IF/NOTIF, ELSE, ENDIF and final condition-stack
check). Op-count and push-size checks on skipped instructions are not modeled.
-/

/-- The selected instructions, continuation, and whether a matching ENDIF was
    found. An unfinished block retains selected instructions so execution errors
    before end-of-script take precedence over the missing ENDIF. -/
structure ConditionalBlock where
  selected : Script
  after : Script
  closed : Bool
  deriving Repr

private def ConditionalBlock.prepend (element : ScriptElement) (active : Bool)
    (block : ConditionalBlock) : ConditionalBlock :=
  if active then { block with selected := element :: block.selected } else block

/-- Scan the tail of an IF/NOTIF. Only depth-zero ELSE toggles selection and only
    depth-zero ENDIF closes this block. Nested delimiters remain in selected
    code; skipped code contributes no stack operations. Repeated ELSE toggles
    are supported, as in Script, even though Miniscript does not emit them. -/
def scanConditional : Nat → Bool → Script → ConditionalBlock
  | _, _, [] => ⟨[], [], false⟩
  | depth, active, element :: rest =>
    match element with
    | .op .OP_IF | .op .OP_NOTIF =>
        (scanConditional (depth + 1) active rest).prepend element active
    | .op .OP_ELSE =>
        match depth with
        | 0 => scanConditional 0 (!active) rest
        | _ + 1 => (scanConditional depth active rest).prepend element active
    | .op .OP_ENDIF =>
        match depth with
        | 0 => ⟨[], rest, true⟩
        | n + 1 => (scanConditional n active rest).prepend element active
    | _ => (scanConditional depth active rest).prepend element active

/-- Select a conditional's branch from the already checked IF/NOTIF argument. -/
def splitConditional (active : Bool) (script : Script) : ConditionalBlock :=
  scanConditional 0 active script

/-- A fixed input has exactly one block decomposition. -/
theorem splitConditional_unique {active : Bool} {script : Script}
    {first second : ConditionalBlock}
    (hfirst : splitConditional active script = first)
    (hsecond : splitConditional active script = second) : first = second :=
  hfirst.symm.trans hsecond

/-- Appending code after a closed block only extends its continuation. -/
theorem scanConditional_append (script suffix : Script) (depth : Nat) (active : Bool)
    (closed : (scanConditional depth active script).closed = true) :
    scanConditional depth active (script ++ suffix) =
      { scanConditional depth active script with
        after := (scanConditional depth active script).after ++ suffix } := by
  induction script generalizing depth active with
  | nil => simp [scanConditional] at closed
  | cons element rest ih =>
    cases element with
    | pushData data =>
      cases active <;> simp_all [scanConditional, ConditionalBlock.prepend]
    | pushNum value =>
      cases active <;> simp_all [scanConditional, ConditionalBlock.prepend]
    | op opcode =>
      cases opcode <;> cases depth <;> cases active <;>
        simp_all [scanConditional, ConditionalBlock.prepend]

end LeanMiniscript.Script
