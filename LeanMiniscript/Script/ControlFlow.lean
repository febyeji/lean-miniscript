import LeanMiniscript.Script.Syntax

namespace LeanMiniscript.Script

/-!
# Script structural properties

The Miniscript compiler emits a closed opcode type and nests every `IF` or
`NOTIF` with the matching `ELSE`/`ENDIF` delimiters. These definitions state
those two guarantees without assigning execution semantics to the script.
-/

/-- The complete opcode universe represented by this model. -/
def modeledOpcodes : List Opcode :=
  [.OP_IF, .OP_NOTIF, .OP_ELSE, .OP_ENDIF,
   .OP_IFDUP, .OP_DUP, .OP_SWAP, .OP_TOALTSTACK, .OP_FROMALTSTACK,
   .OP_ADD, .OP_BOOLAND, .OP_BOOLOR, .OP_0NOTEQUAL,
   .OP_EQUAL, .OP_EQUALVERIFY, .OP_NUMEQUAL,
   .OP_SHA256, .OP_HASH256, .OP_RIPEMD160, .OP_HASH160,
   .OP_CHECKSIG, .OP_CHECKSIGADD, .OP_CHECKMULTISIG,
   .OP_CHECKSEQUENCEVERIFY, .OP_CHECKLOCKTIMEVERIFY,
   .OP_VERIFY, .OP_SIZE]

/-- `Opcode` is deliberately closed over exactly the opcodes modeled here. -/
theorem Opcode.mem_modeledOpcodes (opcode : Opcode) : opcode ∈ modeledOpcodes := by
  cases opcode <;> simp [modeledOpcodes]

/-- Every opcode embedded in a script belongs to the model's closed universe. -/
def UsesOnlyModeledOpcodes (script : Script) : Prop :=
  ∀ opcode, ScriptElement.op opcode ∈ script → opcode ∈ modeledOpcodes

/-- Opcode closure follows at the type boundary, so it holds for every `Script`,
not only compiler output. -/
theorem usesOnlyModeledOpcodes (script : Script) : UsesOnlyModeledOpcodes script := by
  intro opcode _
  exact opcode.mem_modeledOpcodes

/-- An element that is not one of Script's conditional delimiters. -/
def NonConditional : ScriptElement → Prop
  | .op .OP_IF => False
  | .op .OP_NOTIF => False
  | .op .OP_ELSE => False
  | .op .OP_ENDIF => False
  | _ => True

/-- Every element in a script is non-conditional. This recursive form keeps
proofs independent of equality instances for pushed byte arrays. -/
def AllNonConditional : Script → Prop
  | [] => True
  | element :: script => NonConditional element ∧ AllNonConditional script

/-- A structural grammar for correctly nested Script conditionals.

It accepts concatenation of balanced scripts and the four conditional shapes
used by Miniscript: `IF`/`NOTIF`, each with or without an `ELSE` branch.
-/
inductive BalancedControlFlow : Script → Prop where
  | nil : BalancedControlFlow []
  | atom {element : ScriptElement} (nonConditional : NonConditional element) :
      BalancedControlFlow [element]
  | append {left right : Script}
      (leftBalanced : BalancedControlFlow left)
      (rightBalanced : BalancedControlFlow right) :
      BalancedControlFlow (left ++ right)
  | ifThen {body : Script} (bodyBalanced : BalancedControlFlow body) :
      BalancedControlFlow ([.op .OP_IF] ++ body ++ [.op .OP_ENDIF])
  | notifThen {body : Script} (bodyBalanced : BalancedControlFlow body) :
      BalancedControlFlow ([.op .OP_NOTIF] ++ body ++ [.op .OP_ENDIF])
  | ifElse {thenBranch elseBranch : Script}
      (thenBalanced : BalancedControlFlow thenBranch)
      (elseBalanced : BalancedControlFlow elseBranch) :
      BalancedControlFlow
        ([.op .OP_IF] ++ thenBranch ++ [.op .OP_ELSE] ++
          elseBranch ++ [.op .OP_ENDIF])
  | notifElse {thenBranch elseBranch : Script}
      (thenBalanced : BalancedControlFlow thenBranch)
      (elseBalanced : BalancedControlFlow elseBranch) :
      BalancedControlFlow
        ([.op .OP_NOTIF] ++ thenBranch ++ [.op .OP_ELSE] ++
          elseBranch ++ [.op .OP_ENDIF])

/-- A list containing no conditional delimiters is balanced. -/
theorem BalancedControlFlow.ofAllNonConditional
    {script : Script} (allNonConditional : AllNonConditional script) :
    BalancedControlFlow script := by
  induction script with
  | nil => exact .nil
  | cons head tail tailBalanced =>
      have headBalanced : BalancedControlFlow [head] :=
        .atom allNonConditional.1
      have tailBalanced' : BalancedControlFlow tail :=
        tailBalanced allNonConditional.2
      simpa using BalancedControlFlow.append headBalanced tailBalanced'

end LeanMiniscript.Script
