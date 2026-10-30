import LeanMiniscript.Extraction.EquivalenceObligations

/-!
Print the number of unproved equivalence obligations (`--list`: each one).
Fails when `equivalenceObligations` misses or repeats an opcode × version pair.
-/

open Lean
open LeanMiniscript.Script LeanMiniscript.Extraction

/-- `repr` of a nullary constructor is its full declaration name. -/
def ctorName {α : Type} [Repr α] (value : α) : Name :=
  (toString (repr value)).splitOn "." |>.foldl Name.mkStr .anonymous

def ctors (env : Environment) (type : Name) : IO (List Name) :=
  match env.find? type with
  | some (.inductInfo info) => pure info.ctors
  | _ => throw <| IO.userError s!"{type} is not an inductive type"

/-- `sorry` covers `sorryAx` and any other nonstandard axiom. -/
inductive Status where
  | proved | missing | sorry
  deriving BEq

def Status.label : Status → String
  | .proved => "proved"
  | .missing => "missing"
  | .sorry => "sorry"

def status (obligation : EquivalenceObligation) : CoreM Status := do
  let some info := (← getEnv).find? obligation.theoremName | return .missing
  let expected := mkApp2 (mkConst ``OpcodeAgreement)
    (mkConst (ctorName obligation.opcode)) (mkConst (ctorName obligation.version))
  unless info.type == expected do
    throwError "{obligation.theoremName} does not have type {expected}"
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  if (← collectAxioms obligation.theoremName).any (!standard.contains ·) then
    return .sorry
  return .proved

def main (args : List String) : IO UInt32 := do
  let list := args.contains "--list"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `LeanMiniscript.Extraction.EquivalenceObligations }] {}
  let opcodes ← ctors env ``Opcode
  let versions ← ctors env ``SignatureVersion
  let listed := equivalenceObligations.map fun obligation =>
    (ctorName obligation.opcode, ctorName obligation.version)
  let required := opcodes.flatMap fun opcode => versions.map fun version => (opcode, version)
  let missing := required.filter (!listed.contains ·)
  let repeated := required.filter fun pair => (listed.filter (· == pair)).length > 1
  unless missing.isEmpty && repeated.isEmpty do
    for (opcode, version) in missing do
      IO.eprintln s!"not listed: {opcode} {version}"
    for (opcode, version) in repeated do
      IO.eprintln s!"listed more than once: {opcode} {version}"
    return 1
  let (statuses, _) ← (equivalenceObligations.mapM fun obligation => do
      return (obligation, ← status obligation)).toIO
    { fileName := "equivalence_obligations", fileMap := default } { env }
  if list then
    for (obligation, result) in statuses do
      IO.println s!"{result.label} {ctorName obligation.opcode |>.getString!} \
        {ctorName obligation.version |>.getString!} {obligation.theoremName}"
  IO.println (statuses.filter (·.2 != .proved)).length
  return 0
