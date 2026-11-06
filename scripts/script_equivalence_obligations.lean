import LeanMiniscript.Extraction.ScriptEquivalenceObligations

/-!
Print the number of unproved script and VerifyScript equivalence obligations
(`--list`: each one). Fails when `scriptEquivalenceObligations` misses or
repeats a signature version or VerifyScript boundary, or when a theorem does
not have its obligation's type.
-/

open Lean
open LeanMiniscript.Script LeanMiniscript.Extraction

def ctors (env : Environment) (type : Name) : IO (List Name) :=
  match env.find? type with
  | some (.inductInfo info) => pure info.ctors
  | _ => throw <| IO.userError s!"{type} is not an inductive type"

/-- The agreement family and constructor that an obligation proposition
applies: `BaseExecutionAgreement := ScriptExecutionAgreement .base`. -/
def selector (env : Environment) (proposition : Name) : IO (Name × Name) := do
  let some (.defnInfo info) := env.find? proposition
    | throw <| IO.userError s!"{proposition} is not a definition"
  unless info.type == .sort .zero do
    throw <| IO.userError s!"{proposition} is not a Prop"
  match info.value with
  | .app (.const family []) (.const ctor []) =>
      if family == ``ScriptExecutionAgreement || family == ``VerifyScriptAgreement then
        pure (family, ctor)
      else throw <| IO.userError s!"{proposition} does not apply an agreement family"
  | _ => throw <| IO.userError s!"{proposition} does not apply an agreement family"

def familyLabel (family : Name) : String :=
  if family == ``ScriptExecutionAgreement then "execution" else "verification"

/-- `sorry` covers `sorryAx` and any other nonstandard axiom. -/
inductive Status where
  | proved | missing | sorry
  deriving BEq

def Status.label : Status → String
  | .proved => "proved"
  | .missing => "missing"
  | .sorry => "sorry"

def status (obligation : ScriptEquivalenceObligation) : CoreM Status := do
  let some info := (← getEnv).find? obligation.theoremName | return .missing
  let expected := mkConst obligation.proposition
  unless info.type == expected do
    throwError "{obligation.theoremName} does not have type {expected}"
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  if (← collectAxioms obligation.theoremName).any (!standard.contains ·) then
    return .sorry
  return .proved

def main (args : List String) : IO UInt32 := do
  let list := args.contains "--list"
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := `LeanMiniscript.Extraction.ScriptEquivalenceObligations }] {}
  let versions ← ctors env ``SignatureVersion
  let boundaries ← ctors env ``VerifyScriptBoundary
  let required := versions.map (``ScriptExecutionAgreement, ·) ++
    boundaries.map (``VerifyScriptAgreement, ·)
  let listed ← scriptEquivalenceObligations.mapM fun obligation =>
    selector env obligation.proposition
  let missing := required.filter (!listed.contains ·)
  let repeated := required.filter fun pair => (listed.filter (· == pair)).length > 1
  unless missing.isEmpty && repeated.isEmpty && listed.length == required.length do
    for (family, ctor) in missing do
      IO.eprintln s!"not listed: {familyLabel family} {ctor}"
    for (family, ctor) in repeated do
      IO.eprintln s!"listed more than once: {familyLabel family} {ctor}"
    return 1
  let (statuses, _) ← (scriptEquivalenceObligations.mapM fun obligation => do
      return (obligation, ← status obligation)).toIO
    { fileName := "script_equivalence_obligations", fileMap := default } { env }
  if list then
    for ((obligation, result), (family, ctor)) in statuses.zip listed do
      IO.println s!"{result.label} {familyLabel family} {ctor.getString!} \
        {obligation.theoremName}"
  IO.println (statuses.filter (·.2 != .proved)).length
  return 0
