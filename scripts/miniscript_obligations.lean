import LeanMiniscript.Extraction.MiniscriptObligations

/-!
Print the number of unproved Miniscript compilation obligations (`--list`:
each one). Fails when `miniscriptObligations` misses or repeats a property and
script context pair, or when a theorem does not have its obligation's type.
-/

open Lean
open LeanMiniscript.Miniscript LeanMiniscript.Extraction

def ctors (env : Environment) (type : Name) : IO (List Name) :=
  match env.find? type with
  | some (.inductInfo info) => pure info.ctors
  | _ => throw <| IO.userError s!"{type} is not an inductive type"

/-- The property families and their `--list` labels. -/
def properties : List (Name × String) := [
  (``CompiledSatisfaction, "satisfaction"),
  (``CompiledDissatisfaction, "dissatisfaction"),
  (``CompiledNonMalleability, "non-malleability"),
  (``CompiledResourceLimits, "resource-limits")
]

def propertyLabel (family : Name) : String :=
  (properties.lookup family).getD family.toString

/-- The property family and script context that an obligation proposition
applies: `P2WSHSatisfaction := CompiledSatisfaction .p2wsh`. -/
def selector (env : Environment) (proposition : Name) : IO (Name × Name) := do
  let some (.defnInfo info) := env.find? proposition
    | throw <| IO.userError s!"{proposition} is not a definition"
  unless info.type == .sort .zero do
    throw <| IO.userError s!"{proposition} is not a Prop"
  match info.value with
  | .app (.const family []) (.const ctor []) =>
      if (properties.lookup family).isSome then pure (family, ctor)
      else throw <| IO.userError s!"{proposition} does not apply a property family"
  | _ => throw <| IO.userError s!"{proposition} does not apply a property family"

/-- `sorry` covers `sorryAx` and any other nonstandard axiom. -/
inductive Status where
  | proved | missing | sorry
  deriving BEq

def Status.label : Status → String
  | .proved => "proved"
  | .missing => "missing"
  | .sorry => "sorry"

def status (obligation : MiniscriptObligation) : CoreM Status := do
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
  let env ← importModules #[{ module := `LeanMiniscript.Extraction.MiniscriptObligations }] {}
  let contexts ← ctors env ``ScriptContext
  let required := properties.flatMap fun (family, _) => contexts.map (family, ·)
  let listed ← miniscriptObligations.mapM fun obligation =>
    selector env obligation.proposition
  let missing := required.filter (!listed.contains ·)
  let repeated := required.filter fun pair => (listed.filter (· == pair)).length > 1
  unless missing.isEmpty && repeated.isEmpty && listed.length == required.length do
    for (family, ctor) in missing do
      IO.eprintln s!"not listed: {propertyLabel family} {ctor.getString!}"
    for (family, ctor) in repeated do
      IO.eprintln s!"listed more than once: {propertyLabel family} {ctor.getString!}"
    return 1
  let (statuses, _) ← (miniscriptObligations.mapM fun obligation => do
      return (obligation, ← status obligation)).toIO
    { fileName := "miniscript_obligations", fileMap := default } { env }
  if list then
    for ((obligation, result), (family, ctor)) in statuses.zip listed do
      IO.println s!"{result.label} {propertyLabel family} {ctor.getString!} \
        {obligation.theoremName}"
  IO.println (statuses.filter (·.2 != .proved)).length
  return 0
