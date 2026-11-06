import LeanMiniscript.Extraction.CoreLoopFallbacks
import LeanMiniscript.Extraction.ScriptEquivalenceObligations

/-!
Print how many kinds in `coreLoopFallbacks` have a representative script that
`executeTypedScript` runs on Core's raw loop (`--list`: each kind as typed or
fallback instead). Fails when the list misses an opcode byte whose
one-instruction script runs there or a push kind, lists a kind twice, or has a
representative of another kind, and when one of the nine script equivalence
obligations lacks a proof.
-/

open Lean
open LeanMiniscript.Script LeanMiniscript.Extraction

def hex (bytes : ByteArray) : String :=
  String.join <| bytes.toList.map fun byte =>
    let digits := Nat.toDigits 16 byte.toNat
    String.ofList (if digits.length < 2 then '0' :: digits else digits)

def kindLabel : CoreLoopFallbackKind → String
  | .opcode byte => s!"opcode 0x{hex ⟨#[byte]⟩}"
  | .truncatedPush => "truncated push"
  | .nonminimalPush => "nonminimal push"

def ctors (env : Environment) (type : Name) : IO (List Name) :=
  match env.find? type with
  | some (.inductInfo info) => pure info.ctors
  | _ => throw <| IO.userError s!"{type} is not an inductive type"

/-- The agreement family and constructor that an obligation proposition
applies: `BaseExecutionAgreement := ScriptExecutionAgreement .base`. -/
def selector (env : Environment) (proposition : Name) : Option (Name × Name) := do
  let .defnInfo info ← env.find? proposition | none
  unless info.type == .sort .zero do none
  let .app (.const family []) (.const ctor []) := info.value | none
  unless family == ``ScriptExecutionAgreement || family == ``VerifyScriptAgreement do none
  return (family, ctor)

/-- Why an obligation is unproved: it is not an agreement obligation, or its
theorem is missing, has another type, or rests on `sorry` or another
nonstandard axiom. -/
def obligationProblem (obligation : ScriptEquivalenceObligation) :
    CoreM (Option String) := do
  let env ← getEnv
  unless (selector env obligation.proposition).isSome do
    return some s!"not an agreement obligation: {obligation.proposition}"
  let some info := env.find? obligation.theoremName
    | return some s!"missing {obligation.theoremName}"
  unless info.type == mkConst obligation.proposition do
    return some s!"{obligation.theoremName} does not have type {obligation.proposition}"
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  if (← collectAxioms obligation.theoremName).any (!standard.contains ·) then
    return some s!"sorry {obligation.theoremName}"
  return none

/-- Why the nine script equivalence obligations are not all proved: the list
misses or repeats a signature version or VerifyScript boundary, or an
obligation has a problem. -/
def unprovedObligations (env : Environment) : IO (List String) := do
  let versions ← ctors env ``SignatureVersion
  let boundaries ← ctors env ``VerifyScriptBoundary
  let required : List (Name × Name) := versions.map (``ScriptExecutionAgreement, ·) ++
    boundaries.map (``VerifyScriptAgreement, ·)
  let listed := scriptEquivalenceObligations.filterMap (selector env ·.proposition)
  let (problems, _) ← (scriptEquivalenceObligations.filterMapM obligationProblem).toIO
    { fileName := "core_loop_fallbacks", fileMap := default } { env }
  let missing := required.filter (!listed.contains ·)
  let repeated := required.filter fun pair => (listed.filter (· == pair)).length > 1
  return missing.map (fun (_, ctor) => s!"obligation not listed: {ctor}") ++
    repeated.map (fun (_, ctor) => s!"obligation listed more than once: {ctor}") ++ problems

def main (args : List String) : IO UInt32 := do
  let list := args.contains "--list"
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := `LeanMiniscript.Extraction.ScriptEquivalenceObligations }] {}
  let kinds := coreLoopFallbacks.map (·.kind)
  let fallbackBytes := (List.range 256).map Nat.toUInt8 |>.filter fun byte =>
    runsOnCoreLoop (oneInstructionScript byte)
  let required := fallbackBytes.map .opcode ++ [.truncatedPush, .nonminimalPush]
  let errors :=
    (required.filter (!kinds.contains ·)).map (s!"not listed: {kindLabel ·}") ++
    (kinds.eraseDups.filter fun kind => (kinds.filter (· == kind)).length > 1).map
      (s!"listed more than once: {kindLabel ·}") ++
    (coreLoopFallbacks.filter (!·.hasKind)).map fun fallback =>
      s!"representative of another kind: {kindLabel fallback.kind} {hex fallback.bytes}"
  let errors := errors ++ (← unprovedObligations env)
  unless errors.isEmpty do
    errors.forM fun error => IO.eprintln error
    return 1
  if list then
    for fallback in coreLoopFallbacks do
      let status := if runsOnCoreLoop fallback.bytes then "fallback" else "typed"
      IO.println s!"{status} {hex fallback.bytes} {fallback.name}"
  else
    IO.println (coreLoopFallbacks.filter (runsOnCoreLoop ·.bytes)).length
  return 0
