import LeanMiniscript.Extraction.CoreFixtureWitnessData

namespace LeanMiniscript.Extraction

private def amount (source : String) : Option UInt64 :=
  ((Lean.Json.parse source).bind coreFixtureAmount).toOption

example : amount "0" = some 0 := by native_decide
example : amount "0.00000001" = some 1 := by native_decide
example : amount "1e-8" = some 1 := by native_decide
example : amount "0.0000000100" = some 1 := by native_decide
example : amount "0.12345678" = some 12345678 := by native_decide
example : amount "21000000" = some 2100000000000000 := by native_decide
example : amount "21000000.00000001" = none := by native_decide
example : amount "0.000000001" = none := by native_decide
example : amount "-0.00000001" = none := by native_decide
example : amount "1e-100000" = none := by native_decide

example : ((Lean.Json.parse "[\"00\",\"#SCRIPT# 1\",0.00000001]").bind
    (fun json => parseCoreFixtureWitnessSource (some json))).toOption.map
    (fun witness => (witness.elements, witness.amount)) =
    some (["00", "#SCRIPT# 1"], 1) := by native_decide

example : ((Lean.Json.parse "[]").bind
    (fun json => parseCoreFixtureWitnessSource (some json))).toOption.isNone = true := by
  native_decide

example : ((Lean.Json.parse "[7,0]").bind
    (fun json => parseCoreFixtureWitnessSource (some json))).toOption.isNone = true := by
  native_decide

end LeanMiniscript.Extraction
