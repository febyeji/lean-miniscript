import LeanMiniscript.Policy.Text

namespace LeanMiniscript.Policy

open LeanMiniscript.Miniscript

private def keyA : String := "02" ++ String.ofList (List.replicate 64 'a')
private def keyB : String := "03" ++ String.ofList (List.replicate 64 'b')
private def xOnlyKey : String := String.ofList (List.replicate 64 'c')
private def digest32 : String := String.ofList (List.replicate 64 'd')
private def digest20 : String := String.ofList (List.replicate 40 'e')

/-- Parse with hexadecimal keys and print back. -/
private def reprint (input : String) : Except SurfaceParseError String :=
  (parsePolicyHex input).map prettyPolicy

/-- Whether text parses and prints as `expected`. -/
private def reprintsAs (input expected : String) : Bool :=
  match reprint input with
  | .ok printed => printed == expected
  | .error _ => false

/-- Whether text is rejected with exactly `expected`. -/
private def rejectsWith (input : String) (expected : SurfaceParseError) : Bool :=
  match reprint input with
  | .ok _ => false
  | .error error => error == expected

/-! Canonical policy text is a fixed point of parse-then-print. -/

example : reprintsAs s!"pk({keyA})" s!"pk({keyA})" = true := by native_decide

example : reprintsAs s!"pk({xOnlyKey})" s!"pk({xOnlyKey})" = true := by native_decide

example : reprintsAs "UNSATISFIABLE" "UNSATISFIABLE" = true := by native_decide

example : reprintsAs "TRIVIAL" "TRIVIAL" = true := by native_decide

example :
    reprintsAs s!"and(pk({keyA}),or(99@pk({keyB}),older(12960)))"
      s!"and(pk({keyA}),or(99@pk({keyB}),older(12960)))" = true := by
  native_decide

example :
    reprintsAs s!"thresh(2,pk({keyA}),pk({keyB}),sha256({digest32}),after(100))"
      s!"thresh(2,pk({keyA}),pk({keyB}),sha256({digest32}),after(100))" = true := by
  native_decide

example :
    reprintsAs s!"or(hash256({digest32}),or(ripemd160({digest20}),hash160({digest20})))"
      s!"or(hash256({digest32}),or(ripemd160({digest20}),hash160({digest20})))" = true := by
  native_decide

/-- A weight on the right branch only, and on a leaf atom. -/
example :
    reprintsAs s!"or(pk({keyA}),3@UNSATISFIABLE)"
      s!"or(pk({keyA}),3@UNSATISFIABLE)" = true := by
  native_decide

/-! Spelling normalization: whitespace is dropped and the default weight `1@`
is omitted when printing. -/

example :
    reprintsAs s!"or( 1@pk({keyA}) , 1@pk({keyB}) )"
      s!"or(pk({keyA}),pk({keyB}))" = true := by
  native_decide

/-! Weights are recorded in the AST. -/

example :
    (match parsePolicyHex s!"or(99@pk({keyA}),pk({keyB}))" with
      | .ok (.or 99 (.key _) 1 (.key _)) => true
      | _ => false) = true := by
  native_decide

/-! Rejected text. -/

example :
    rejectsWith s!"and(pk({keyA}))"
      (.invalidArity 0 "and" "exactly 2 arguments" 1) = true := by
  native_decide

example :
    rejectsWith s!"or(x@pk({keyA}),pk({keyB}))"
      (.invalidNumber 3 "x") = true := by
  native_decide

/-- Weights are only meaningful on `or` branches. -/
example :
    rejectsWith s!"and(2@pk({keyA}),pk({keyB}))"
      (.unknownFragment 4 "2@pk") = true := by
  native_decide

/-- Miniscript wrappers are not policy syntax. -/
example : rejectsWith s!"v:pk({keyA})" (.unknownWrapper 0 "v") = true := by
  native_decide

example : rejectsWith s!"multi(1,{keyA})" (.unknownFragment 0 "multi") = true := by
  native_decide

example :
    rejectsWith s!"thresh(1)"
      (.invalidArity 0 "thresh" "a threshold and at least 1 item" 1) = true := by
  native_decide

example : rejectsWith s!"sha256({digest20})" (.invalidHashLength 7 "sha256" 32 20) = true := by
  native_decide

example : rejectsWith "" .emptyInput = true := by native_decide

end LeanMiniscript.Policy
