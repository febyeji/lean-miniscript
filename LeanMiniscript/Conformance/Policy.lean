import LeanMiniscript.Policy.Text

namespace LeanMiniscript.Conformance.Policy

open LeanMiniscript.Miniscript
open LeanMiniscript.Policy

private def key : String :=
  "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"

private def digest : String :=
  "0000000000000000000000000000000000000000000000000000000000000000"

/-! Policy text is checked at the AST boundary. The compiler examples cover
the later policy-to-Miniscript translation separately. -/

example : (match parsePolicyHex s!"and(pk({key}),older(100))" with
    | .ok (.and (.key parsedKey) (.older 100)) =>
        match resolveHexKey key with
        | .ok expected => parsedKey.bytes == expected.bytes
        | .error _ => false
    | _ => false) = true := by
  native_decide

example : (match parsePolicyHex s!"or(99@pk({key}),1@sha256({digest}))" with
    | .ok (.or 99 (.key _) 1 (.sha256 hash)) =>
        hash.bytes == (SurfaceParser.decodeHex? digest).get!
    | _ => false) = true := by
  native_decide

example : (match parsePolicyHex s!"thresh(2,pk({key}),older(100),TRIVIAL)" with
    | .ok (.thresh 2 [(.key _), (.older 100), .trivial]) => true
    | _ => false) = true := by
  native_decide

end LeanMiniscript.Conformance.Policy
