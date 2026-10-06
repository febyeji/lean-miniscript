import LeanMiniscript.Miniscript.DescriptorParser

namespace LeanMiniscript.Miniscript.DescriptorErrorExamples

-- Published BIP380 test keys exercise secret-bearing errors, including tokens
-- appearing in the wrong syntactic role before key resolution is reached.
private def uncompressedWIF : String :=
  "5KYZdUEo39z3FPrtuX2QbbwGnNP5zTd7yyr2SC1j299sBCnWjss"

private def extendedPrivate : String :=
  "xprvA1RpRA33e1JQ7ifknakTFpgNXPmW2YvmhqLQYMmrj4xJXXWYpDPS3xz7iAxn8L39njGVyuoseXzU6rcxFLJ8HFsTjSyQbLYnMpCqE2VbFWc"

private def hides (message secret : String) : Bool :=
  (message.splitOn secret).length == 1

private def malformed (secret : String) : Array String := #[
  secret, secret ++ "(1)", secret ++ ":1", "1 " ++ secret,
  "older(" ++ secret ++ ")", "pk(" ++ secret ++ "/*)",
  "sha256(" ++ secret ++ ")", "pk(" ++ secret ++ "," ++ secret ++ ")",
  "pk(" ++ secret ++ ")" ++ secret, "(" ++ secret ++ ")"]

private def errorsHide (secret : String) : Bool :=
  (malformed secret).all (fun input =>
    match parseSurfaceDescriptor .p2wsh input with
    | .ok _ => false
    | .error error => hides (reprStr error) secret) &&
  (malformed secret).all (fun input =>
    match deriveOutputDescriptor ("wsh(" ++ input ++ ")") with
    | .ok _ => false
    | .error error => hides error secret)

example : errorsHide uncompressedWIF = true := by native_decide
example : errorsHide extendedPrivate = true := by native_decide

-- Preserve error category, token position and useful static diagnostics.
private def errorIs (input : String) (expected : SurfaceParseError) : Bool :=
  match parseSurfaceDescriptor .p2wsh input with
  | .ok _ => false
  | .error error => error == expected

example : errorIs ("pk(" ++ uncompressedWIF ++ ")")
    (.keyContext 3 "[redacted]" .p2wsh) = true := by native_decide

example : errorIs ("pk(" ++ extendedPrivate ++ "/*)")
    (.keyResolution 3 "[redacted]" "A wildcard key requires a child index") = true := by
  native_decide

example : errorIs ("older(" ++ extendedPrivate ++ ")")
    (.invalidNumber 6 "[redacted]") = true := by native_decide

example :
    (match deriveOutputDescriptor ("sh(wsh(pk(" ++ uncompressedWIF ++ ")))" ) with
    | .ok _ => false
    | .error error => hides error uncompressedWIF) = true := by native_decide

example :
    (match deriveOutputDescriptor
      ("tr(79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,pk(" ++
        extendedPrivate ++ "/*))") with
    | .ok _ => false
    | .error error => hides error extendedPrivate) = true := by native_decide

end LeanMiniscript.Miniscript.DescriptorErrorExamples
