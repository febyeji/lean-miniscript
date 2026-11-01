import LeanMiniscript.Policy.Cli

namespace LeanMiniscript.Policy.Cli

open LeanMiniscript.Script

private def x : String := "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
private def key : String := "02" ++ x

example : (parseArgs ["--", "compile", "--context", "tapscript", s!"pk({key})"]).toOption =
    some (.compile .tapscript s!"pk({key})") := by native_decide

example : (parseArgs ["compile", s!"pk({key})"]).toOption =
    some (.compile .p2wsh s!"pk({key})") := by native_decide

example : (parseArgs [s!"pk({key})"]).toOption = some (.parse s!"pk({key})") := by native_decide

example : (parseArgs ["parse", s!"pk({key})"]).toOption = some (.parse s!"pk({key})") := by native_decide

example : (parseArgs ["--", "--help"]).toOption = some .help := by native_decide

example : (parseArgs ["compile", "--context", "legacy", s!"pk({key})"]).toBool = false := by
  native_decide

example : (parseArgs ["compile"]).toBool = false := by native_decide

example : (parseArgs ["compile", "--context", "tapscript"]).toBool = false := by native_decide

/-- The same compressed key produces a 33-byte push in P2WSH and an x-only
32-byte push in Tapscript, followed by CHECKSIG. -/
example : (match compileReport .p2wsh s!"pk({key})" with
    | .ok report => report.miniscript == s!"pk({key})" &&
        byteArrayHex report.script == "21" ++ key ++ "ac" && report.script.size == 35 &&
        report.resources.staticOps == 1 && report.resources.satisfactionInitialStack == some 1
    | .error _ => false) = true := by native_decide

example : (match compileReport .tapscript s!"pk({key})" with
    | .ok report => report.miniscript == s!"pk({x})" &&
        byteArrayHex report.script == "20" ++ x ++ "ac" && report.script.size == 34
    | .error _ => false) = true := by native_decide

/-- The unlikely key branch compiles to PKH with the generator key's
concrete HASH160, exercising the byte compiler through the CLI boundary. -/
example : (match compileReport .p2wsh s!"or(99@pk(03{x}),1@pk({key}))" with
    | .ok report => byteArrayHex report.script ==
        "2103" ++ x ++ "ac736476a914751e76e8199196d454941c45d1b3a323f1433bd688ac68"
    | .error _ => false) = true := by native_decide

example : (compileReport .p2wsh s!"pk({x})").toBool = false := by native_decide
example : (compileReport .p2wsh "older(100)").toBool = false := by native_decide
example : (compileReport .tapscript "pk(").toBool = false := by native_decide


example : (parseArgs ["--", "descriptor", s!"combo({key})"]).toOption =
    some (.descriptor none s!"combo({key})") := by native_decide

example : (parseArgs ["descriptor", "--index", "7", s!"pkh({key})"]).toOption =
    some (.descriptor (some 7) s!"pkh({key})") := by native_decide

example : (parseArgs ["descriptor", "--index", "x", s!"pkh({key})"]).toBool = false := by
  native_decide

example : (parseArgs ["descriptor"]).toBool = false := by native_decide

/-- combo() prints its P2PK, P2PKH, P2WPKH, and P2SH-P2WPKH scripts in order. -/
example : execute (.descriptor none s!"combo({key})") = .ok (String.intercalate "\n" [
    s!"script_pubkey: 21{key}ac",
    "script_pubkey: 76a914751e76e8199196d454941c45d1b3a323f1433bd688ac",
    "script_pubkey: 0014751e76e8199196d454941c45d1b3a323f1433bd6",
    "script_pubkey: a914bcfeb728b584253d5f3f70bcb780e9ef218a68f487"]) := by native_decide

example : execute (.descriptor none "addr(1BgGZ9tcN4rm9KBzDn7KprQz87SZ26SAMH)") =
    .ok "script_pubkey: 76a914751e76e8199196d454941c45d1b3a323f1433bd688ac" := by native_decide

example : (execute (.descriptor none "addr(1BgGZ9tcN4rm9KBzDn7KprQz87SZ26SAMx)")).toBool =
    false := by native_decide

end LeanMiniscript.Policy.Cli
