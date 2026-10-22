import Lake
open Lake DSL

require lean_hash160 from git
  "https://github.com/febyeji/lean-hash160.git" @
  "d55f38607f76104609004cdaca27ef0e21f372b6"

package lean_miniscript where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib LeanMiniscript where
  roots := #[`LeanMiniscript]

@[default_target]
lean_lib LeanMiniscriptProofs where
  roots := #[`LeanMiniscript.Proofs]

@[default_target]
lean_lib LeanMiniscriptExperimental where
  roots := #[`LeanMiniscript.Experimental]

@[default_target]
lean_lib LeanMiniscriptTests where
  roots := #[`LeanMiniscript.Tests]

@[default_target]
lean_exe core_fixture_audit where
  root := `LeanMiniscript.Extraction.BitcoinCoreAuditMain

@[default_target]
lean_exe script_cli where
  root := `LeanMiniscript.Extraction.ScriptCliMain

@[default_target]
lean_exe policy_cli where
  root := `LeanMiniscript.PolicyCliMain

@[default_target]
lean_exe psbt_cli where
  root := `LeanMiniscript.PsbtCliMain
