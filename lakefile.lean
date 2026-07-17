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
  roots := #[`LeanMiniscriptProofs]

@[default_target]
lean_lib LeanMiniscriptExperimental where
  roots := #[`LeanMiniscriptExperimental]

@[default_target]
lean_lib LeanMiniscriptTests where
  roots := #[`LeanMiniscriptTests]
