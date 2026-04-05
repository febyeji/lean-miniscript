import Lake
open Lake DSL

package lean_miniscript where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib LeanMiniscript where
  roots := #[`LeanMiniscript]
