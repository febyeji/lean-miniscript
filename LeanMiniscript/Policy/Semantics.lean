import LeanMiniscript.Policy.Syntax
import LeanMiniscript.Miniscript.AtomMaterial

/-!
# Policy semantics

A policy denotes the set of spending materials that satisfy it.
`Policy.eval` is that denotational meaning over the shared Miniscript
`Material` vocabulary: keys that will sign, hashlocks whose preimages are
known, and timelocks met by the spending transaction. The same material
interprets Miniscript leaves through `Material.atom`, and a concrete
satisfaction environment induces it through `SatEnv.material`.
-/

namespace LeanMiniscript.Policy

open LeanMiniscript.Miniscript
open LeanMiniscript.Script

namespace Policy

mutual
  /-- Denotational meaning: whether the material satisfies the policy. -/
  def eval (material : Material) : Policy → Bool
    | .unsatisfiable => false
    | .trivial => true
    | .key pubKey => material.signs pubKey
    | .after n => material.after n
    | .older n => material.older n
    | .sha256 hash => material.preimage (.sha256 hash)
    | .hash256 hash => material.preimage (.hash256 hash)
    | .ripemd160 hash => material.preimage (.ripemd160 hash)
    | .hash160 hash => material.preimage (.hash160 hash)
    | .and left right => eval material left && eval material right
    | .or _ left _ right => eval material left || eval material right
    | .thresh k subs => decide (k ≤ evalCount material subs)

  /-- Number of satisfied policies in a list. -/
  def evalCount (material : Material) : List Policy → Nat
    | [] => 0
    | sub :: subs =>
        (if eval material sub then 1 else 0) + evalCount material subs
end

/-- Propositional form of `eval`. -/
def Satisfies (material : Material) (policy : Policy) : Prop :=
  policy.eval material = true

end Policy

end LeanMiniscript.Policy
