import LeanMiniscript.Miniscript.SatisfactionEnvironment

/-!
# Atom material

`Material` records which atomic spending conditions are available: keys that
will sign, hashlocks whose preimages are known, and absolute/relative
timelocks that the spending transaction meets. `Material.atom` interprets that
availability on Miniscript leaves, giving the atom predicate expected by
`CoreFragment.isSatisfiableWith`.

A concrete satisfaction environment induces material through
`SatEnv.material`. `SatisfactionPossibilityProofs` shows that, for every valid
Miniscript, raw satisfier candidates exist exactly when the fragment is
structurally satisfiable under this induced material.
-/

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- Availability of every atomic spending condition. -/
structure Material where
  /-- Keys whose owners provide a signature. -/
  signs : PubKey → Bool
  /-- Hashlocks whose preimage is known. -/
  preimage : HashLock → Bool
  /-- Absolute timelocks `after(n)` met by the spending transaction. -/
  after : Nat → Bool
  /-- Relative timelocks `older(n)` met by the spending transaction. -/
  older : Nat → Bool

namespace Material

/-- Number of keys in a list whose owners sign. -/
def signerCount (material : Material) : List PubKey → Nat
  | [] => 0
  | key :: keys =>
      (if material.signs key then 1 else 0) + signerCount material keys

/-- Interpret material on Miniscript leaves. Multisignature leaves are
    available when enough listed keys sign; connectives and wrappers are not
    atoms and are never consulted by `isSatisfiableWith`. -/
def atom (material : Material) : CoreFragment → Bool
  | .pk_k key | .pk_h key => material.signs key
  | .older n => material.older n
  | .after n => material.after n
  | .sha256 hash => material.preimage (.sha256 hash)
  | .hash256 hash => material.preimage (.hash256 hash)
  | .ripemd160 hash => material.preimage (.ripemd160 hash)
  | .hash160 hash => material.preimage (.hash160 hash)
  | .multi k keys | .multi_a k keys => decide (k ≤ material.signerCount keys)
  | _ => false

end Material

/-- Atom availability induced by a concrete satisfaction environment. A key
    signs when the environment returns a signature, a hashlock is available
    when it returns a preimage, and timelocks follow the Script interpreter's
    `locktimeSatisfied`/`sequenceSatisfied` checks on the transaction. -/
def SatEnv.material (env : SatEnv) : Material where
  signs key := (env.signatureFor key).isSome
  preimage lock := (env.preimageFor lock).isSome
  after n := decide (locktimeSatisfied n env.txCtx)
  older n := decide (sequenceSatisfied n env.txCtx)

end LeanMiniscript.Miniscript
