import Lean

namespace LeanMiniscript.Bitcoin.Secp256k1

/-! Executable affine secp256k1 operations for public-input verification.
These follow the BIP340 reference algorithm. No curve-correctness theorem or
constant-time signing interface is claimed. Callers of point operations must
supply canonical on-curve coordinates; `liftX` enforces that at byte boundaries.
-/

def field : Nat := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
def order : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

/-- Infinity is `none`; finite points have canonical affine coordinates. -/
abbrev Point := Option (Nat × Nat)

def generator : Point := some
  (0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
   0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8)

def decodeBE (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => 256 * value + byte.toNat) 0

def powMod (base exponent modulus : Nat) : Nat :=
  if exponent = 0 then 1 % modulus
  else
    let half := powMod base (exponent / 2) modulus
    let square := half * half % modulus
    if exponent % 2 = 0 then square else square * base % modulus
termination_by exponent
decreasing_by omega

private def sub (a b : Nat) : Nat := (a % field + field - b % field) % field

def pointAdd (a b : Point) : Point :=
  match a, b with
  | none, _ => b
  | _, none => a
  | some (x₁, y₁), some (x₂, y₂) =>
      if x₁ = x₂ && (y₁ + y₂) % field = 0 then none
      else
        let slope := if x₁ = x₂ then
          3 * x₁ * x₁ * powMod (2 * y₁) (field - 2) field % field
        else sub y₂ y₁ * powMod (sub x₂ x₁) (field - 2) field % field
        let x₃ := sub (sub (slope * slope) x₁) x₂
        some (x₃, sub (slope * sub x₁ x₃) y₁)

def pointMul (point : Point) (scalar : Nat) : Point :=
  if scalar = 0 then none
  else
    let half := pointMul point (scalar / 2)
    let doubled := pointAdd half half
    if scalar % 2 = 0 then doubled else pointAdd doubled point
termination_by scalar
decreasing_by omega

/-- BIP340's unique even-Y lift, rejecting out-of-field and non-curve X values. -/
def liftX (x : Nat) : Point :=
  if x ≥ field then none
  else
    let square := (x * x % field * x + 7) % field
    let y := powMod square ((field + 1) / 4) field
    if y * y % field ≠ square then none
    else some (x, if y % 2 = 0 then y else field - y)

end LeanMiniscript.Bitcoin.Secp256k1
