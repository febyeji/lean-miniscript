import LeanMiniscript.Miniscript.CompileConcrete
import LeanMiniscript.Miniscript.CompileConcreteChecked
import LeanMiniscript.Miniscript.Structural

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

private theorem foldlPush_size {α : Type} (values : List α)
    (byte : α → UInt8) (output : ByteArray) :
    (values.foldl (fun bytes value => bytes.push (byte value)) output).size =
      output.size + values.length := by
  induction values generalizing output with
  | nil => simp
  | cons value values ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, ByteArray.size_push]
      omega

private theorem appendUInt32_size
    (endianness : LeanHash160.Internal.Endianness)
    (output : ByteArray) (word : UInt32) :
    (LeanHash160.Internal.appendUInt32 endianness output word).size =
      output.size + 4 := by
  cases endianness <;>
    simp only [LeanHash160.Internal.appendUInt32,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one,
      List.forIn_pure_yield_eq_foldl]
  · change
      (List.foldl
        (fun bytes index => bytes.push
          (((word >>> UInt32.ofNat (8 * (3 - index))) &&& 0xff).toUInt8))
        output (List.range' 0 4)).size = output.size + 4
    rw [foldlPush_size, List.length_range']
  · change
      (List.foldl
        (fun bytes index => bytes.push
          (((word >>> UInt32.ofNat (8 * index)) &&& 0xff).toUInt8))
        output (List.range' 0 4)).size = output.size + 4
    rw [foldlPush_size, List.length_range']

private theorem ripemd160_size (bytes : ByteArray) :
    (LeanHash160.RIPEMD160.hash bytes).size = 20 := by
  simp only [LeanHash160.RIPEMD160.hash,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one,
    List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, Id.run_pure]
  generalize List.foldl _ _ _ = state
  cases state with
  | mk h0 h1 h2 h3 h4 =>
      change
        (ByteArray.size
          ([h0, h1, h2, h3, h4].foldl
            (LeanHash160.Internal.appendUInt32 .little) ByteArray.empty)) = 20
      simp [appendUInt32_size]

/-!
# Executable compilation guarantees

Proofs are kept separate from `CompileConcrete` so consumers that only need the
executable compiler do not import the relational and structural proof graph.
-/

/-- Bitcoin's concrete HASH160 resolver always returns a 20-byte digest. -/
@[simp]
theorem concreteKeyHash_size (key : PubKey) :
    (concreteKeyHash key).size = 20 := by
  simpa [concreteKeyHash, Hash160.size, Hash160.ofBytes,
    LeanHash160.hash160] using ripemd160_size (LeanHash160.SHA256.hash key.bytes)

/-- Concrete core compilation is an instance of the relational BIP 379 result. -/
theorem compileConcrete_conforms (fragment : CoreFragment) :
    Bip379Compilation concreteKeyHash fragment (compileConcrete fragment) :=
  compileWithKeyHash_conforms concreteKeyHash fragment

/-- Concrete surface compilation conforms after desugaring. -/
theorem compileSurfaceConcrete_conforms (fragment : SurfaceFragment) :
    Bip379Compilation concreteKeyHash (desugar fragment)
      (compileSurfaceConcrete fragment) :=
  compileSurfaceWithKeyHash_conforms concreteKeyHash fragment

/-- Concrete core compilation has balanced conditional control flow. -/
theorem compileConcrete_balancedControlFlow (fragment : CoreFragment) :
    BalancedControlFlow (compileConcrete fragment) :=
  compileWithKeyHash_balancedControlFlow concreteKeyHash fragment

/-- Concrete surface compilation has balanced conditional control flow. -/
theorem compileSurfaceConcrete_balancedControlFlow (fragment : SurfaceFragment) :
    BalancedControlFlow (compileSurfaceConcrete fragment) :=
  compileSurfaceWithKeyHash_balancedControlFlow concreteKeyHash fragment

/-- Concrete core compilation emits only opcodes allowed by the validated
Script context. -/
theorem compileConcrete_scriptAllowed
    {ctx : ScriptContext} {fragment : CoreFragment}
    (wellFormed : fragment.WellFormed ctx) :
    ScriptAllowed ctx (compileConcrete fragment) :=
  compileWithKeyHash_scriptAllowed concreteKeyHash wellFormed

/-- Concrete surface compilation emits only opcodes allowed by the validated
Script context. -/
theorem compileSurfaceConcrete_scriptAllowed
    {ctx : ScriptContext} {fragment : SurfaceFragment}
    (wellFormed : fragment.WellFormed ctx) :
    ScriptAllowed ctx (compileSurfaceConcrete fragment) :=
  compileSurfaceWithKeyHash_scriptAllowed concreteKeyHash wellFormed

/-- Concrete checked-core compilation carries context safety from the checked
boundary. -/
theorem compileConcreteChecked_scriptAllowed {ctx : ScriptContext}
    (checked : CheckedFragment ctx) :
    ScriptAllowed ctx (compileConcreteChecked checked) :=
  compileCheckedWithKeyHash_scriptAllowed concreteKeyHash checked

/-- Concrete checked-surface compilation carries context safety from the
checked boundary. -/
theorem compileSurfaceConcreteChecked_scriptAllowed {ctx : ScriptContext}
    (checked : CheckedSurfaceFragment ctx) :
    ScriptAllowed ctx (compileSurfaceConcreteChecked checked) :=
  compileCheckedSurfaceWithKeyHash_scriptAllowed concreteKeyHash checked

end LeanMiniscript.Miniscript
