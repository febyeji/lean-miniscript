import LeanMiniscript.Miniscript.CompileConcreteProofs
import LeanMiniscript.Script.RuntimeLimits
import LeanMiniscript.Script.ScriptNumProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

private def SmallPushes (script : Script) : Prop :=
  ∀ element ∈ script, element.pushSize ≤ 33

@[simp] private theorem small_nil : SmallPushes [] := by simp [SmallPushes]
@[simp] private theorem small_cons (element : ScriptElement) (script : Script) :
    SmallPushes (element :: script) ↔ element.pushSize ≤ 33 ∧ SmallPushes script := by
  simp [SmallPushes]
@[simp] private theorem small_append (left right : Script) :
    SmallPushes (left ++ right) ↔ SmallPushes left ∧ SmallPushes right := by
  simp [SmallPushes, or_imp, forall_and]
@[simp] private theorem small_op (opcode : Opcode) :
    (ScriptElement.op opcode).pushSize ≤ 33 := by simp [ScriptElement.pushSize]

private theorem small_nat {n : Nat} (bound : n < 2147483648) :
    (ScriptElement.pushNum n).pushSize ≤ 33 := by
  have decoded := decodeScriptNum_scriptNat_of_lt bound false
  unfold decodeScriptNum at decoded
  split at decoded
  · contradiction
  · change (scriptNat n).size ≤ 33
    change ¬ (scriptNat n).size > 4 at ‹¬ _›
    omega

private theorem small_key {ctx : ScriptContext} {key : PubKey}
    (valid : validResolvedPubKey ctx key) :
    (ScriptElement.pushData key).pushSize ≤ 33 := by
  cases ctx <;> simp only [validResolvedPubKey, validCompressedPubKeyBytes, PubKey.size] at valid
  all_goals simp only [ScriptElement.pushSize]; omega

private theorem Bip379VerifyCompilation.smallPushes
    {script verified : Script} (conforms : Bip379VerifyCompilation script verified)
    (small : SmallPushes script) : SmallPushes verified := by
  cases conforms <;> simp_all

private theorem Bip379KeyPushCompilation.smallPushes
    {ctx : ScriptContext} {keys : List PubKey} {script : Script}
    (conforms : Bip379KeyPushCompilation keys script)
    (valid : CoreFragment.allKeysValid ctx keys) : SmallPushes script := by
  induction conforms with
  | nil => simp
  | cons tail ih => exact small_cons _ _ |>.mpr ⟨small_key valid.1, ih valid.2⟩

private theorem Bip379CheckSigAddTailCompilation.smallPushes
    {ctx : ScriptContext} {keys : List PubKey} {script : Script}
    (conforms : Bip379CheckSigAddTailCompilation keys script)
    (valid : CoreFragment.allKeysValid ctx keys) : SmallPushes script := by
  induction conforms with
  | nil => simp
  | cons tail ih => simpa using And.intro (small_key valid.1) (ih valid.2)

private theorem Bip379CheckSigAddCompilation.smallPushes
    {ctx : ScriptContext} {keys : List PubKey} {script : Script}
    (conforms : Bip379CheckSigAddCompilation keys script)
    (valid : CoreFragment.allKeysValid ctx keys) : SmallPushes script := by
  cases conforms with
  | nil => simpa using (small_nat (n := 0) (by decide))
  | cons tail => simpa using And.intro (small_key valid.1) (tail.smallPushes valid.2)

mutual
private theorem Bip379Compilation.smallPushes
    {keyHash : PubKey → Hash160} {fragment : CoreFragment} {script : Script}
    (conforms : Bip379Compilation keyHash fragment script)
    (hashes : ∀ key, (keyHash key).size ≤ 33)
    {ctx : ScriptContext} (valid : fragment.WellFormed ctx) : SmallPushes script := by
  cases conforms with
  | zero => simpa using (small_nat (n := 0) (by decide))
  | one => simpa using (small_nat (n := 1) (by decide))
  | pkK key => simpa using small_key valid
  | pkH key => simpa [ScriptElement.pushSize, Hash160.size] using hashes key
  | older n | after n => simpa using small_nat valid.2
  | sha256 hash | hash256 hash =>
      have size : hash.bytes.size = 32 := valid
      simp [ScriptElement.pushSize, size, show (scriptNum 32).size ≤ 33 by decide]
  | ripemd160 hash | hash160 hash =>
      have size : hash.bytes.size = 20 := valid
      simp [ScriptElement.pushSize, size, show (scriptNum 32).size ≤ 33 by decide]
  | andV first second | andB first second =>
      simpa using And.intro (first.smallPushes hashes valid.1) (second.smallPushes hashes valid.2.1)
  | orB first second | orC first second | orD first second | orI first second =>
      simpa using And.intro (first.smallPushes hashes valid.1) (second.smallPushes hashes valid.2)
  | andor first second third =>
      simpa [and_assoc] using And.intro (first.smallPushes hashes valid.1)
        (And.intro (third.smallPushes hashes valid.2.2.1) (second.smallPushes hashes valid.2.1))
  | a inner | s inner | c inner | d inner | j inner | n inner =>
      simpa using inner.smallPushes hashes valid
  | v inner verified => exact verified.smallPushes (inner.smallPushes hashes valid)
  | thresh inner =>
      simpa using And.intro (inner.smallPushes hashes valid.2.1) (small_nat valid.2.2.2)
  | multi threshold keys =>
      have count := valid.2.2.1
      change _ ≤ 20 at count
      have bound := valid.2.1.2
      simpa [and_assoc] using And.intro (small_nat (by omega : threshold < 2147483648))
        (And.intro (keys.smallPushes valid.2.2.2) (small_nat (by omega)))
  | multiA threshold keys =>
      have count := valid.2.2.1
      change _ ≤ 999 at count
      have bound := valid.2.1.2
      simpa using And.intro (keys.smallPushes valid.2.2.2)
        (small_nat (by omega : threshold < 2147483648))

private theorem Bip379ThreshCompilation.smallPushes
    {keyHash : PubKey → Hash160} {fragments : List CoreFragment} {script : Script}
    (conforms : Bip379ThreshCompilation keyHash fragments script)
    (hashes : ∀ key, (keyHash key).size ≤ 33)
    {ctx : ScriptContext} (valid : CoreFragment.allWellFormed ctx fragments) : SmallPushes script := by
  cases conforms with
  | nil => simp
  | cons first rest => simpa using And.intro (first.smallPushes hashes valid.1) (rest.smallPushes hashes valid.2)

private theorem Bip379ThreshTailCompilation.smallPushes
    {keyHash : PubKey → Hash160} {fragments : List CoreFragment} {script : Script}
    (conforms : Bip379ThreshTailCompilation keyHash fragments script)
    (hashes : ∀ key, (keyHash key).size ≤ 33)
    {ctx : ScriptContext} (valid : CoreFragment.allWellFormed ctx fragments) : SmallPushes script := by
  cases conforms with
  | nil => simp
  | cons first rest => simpa using And.intro (first.smallPushes hashes valid.1) (rest.smallPushes hashes valid.2)
end

/-- Concrete compilation of a well-formed Miniscript only pushes keys, hashes
and bounded numbers, each at most 33 bytes in either supported context. -/
theorem compileConcrete_pushSize_le {ctx : ScriptContext} {fragment : CoreFragment}
    (valid : fragment.WellFormed ctx) :
    ∀ element ∈ compileConcrete fragment, element.pushSize ≤ 33 :=
  (compileConcrete_conforms fragment).smallPushes (by intro key; simp) valid

end LeanMiniscript.Miniscript
