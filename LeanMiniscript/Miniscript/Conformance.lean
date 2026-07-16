import LeanMiniscript.Miniscript.Compile

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-!
# BIP 379 compilation conformance

`Bip379Compilation` states the selected translation scheme independently from
the executable compiler. It deliberately uses the general `VERIFY` encoding;
specialized VERIFY-opcode substitutions are permitted alternative encodings
but are not produced by this model.
-/

/-- Independent relational specification for pushing a list of public keys. -/
inductive Bip379KeyPushCompilation : List PubKey → Script → Prop where
  | nil : Bip379KeyPushCompilation [] []
  | cons {key : PubKey} {keys : List PubKey} {tailScript : Script}
      (tailConforms : Bip379KeyPushCompilation keys tailScript) :
      Bip379KeyPushCompilation (key :: keys) (.pushData key :: tailScript)

/-- Independent relational specification for the `CHECKSIGADD` tail. -/
inductive Bip379CheckSigAddTailCompilation : List PubKey → Script → Prop where
  | nil : Bip379CheckSigAddTailCompilation [] []
  | cons {key : PubKey} {keys : List PubKey} {tailScript : Script}
      (tailConforms : Bip379CheckSigAddTailCompilation keys tailScript) :
      Bip379CheckSigAddTailCompilation (key :: keys)
        ([.pushData key, .op .OP_CHECKSIGADD] ++ tailScript)

/-- Independent relational specification for the first-key-special
`CHECKSIG`/`CHECKSIGADD` sequence used by `multi_a`. -/
inductive Bip379CheckSigAddCompilation : List PubKey → Script → Prop where
  | nil : Bip379CheckSigAddCompilation [] [.pushNum 0]
  | cons {key : PubKey} {keys : List PubKey} {tailScript : Script}
      (tailConforms : Bip379CheckSigAddTailCompilation keys tailScript) :
      Bip379CheckSigAddCompilation (key :: keys)
        ([.pushData key, .op .OP_CHECKSIG] ++ tailScript)

mutual

/-- Relational form of the BIP 379 translation schemes selected by this model. -/
inductive Bip379Compilation
    (keyHash : PubKey → Hash160) : CoreFragment → Script → Prop where
  | zero : Bip379Compilation keyHash .zero [.pushNum 0]
  | one : Bip379Compilation keyHash .one [.pushNum 1]
  | pkK (key : PubKey) :
      Bip379Compilation keyHash (.pk_k key) [.pushData key]
  | pkH (key : PubKey) :
      Bip379Compilation keyHash (.pk_h key)
        [.op .OP_DUP, .op .OP_HASH160, .pushData (keyHash key), .op .OP_EQUALVERIFY]
  | older (n : Nat) :
      Bip379Compilation keyHash (.older n) [.pushNum n, .op .OP_CHECKSEQUENCEVERIFY]
  | after (n : Nat) :
      Bip379Compilation keyHash (.after n) [.pushNum n, .op .OP_CHECKLOCKTIMEVERIFY]
  | sha256 (hash : Hash256) :
      Bip379Compilation keyHash (.sha256 hash)
        [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY,
          .op .OP_SHA256, .pushData hash, .op .OP_EQUAL]
  | hash256 (hash : Hash256) :
      Bip379Compilation keyHash (.hash256 hash)
        [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY,
          .op .OP_HASH256, .pushData hash, .op .OP_EQUAL]
  | ripemd160 (hash : Hash160) :
      Bip379Compilation keyHash (.ripemd160 hash)
        [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY,
          .op .OP_RIPEMD160, .pushData hash, .op .OP_EQUAL]
  | hash160 (hash : Hash160) :
      Bip379Compilation keyHash (.hash160 hash)
        [.op .OP_SIZE, .pushNum 32, .op .OP_EQUALVERIFY,
          .op .OP_HASH160, .pushData hash, .op .OP_EQUAL]
  | andV {x y : CoreFragment} {xScript yScript : Script}
      (xConforms : Bip379Compilation keyHash x xScript)
      (yConforms : Bip379Compilation keyHash y yScript) :
      Bip379Compilation keyHash (.and_v x y) (xScript ++ yScript)
  | andB {x y : CoreFragment} {xScript yScript : Script}
      (xConforms : Bip379Compilation keyHash x xScript)
      (yConforms : Bip379Compilation keyHash y yScript) :
      Bip379Compilation keyHash (.and_b x y)
        (xScript ++ yScript ++ [.op .OP_BOOLAND])
  | orB {x y : CoreFragment} {xScript yScript : Script}
      (xConforms : Bip379Compilation keyHash x xScript)
      (yConforms : Bip379Compilation keyHash y yScript) :
      Bip379Compilation keyHash (.or_b x y)
        (xScript ++ yScript ++ [.op .OP_BOOLOR])
  | orC {x y : CoreFragment} {xScript yScript : Script}
      (xConforms : Bip379Compilation keyHash x xScript)
      (yConforms : Bip379Compilation keyHash y yScript) :
      Bip379Compilation keyHash (.or_c x y)
        (xScript ++ [.op .OP_NOTIF] ++ yScript ++ [.op .OP_ENDIF])
  | orD {x y : CoreFragment} {xScript yScript : Script}
      (xConforms : Bip379Compilation keyHash x xScript)
      (yConforms : Bip379Compilation keyHash y yScript) :
      Bip379Compilation keyHash (.or_d x y)
        (xScript ++ [.op .OP_IFDUP, .op .OP_NOTIF] ++ yScript ++ [.op .OP_ENDIF])
  | orI {x y : CoreFragment} {xScript yScript : Script}
      (xConforms : Bip379Compilation keyHash x xScript)
      (yConforms : Bip379Compilation keyHash y yScript) :
      Bip379Compilation keyHash (.or_i x y)
        ([.op .OP_IF] ++ xScript ++ [.op .OP_ELSE] ++ yScript ++ [.op .OP_ENDIF])
  | andor {x y z : CoreFragment} {xScript yScript zScript : Script}
      (xConforms : Bip379Compilation keyHash x xScript)
      (yConforms : Bip379Compilation keyHash y yScript)
      (zConforms : Bip379Compilation keyHash z zScript) :
      Bip379Compilation keyHash (.andor x y z)
        (xScript ++ [.op .OP_NOTIF] ++ zScript ++ [.op .OP_ELSE] ++
          yScript ++ [.op .OP_ENDIF])
  | a {x : CoreFragment} {script : Script}
      (conforms : Bip379Compilation keyHash x script) :
      Bip379Compilation keyHash (.a x)
        ([.op .OP_TOALTSTACK] ++ script ++ [.op .OP_FROMALTSTACK])
  | s {x : CoreFragment} {script : Script}
      (conforms : Bip379Compilation keyHash x script) :
      Bip379Compilation keyHash (.s x) ([.op .OP_SWAP] ++ script)
  | c {x : CoreFragment} {script : Script}
      (conforms : Bip379Compilation keyHash x script) :
      Bip379Compilation keyHash (.c x) (script ++ [.op .OP_CHECKSIG])
  | d {x : CoreFragment} {script : Script}
      (conforms : Bip379Compilation keyHash x script) :
      Bip379Compilation keyHash (.d x)
        ([.op .OP_DUP, .op .OP_IF] ++ script ++ [.op .OP_ENDIF])
  | v {x : CoreFragment} {script : Script}
      (conforms : Bip379Compilation keyHash x script) :
      Bip379Compilation keyHash (.v x) (script ++ [.op .OP_VERIFY])
  | j {x : CoreFragment} {script : Script}
      (conforms : Bip379Compilation keyHash x script) :
      Bip379Compilation keyHash (.j x)
        ([.op .OP_SIZE, .op .OP_0NOTEQUAL, .op .OP_IF] ++ script ++ [.op .OP_ENDIF])
  | n {x : CoreFragment} {script : Script}
      (conforms : Bip379Compilation keyHash x script) :
      Bip379Compilation keyHash (.n x) (script ++ [.op .OP_0NOTEQUAL])
  | thresh {k : Nat} {fragments : List CoreFragment} {script : Script}
      (conforms : Bip379ThreshCompilation keyHash fragments script) :
      Bip379Compilation keyHash (.thresh k fragments)
        (script ++ [.pushNum k, .op .OP_EQUAL])
  | multi (k : Nat) {keys : List PubKey} {keyScript : Script}
      (keysConform : Bip379KeyPushCompilation keys keyScript) :
      Bip379Compilation keyHash (.multi k keys)
        ([.pushNum k] ++ keyScript ++
          [.pushNum keys.length, .op .OP_CHECKMULTISIG])
  | multiA (k : Nat) {keys : List PubKey} {keyScript : Script}
      (keysConform : Bip379CheckSigAddCompilation keys keyScript) :
      Bip379Compilation keyHash (.multi_a k keys)
        (keyScript ++ [.pushNum k, .op .OP_NUMEQUAL])

/-- Relational form of the first-child-special threshold translation. -/
inductive Bip379ThreshCompilation
    (keyHash : PubKey → Hash160) : List CoreFragment → Script → Prop where
  | nil : Bip379ThreshCompilation keyHash [] []
  | cons {fragment : CoreFragment} {fragments : List CoreFragment}
      {script tailScript : Script}
      (headConforms : Bip379Compilation keyHash fragment script)
      (tailConforms : Bip379ThreshTailCompilation keyHash fragments tailScript) :
      Bip379ThreshCompilation keyHash (fragment :: fragments) (script ++ tailScript)

/-- Relational form of threshold children that each receive a trailing `ADD`. -/
inductive Bip379ThreshTailCompilation
    (keyHash : PubKey → Hash160) : List CoreFragment → Script → Prop where
  | nil : Bip379ThreshTailCompilation keyHash [] []
  | cons {fragment : CoreFragment} {fragments : List CoreFragment}
      {script tailScript : Script}
      (headConforms : Bip379Compilation keyHash fragment script)
      (tailConforms : Bip379ThreshTailCompilation keyHash fragments tailScript) :
      Bip379ThreshTailCompilation keyHash (fragment :: fragments)
        (script ++ [.op .OP_ADD] ++ tailScript)

end

/-- The executable key-push helper implements the independent list relation. -/
theorem compileKeyPushes_conforms (keys : List PubKey) :
    Bip379KeyPushCompilation keys (compileKeyPushes keys) := by
  induction keys with
  | nil => exact .nil
  | cons key keys keysConform => exact .cons keysConform

/-- The executable `CHECKSIGADD` tail implements its independent relation. -/
theorem compileCheckSigAddTail_conforms (keys : List PubKey) :
    Bip379CheckSigAddTailCompilation keys (compileCheckSigAddTail keys) := by
  induction keys with
  | nil => exact .nil
  | cons key keys keysConform => exact .cons keysConform

/-- The executable first-key-special sequence implements its independent relation. -/
theorem compileCheckSigAdd_conforms (keys : List PubKey) :
    Bip379CheckSigAddCompilation keys (compileCheckSigAdd keys) := by
  cases keys with
  | nil => exact .nil
  | cons key keys => exact .cons (compileCheckSigAddTail_conforms keys)

mutual

theorem compileWithKeyHash_conforms
    (keyHash : PubKey → Hash160) (fragment : CoreFragment) :
    Bip379Compilation keyHash fragment (compileWithKeyHash keyHash fragment) := by
  cases fragment with
  | zero => exact .zero
  | one => exact .one
  | pk_k key => exact .pkK key
  | pk_h key => exact .pkH key
  | older n => exact .older n
  | after n => exact .after n
  | sha256 hash => exact .sha256 hash
  | hash256 hash => exact .hash256 hash
  | ripemd160 hash => exact .ripemd160 hash
  | hash160 hash => exact .hash160 hash
  | and_v x y =>
      apply Bip379Compilation.andV
      · exact compileWithKeyHash_conforms keyHash x
      · exact compileWithKeyHash_conforms keyHash y
  | and_b x y =>
      apply Bip379Compilation.andB
      · exact compileWithKeyHash_conforms keyHash x
      · exact compileWithKeyHash_conforms keyHash y
  | or_b x y =>
      apply Bip379Compilation.orB
      · exact compileWithKeyHash_conforms keyHash x
      · exact compileWithKeyHash_conforms keyHash y
  | or_c x y =>
      apply Bip379Compilation.orC
      · exact compileWithKeyHash_conforms keyHash x
      · exact compileWithKeyHash_conforms keyHash y
  | or_d x y =>
      apply Bip379Compilation.orD
      · exact compileWithKeyHash_conforms keyHash x
      · exact compileWithKeyHash_conforms keyHash y
  | or_i x y =>
      apply Bip379Compilation.orI
      · exact compileWithKeyHash_conforms keyHash x
      · exact compileWithKeyHash_conforms keyHash y
  | andor x y z =>
      apply Bip379Compilation.andor
      · exact compileWithKeyHash_conforms keyHash x
      · exact compileWithKeyHash_conforms keyHash y
      · exact compileWithKeyHash_conforms keyHash z
  | a x => exact .a (compileWithKeyHash_conforms keyHash x)
  | s x => exact .s (compileWithKeyHash_conforms keyHash x)
  | c x => exact .c (compileWithKeyHash_conforms keyHash x)
  | d x => exact .d (compileWithKeyHash_conforms keyHash x)
  | v x => exact .v (compileWithKeyHash_conforms keyHash x)
  | j x => exact .j (compileWithKeyHash_conforms keyHash x)
  | n x => exact .n (compileWithKeyHash_conforms keyHash x)
  | thresh k fragments =>
      exact .thresh (compileThreshWithKeyHash_conforms keyHash fragments)
  | multi k keys => exact .multi k (compileKeyPushes_conforms keys)
  | multi_a k keys => exact .multiA k (compileCheckSigAdd_conforms keys)

theorem compileThreshWithKeyHash_conforms
    (keyHash : PubKey → Hash160) (fragments : List CoreFragment) :
    Bip379ThreshCompilation keyHash fragments
      (compileThreshWithKeyHash keyHash fragments) := by
  cases fragments with
  | nil => exact .nil
  | cons fragment fragments =>
      apply Bip379ThreshCompilation.cons
      · exact compileWithKeyHash_conforms keyHash fragment
      · exact compileThreshTailWithKeyHash_conforms keyHash fragments

theorem compileThreshTailWithKeyHash_conforms
    (keyHash : PubKey → Hash160) (fragments : List CoreFragment) :
    Bip379ThreshTailCompilation keyHash fragments
      (compileThreshTailWithKeyHash keyHash fragments) := by
  cases fragments with
  | nil => exact .nil
  | cons fragment fragments =>
      apply Bip379ThreshTailCompilation.cons
      · exact compileWithKeyHash_conforms keyHash fragment
      · exact compileThreshTailWithKeyHash_conforms keyHash fragments

end

/-- The independent key-push relation uniquely determines the executable helper. -/
theorem Bip379KeyPushCompilation.eq_compileKeyPushes
    {keys : List PubKey} {script : Script}
    (conforms : Bip379KeyPushCompilation keys script) :
    script = compileKeyPushes keys := by
  induction conforms with
  | nil => rfl
  | cons tailConforms tailEq => simp [compileKeyPushes, tailEq]

/-- The independent `CHECKSIGADD` tail relation uniquely determines its helper. -/
theorem Bip379CheckSigAddTailCompilation.eq_compileCheckSigAddTail
    {keys : List PubKey} {script : Script}
    (conforms : Bip379CheckSigAddTailCompilation keys script) :
    script = compileCheckSigAddTail keys := by
  induction conforms with
  | nil => rfl
  | cons tailConforms tailEq => simp [compileCheckSigAddTail, tailEq]

/-- The independent first-key-special relation uniquely determines its helper. -/
theorem Bip379CheckSigAddCompilation.eq_compileCheckSigAdd
    {keys : List PubKey} {script : Script}
    (conforms : Bip379CheckSigAddCompilation keys script) :
    script = compileCheckSigAdd keys := by
  cases conforms with
  | nil => rfl
  | cons tailConforms =>
      simp [compileCheckSigAdd, tailConforms.eq_compileCheckSigAddTail]

mutual

theorem Bip379Compilation.eq_compileWithKeyHash
    {keyHash : PubKey → Hash160} {fragment : CoreFragment} {script : Script}
    (conforms : Bip379Compilation keyHash fragment script) :
    script = compileWithKeyHash keyHash fragment := by
  cases conforms with
  | zero => rfl
  | one => rfl
  | pkK => rfl
  | pkH => rfl
  | older => rfl
  | after => rfl
  | sha256 => rfl
  | hash256 => rfl
  | ripemd160 => rfl
  | hash160 => rfl
  | multi k keysConform =>
      simp [compileWithKeyHash, keysConform.eq_compileKeyPushes]
  | multiA k keysConform =>
      simp [compileWithKeyHash, keysConform.eq_compileCheckSigAdd]
  | andV xConforms yConforms =>
      simp [compileWithKeyHash, xConforms.eq_compileWithKeyHash,
        yConforms.eq_compileWithKeyHash]
  | andB xConforms yConforms =>
      simp [compileWithKeyHash, xConforms.eq_compileWithKeyHash,
        yConforms.eq_compileWithKeyHash]
  | orB xConforms yConforms =>
      simp [compileWithKeyHash, xConforms.eq_compileWithKeyHash,
        yConforms.eq_compileWithKeyHash]
  | orC xConforms yConforms =>
      simp [compileWithKeyHash, xConforms.eq_compileWithKeyHash,
        yConforms.eq_compileWithKeyHash]
  | orD xConforms yConforms =>
      simp [compileWithKeyHash, xConforms.eq_compileWithKeyHash,
        yConforms.eq_compileWithKeyHash]
  | orI xConforms yConforms =>
      simp [compileWithKeyHash, xConforms.eq_compileWithKeyHash,
        yConforms.eq_compileWithKeyHash]
  | andor xConforms yConforms zConforms =>
      simp [compileWithKeyHash, xConforms.eq_compileWithKeyHash,
        yConforms.eq_compileWithKeyHash, zConforms.eq_compileWithKeyHash]
  | a conforms =>
      simp [compileWithKeyHash, conforms.eq_compileWithKeyHash]
  | s conforms =>
      simp [compileWithKeyHash, conforms.eq_compileWithKeyHash]
  | c conforms =>
      simp [compileWithKeyHash, conforms.eq_compileWithKeyHash]
  | d conforms =>
      simp [compileWithKeyHash, conforms.eq_compileWithKeyHash]
  | v conforms =>
      simp [compileWithKeyHash, conforms.eq_compileWithKeyHash]
  | j conforms =>
      simp [compileWithKeyHash, conforms.eq_compileWithKeyHash]
  | n conforms =>
      simp [compileWithKeyHash, conforms.eq_compileWithKeyHash]
  | thresh conforms =>
      simp [compileWithKeyHash, conforms.eq_compileThreshWithKeyHash]

theorem Bip379ThreshCompilation.eq_compileThreshWithKeyHash
    {keyHash : PubKey → Hash160} {fragments : List CoreFragment} {script : Script}
    (conforms : Bip379ThreshCompilation keyHash fragments script) :
    script = compileThreshWithKeyHash keyHash fragments := by
  cases conforms with
  | nil => rfl
  | cons headConforms tailConforms =>
      simp [compileThreshWithKeyHash, headConforms.eq_compileWithKeyHash,
        tailConforms.eq_compileThreshTailWithKeyHash]

theorem Bip379ThreshTailCompilation.eq_compileThreshTailWithKeyHash
    {keyHash : PubKey → Hash160} {fragments : List CoreFragment} {script : Script}
    (conforms : Bip379ThreshTailCompilation keyHash fragments script) :
    script = compileThreshTailWithKeyHash keyHash fragments := by
  cases conforms with
  | nil => rfl
  | cons headConforms tailConforms =>
      simp [compileThreshTailWithKeyHash, headConforms.eq_compileWithKeyHash,
        tailConforms.eq_compileThreshTailWithKeyHash]

end

/-- The executable compiler and the relational BIP 379 schemes agree exactly. -/
theorem bip379Compilation_iff
    (keyHash : PubKey → Hash160) (fragment : CoreFragment) (script : Script) :
    Bip379Compilation keyHash fragment script ↔
      script = compileWithKeyHash keyHash fragment := by
  constructor
  · exact Bip379Compilation.eq_compileWithKeyHash
  · intro scriptEq
    subst script
    exact compileWithKeyHash_conforms keyHash fragment

/-- The formal compiler is an instance of the general relational conformance result. -/
theorem compile_conforms (fragment : CoreFragment) :
    Bip379Compilation modelKeyHash fragment (compile fragment) :=
  compileWithKeyHash_conforms modelKeyHash fragment

/-- Surface compilation conforms after its explicitly defined desugaring step. -/
theorem compileSurfaceWithKeyHash_conforms
    (keyHash : PubKey → Hash160) (fragment : SurfaceFragment) :
    Bip379Compilation keyHash (desugar fragment)
      (compileSurfaceWithKeyHash keyHash fragment) :=
  compileWithKeyHash_conforms keyHash (desugar fragment)

/-- The abstract-HASH160 surface compiler conforms after desugaring. -/
theorem compileSurface_conforms (fragment : SurfaceFragment) :
    Bip379Compilation modelKeyHash (desugar fragment) (compileSurface fragment) :=
  compileSurfaceWithKeyHash_conforms modelKeyHash fragment

end LeanMiniscript.Miniscript
