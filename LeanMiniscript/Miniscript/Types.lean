import LeanMiniscript.Miniscript.Syntax

namespace LeanMiniscript.Miniscript

/-- The four base types of the Miniscript type system.
    Each describes the stack behavior of a fragment. -/
inductive BaseType where
  | B  -- Base: consumes input, pushes nonzero (success) or zero (failure)
  | V  -- Verify: consumes input, pushes nothing (success) or aborts (failure)
  | K  -- Key: pushes a public key
  | W  -- Wrapped: like B but input comes from alt stack
  deriving Repr, DecidableEq, BEq

/-- Correctness modifier properties.
    These refine the base type with stack-shape guarantees. -/
structure CorrectnessModifiers where
  /-- z (zero-arg): consumes no stack elements beyond input -/
  z : Bool := false
  /-- o (one-arg): consumes exactly one stack element -/
  o : Bool := false
  /-- n (nonzero): requires nonzero input -/
  n : Bool := false
  /-- d (dissatisfiable): can be dissatisfied with empty witness -/
  d : Bool := false
  /-- u (unit): on success, pushes exactly 1 (not just any nonzero) -/
  u : Bool := false
  deriving Repr, DecidableEq, BEq

/-- Malleability modifier properties. Kept separate from the correctness type
    modifiers because BIP 379 presents them in a distinct analysis table. -/
structure MalleabilityModifiers where
  /-- f (forced): cannot be dissatisfied (always succeeds or aborts) -/
  f : Bool := false
  /-- e (expressive): if not f, then must be d -/
  e : Bool := false
  deriving Repr, DecidableEq, BEq

/-- A complete Miniscript correctness type: base type + correctness modifiers. -/
structure MiniType where
  base : BaseType
  mods : CorrectnessModifiers
  deriving Repr

namespace CorrectnessModifiers

/-- All fragments in a sequence are zero-argument. -/
def allZ : List CorrectnessModifiers → Bool
  | [] => true
  | mods :: rest => mods.z && allZ rest

/-- Exactly one fragment in a sequence is one-argument, and all others are
    zero-argument. -/
def oneOWithRestZ : List CorrectnessModifiers → Bool
  | [] => false
  | mods :: rest => (mods.o && allZ rest) || (mods.z && oneOWithRestZ rest)

end CorrectnessModifiers

namespace MiniType

/-- Modifiers from a typed fragment list, preserving order. -/
def modifiers : List MiniType → List CorrectnessModifiers
  | [] => []
  | ty :: rest => ty.mods :: modifiers rest

end MiniType

/-- Core connectives such as `or_i` and `andor` branch to B/K/V fragments, but
    not W fragments. -/
def branchBase : BaseType → Prop
  | .B => True
  | .K => True
  | .V => True
  | .W => False

/-- Rest fragments in `thresh(k, X1, ..., Xn)` are Wdu fragments. -/
def thresholdRestTypes : List MiniType → Prop
  | [] => True
  | ty :: rest =>
      ty.base = .W ∧ ty.mods.d = true ∧ ty.mods.u = true ∧
        thresholdRestTypes rest

/- Typing judgment: `HasType fragment ty` means a core AST fragment has type
   `ty`.

   BIP 379 type system: each fragment has a base type (B/V/K/W)
   and correctness modifier properties (z, o, n, d, u).

   The rules cover every core constructor. They intentionally remain separate
   from `Miniscript.Validation`: context and size side conditions live there,
   while this judgment records the local stack-shape typing discipline. -/
mutual
/-- Typing judgment for one core fragment. -/
inductive HasType : CoreFragment → MiniType → Prop where
  /-- `0`: Bzdu. -/
  | zero :
      HasType .zero ⟨.B, { z := true, d := true, u := true }⟩

  /-- `1`: Bzu. -/
  | one :
      HasType .one ⟨.B, { z := true, u := true }⟩

  /-- pk_k(key): pushes key, then OP_CHECKSIG consumes sig+key, pushes 0/1.
      Type: Ko — needs one stack arg (the signature), nonzero, dissatisfiable, unit.
      BIP 379: K, o, n, d, u -/
  | pk_k : (key : PubKey) →
      HasType (.pk_k key) ⟨.K, {
        o := true, n := true, d := true, u := true
      }⟩

  /-- pk_h(key): OP_DUP OP_HASH160 <hash> OP_EQUALVERIFY.
      Type: Kndu. -/
  | pk_h : (key : PubKey) →
      HasType (.pk_h key) ⟨.K, {
        n := true, d := true, u := true
      }⟩

  /-- `older(n)`: Bz, timelock check fragment. -/
  | older : (n : Nat) →
      HasType (.older n) ⟨.B, { z := true }⟩

  /-- `after(n)`: Bz, timelock check fragment. -/
  | after : (n : Nat) →
      HasType (.after n) ⟨.B, { z := true }⟩

  /-- Hash preimage fragments are Bondu. -/
  | sha256 : (hash : Hash256) →
      HasType (.sha256 hash) ⟨.B, {
        o := true, n := true, d := true, u := true
      }⟩

  /-- Hash preimage fragments are Bondu. -/
  | hash256 : (hash : Hash256) →
      HasType (.hash256 hash) ⟨.B, {
        o := true, n := true, d := true, u := true
      }⟩

  /-- Hash preimage fragments are Bondu. -/
  | ripemd160 : (hash : Hash160) →
      HasType (.ripemd160 hash) ⟨.B, {
        o := true, n := true, d := true, u := true
      }⟩

  /-- Hash preimage fragments are Bondu. -/
  | hash160 : (hash : Hash160) →
      HasType (.hash160 hash) ⟨.B, {
        o := true, n := true, d := true, u := true
      }⟩

  /-- and_v(X,Y): [X] [Y] where X is V-type.
      X executes (V: succeeds silently or aborts), then Y executes.
      Result type = Y's base type; modifiers propagate.
      BIP 379: and_v type = Y.base, z=X.z∧Y.z, o=X.z∧Y.o ∨ X.o∧Y.z,
               n=X.n∨(X.z∧Y.n), u=Y.u -/
  | and_v : {X Y : CoreFragment} → {modsX : CorrectnessModifiers} → {tyY : MiniType} →
      HasType X ⟨.V, modsX⟩ →
      HasType Y tyY →
      branchBase tyY.base →
      HasType (.and_v X Y) ⟨tyY.base, {
        z := modsX.z && tyY.mods.z
        o := (modsX.z && tyY.mods.o) || (modsX.o && tyY.mods.z)
        n := modsX.n || (modsX.z && tyY.mods.n)
        d := false  -- and_v is never dissatisfiable (V-type X aborts on failure)
        u := tyY.mods.u
      }⟩

  /-- and_b(X,Y): [X] [Y] OP_BOOLAND, with X:B and Y:W. -/
  | and_b : {X Y : CoreFragment} → {modsX modsY : CorrectnessModifiers} →
      HasType X ⟨.B, modsX⟩ →
      HasType Y ⟨.W, modsY⟩ →
      HasType (.and_b X Y) ⟨.B, {
        z := modsX.z && modsY.z
        o := (modsX.z && modsY.o) || (modsX.o && modsY.z)
        n := modsX.n || (modsX.z && modsY.n)
        d := modsX.d && modsY.d
        u := true
      }⟩

  /-- or_b(X,Y): [X] [Y] OP_BOOLOR. Both must be dissatisfiable.
      BIP 379: B, X:Bd, Y:Wd → result z=X.z∧Y.z,
               o=X.z∧Y.o ∨ X.o∧Y.z, d/u set. -/
  | or_b : {X Y : CoreFragment} → {modsX modsY : CorrectnessModifiers} →
      HasType X ⟨.B, modsX⟩ →
      modsX.d = true →
      HasType Y ⟨.W, modsY⟩ →
      modsY.d = true →
      HasType (.or_b X Y) ⟨.B, {
        z := modsX.z && modsY.z
        o := (modsX.z && modsY.o) || (modsX.o && modsY.z)
        n := false
        d := true
        u := true
      }⟩

  /-- or_c(X,Y): [X] OP_NOTIF [Y] OP_ENDIF, with X:Bdu and Y:V. -/
  | or_c : {X Y : CoreFragment} → {modsX modsY : CorrectnessModifiers} →
      HasType X ⟨.B, modsX⟩ →
      modsX.d = true → modsX.u = true →
      HasType Y ⟨.V, modsY⟩ →
      HasType (.or_c X Y) ⟨.V, {
        z := modsX.z && modsY.z
        o := modsX.o && modsY.z
        n := false
        d := false
        u := false
      }⟩

  /-- or_d(X,Y): [X] OP_IFDUP OP_NOTIF [Y] OP_ENDIF, with X:Bdu and Y:B. -/
  | or_d : {X Y : CoreFragment} → {modsX modsY : CorrectnessModifiers} →
      HasType X ⟨.B, modsX⟩ →
      modsX.d = true → modsX.u = true →
      HasType Y ⟨.B, modsY⟩ →
      HasType (.or_d X Y) ⟨.B, {
        z := modsX.z && modsY.z
        o := modsX.o && modsY.z
        n := false
        d := modsY.d
        u := modsY.u
      }⟩

  /-- or_i(X,Y): OP_IF [X] OP_ELSE [Y] OP_ENDIF. Both branches have the same
      B/K/V base type. -/
  | or_i : {X Y : CoreFragment} → {tyX tyY : MiniType} →
      HasType X tyX →
      HasType Y tyY →
      branchBase tyX.base →
      tyX.base = tyY.base →
      HasType (.or_i X Y) ⟨tyX.base, {
        z := false
        o := tyX.mods.z && tyY.mods.z
        n := false
        d := tyX.mods.d || tyY.mods.d
        u := tyX.mods.u && tyY.mods.u
      }⟩

  /-- andor(X,Y,Z): [X] OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF, with X:Bdu and
      Y/Z sharing a B/K/V base type. -/
  | andor : {X Y Z : CoreFragment} →
      {modsX : CorrectnessModifiers} → {tyY tyZ : MiniType} →
      HasType X ⟨.B, modsX⟩ →
      modsX.d = true → modsX.u = true →
      HasType Y tyY →
      HasType Z tyZ →
      branchBase tyY.base →
      tyY.base = tyZ.base →
      HasType (.andor X Y Z) ⟨tyY.base, {
        z := modsX.z && tyY.mods.z && tyZ.mods.z
        o := (modsX.z && tyY.mods.o && tyZ.mods.o) ||
          (modsX.o && tyY.mods.z && tyZ.mods.z)
        n := false
        d := tyZ.mods.d
        u := tyY.mods.u && tyZ.mods.u
      }⟩

  /-- Wrapper `c`: [X] OP_CHECKSIG. Converts K to B.
      BIP 379: c(X:K) → B, modifiers: o=X.o, n=X.n, d=X.d, u=true -/
  | c_wrap : {X : CoreFragment} → {modsX : CorrectnessModifiers} →
      HasType X ⟨.K, modsX⟩ →
      HasType (.c X) ⟨.B, {
        z := false
        o := modsX.o
        n := modsX.n
        d := modsX.d
        u := true
      }⟩

  /-- Wrapper `v`: [X] OP_VERIFY. Converts B to V.
      BIP 379: v(X:B) → V, modifiers: z=X.z, o=X.o, n=X.n, f=true -/
  | v_wrap : {X : CoreFragment} → {modsX : CorrectnessModifiers} →
      HasType X ⟨.B, modsX⟩ →
      HasType (.v X) ⟨.V, {
        z := modsX.z
        o := modsX.o
        n := modsX.n
        d := false
        u := false
      }⟩

  /-- Wrapper `a`: OP_TOALTSTACK [X] OP_FROMALTSTACK. Converts B to W.
      BIP 379: a(X:B) → W -/
  | a_wrap : {X : CoreFragment} → {modsX : CorrectnessModifiers} →
      HasType X ⟨.B, modsX⟩ →
      HasType (.a X) ⟨.W, {
        z := false
        o := false
        n := false
        d := modsX.d
        u := modsX.u
      }⟩

  /-- Wrapper `s`: OP_SWAP [X]. Converts Bo to W.
      BIP 379: s(X:Bo) → W -/
  | s_wrap : {X : CoreFragment} → {modsX : CorrectnessModifiers} →
      HasType X ⟨.B, modsX⟩ →
      modsX.o = true →
      HasType (.s X) ⟨.W, {
        z := false
        o := false
        n := false
        d := modsX.d
        u := modsX.u
      }⟩

  /-- Wrapper `d`: OP_DUP OP_IF [X] OP_ENDIF. Converts Vz to Bondu, except
      the context-free model does not assert the Tapscript-only `u` modifier. -/
  | d_wrap : {X : CoreFragment} → {modsX : CorrectnessModifiers} →
      HasType X ⟨.V, modsX⟩ →
      modsX.z = true →
      HasType (.d X) ⟨.B, {
        z := false
        o := true
        n := true
        d := true
        u := false
      }⟩

  /-- Wrapper `j`: OP_SIZE OP_0NOTEQUAL OP_IF [X] OP_ENDIF. Keeps B behavior
      behind an explicit non-empty witness check. -/
  | j_wrap : {X : CoreFragment} → {modsX : CorrectnessModifiers} →
      HasType X ⟨.B, modsX⟩ →
      modsX.n = true →
      HasType (.j X) ⟨.B, {
        z := false
        o := modsX.o
        n := true
        d := true
        u := modsX.u
      }⟩

  /-- Wrapper `n`: [X] OP_0NOTEQUAL. Converts B to B with unit success. -/
  | n_wrap : {X : CoreFragment} → {modsX : CorrectnessModifiers} →
      HasType X ⟨.B, modsX⟩ →
      HasType (.n X) ⟨.B, {
        z := modsX.z
        o := modsX.o
        n := modsX.n
        d := modsX.d
        u := true
      }⟩

  /-- `thresh(k, X1, ..., Xn)`: first child is Bdu; remaining children are Wdu. -/
  | thresh : {k : Nat} → {X : CoreFragment} → {Xs : List CoreFragment} →
      {modsX : CorrectnessModifiers} → {restTypes : List MiniType} →
      HasType X ⟨.B, modsX⟩ →
      modsX.d = true → modsX.u = true →
      HasTypeList Xs restTypes →
      thresholdRestTypes restTypes →
      1 ≤ k → k ≤ (X :: Xs).length →
      HasType (.thresh k (X :: Xs)) ⟨.B, {
        z := CorrectnessModifiers.allZ (modsX :: MiniType.modifiers restTypes)
        o := CorrectnessModifiers.oneOWithRestZ (modsX :: MiniType.modifiers restTypes)
        n := false
        d := true
        u := true
      }⟩

  /-- Legacy multisig is Bndu. Key-count and context restrictions are handled by
      validation; typing records the stack behavior. -/
  | multi : (k : Nat) → (keys : List PubKey) →
      1 ≤ k → k ≤ keys.length →
      HasType (.multi k keys) ⟨.B, {
        z := false
        o := false
        n := true
        d := true
        u := true
      }⟩

  /-- Tapscript CHECKSIGADD multisig is Bdu. -/
  | multi_a : (k : Nat) → (keys : List PubKey) →
      1 ≤ k → k ≤ keys.length →
      HasType (.multi_a k keys) ⟨.B, {
        z := false
        o := false
        n := false
        d := true
        u := true
      }⟩

/-- Pointwise typing for nested fragment lists, used by `thresh`. -/
inductive HasTypeList : List CoreFragment → List MiniType → Prop where
  | nil : HasTypeList [] []
  | cons : {fragment : CoreFragment} → {ty : MiniType} →
      {fragments : List CoreFragment} → {types : List MiniType} →
      HasType fragment ty →
      HasTypeList fragments types →
      HasTypeList (fragment :: fragments) (ty :: types)
end

/-- A core AST fragment is well-typed if there exists some type for it. -/
def wellTyped (f : CoreFragment) : Prop := ∃ ty, HasType f ty

/-- A typed `thresh` fragment always carries a nonempty child list. The raw AST
    and compiler are total over lists, but the typing rule is the side condition
    that excludes `thresh(k, [])` from well-typed Miniscript. -/
theorem typed_thresh_has_children {k : Nat} {fragments : List CoreFragment}
    {ty : MiniType} :
    HasType (.thresh k fragments) ty → ∃ X Xs, fragments = X :: Xs := by
  intro h
  cases h with
  | thresh => exact ⟨_, _, rfl⟩

/-- A typed `multi_a` fragment always carries a nonempty key list because the
    typing rule requires `1 ≤ k ≤ keys.length`. This is the theorem-level side
    condition that justifies `compileCheckSigAdd`'s total empty-list fallback. -/
theorem typed_multi_a_has_keys {k : Nat} {keys : List PubKey} {ty : MiniType} :
    HasType (.multi_a k keys) ty → keys ≠ [] := by
  intro h
  cases h with
  | multi_a k keys hk hle =>
      intro hnil
      rw [hnil] at hle
      have hle0 : k ≤ 0 := by simpa using hle
      exact Nat.not_succ_le_zero 0 (Nat.le_trans hk hle0)

/-- Sanity check: the singleton `multi_a` case is constructible when the key-count
    side condition is satisfied. -/
example : HasType (.multi_a 1 [ByteArray.empty])
    ⟨.B, { d := true, u := true }⟩ := by
  exact HasType.multi_a 1 [ByteArray.empty] (by decide) (by decide)

/-- Sanity check: singleton `thresh` is constructible and uses the nonempty-list
    typing rule rather than the compiler's raw-list fallback. -/
example : HasType (.thresh 1 [.zero])
    ⟨.B, { z := true, d := true, u := true }⟩ := by
  exact HasType.thresh HasType.zero rfl rfl HasTypeList.nil trivial
    (by decide) (by decide)

end LeanMiniscript.Miniscript
