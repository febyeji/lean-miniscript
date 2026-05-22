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

/-- Type modifier properties.
    These refine the base type with additional guarantees. -/
structure TypeModifiers where
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
  /-- f (forced): cannot be dissatisfied (always succeeds or aborts) -/
  f : Bool := false
  /-- e (expressive): if not f, then must be d -/
  e : Bool := false
  deriving Repr, DecidableEq, BEq

/-- A complete Miniscript type: base type + modifiers. -/
structure MiniType where
  base : BaseType
  mods : TypeModifiers
  deriving Repr

/-- Typing judgment: `HasType fragment ty` means a core AST fragment has type
    `ty`.

    BIP 379 type system: each fragment has a base type (B/V/K/W)
    and modifier properties (z, o, n, d, u, f, e).

    The current rules cover the first core constructors needed to make the
    AST-first path executable: leaves, selected connectives, and wrappers.

    TODO(theorem): extend `HasType` to every `CoreFragment` constructor before
    stating the full core type-soundness theorem. -/
inductive HasType : CoreFragment → MiniType → Prop where
  /-- pk_k(key): pushes key, then OP_CHECKSIG consumes sig+key, pushes 0/1.
      Type: Ko — needs one stack arg (the signature), nonzero, dissatisfiable, unit.
      BIP 379: K, o, n, d, u -/
  | pk_k : (key : PubKey) →
      HasType (.pk_k key) ⟨.K, { o := true, n := true, d := true, u := true }⟩

  /-- pk_h(key): OP_DUP OP_HASH160 <hash> OP_EQUALVERIFY OP_CHECKSIG.
      Type: Kond u — same as pk_k but needs key on stack too (still one arg net).
      BIP 379: K, o, n, d, u -/
  | pk_h : (key : PubKey) →
      HasType (.pk_h key) ⟨.K, { o := true, n := true, d := true, u := true }⟩

  /-- and_v(X,Y): [X] [Y] where X is V-type.
      X executes (V: succeeds silently or aborts), then Y executes.
      Result type = Y's base type; modifiers propagate.
      BIP 379: and_v type = Y.base, z=X.z∧Y.z, o=X.z∧Y.o ∨ X.o∧Y.z,
               n=X.n∨(X.z∧Y.n), u=Y.u, f=X.f∧Y.f (simplified subset here) -/
  | and_v : {X Y : CoreFragment} → {modsX : TypeModifiers} → {tyY : MiniType} →
      HasType X ⟨.V, modsX⟩ →
      HasType Y tyY →
      HasType (.and_v X Y) ⟨tyY.base, {
        z := modsX.z && tyY.mods.z
        o := (modsX.z && tyY.mods.o) || (modsX.o && tyY.mods.z)
        n := modsX.n || (modsX.z && tyY.mods.n)
        d := false  -- and_v is never dissatisfiable (V-type X aborts on failure)
        u := tyY.mods.u
        f := modsX.f && tyY.mods.f
        e := false
      }⟩

  /-- or_b(X,Y): [X] [Y] OP_BOOLOR. Both must be dissatisfiable.
      BIP 379: B, X:Bde, Y:Wde → result d=X.d∧Y.d, z=false,
               o=X.z∧Y.o ∨ X.o∧Y.z (simplified) -/
  | or_b : {X Y : CoreFragment} → {modsX modsY : TypeModifiers} →
      HasType X ⟨.B, modsX⟩ →
      modsX.d = true → modsX.e = true →
      HasType Y ⟨.W, modsY⟩ →
      modsY.d = true → modsY.e = true →
      HasType (.or_b X Y) ⟨.B, {
        z := false
        o := (modsX.z && modsY.o) || (modsX.o && modsY.z)
        n := modsX.n || modsY.n  -- simplified
        d := true
        u := modsX.u && modsY.u
        f := false
        e := true
      }⟩

  /-- Wrapper `c`: [X] OP_CHECKSIG. Converts K to B.
      BIP 379: c(X:K) → B, modifiers: o=X.o, n=X.n, d=X.d, u=true -/
  | c_wrap : {X : CoreFragment} → {modsX : TypeModifiers} →
      HasType X ⟨.K, modsX⟩ →
      HasType (.c X) ⟨.B, {
        z := false
        o := modsX.o
        n := modsX.n
        d := modsX.d
        u := true
        f := false
        e := false
      }⟩

  /-- Wrapper `v`: [X] OP_VERIFY. Converts B to V.
      BIP 379: v(X:B) → V, modifiers: z=X.z, o=X.o, n=X.n, f=true -/
  | v_wrap : {X : CoreFragment} → {modsX : TypeModifiers} →
      HasType X ⟨.B, modsX⟩ →
      HasType (.v X) ⟨.V, {
        z := modsX.z
        o := modsX.o
        n := modsX.n
        d := false
        u := false
        f := true
        e := false
      }⟩

  /-- Wrapper `a`: OP_TOALTSTACK [X] OP_FROMALTSTACK. Converts B to W.
      BIP 379: a(X:B) → W -/
  | a_wrap : {X : CoreFragment} → {modsX : TypeModifiers} →
      HasType X ⟨.B, modsX⟩ →
      HasType (.a X) ⟨.W, {
        z := false
        o := modsX.o  -- simplified
        n := modsX.n
        d := modsX.d
        u := modsX.u
        f := modsX.f
        e := modsX.e
      }⟩

  /-- Wrapper `s`: OP_SWAP [X]. Converts Bo to W.
      BIP 379: s(X:Bo) → W -/
  | s_wrap : {X : CoreFragment} → {modsX : TypeModifiers} →
      HasType X ⟨.B, modsX⟩ →
      modsX.o = true →
      HasType (.s X) ⟨.W, {
        z := false
        o := modsX.o
        n := modsX.n
        d := modsX.d
        u := modsX.u
        f := modsX.f
        e := modsX.e
      }⟩

/-- A core AST fragment is well-typed if there exists some type for it. -/
def wellTyped (f : CoreFragment) : Prop := ∃ ty, HasType f ty

end LeanMiniscript.Miniscript
