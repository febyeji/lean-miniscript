import LeanMiniscript.Miniscript.SurfaceParser
import LeanMiniscript.Miniscript.SurfaceParserProofs.RawParser
import LeanMiniscript.Miniscript.SurfaceParserProofs.Atoms

namespace LeanMiniscript.Miniscript

namespace SurfaceParser

/-!
# Surface parser proofs: canonical wrappers and leaf elaboration

Canonical wrapper chains and elaboration correctness for leaf fragments and
fixed-arity calls of canonical surface expressions.

Some helpers here were `private` in the former single-file `SurfaceParserProofs`
module. They are visible only so that sibling submodules can use them; treat
them as internal proof helpers, not stable API.
-/

def CanonicalWrapper (wrapper : Char) : Prop :=
  wrapper = 'a' ∨ wrapper = 's' ∨ wrapper = 'c' ∨ wrapper = 'd' ∨
    wrapper = 'v' ∨ wrapper = 'j' ∨ wrapper = 'n' ∨ wrapper = 't' ∨
    wrapper = 'l' ∨ wrapper = 'u'

def CanonicalWrappers (name : String) : Prop :=
  ∀ wrapper ∈ name.toList, CanonicalWrapper wrapper

def wrapSurface : Char → SurfaceFragment → SurfaceFragment
  | 'a', fragment => .core (.a (desugar fragment))
  | 's', fragment => .core (.s (desugar fragment))
  | 'c', fragment => .core (.c (desugar fragment))
  | 'd', fragment => .core (.d (desugar fragment))
  | 'v', fragment => .core (.v (desugar fragment))
  | 'j', fragment => .core (.j (desugar fragment))
  | 'n', fragment => .core (.n (desugar fragment))
  | 't', fragment => .t fragment
  | 'l', fragment => .l fragment
  | 'u', fragment => .u fragment
  | _, fragment => fragment

def wrapSurfaceChain (name : String)
    (inner : SurfaceFragment) : SurfaceFragment :=
  name.toList.foldr wrapSurface inner

private theorem applyWrapper_of_canonical
    (position : Nat) (wrapper : Char) (inner : SurfaceFragment)
    (hCanonical : CanonicalWrapper wrapper) :
    applyWrapper position wrapper inner = .ok (wrapSurface wrapper inner) := by
  rcases hCanonical with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> rfl

private theorem applyWrapperChain_of_canonical
    (position : Nat) (name : String) (inner : SurfaceFragment)
    (hCanonical : CanonicalWrappers name) :
    applyWrapperChain position name inner =
      .ok (wrapSurfaceChain name inner) := by
  unfold applyWrapperChain wrapSurfaceChain CanonicalWrappers at *
  generalize name.toList = wrappers at hCanonical ⊢
  induction wrappers with
  | nil => rfl
  | cons wrapper wrappers ih =>
      have hWrapper := hCanonical wrapper (by simp)
      have hWrappers : ∀ candidate ∈ wrappers,
          CanonicalWrapper candidate := by
        intro candidate hMem
        exact hCanonical candidate (by simp [hMem])
      rw [List.foldrM_cons, ih hWrappers]
      exact applyWrapper_of_canonical position wrapper _ hWrapper

theorem wrapSurfaceChain_append
    (first second : String) (inner : SurfaceFragment) :
    wrapSurfaceChain (first ++ second) inner =
      wrapSurfaceChain first (wrapSurfaceChain second inner) := by
  simp [wrapSurfaceChain, String.toList_append, List.foldr_append]

theorem canonicalWrappers_append_char
    (wrappers : String) (wrapper : Char)
    (hWrappers : CanonicalWrappers wrappers)
    (hWrapper : CanonicalWrapper wrapper) :
    CanonicalWrappers (wrappers ++ String.ofList [wrapper]) := by
  intro candidate hMem
  simp only [String.toList_append, String.toList_ofList,
    List.mem_append, List.mem_singleton] at hMem
  rcases hMem with hMem | rfl
  · exact hWrappers candidate hMem
  · exact hWrapper

private theorem canonicalWrapper_atomCharSafe (wrapper : Char)
    (hCanonical : CanonicalWrapper wrapper) :
    SurfaceText.isSpace wrapper = false ∧
      SurfaceText.isPunctuation wrapper = false := by
  rcases hCanonical with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> decide

private theorem atomSafe_of_canonicalWrappers
    (wrappers : String) (hNonempty : wrappers ≠ "")
    (hCanonical : CanonicalWrappers wrappers) :
    SurfaceText.AtomSafe wrappers := by
  constructor
  · simpa using hNonempty
  · intro wrapper hMem
    exact canonicalWrapper_atomCharSafe wrapper
      (hCanonical wrapper hMem)


private def CanonicalExprElaborates (context : ScriptContext)
    (expr : SurfaceText.Expr) (fragment : SurfaceFragment) : Prop :=
  ∀ (fuel : Nat) (raw : RawSurfaceExpr),
    raw.toExpr = expr → expr.lexemes.length < fuel →
      elaborateRawFuel context resolveHexKey fuel raw = .ok fragment

def CanonicalExprCorrect (context : ScriptContext)
    (expr : SurfaceText.Expr) (fragment : SurfaceFragment) : Prop :=
  expr.AtomsSafe ∧ CanonicalExprElaborates context expr fragment

theorem canonicalExprCorrect_prependWrappers
    (context : ScriptContext) (wrappers : String)
    (body : SurfaceText.Expr) (fragment : SurfaceFragment)
    (hWrappers : CanonicalWrappers wrappers)
    (hBody : CanonicalExprCorrect context body fragment) :
    CanonicalExprCorrect context
      (SurfaceText.prependWrappers wrappers body)
      (wrapSurfaceChain wrappers fragment) := by
  constructor
  · by_cases hEmpty : wrappers.isEmpty
    · have hWrappersEmpty : wrappers = "" := String.isEmpty_iff.mp hEmpty
      subst wrappers
      simpa [SurfaceText.prependWrappers] using hBody.1
    · have hNonempty : wrappers ≠ "" := by
        intro hWrappersEmpty
        subst wrappers
        simp at hEmpty
      rw [SurfaceText.prependWrappers, if_neg hEmpty]
      unfold SurfaceText.Expr.AtomsSafe
      exact ⟨atomSafe_of_canonicalWrappers wrappers hNonempty hWrappers,
        hBody.1⟩
  · intro fuel raw hRaw hFuel
    by_cases hEmpty : wrappers.isEmpty
    · have hWrappersEmpty : wrappers = "" := String.isEmpty_iff.mp hEmpty
      subst wrappers
      simpa [SurfaceText.prependWrappers, wrapSurfaceChain] using
        hBody.2 fuel raw (by
          simpa [SurfaceText.prependWrappers] using hRaw) (by
          simpa [SurfaceText.prependWrappers] using hFuel)
    · cases raw with
      | atom position value =>
          simp [RawSurfaceExpr.toExpr, SurfaceText.prependWrappers, hEmpty]
            at hRaw
      | call position name arguments =>
          simp [RawSurfaceExpr.toExpr, SurfaceText.prependWrappers, hEmpty]
            at hRaw
      | wrapper position name inner =>
          simp only [RawSurfaceExpr.toExpr, SurfaceText.prependWrappers,
            hEmpty] at hRaw
          cases hRaw
          cases fuel with
          | zero =>
              simp at hFuel
          | succ fuel =>
              have hInnerFuel :
                  (SurfaceText.Expr.lexemes inner.toExpr).length < fuel := by
                simp [SurfaceText.prependWrappers, hEmpty,
                  SurfaceText.Expr.lexemes] at hFuel
                omega
              simp only [elaborateRawFuel]
              rw [hBody.2 fuel inner rfl hInnerFuel]
              exact applyWrapperChain_of_canonical position wrappers fragment
                hWrappers

private theorem canonicalExprCorrect_atom
    (context : ScriptContext) (value : String) (fragment : SurfaceFragment)
    (hSafe : SurfaceText.AtomSafe value)
    (hElaborate : ∀ (fuel position : Nat),
      (SurfaceText.Expr.atom value).lexemes.length < fuel →
        elaborateRawFuel context resolveHexKey fuel (.atom position value) =
          .ok fragment) :
    CanonicalExprCorrect context (.atom value) fragment := by
  constructor
  · unfold SurfaceText.Expr.AtomsSafe
    exact hSafe
  · intro fuel raw hRaw hFuel
    cases raw with
    | atom position rawValue =>
        simp only [RawSurfaceExpr.toExpr] at hRaw
        cases hRaw
        exact hElaborate fuel position hFuel
    | wrapper => simp [RawSurfaceExpr.toExpr] at hRaw
    | call => simp [RawSurfaceExpr.toExpr] at hRaw

theorem canonicalExprCorrect_call
    (context : ScriptContext) (name : String)
    (arguments : List SurfaceText.Expr) (fragment : SurfaceFragment)
    (hNameSafe : SurfaceText.AtomSafe name)
    (hArgumentsSafe : ∀ argument ∈ arguments, argument.AtomsSafe)
    (hElaborate : ∀ (fuel position : Nat)
      (rawArguments : List RawSurfaceExpr),
      rawArguments.map RawSurfaceExpr.toExpr = arguments →
      (SurfaceText.Expr.call name arguments).lexemes.length < fuel →
        elaborateRawFuel context resolveHexKey fuel
          (.call position name rawArguments) = .ok fragment) :
    CanonicalExprCorrect context (.call name arguments) fragment := by
  constructor
  · unfold SurfaceText.Expr.AtomsSafe
    exact ⟨hNameSafe, hArgumentsSafe⟩
  · intro fuel raw hRaw hFuel
    cases raw with
    | atom => simp [RawSurfaceExpr.toExpr] at hRaw
    | wrapper => simp [RawSurfaceExpr.toExpr] at hRaw
    | call position rawName rawArguments =>
        simp only [RawSurfaceExpr.toExpr] at hRaw
        cases hRaw
        exact hElaborate fuel position rawArguments rfl hFuel

theorem rawExprMap_eq_cons
    (raws : List RawSurfaceExpr) (expr : SurfaceText.Expr)
    (exprs : List SurfaceText.Expr)
    (hMap : raws.map RawSurfaceExpr.toExpr = expr :: exprs) :
    ∃ raw rest, raws = raw :: rest ∧ raw.toExpr = expr ∧
      rest.map RawSurfaceExpr.toExpr = exprs := by
  cases raws with
  | nil => simp at hMap
  | cons raw rest =>
      simp only [List.map_cons, List.cons.injEq] at hMap
      exact ⟨raw, rest, rfl, hMap.1, hMap.2⟩

theorem rawExprMap_eq_nil (raws : List RawSurfaceExpr)
    (hMap : raws.map RawSurfaceExpr.toExpr = []) : raws = [] := by
  cases raws <;> simp_all

theorem rawExprMap_eq_singleton
    (raws : List RawSurfaceExpr) (expr : SurfaceText.Expr)
    (hMap : raws.map RawSurfaceExpr.toExpr = [expr]) :
    ∃ raw, raws = [raw] ∧ raw.toExpr = expr := by
  obtain ⟨raw, rest, rfl, hRaw, hRest⟩ :=
    rawExprMap_eq_cons raws expr [] hMap
  have : rest = [] := rawExprMap_eq_nil rest hRest
  subst rest
  exact ⟨raw, rfl, hRaw⟩

theorem rawExprMap_eq_pair
    (raws : List RawSurfaceExpr) (first second : SurfaceText.Expr)
    (hMap : raws.map RawSurfaceExpr.toExpr = [first, second]) :
    ∃ firstRaw secondRaw,
      raws = [firstRaw, secondRaw] ∧
        firstRaw.toExpr = first ∧ secondRaw.toExpr = second := by
  obtain ⟨firstRaw, rest, rfl, hFirst, hRest⟩ :=
    rawExprMap_eq_cons raws first [second] hMap
  obtain ⟨secondRaw, hRest, hSecond⟩ :=
    rawExprMap_eq_singleton rest second hRest
  subst rest
  exact ⟨firstRaw, secondRaw, rfl, hFirst, hSecond⟩

private theorem rawExprMap_eq_triple
    (raws : List RawSurfaceExpr) (first second third : SurfaceText.Expr)
    (hMap : raws.map RawSurfaceExpr.toExpr = [first, second, third]) :
    ∃ firstRaw secondRaw thirdRaw,
      raws = [firstRaw, secondRaw, thirdRaw] ∧
        firstRaw.toExpr = first ∧ secondRaw.toExpr = second ∧
          thirdRaw.toExpr = third := by
  obtain ⟨firstRaw, rest, rfl, hFirst, hRest⟩ :=
    rawExprMap_eq_cons raws first [second, third] hMap
  obtain ⟨secondRaw, thirdRaw, hRest, hSecond, hThird⟩ :=
    rawExprMap_eq_pair rest second third hRest
  subst rest
  exact ⟨firstRaw, secondRaw, thirdRaw, rfl, hFirst, hSecond, hThird⟩

theorem canonicalWrappers_empty : CanonicalWrappers "" := by
  intro wrapper hMem
  simp at hMem

theorem canonicalExprCorrect_zero (context : ScriptContext) :
    CanonicalExprCorrect context (.atom "0") (.core .zero) := by
  apply canonicalExprCorrect_atom
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · intro fuel position hFuel
    cases fuel with
    | zero => simp at hFuel
    | succ fuel => simp [elaborateRawFuel]; rfl

theorem canonicalExprCorrect_one (context : ScriptContext) :
    CanonicalExprCorrect context (.atom "1") (.core .one) := by
  apply canonicalExprCorrect_atom
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · intro fuel position hFuel
    cases fuel with
    | zero => simp at hFuel
    | succ fuel => simp [elaborateRawFuel]; rfl

private theorem canonicalExprCorrect_unaryAtomCall
    (context : ScriptContext) (name token : String)
    (fragment : SurfaceFragment)
    (hNameSafe : SurfaceText.AtomSafe name)
    (hTokenSafe : SurfaceText.AtomSafe token)
    (hElaborate : ∀ (fuel callPosition atomPosition : Nat), 0 < fuel →
      elaborateRawFuel context resolveHexKey fuel
        (.call callPosition name [.atom atomPosition token]) = .ok fragment) :
    CanonicalExprCorrect context
      (.call name [.atom token]) fragment := by
  apply canonicalExprCorrect_call
  · exact hNameSafe
  · intro argument hMem
    simp only [List.mem_singleton] at hMem
    subst argument
    unfold SurfaceText.Expr.AtomsSafe
    exact hTokenSafe
  · intro fuel callPosition rawArguments hMap hFuel
    obtain ⟨raw, rfl, hRaw⟩ :=
      rawExprMap_eq_singleton rawArguments (.atom token) hMap
    cases raw with
    | atom atomPosition rawToken =>
        simp only [RawSurfaceExpr.toExpr] at hRaw
        cases hRaw
        exact hElaborate fuel callPosition atomPosition (by omega)
    | wrapper => simp [RawSurfaceExpr.toExpr] at hRaw
    | call => simp [RawSurfaceExpr.toExpr] at hRaw

private theorem canonicalExprCorrect_keyCall
    (context : ScriptContext) (name : String) (key : PubKey)
    (fragment : SurfaceFragment)
    (hValid : validResolvedPubKey context key)
    (hNameSafe : SurfaceText.AtomSafe name)
    (hElaborate : ∀ (fuel callPosition atomPosition : Nat), 0 < fuel →
      elaborateRawFuel context resolveHexKey fuel
        (.call callPosition name [.atom atomPosition (prettyPubKey key)]) =
          .ok fragment) :
    CanonicalExprCorrect context
      (.call name [.atom (prettyPubKey key)]) fragment := by
  apply canonicalExprCorrect_unaryAtomCall
  · exact hNameSafe
  · apply atomSafe_byteArrayHex
    cases context <;>
      simp_all [validResolvedPubKey, validCompressedPubKeyBytes, PubKey.size]
  · exact hElaborate

theorem canonicalExprCorrect_pk
    (context : ScriptContext) (key : PubKey)
    (hValid : validResolvedPubKey context key) :
    CanonicalExprCorrect context
      (.call "pk" [.atom (prettyPubKey key)]) (.pk key) := by
  apply canonicalExprCorrect_keyCall context "pk" key (.pk key) hValid
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          resolveKeyRaw_prettyPubKey context atomPosition key hValid]
        rfl

theorem canonicalExprCorrect_pkh
    (context : ScriptContext) (key : PubKey)
    (hValid : validResolvedPubKey context key) :
    CanonicalExprCorrect context
      (.call "pkh" [.atom (prettyPubKey key)]) (.pkh key) := by
  apply canonicalExprCorrect_keyCall context "pkh" key (.pkh key) hValid
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          resolveKeyRaw_prettyPubKey context atomPosition key hValid]
        rfl

theorem canonicalExprCorrect_pk_k
    (context : ScriptContext) (key : PubKey)
    (hValid : validResolvedPubKey context key) :
    CanonicalExprCorrect context
      (.call "pk_k" [.atom (prettyPubKey key)]) (.core (.pk_k key)) := by
  apply canonicalExprCorrect_keyCall context "pk_k" key (.core (.pk_k key))
    hValid
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          resolveKeyRaw_prettyPubKey context atomPosition key hValid]
        rfl

theorem canonicalExprCorrect_pk_h
    (context : ScriptContext) (key : PubKey)
    (hValid : validResolvedPubKey context key) :
    CanonicalExprCorrect context
      (.call "pk_h" [.atom (prettyPubKey key)]) (.core (.pk_h key)) := by
  apply canonicalExprCorrect_keyCall context "pk_h" key (.core (.pk_h key))
    hValid
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          resolveKeyRaw_prettyPubKey context atomPosition key hValid]
        rfl

theorem canonicalExprCorrect_older
    (context : ScriptContext) (value : Nat) :
    CanonicalExprCorrect context
      (.call "older" [.atom (toString value)]) (.core (.older value)) := by
  apply canonicalExprCorrect_unaryAtomCall
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · exact atomSafe_toString value
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel]
        simp only [unaryArgument]
        simp
        change (fun result => SurfaceFragment.core (.older result)) <$>
          parseNatRaw "a relative timelock"
            (.atom atomPosition (toString value)) = .ok (.core (.older value))
        rw [parseNatRaw_toString "a relative timelock" atomPosition value]
        rfl

theorem canonicalExprCorrect_after
    (context : ScriptContext) (value : Nat) :
    CanonicalExprCorrect context
      (.call "after" [.atom (toString value)]) (.core (.after value)) := by
  apply canonicalExprCorrect_unaryAtomCall
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · exact atomSafe_toString value
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel]
        simp only [unaryArgument]
        simp
        change (fun result => SurfaceFragment.core (.after result)) <$>
          parseNatRaw "an absolute timelock"
            (.atom atomPosition (toString value)) = .ok (.core (.after value))
        rw [parseNatRaw_toString "an absolute timelock" atomPosition value]
        rfl

theorem canonicalExprCorrect_sha256
    (context : ScriptContext) (hash : Hash256)
    (hValid : validHash256 hash) :
    CanonicalExprCorrect context
      (.call "sha256" [.atom (LeanMiniscript.Script.byteArrayHex hash.bytes)])
      (.core (.sha256 hash)) := by
  apply canonicalExprCorrect_unaryAtomCall
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · apply atomSafe_byteArrayHex
    unfold validHash256 Hash256.size at hValid
    omega
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          parseHashBytes_byteArrayHex "sha256" 32 atomPosition hash.bytes
            (by simpa [validHash256, Hash256.size] using hValid)]
        rfl

theorem canonicalExprCorrect_hash256
    (context : ScriptContext) (hash : Hash256)
    (hValid : validHash256 hash) :
    CanonicalExprCorrect context
      (.call "hash256" [.atom (LeanMiniscript.Script.byteArrayHex hash.bytes)])
      (.core (.hash256 hash)) := by
  apply canonicalExprCorrect_unaryAtomCall
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · apply atomSafe_byteArrayHex
    unfold validHash256 Hash256.size at hValid
    omega
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          parseHashBytes_byteArrayHex "hash256" 32 atomPosition hash.bytes
            (by simpa [validHash256, Hash256.size] using hValid)]
        rfl

theorem canonicalExprCorrect_ripemd160
    (context : ScriptContext) (hash : Hash160)
    (hValid : validHash160 hash) :
    CanonicalExprCorrect context
      (.call "ripemd160"
        [.atom (LeanMiniscript.Script.byteArrayHex hash.bytes)])
      (.core (.ripemd160 hash)) := by
  apply canonicalExprCorrect_unaryAtomCall
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · apply atomSafe_byteArrayHex
    unfold validHash160 Hash160.size at hValid
    omega
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          parseHashBytes_byteArrayHex "ripemd160" 20 atomPosition hash.bytes
            (by simpa [validHash160, Hash160.size] using hValid)]
        rfl

theorem canonicalExprCorrect_hash160
    (context : ScriptContext) (hash : Hash160)
    (hValid : validHash160 hash) :
    CanonicalExprCorrect context
      (.call "hash160" [.atom (LeanMiniscript.Script.byteArrayHex hash.bytes)])
      (.core (.hash160 hash)) := by
  apply canonicalExprCorrect_unaryAtomCall
  · simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
      SurfaceText.isPunctuation]
  · apply atomSafe_byteArrayHex
    unfold validHash160 Hash160.size at hValid
    omega
  · intro fuel callPosition atomPosition hFuel
    cases fuel with
    | zero => omega
    | succ fuel =>
        simp [elaborateRawFuel, unaryArgument,
          parseHashBytes_byteArrayHex "hash160" 20 atomPosition hash.bytes
            (by simpa [validHash160, Hash160.size] using hValid)]
        rfl

theorem canonicalExprCorrect_binaryCall
    (context : ScriptContext) (name : String)
    (firstExpr secondExpr : SurfaceText.Expr)
    (firstFragment secondFragment result : SurfaceFragment)
    (hNameSafe : SurfaceText.AtomSafe name)
    (hFirst : CanonicalExprCorrect context firstExpr firstFragment)
    (hSecond : CanonicalExprCorrect context secondExpr secondFragment)
    (hElaborate : ∀ (fuel callPosition : Nat)
      (firstRaw secondRaw : RawSurfaceExpr),
      elaborateRawFuel context resolveHexKey fuel firstRaw = .ok firstFragment →
      elaborateRawFuel context resolveHexKey fuel secondRaw = .ok secondFragment →
      elaborateRawFuel context resolveHexKey (fuel + 1)
        (.call callPosition name [firstRaw, secondRaw]) = .ok result) :
    CanonicalExprCorrect context
      (.call name [firstExpr, secondExpr]) result := by
  apply canonicalExprCorrect_call
  · exact hNameSafe
  · intro argument hMem
    simp at hMem
    rcases hMem with rfl | rfl
    · exact hFirst.1
    · exact hSecond.1
  · intro fuel callPosition rawArguments hMap hFuel
    obtain ⟨firstRaw, secondRaw, rfl, hFirstRaw, hSecondRaw⟩ :=
      rawExprMap_eq_pair rawArguments firstExpr secondExpr hMap
    cases fuel with
    | zero => simp at hFuel
    | succ fuel =>
        have hFirstFuel : firstExpr.lexemes.length < fuel := by
          simp [SurfaceText.Expr.lexemes, SurfaceText.argumentLexemes] at hFuel
          omega
        have hSecondFuel : secondExpr.lexemes.length < fuel := by
          simp [SurfaceText.Expr.lexemes, SurfaceText.argumentLexemes] at hFuel
          omega
        exact hElaborate fuel callPosition firstRaw secondRaw
          (hFirst.2 fuel firstRaw hFirstRaw hFirstFuel)
          (hSecond.2 fuel secondRaw hSecondRaw hSecondFuel)

theorem canonicalExprCorrect_ternaryCall
    (context : ScriptContext) (name : String)
    (firstExpr secondExpr thirdExpr : SurfaceText.Expr)
    (firstFragment secondFragment thirdFragment result : SurfaceFragment)
    (hNameSafe : SurfaceText.AtomSafe name)
    (hFirst : CanonicalExprCorrect context firstExpr firstFragment)
    (hSecond : CanonicalExprCorrect context secondExpr secondFragment)
    (hThird : CanonicalExprCorrect context thirdExpr thirdFragment)
    (hElaborate : ∀ (fuel callPosition : Nat)
      (firstRaw secondRaw thirdRaw : RawSurfaceExpr),
      elaborateRawFuel context resolveHexKey fuel firstRaw = .ok firstFragment →
      elaborateRawFuel context resolveHexKey fuel secondRaw = .ok secondFragment →
      elaborateRawFuel context resolveHexKey fuel thirdRaw = .ok thirdFragment →
      elaborateRawFuel context resolveHexKey (fuel + 1)
        (.call callPosition name [firstRaw, secondRaw, thirdRaw]) = .ok result) :
    CanonicalExprCorrect context
      (.call name [firstExpr, secondExpr, thirdExpr]) result := by
  apply canonicalExprCorrect_call
  · exact hNameSafe
  · intro argument hMem
    simp at hMem
    rcases hMem with rfl | rfl | rfl
    · exact hFirst.1
    · exact hSecond.1
    · exact hThird.1
  · intro fuel callPosition rawArguments hMap hFuel
    obtain ⟨firstRaw, secondRaw, thirdRaw, rfl, hFirstRaw, hSecondRaw,
      hThirdRaw⟩ :=
      rawExprMap_eq_triple rawArguments firstExpr secondExpr thirdExpr hMap
    cases fuel with
    | zero => simp at hFuel
    | succ fuel =>
        have hFirstFuel : firstExpr.lexemes.length < fuel := by
          simp [SurfaceText.Expr.lexemes, SurfaceText.argumentLexemes] at hFuel
          omega
        have hSecondFuel : secondExpr.lexemes.length < fuel := by
          simp [SurfaceText.Expr.lexemes, SurfaceText.argumentLexemes] at hFuel
          omega
        have hThirdFuel : thirdExpr.lexemes.length < fuel := by
          simp [SurfaceText.Expr.lexemes, SurfaceText.argumentLexemes] at hFuel
          omega
        exact hElaborate fuel callPosition firstRaw secondRaw thirdRaw
          (hFirst.2 fuel firstRaw hFirstRaw hFirstFuel)
          (hSecond.2 fuel secondRaw hSecondRaw hSecondFuel)
          (hThird.2 fuel thirdRaw hThirdRaw hThirdFuel)

def CanonicalExprListCorrect (context : ScriptContext)
    (exprs : List SurfaceText.Expr) (fragments : List SurfaceFragment) : Prop :=
  (∀ expr ∈ exprs, expr.AtomsSafe) ∧
    ∀ (fuel : Nat) (raws : List RawSurfaceExpr),
      raws.map RawSurfaceExpr.toExpr = exprs →
      (∀ expr ∈ exprs, expr.lexemes.length < fuel) →
        raws.mapM (elaborateRawFuel context resolveHexKey fuel) = .ok fragments

theorem lexemes_length_le_argumentLexemes_of_mem
    (expr : SurfaceText.Expr) (arguments : List SurfaceText.Expr)
    (hMem : expr ∈ arguments) :
    expr.lexemes.length ≤ (SurfaceText.argumentLexemes arguments).length := by
  induction arguments with
  | nil => simp at hMem
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp only [List.mem_singleton] at hMem
          subst expr
          simp [SurfaceText.argumentLexemes]
      | cons next rest =>
          simp only [List.mem_cons] at hMem
          rcases hMem with rfl | hMem
          · simp [SurfaceText.argumentLexemes]
          · have hMemTail : expr ∈ next :: rest := by simpa using hMem
            have hTail := ih hMemTail
            simp [SurfaceText.argumentLexemes] at hTail ⊢
            omega

theorem lexemes_length_lt_call_of_mem
    (name : String) (arguments : List SurfaceText.Expr)
    (expr : SurfaceText.Expr) (hMem : expr ∈ arguments) :
    expr.lexemes.length <
      (SurfaceText.Expr.call name arguments).lexemes.length := by
  have hLe := lexemes_length_le_argumentLexemes_of_mem expr arguments hMem
  simp [SurfaceText.Expr.lexemes]
  omega

theorem canonicalKeyListCorrect
    (context : ScriptContext) (keys : List PubKey)
    (hValid : CoreFragment.allKeysValid context keys) :
    (∀ expr ∈ keys.map (fun key => SurfaceText.Expr.atom (prettyPubKey key)),
      expr.AtomsSafe) ∧
    ∀ raws : List RawSurfaceExpr,
      raws.map RawSurfaceExpr.toExpr =
        keys.map (fun key => SurfaceText.Expr.atom (prettyPubKey key)) →
      raws.mapM (resolveKeyRaw context resolveHexKey) = .ok keys := by
  induction keys with
  | nil =>
      constructor
      · simp
      · intro raws hMap
        have : raws = [] := rawExprMap_eq_nil raws (by simpa using hMap)
        subst raws
        rfl
  | cons key keys ih =>
      simp only [CoreFragment.allKeysValid] at hValid
      have hKeyPositive : 0 < key.bytes.size := by
        cases context <;>
          simp_all [validResolvedPubKey, validCompressedPubKeyBytes, PubKey.size]
      have hTail := ih hValid.2
      constructor
      · intro expr hMem
        simp only [List.map_cons, List.mem_cons] at hMem
        rcases hMem with rfl | hMem
        · unfold SurfaceText.Expr.AtomsSafe
          exact atomSafe_byteArrayHex key.bytes hKeyPositive
        · exact hTail.1 expr hMem
      · intro raws hMap
        obtain ⟨raw, rest, rfl, hRaw, hRest⟩ :=
          rawExprMap_eq_cons raws (.atom (prettyPubKey key))
            (keys.map (fun tailKey => .atom (prettyPubKey tailKey))) hMap
        cases raw with
        | atom position token =>
            simp only [RawSurfaceExpr.toExpr] at hRaw
            cases hRaw
            simp only [List.mapM_cons]
            rw [resolveKeyRaw_prettyPubKey context position key hValid.1]
            rw [hTail.2 rest hRest]
            rfl
        | wrapper => simp [RawSurfaceExpr.toExpr] at hRaw
        | call => simp [RawSurfaceExpr.toExpr] at hRaw

end SurfaceParser

end LeanMiniscript.Miniscript
