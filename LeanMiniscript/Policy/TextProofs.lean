import LeanMiniscript.Policy.Text
import LeanMiniscript.Miniscript.SurfaceParserProofs

/-! Canonical policy text round-trip proofs. -/

namespace LeanMiniscript.Policy

open LeanMiniscript.Miniscript
open LeanMiniscript.Miniscript.SurfaceParser
open LeanMiniscript.Script (byteArrayHex)

namespace Policy

mutual
  /-- Leaves that the hexadecimal printer and `parsePolicyHex` round-trip:
      32- or 33-byte keys, 32-byte SHA256/HASH256 digests, 20-byte
      RIPEMD160/HASH160 digests, and thresholds with at least one branch. -/
  def HexTextSafe : Policy → Prop
    | .key pubKey => pubKey.size = 32 ∨ pubKey.size = 33
    | .sha256 hash => hash.size = 32
    | .hash256 hash => hash.size = 32
    | .ripemd160 hash => hash.size = 20
    | .hash160 hash => hash.size = 20
    | .and left right => HexTextSafe left ∧ HexTextSafe right
    | .or _ left _ right => HexTextSafe left ∧ HexTextSafe right
    | .thresh _ subs => subs ≠ [] ∧ allHexTextSafe subs
    | _ => True

  /-- Every policy in a list is hexadecimal-text safe. -/
  def allHexTextSafe : List Policy → Prop
    | [] => True
    | sub :: subs => HexTextSafe sub ∧ allHexTextSafe subs
end

end Policy

namespace PolicyText

/-- A canonical expression elaborates to `policy` from every raw parse whose
    positions are forgotten to it, given enough fuel. -/
def Elaborates (expr : SurfaceText.Expr) (policy : Policy) : Prop :=
  ∀ (fuel : Nat) (raw : RawSurfaceExpr),
    raw.toExpr = expr → expr.lexemes.length < fuel →
      elaboratePolicyFuel resolveHexKey fuel raw = .ok policy

/-- Tokenization safety together with elaboration. -/
def Correct (expr : SurfaceText.Expr) (policy : Policy) : Prop :=
  expr.AtomsSafe ∧ Elaborates expr policy

/-- The head atom of a canonical expression contains no weight separator. -/
def HeadNoAt : SurfaceText.Expr → Prop
  | .atom value => '@' ∉ value.toList
  | .call name _ => '@' ∉ name.toList
  | .wrapper _ _ => False

theorem splitAtChar_of_not_mem (separator : Char) (chars : List Char)
    (hNot : separator ∉ chars) : splitAtChar separator chars = none := by
  induction chars with
  | nil => rfl
  | cons char chars ih =>
      simp only [List.mem_cons, not_or] at hNot
      simp [splitAtChar, Ne.symm hNot.1, ih hNot.2]

theorem splitAtChar_append (separator : Char) (before after : List Char)
    (hNot : separator ∉ before) :
    splitAtChar separator (before ++ separator :: after) = some (before, after) := by
  induction before with
  | nil => simp [splitAtChar]
  | cons char chars ih =>
      simp only [List.mem_cons, not_or] at hNot
      simp [splitAtChar, Ne.symm hNot.1, ih hNot.2]

theorem at_not_mem_toString (value : Nat) : '@' ∉ (toString value).toList := by
  have hNat := String.isNat_iff.mp (Nat.isNat_repr value)
  intro hMem
  rcases hNat.2.1 '@' hMem with hDigit | hUnderscore
  · simp [Char.isDigit] at hDigit
  · simp at hUnderscore

theorem stripWeight_weighted (position weight : Nat) (name : String)
    (hName : '@' ∉ name.toList) :
    stripWeight position
        (if weight = 1 then name else toString weight ++ "@" ++ name) =
      .ok (weight, name) := by
  by_cases hOne : weight = 1
  · subst weight
    simp [stripWeight, splitWeight, splitAtChar_of_not_mem _ _ hName]
    rfl
  · have hSplit : splitAtChar '@' (toString weight ++ "@" ++ name).toList =
        some ((toString weight).toList, name.toList) := by
      rw [String.toList_append, String.toList_append]
      have : ("@" : String).toList = ['@'] := by decide
      rw [this, List.append_assoc]
      exact splitAtChar_append '@' _ _ (at_not_mem_toString weight)
    have hNat : (toString weight).toNat? = some weight := Nat.toNat?_repr weight
    simp only [hOne, if_false, stripWeight, splitWeight]
    rw [hSplit]
    simp only [Option.map_some, String.ofList_toList, hNat]
    rfl

theorem weightedExpr_lexemes_length (weight : Nat) (expr : SurfaceText.Expr) :
    (weightedExpr weight expr).lexemes.length = expr.lexemes.length := by
  unfold weightedExpr
  split
  · rfl
  · cases expr <;> simp [SurfaceText.Expr.lexemes]

theorem atomSafe_weighted (weight : Nat) (name : String)
    (hName : SurfaceText.AtomSafe name) :
    SurfaceText.AtomSafe (toString weight ++ "@" ++ name) := by
  have hWeight := atomSafe_toString weight
  constructor
  · simp [String.toList_append]
  · intro char hMem
    simp only [String.toList_append, List.mem_append] at hMem
    rcases hMem with (hMem | hMem) | hMem
    · exact hWeight.2 char hMem
    · have : ("@" : String).toList = ['@'] := by decide
      rw [this, List.mem_singleton] at hMem
      subst char
      decide
    · exact hName.2 char hMem

theorem weightedExpr_atomsSafe (weight : Nat) (expr : SurfaceText.Expr)
    (hSafe : expr.AtomsSafe) : (weightedExpr weight expr).AtomsSafe := by
  unfold weightedExpr
  split
  · exact hSafe
  · cases expr with
    | atom value =>
        simp only [SurfaceText.Expr.AtomsSafe] at hSafe ⊢
        exact atomSafe_weighted weight value hSafe
    | wrapper name inner =>
        simp only [SurfaceText.Expr.AtomsSafe] at hSafe ⊢
        exact ⟨atomSafe_weighted weight name hSafe.1, hSafe.2⟩
    | call name arguments =>
        simp only [SurfaceText.Expr.AtomsSafe] at hSafe ⊢
        exact ⟨atomSafe_weighted weight name hSafe.1, hSafe.2⟩

/-- A raw parse of a weighted canonical branch strips back to the unweighted
    branch and its weight. -/
theorem stripRawWeight_weighted (weight : Nat) (expr : SurfaceText.Expr)
    (hHead : HeadNoAt expr) (raw : RawSurfaceExpr)
    (hRaw : raw.toExpr = weightedExpr weight expr) :
    ∃ stripped, stripRawWeight raw = .ok (weight, stripped) ∧
      stripped.toExpr = expr := by
  cases expr with
  | wrapper => exact absurd hHead id
  | atom value =>
      cases raw with
      | atom position rawValue =>
          refine ⟨.atom position value, ?_, by simp [RawSurfaceExpr.toExpr]⟩
          have hValue : rawValue =
              (if weight = 1 then value else toString weight ++ "@" ++ value) := by
            unfold weightedExpr at hRaw
            split at hRaw <;> simp_all [RawSurfaceExpr.toExpr]
          subst rawValue
          simp only [stripRawWeight, stripWeight_weighted position weight value hHead]
          rfl
      | wrapper => unfold weightedExpr at hRaw; split at hRaw <;> simp_all [RawSurfaceExpr.toExpr]
      | call => unfold weightedExpr at hRaw; split at hRaw <;> simp_all [RawSurfaceExpr.toExpr]
  | call name arguments =>
      cases raw with
      | call position rawName rawArguments =>
          refine ⟨.call position name rawArguments, ?_, ?_⟩
          · have hName : rawName =
                (if weight = 1 then name else toString weight ++ "@" ++ name) := by
              unfold weightedExpr at hRaw
              split at hRaw <;> simp_all [RawSurfaceExpr.toExpr]
            subst rawName
            simp only [stripRawWeight, stripWeight_weighted position weight name hHead]
            rfl
          · unfold weightedExpr at hRaw
            split at hRaw <;> simp_all [RawSurfaceExpr.toExpr]
      | wrapper => unfold weightedExpr at hRaw; split at hRaw <;> simp_all [RawSurfaceExpr.toExpr]
      | atom => unfold weightedExpr at hRaw; split at hRaw <;> simp_all [RawSurfaceExpr.toExpr]

theorem correct_atom (value : String) (policy : Policy)
    (hSafe : SurfaceText.AtomSafe value)
    (hElaborate : ∀ (fuel position : Nat),
      elaboratePolicyFuel resolveHexKey (fuel + 1) (.atom position value) =
        .ok policy) :
    Correct (.atom value) policy := by
  refine ⟨by simpa [SurfaceText.Expr.AtomsSafe] using hSafe, ?_⟩
  intro fuel raw hRaw hFuel
  cases raw with
  | atom position rawValue =>
      simp only [RawSurfaceExpr.toExpr, SurfaceText.Expr.atom.injEq] at hRaw
      subst rawValue
      cases fuel with
      | zero => simp at hFuel
      | succ fuel => exact hElaborate fuel position
  | wrapper => simp [RawSurfaceExpr.toExpr] at hRaw
  | call => simp [RawSurfaceExpr.toExpr] at hRaw

theorem correct_unaryAtomCall (name token : String) (policy : Policy)
    (hNameSafe : SurfaceText.AtomSafe name)
    (hTokenSafe : SurfaceText.AtomSafe token)
    (hElaborate : ∀ (fuel callPosition atomPosition : Nat),
      elaboratePolicyFuel resolveHexKey (fuel + 1)
        (.call callPosition name [.atom atomPosition token]) = .ok policy) :
    Correct (.call name [.atom token]) policy := by
  refine ⟨?_, ?_⟩
  · simp only [SurfaceText.Expr.AtomsSafe]
    refine ⟨hNameSafe, ?_⟩
    intro argument hMem
    simp only [List.mem_singleton] at hMem
    subst argument
    simpa [SurfaceText.Expr.AtomsSafe] using hTokenSafe
  · intro fuel raw hRaw hFuel
    cases raw with
    | atom => simp [RawSurfaceExpr.toExpr] at hRaw
    | wrapper => simp [RawSurfaceExpr.toExpr] at hRaw
    | call callPosition rawName rawArguments =>
        simp only [RawSurfaceExpr.toExpr, SurfaceText.Expr.call.injEq] at hRaw
        obtain ⟨rfl, hMap⟩ := hRaw
        obtain ⟨argument, rfl, hArgument⟩ :=
          rawExprMap_eq_singleton rawArguments (.atom token) hMap
        cases argument with
        | atom atomPosition rawToken =>
            simp only [RawSurfaceExpr.toExpr, SurfaceText.Expr.atom.injEq]
              at hArgument
            subst rawToken
            cases fuel with
            | zero => simp at hFuel
            | succ fuel => exact hElaborate fuel callPosition atomPosition
        | wrapper => simp [RawSurfaceExpr.toExpr] at hArgument
        | call => simp [RawSurfaceExpr.toExpr] at hArgument

theorem parseNatRaw_repr (role : String) (position value : Nat) :
    parseNatRaw role (.atom position value.repr) = .ok value :=
  parseNatRaw_toString role position value

theorem atomSafe_literal_pk : SurfaceText.AtomSafe "pk" := by
  simp [SurfaceText.AtomSafe, SurfaceText.isSpace, SurfaceText.isPunctuation]

theorem atomSafe_hash (bytes : ByteArray) (size : Nat) (hSize : bytes.size = size)
    (hPositive : 0 < size) : SurfaceText.AtomSafe (byteArrayHex bytes) :=
  atomSafe_byteArrayHex bytes (by omega)

end PolicyText

open PolicyText in
mutual

/-- Every hexadecimal-text-safe policy prints to tokenizable text whose raw
    parse elaborates back to the same policy. -/
theorem policyText_correct :
    (policy : Policy) → policy.HexTextSafe →
      Correct (policy.toExprWith prettyPubKey) policy ∧
        HeadNoAt (policy.toExprWith prettyPubKey)
  | .unsatisfiable, _ => by
      refine ⟨correct_atom _ _ ?_ ?_, ?_⟩
      · simp [SurfaceText.AtomSafe, SurfaceText.isSpace, SurfaceText.isPunctuation]
      · intro fuel position
        simp [elaboratePolicyFuel]
        rfl
      · simp [HeadNoAt, Policy.toExprWith]
  | .trivial, _ => by
      refine ⟨correct_atom _ _ ?_ ?_, ?_⟩
      · simp [SurfaceText.AtomSafe, SurfaceText.isSpace, SurfaceText.isPunctuation]
      · intro fuel position
        simp [elaboratePolicyFuel]
        rfl
      · simp [HeadNoAt, Policy.toExprWith]
  | .key pubKey, hSafe => by
      refine ⟨correct_unaryAtomCall _ _ _ atomSafe_literal_pk ?_ ?_, ?_⟩
      · apply atomSafe_byteArrayHex
        simp only [Policy.HexTextSafe, PubKey.size] at hSafe
        omega
      · intro fuel callPosition atomPosition
        have hResolve := resolveHexKey_prettyPubKey pubKey hSafe
        simp [elaboratePolicyFuel, unaryArgument, resolvePolicyKeyRaw, rawAtom,
          hResolve]
        rfl
      · simp [HeadNoAt, Policy.toExprWith]
  | .after n, _ => by
      refine ⟨correct_unaryAtomCall _ _ _ ?_ (atomSafe_toString n) ?_, ?_⟩
      · simp [SurfaceText.AtomSafe, SurfaceText.isSpace, SurfaceText.isPunctuation]
      · intro fuel callPosition atomPosition
        simp [elaboratePolicyFuel, unaryArgument,
          PolicyText.parseNatRaw_repr]
        rfl
      · simp [HeadNoAt, Policy.toExprWith]
  | .older n, _ => by
      refine ⟨correct_unaryAtomCall _ _ _ ?_ (atomSafe_toString n) ?_, ?_⟩
      · simp [SurfaceText.AtomSafe, SurfaceText.isSpace, SurfaceText.isPunctuation]
      · intro fuel callPosition atomPosition
        simp [elaboratePolicyFuel, unaryArgument,
          PolicyText.parseNatRaw_repr]
        rfl
      · simp [HeadNoAt, Policy.toExprWith]
  | .sha256 hash, hSafe => by
      simp only [Policy.HexTextSafe, Hash256.size] at hSafe
      refine ⟨correct_unaryAtomCall _ _ _ ?_
        (atomSafe_byteArrayHex _ (by omega)) ?_, ?_⟩
      · simp [SurfaceText.AtomSafe, SurfaceText.isSpace, SurfaceText.isPunctuation]
      · intro fuel callPosition atomPosition
        simp [elaboratePolicyFuel, unaryArgument,
          parseHashBytes_byteArrayHex _ _ _ _ hSafe]
        rfl
      · simp [HeadNoAt, Policy.toExprWith]
  | .hash256 hash, hSafe => by
      simp only [Policy.HexTextSafe, Hash256.size] at hSafe
      refine ⟨correct_unaryAtomCall _ _ _ ?_
        (atomSafe_byteArrayHex _ (by omega)) ?_, ?_⟩
      · simp [SurfaceText.AtomSafe, SurfaceText.isSpace, SurfaceText.isPunctuation]
      · intro fuel callPosition atomPosition
        simp [elaboratePolicyFuel, unaryArgument,
          parseHashBytes_byteArrayHex _ _ _ _ hSafe]
        rfl
      · simp [HeadNoAt, Policy.toExprWith]
  | .ripemd160 hash, hSafe => by
      simp only [Policy.HexTextSafe, Hash160.size] at hSafe
      refine ⟨correct_unaryAtomCall _ _ _ ?_
        (atomSafe_byteArrayHex _ (by omega)) ?_, ?_⟩
      · simp [SurfaceText.AtomSafe, SurfaceText.isSpace, SurfaceText.isPunctuation]
      · intro fuel callPosition atomPosition
        simp [elaboratePolicyFuel, unaryArgument,
          parseHashBytes_byteArrayHex _ _ _ _ hSafe]
        rfl
      · simp [HeadNoAt, Policy.toExprWith]
  | .hash160 hash, hSafe => by
      simp only [Policy.HexTextSafe, Hash160.size] at hSafe
      refine ⟨correct_unaryAtomCall _ _ _ ?_
        (atomSafe_byteArrayHex _ (by omega)) ?_, ?_⟩
      · simp [SurfaceText.AtomSafe, SurfaceText.isSpace, SurfaceText.isPunctuation]
      · intro fuel callPosition atomPosition
        simp [elaboratePolicyFuel, unaryArgument,
          parseHashBytes_byteArrayHex _ _ _ _ hSafe]
        rfl
      · simp [HeadNoAt, Policy.toExprWith]
  | .and left right, hSafe => by
      obtain ⟨hLeft, _⟩ := policyText_correct left hSafe.1
      obtain ⟨hRight, _⟩ := policyText_correct right hSafe.2
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [Policy.toExprWith, SurfaceText.Expr.AtomsSafe]
        refine ⟨by simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
          SurfaceText.isPunctuation], ?_⟩
        intro argument hMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
        rcases hMem with rfl | rfl
        · exact hLeft.1
        · exact hRight.1
      · intro fuel raw hRaw hFuel
        cases raw with
        | atom => simp [RawSurfaceExpr.toExpr, Policy.toExprWith] at hRaw
        | wrapper => simp [RawSurfaceExpr.toExpr, Policy.toExprWith] at hRaw
        | call callPosition rawName rawArguments =>
            simp only [RawSurfaceExpr.toExpr, Policy.toExprWith,
              SurfaceText.Expr.call.injEq] at hRaw
            obtain ⟨rfl, hMap⟩ := hRaw
            obtain ⟨leftRaw, rightRaw, rfl, hLeftRaw, hRightRaw⟩ :=
              rawExprMap_eq_pair rawArguments _ _ hMap
            cases fuel with
            | zero => simp at hFuel
            | succ fuel =>
                have hLeftFuel :
                    (left.toExprWith prettyPubKey).lexemes.length < fuel := by
                  simp [Policy.toExprWith, SurfaceText.Expr.lexemes,
                    SurfaceText.argumentLexemes] at hFuel
                  omega
                have hRightFuel :
                    (right.toExprWith prettyPubKey).lexemes.length < fuel := by
                  simp [Policy.toExprWith, SurfaceText.Expr.lexemes,
                    SurfaceText.argumentLexemes] at hFuel
                  omega
                simp [elaboratePolicyFuel, binaryArguments,
                  hLeft.2 fuel leftRaw hLeftRaw hLeftFuel,
                  hRight.2 fuel rightRaw hRightRaw hRightFuel]
                rfl
      · simp [HeadNoAt, Policy.toExprWith]
  | .or leftWeight left rightWeight right, hSafe => by
      obtain ⟨hLeft, hLeftHead⟩ := policyText_correct left hSafe.1
      obtain ⟨hRight, hRightHead⟩ := policyText_correct right hSafe.2
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [Policy.toExprWith, SurfaceText.Expr.AtomsSafe]
        refine ⟨by simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
          SurfaceText.isPunctuation], ?_⟩
        intro argument hMem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
        rcases hMem with rfl | rfl
        · exact weightedExpr_atomsSafe _ _ hLeft.1
        · exact weightedExpr_atomsSafe _ _ hRight.1
      · intro fuel raw hRaw hFuel
        cases raw with
        | atom => simp [RawSurfaceExpr.toExpr, Policy.toExprWith] at hRaw
        | wrapper => simp [RawSurfaceExpr.toExpr, Policy.toExprWith] at hRaw
        | call callPosition rawName rawArguments =>
            simp only [RawSurfaceExpr.toExpr, Policy.toExprWith,
              SurfaceText.Expr.call.injEq] at hRaw
            obtain ⟨rfl, hMap⟩ := hRaw
            obtain ⟨leftRaw, rightRaw, rfl, hLeftRaw, hRightRaw⟩ :=
              rawExprMap_eq_pair rawArguments _ _ hMap
            obtain ⟨leftStripped, hLeftStrip, hLeftStripped⟩ :=
              stripRawWeight_weighted leftWeight _ hLeftHead leftRaw hLeftRaw
            obtain ⟨rightStripped, hRightStrip, hRightStripped⟩ :=
              stripRawWeight_weighted rightWeight _ hRightHead rightRaw hRightRaw
            cases fuel with
            | zero => simp at hFuel
            | succ fuel =>
                have hLeftFuel :
                    (left.toExprWith prettyPubKey).lexemes.length < fuel := by
                  simp [Policy.toExprWith, SurfaceText.Expr.lexemes,
                    SurfaceText.argumentLexemes, weightedExpr_lexemes_length] at hFuel
                  omega
                have hRightFuel :
                    (right.toExprWith prettyPubKey).lexemes.length < fuel := by
                  simp [Policy.toExprWith, SurfaceText.Expr.lexemes,
                    SurfaceText.argumentLexemes, weightedExpr_lexemes_length] at hFuel
                  omega
                have hL := hLeft.2 fuel leftStripped hLeftStripped hLeftFuel
                have hR := hRight.2 fuel rightStripped hRightStripped hRightFuel
                simp [elaboratePolicyFuel, binaryArguments, hLeftStrip,
                  hRightStrip]
                show (elaboratePolicyFuel resolveHexKey fuel leftStripped >>=
                  fun left => Policy.or leftWeight left rightWeight <$>
                    elaboratePolicyFuel resolveHexKey fuel rightStripped) = _
                rw [hL, hR]
                rfl
      · simp [HeadNoAt, Policy.toExprWith]
  | .thresh k subs, hSafe => by
      obtain ⟨hNonempty, hSubsSafe⟩ := hSafe
      obtain ⟨hSubsAtoms, hSubsElaborate⟩ := policyTextList_correct subs hSubsSafe
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp only [Policy.toExprWith, SurfaceText.Expr.AtomsSafe]
        refine ⟨by simp [SurfaceText.AtomSafe, SurfaceText.isSpace,
          SurfaceText.isPunctuation], ?_⟩
        intro argument hMem
        simp only [List.mem_cons] at hMem
        rcases hMem with rfl | hMem
        · simpa [SurfaceText.Expr.AtomsSafe] using atomSafe_toString k
        · exact hSubsAtoms argument hMem
      · intro fuel raw hRaw hFuel
        cases raw with
        | atom => simp [RawSurfaceExpr.toExpr, Policy.toExprWith] at hRaw
        | wrapper => simp [RawSurfaceExpr.toExpr, Policy.toExprWith] at hRaw
        | call callPosition rawName rawArguments =>
            simp only [RawSurfaceExpr.toExpr, Policy.toExprWith,
              SurfaceText.Expr.call.injEq] at hRaw
            obtain ⟨rfl, hMap⟩ := hRaw
            obtain ⟨thresholdRaw, subRaws, rfl, hThresholdRaw, hSubRaws⟩ :=
              rawExprMap_eq_cons rawArguments _ _ hMap
            cases fuel with
            | zero => simp at hFuel
            | succ fuel =>
                have hSubFuel : ∀ expr ∈ Policy.listToExprWith prettyPubKey subs,
                    expr.lexemes.length < fuel := by
                  intro expr hMem
                  have hLt := lexemes_length_lt_call_of_mem "thresh"
                    (.atom (toString k) :: Policy.listToExprWith prettyPubKey subs)
                    expr (List.mem_cons_of_mem _ hMem)
                  simp only [Policy.toExprWith] at hFuel
                  omega
                have hSubs := hSubsElaborate fuel subRaws hSubRaws hSubFuel
                cases thresholdRaw with
                | atom thresholdPosition thresholdText =>
                    simp only [RawSurfaceExpr.toExpr,
                      SurfaceText.Expr.atom.injEq] at hThresholdRaw
                    subst thresholdText
                    have hSubRawsNonempty : subRaws.isEmpty = false := by
                      cases subRaws with
                      | nil =>
                          cases subs with
                          | nil => exact absurd rfl hNonempty
                          | cons => simp [Policy.listToExprWith] at hSubRaws
                      | cons => rfl
                    simp [elaboratePolicyFuel, variadicArguments,
                      hSubRawsNonempty, PolicyText.parseNatRaw_repr, hSubs]
                    rfl
                | wrapper => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
                | call => simp [RawSurfaceExpr.toExpr] at hThresholdRaw
      · simp [HeadNoAt, Policy.toExprWith]

/-- List counterpart of `policyText_correct` for threshold branches. -/
theorem policyTextList_correct :
    (subs : List Policy) → Policy.allHexTextSafe subs →
      (∀ expr ∈ Policy.listToExprWith prettyPubKey subs, expr.AtomsSafe) ∧
      ∀ (fuel : Nat) (raws : List RawSurfaceExpr),
        raws.map RawSurfaceExpr.toExpr = Policy.listToExprWith prettyPubKey subs →
        (∀ expr ∈ Policy.listToExprWith prettyPubKey subs,
          expr.lexemes.length < fuel) →
        raws.mapM (elaboratePolicyFuel resolveHexKey fuel) = .ok subs
  | [], _ => by
      refine ⟨by simp [Policy.listToExprWith], ?_⟩
      intro fuel raws hMap _
      have : raws = [] := rawExprMap_eq_nil raws (by simpa [Policy.listToExprWith] using hMap)
      subst raws
      rfl
  | sub :: subs, hSafe => by
      obtain ⟨hSub, _⟩ := policyText_correct sub hSafe.1
      obtain ⟨hSubsAtoms, hSubsElaborate⟩ := policyTextList_correct subs hSafe.2
      refine ⟨?_, ?_⟩
      · intro expr hMem
        simp only [Policy.listToExprWith, List.mem_cons] at hMem
        rcases hMem with rfl | hMem
        · exact hSub.1
        · exact hSubsAtoms expr hMem
      · intro fuel raws hMap hFuel
        obtain ⟨raw, rest, rfl, hRaw, hRest⟩ :=
          rawExprMap_eq_cons raws _ _ (by simpa [Policy.listToExprWith] using hMap)
        have hHeadFuel := hFuel (sub.toExprWith prettyPubKey)
          (by simp [Policy.listToExprWith])
        have hRestFuel : ∀ expr ∈ Policy.listToExprWith prettyPubKey subs,
            expr.lexemes.length < fuel := fun expr hMem =>
          hFuel expr (by simp [Policy.listToExprWith, hMem])
        simp [List.mapM_cons, hSub.2 fuel raw hRaw hHeadFuel,
          hSubsElaborate fuel rest hRest hRestFuel]
        rfl

end

/-- `parsePolicyHex` is a left inverse of `prettyPolicy` on hexadecimal-text
    safe policies whose text stays within the shared recursion limit. -/
theorem parsePolicyHex_prettyPolicy (policy : Policy)
    (hSafe : policy.HexTextSafe)
    (hDepth : policyTextWithinRecursionLimit (prettyPolicy policy) = true) :
    parsePolicyHex (prettyPolicy policy) = .ok policy := by
  let expr := policy.toExprWith prettyPubKey
  have hCorrect := (policyText_correct policy hSafe).1
  let tokens := tokenizeSurface expr.render
  have hTokens : tokens.map SurfaceToken.toLexeme = expr.lexemes :=
    tokenizeSurface_renderExpr expr hCorrect.1
  have hTokensNonempty : tokens ≠ [] := by
    intro hEmpty
    have hExprEmpty : expr.lexemes = [] := by
      rw [← hTokens]
      simp [hEmpty]
    exact SurfaceText.Expr.lexemes_ne_nil expr hExprEmpty
  obtain ⟨raw, hParse, hRaw⟩ :=
    parseRaw_tokenizeSurface_renderExpr expr hCorrect.1
  have hLengths : tokens.length = expr.lexemes.length := by
    have := congrArg List.length hTokens
    simpa using this
  have hElaborate :
      elaboratePolicyFuel resolveHexKey (tokens.length + 1) raw = .ok policy :=
    hCorrect.2 _ raw hRaw (by rw [hLengths]; exact Nat.lt_succ_self _)
  have hTokensIsEmpty : tokens.isEmpty = false := by
    cases hTokensValue : tokens with
    | nil => exact False.elim (hTokensNonempty hTokensValue)
    | cons => rfl
  have hWithin : tokensWithinSurfaceRecursionLimit tokens = true := by
    simpa [policyTextWithinRecursionLimit, prettyPolicy, prettyPolicyWith]
      using hDepth
  unfold parsePolicyHex parsePolicy
  change (do
    if tokens.isEmpty then
      Except.error SurfaceParseError.emptyInput
    else if !tokensWithinSurfaceRecursionLimit tokens then
      Except.error (.maxRecursionDepthExceeded maxSurfaceRecursionDepth)
    else
      let (raw, remaining) ← parseRaw tokens
      match remaining with
      | token :: _ =>
          Except.error (.trailingInput token.position (tokenText token))
      | [] => elaboratePolicyFuel resolveHexKey (tokens.length + 1) raw) = _
  rw [if_neg (by simpa using hTokensIsEmpty), hWithin]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [hParse]
  exact hElaborate

end LeanMiniscript.Policy
