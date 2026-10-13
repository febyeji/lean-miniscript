import LeanMiniscript.Psbt.Roles

namespace LeanMiniscript.Psbt

/-!
# Combiner properties

`mergeMap` is a left-biased union by key. It is idempotent and associative
exactly, preserves key uniqueness and framing well-formedness, keeps every
left record, and resolves each key to the left value when present and the
right value otherwise. On maps without conflicting values, lookups do not
depend on argument order, and every record of both inputs is retained. The
PSBT combiner lifts these map-wise.
-/

/-- Two maps assign no key different values. -/
def KeyValueMap.Compatible (left right : KeyValueMap) : Prop :=
  ∀ key value other, left.lookup key = some value → right.lookup key = some other → value = other

/-- Whether a map has a record with this key. -/
def KeyValueMap.hasKey (map : KeyValueMap) (key : ByteArray) : Bool :=
  map.any (fun record => decide (record.key = key))

theorem mergeMap_eq (left right : KeyValueMap) :
    mergeMap left right = left ++ right.filter (fun record => !left.hasKey record.key) := rfl

theorem KeyValueMap.hasKey_iff {map : KeyValueMap} {key : ByteArray} :
    map.hasKey key = true ↔ key ∈ map.map Record.key := by
  simp only [KeyValueMap.hasKey, List.any_eq_true, decide_eq_true_eq, List.mem_map]

theorem KeyValueMap.lookup_cons (record : Record) (records : KeyValueMap) (key : ByteArray) :
    KeyValueMap.lookup (record :: records) key =
      if record.key = key then some record.value else KeyValueMap.lookup records key := by
  by_cases same : record.key = key <;> simp [KeyValueMap.lookup, same]

theorem KeyValueMap.lookup_nil (key : ByteArray) : KeyValueMap.lookup [] key = none := rfl

theorem KeyValueMap.lookup_append (left right : KeyValueMap) (key : ByteArray) :
    KeyValueMap.lookup (left ++ right) key = (left.lookup key).or (right.lookup key) := by
  induction left with
  | nil => simp [KeyValueMap.lookup_nil]
  | cons record records ih =>
    simp only [List.cons_append, KeyValueMap.lookup_cons, ih]
    split <;> simp

theorem KeyValueMap.lookup_eq_none {map : KeyValueMap} {key : ByteArray} :
    map.lookup key = none ↔ key ∉ map.map Record.key := by
  induction map with
  | nil => simp [KeyValueMap.lookup_nil]
  | cons record records ih =>
    rw [KeyValueMap.lookup_cons]
    by_cases same : record.key = key
    · simp [same]
    · simp [same, ih, Ne.symm same]

/-- Filtering away keys other than the looked-up one leaves the lookup unchanged. -/
theorem KeyValueMap.lookup_filter {map : KeyValueMap} {keep : Record → Bool} {key : ByteArray}
    (kept : ∀ record ∈ map, record.key = key → keep record = true) :
    KeyValueMap.lookup (map.filter keep) key = map.lookup key := by
  induction map with
  | nil => rfl
  | cons record records ih =>
    have tail := ih (fun r member => kept r (by simp [member]))
    by_cases same : record.key = key
    · have : keep record = true := kept record (by simp) same
      simp [this, KeyValueMap.lookup_cons, same]
    · by_cases keepIt : keep record = true
      · simp [keepIt, KeyValueMap.lookup_cons, same, tail]
      · simp [keepIt, KeyValueMap.lookup_cons, same, tail]

/-- The merged lookup is the left value, falling back to the right one. -/
theorem lookup_mergeMap (left right : KeyValueMap) (key : ByteArray) :
    (mergeMap left right).lookup key = (left.lookup key).or (right.lookup key) := by
  rw [mergeMap_eq, KeyValueMap.lookup_append]
  cases found : left.lookup key with
  | some value => rfl
  | none =>
    have absent := KeyValueMap.lookup_eq_none.mp found
    simp only [Option.none_or]
    apply KeyValueMap.lookup_filter
    intro record _ same
    simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, KeyValueMap.hasKey_iff, same]
    exact absent

/-- Merging a map with itself is the identity. -/
theorem mergeMap_self (map : KeyValueMap) : mergeMap map map = map := by
  rw [mergeMap_eq]
  have : map.filter (fun record => !map.hasKey record.key) = [] := by
    rw [List.filter_eq_nil_iff]
    intro record member
    have present := KeyValueMap.hasKey_iff.mpr (List.mem_map_of_mem (f := Record.key) member)
    simp [present]
  simp [this]

/-- Merging is associative, as maps and not only up to lookups. -/
theorem mergeMap_assoc (first second third : KeyValueMap) :
    mergeMap (mergeMap first second) third = mergeMap first (mergeMap second third) := by
  simp only [mergeMap_eq, List.append_assoc, List.filter_append, List.filter_filter]
  congr 2
  apply List.filter_congr
  intro record _
  simp only [KeyValueMap.hasKey, List.any_append, List.any_filter]
  cases hFirst : first.any (fun r => decide (r.key = record.key)) <;>
    cases hSecond : second.any (fun r => decide (r.key = record.key)) <;>
    simp_all [List.any_eq_true, List.any_eq_false]
  obtain ⟨x, member, same⟩ := hSecond
  exact ⟨x, member, fun y inFirst => by rw [same]; exact hFirst y inFirst, same⟩

/-- Every left record is retained. -/
theorem mem_mergeMap_left {left right : KeyValueMap} {record : Record} (member : record ∈ left) :
    record ∈ mergeMap left right := by
  rw [mergeMap_eq]; exact List.mem_append_left _ member

/-- Every merged record comes from one of the inputs. -/
theorem mem_mergeMap {left right : KeyValueMap} {record : Record}
    (member : record ∈ mergeMap left right) : record ∈ left ∨ record ∈ right := by
  rw [mergeMap_eq, List.mem_append, List.mem_filter] at member
  rcases member with inLeft | ⟨inRight, _⟩
  · exact .inl inLeft
  · exact .inr inRight

/-- Key uniqueness is preserved. -/
theorem mergeMap_unique {left right : KeyValueMap} (leftUnique : left.Unique)
    (rightUnique : right.Unique) : (mergeMap left right).Unique := by
  unfold KeyValueMap.Unique at *
  rw [mergeMap_eq, List.map_append, List.nodup_append]
  refine ⟨leftUnique, List.Nodup.sublist (List.Sublist.map Record.key List.filter_sublist) rightUnique, ?_⟩
  intro key inLeft other inFiltered same
  subst same
  obtain ⟨record, member, rfl⟩ := List.mem_map.mp inFiltered
  rw [List.mem_filter] at member
  have := member.2
  simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, KeyValueMap.hasKey_iff] at this
  exact this inLeft

/-- Framing well-formedness is preserved. -/
theorem mergeMap_wellFormed {left right : KeyValueMap} (leftFormed : left.WellFormed)
    (rightFormed : right.WellFormed) : (mergeMap left right).WellFormed := by
  refine ⟨fun record member => ?_, mergeMap_unique leftFormed.2 rightFormed.2⟩
  rcases mem_mergeMap member with inLeft | inRight
  · exact leftFormed.1 record inLeft
  · exact rightFormed.1 record inRight

/-- Without conflicting values, lookups do not depend on argument order. -/
theorem lookup_mergeMap_comm {left right : KeyValueMap} (compatible : left.Compatible right)
    (key : ByteArray) : (mergeMap left right).lookup key = (mergeMap right left).lookup key := by
  rw [lookup_mergeMap, lookup_mergeMap]
  cases hLeft : left.lookup key <;> cases hRight : right.lookup key <;> simp
  exact compatible key _ _ hLeft hRight

theorem KeyValueMap.lookup_of_mem {map : KeyValueMap} (unique : map.Unique) {record : Record}
    (member : record ∈ map) : map.lookup record.key = some record.value := by
  induction map with
  | nil => simp at member
  | cons head tail ih =>
    unfold KeyValueMap.Unique at unique
    rw [List.map_cons, List.nodup_cons] at unique
    rw [KeyValueMap.lookup_cons]
    rcases List.mem_cons.mp member with same | inTail
    · subst same; simp
    · have different : head.key ≠ record.key := by
        intro same
        exact unique.1 (same ▸ List.mem_map_of_mem inTail)
      simp [different, ih unique.2 inTail]

theorem KeyValueMap.mem_of_lookup {map : KeyValueMap} {key value : ByteArray}
    (found : map.lookup key = some value) : ⟨key, value⟩ ∈ map := by
  induction map with
  | nil => simp [KeyValueMap.lookup_nil] at found
  | cons head tail ih =>
    rw [KeyValueMap.lookup_cons] at found
    split at found
    · rename_i same
      cases head
      simp_all
    · exact List.mem_cons_of_mem _ (ih found)

/-- BIP174: without conflicts, the combination contains every key-value
pair of both inputs. -/
theorem mem_mergeMap_right {left right : KeyValueMap} (rightUnique : right.Unique) (compatible : left.Compatible right) {record : Record}
    (member : record ∈ right) : record ∈ mergeMap left right := by
  have inRight := KeyValueMap.lookup_of_mem rightUnique member
  have merged := lookup_mergeMap left right record.key
  cases hLeft : left.lookup record.key with
  | none =>
    rw [hLeft, inRight] at merged
    exact KeyValueMap.mem_of_lookup merged
  | some value =>
    have := compatible _ _ _ hLeft inRight
    subst this
    exact mem_mergeMap_left (KeyValueMap.mem_of_lookup hLeft)

/-! ## PSBT-level combiner -/

private theorem zipWith_mergeMap_assoc :
    ∀ (first second third : List KeyValueMap),
      List.zipWith mergeMap (List.zipWith mergeMap first second) third =
        List.zipWith mergeMap first (List.zipWith mergeMap second third)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | a :: first, b :: second, c :: third => by
    simp [List.zipWith_cons_cons, mergeMap_assoc, zipWith_mergeMap_assoc first second third]

theorem Psbt.combineMaps_self (psbt : Psbt) : psbt.combineMaps psbt = psbt := by
  simp [Psbt.combineMaps, mergeMap_self]

theorem Psbt.combineMaps_assoc (first second third : Psbt) :
    (first.combineMaps second).combineMaps third = first.combineMaps (second.combineMaps third) := by
  simp [Psbt.combineMaps, mergeMap_assoc, zipWith_mergeMap_assoc]

private theorem zipWith_mergeMap_wellFormed :
    ∀ (left right : List KeyValueMap), (∀ map ∈ left, map.WellFormed) →
      (∀ map ∈ right, map.WellFormed) → ∀ map ∈ List.zipWith mergeMap left right, map.WellFormed
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | a :: left, b :: right, leftFormed, rightFormed => by
    intro map member
    rw [List.zipWith_cons_cons, List.mem_cons] at member
    rcases member with same | rest
    · subst same
      exact mergeMap_wellFormed (leftFormed a (by simp)) (rightFormed b (by simp))
    · exact zipWith_mergeMap_wellFormed left right
        (fun m h => leftFormed m (by simp [h])) (fun m h => rightFormed m (by simp [h])) map rest

theorem Psbt.combineMaps_wellFormed {left right : Psbt} (leftFormed : left.WellFormed)
    (rightFormed : right.WellFormed) : (left.combineMaps right).WellFormed :=
  ⟨mergeMap_wellFormed leftFormed.1 rightFormed.1,
   zipWith_mergeMap_wellFormed _ _ leftFormed.2.1 rightFormed.2.1,
   zipWith_mergeMap_wellFormed _ _ leftFormed.2.2 rightFormed.2.2⟩

/-- A successful combination is the map-wise union and decodes. -/
theorem Psbt.combine_spec {left right combined : Psbt}
    (success : left.combine right = .ok combined) :
    combined = left.combineMaps right ∧ ∃ decoded, combined.decode = .ok decoded := by
  unfold Psbt.combine at success
  cases hl : liftPsbt left.decode with
  | error error => simp [hl, bind, Except.bind] at success
  | ok leftDecoded =>
    cases hr : liftPsbt right.decode with
    | error error => simp [hl, hr, bind, Except.bind] at success
    | ok rightDecoded =>
      cases il : leftDecoded.uniqueId with
      | error error => simp [hl, hr, il, bind, Except.bind] at success
      | ok leftId =>
        cases ir : rightDecoded.uniqueId with
        | error error => simp [hl, hr, il, ir, bind, Except.bind] at success
        | ok rightId =>
          simp only [hl, hr, il, ir, bind, Except.bind] at success
          split at success
          · simp [throw, throwThe, MonadExceptOf.throw] at success
          · simp only [pure, Except.pure, Psbt.checked, bind, Except.bind] at success
            cases decoded : liftPsbt (left.combineMaps right).decode with
            | error error => simp [decoded] at success
            | ok value =>
              simp only [decoded, Except.ok.injEq] at success
              subst success
              refine ⟨rfl, value, ?_⟩
              cases h : (left.combineMaps right).decode <;> simp_all [liftPsbt, Except.mapError]

/-- A decodable PSBT combines with itself to itself, whenever its transaction
identifier is defined. -/
theorem Psbt.combine_self {psbt : Psbt} {decoded : DecodedPsbt} {identifier : Nat × ByteArray}
    (decodes : psbt.decode = .ok decoded) (identified : decoded.uniqueId = .ok identifier) :
    psbt.combine psbt = .ok psbt := by
  have lifted : liftPsbt psbt.decode = .ok decoded := by
    simp [liftPsbt, decodes, Except.mapError]
  simp [Psbt.combine, lifted, identified, bind, Except.bind, Psbt.combineMaps_self,
    Psbt.checked, pure, Except.pure]

/-- Lookups in a combination do not depend on argument order for compatible
maps; this holds for the global map and each input and output map. -/
theorem Psbt.combine_lookup_comm {left right first second : Psbt}
    (leftFirst : left.combine right = .ok first) (rightFirst : right.combine left = .ok second)
    (compatible : left.global.Compatible right.global) (key : ByteArray) :
    first.global.lookup key = second.global.lookup key := by
  rw [(Psbt.combine_spec leftFirst).1, (Psbt.combine_spec rightFirst).1]
  exact lookup_mergeMap_comm compatible key

theorem Psbt.combine_input_lookup_comm {left right first second : Psbt}
    (leftFirst : left.combine right = .ok first) (rightFirst : right.combine left = .ok second)
    {index : Nat} {leftMap rightMap : KeyValueMap}
    (leftInput : left.inputs[index]? = some leftMap) (rightInput : right.inputs[index]? = some rightMap)
    (compatible : leftMap.Compatible rightMap) (key : ByteArray) :
    (first.inputs[index]?.map (·.lookup key)) = (second.inputs[index]?.map (·.lookup key)) := by
  rw [(Psbt.combine_spec leftFirst).1, (Psbt.combine_spec rightFirst).1]
  simp only [Psbt.combineMaps, List.getElem?_zipWith, leftInput, rightInput]
  simp [lookup_mergeMap_comm compatible key]

end LeanMiniscript.Psbt
