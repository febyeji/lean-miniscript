import LeanMiniscript.Miniscript.OutputDescriptor
import LeanMiniscript.Bitcoin.TaprootControlBlockProofs

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Bitcoin

/-- The serialized spending data recovers its original key, output parity,
and leaf-to-root path under the control-block width and depth requirements. -/
theorem DescriptorLeafInfo.spendInfo_parse
    (leaf : DescriptorLeafInfo) (internalKey : ByteArray) (outputParity : Bool)
    (keySize : internalKey.size = 32) (depth : leaf.merklePath.length ≤ 128)
    (sizes : ∀ sibling ∈ leaf.merklePath, sibling.size = 32) :
    parseTaprootControlBlock (leaf.spendInfo internalKey outputParity).controlBlock =
      .ok { leafVersion := 0xc0, outputParity, internalKey, merklePath := leaf.merklePath } :=
  parseTaprootControlBlock_serialized internalKey outputParity leaf.merklePath
    keySize depth sizes

/-- Successful tree compilation produces 32-byte roots and sibling hashes.
Every leaf path reconstructs that root within the supplied branch budget. -/
theorem DescriptorTree.compile_paths
    {tree : DescriptorTree} {maxDepth : Nat} {info : DescriptorTreeInfo}
    (compiled : tree.compile maxDepth = .ok info) :
    info.merkleRoot.size = 32 ∧
      ∀ leaf ∈ info.leaves,
        leaf.merklePath.foldl tapbranchHash (tapleafHash leaf.script 0xc0) = info.merkleRoot ∧
        leaf.merklePath.length ≤ maxDepth ∧
        ∀ sibling ∈ leaf.merklePath, sibling.size = 32 := by
  induction tree generalizing maxDepth info with
  | leaf fragment =>
      simp only [DescriptorTree.compile, bind, Except.bind] at compiled
      split at compiled
      · cases compiled
      · cases compiled
        simp
  | branch left right leftIH rightIH =>
      cases maxDepth with
      | zero => simp [DescriptorTree.compile] at compiled
      | succ depth =>
          cases leftEq : left.compile depth with
          | error error => simp [DescriptorTree.compile, leftEq, bind, Except.bind] at compiled
          | ok leftInfo =>
              cases rightEq : right.compile depth with
              | error error =>
                  simp [DescriptorTree.compile, leftEq, rightEq, bind, Except.bind] at compiled
              | ok rightInfo =>
                  simp only [DescriptorTree.compile, leftEq, rightEq, bind, Except.bind,
                    pure, Except.pure, Except.ok.injEq] at compiled
                  subst info
                  obtain ⟨leftSize, leftPaths⟩ := leftIH leftEq
                  obtain ⟨rightSize, rightPaths⟩ := rightIH rightEq
                  refine ⟨tapbranchHash_size _ _, ?_⟩
                  intro leaf member
                  simp only [DescriptorTreeInfo.branch, List.mem_append, List.mem_map] at member
                  rcases member with ⟨original, member, rfl⟩ | ⟨original, member, rfl⟩
                  · obtain ⟨rootEq, lengthLe, sizes⟩ := leftPaths original member
                    refine ⟨?_, ?_, ?_⟩
                    · simpa [DescriptorLeafInfo.withSibling, DescriptorTreeInfo.branch,
                        List.foldl_append] using
                        congrArg (fun root => tapbranchHash root rightInfo.merkleRoot) rootEq
                    · simpa [DescriptorLeafInfo.withSibling] using Nat.succ_le_succ lengthLe
                    · simpa [DescriptorLeafInfo.withSibling, or_imp, forall_and] using
                        And.intro sizes rightSize
                  · obtain ⟨rootEq, lengthLe, sizes⟩ := rightPaths original member
                    refine ⟨?_, ?_, ?_⟩
                    · simp only [DescriptorLeafInfo.withSibling, List.foldl_append,
                        List.foldl_cons, List.foldl_nil, rootEq, DescriptorTreeInfo.branch]
                      exact tapbranchHash_comm (rightSize.trans leftSize.symm)
                    · simpa [DescriptorLeafInfo.withSibling] using Nat.succ_le_succ lengthLe
                    · simpa [DescriptorLeafInfo.withSibling, or_imp, forall_and] using
                        And.intro sizes leftSize

/-- The existing control-block root calculation recovers the compiled root
from every generated leaf path. Internal key and parity do not affect this fold. -/
theorem DescriptorTree.compile_controlMerkleRoot
    {tree : DescriptorTree} {maxDepth : Nat} {info : DescriptorTreeInfo}
    (compiled : tree.compile maxDepth = .ok info)
    {leaf : DescriptorLeafInfo} (member : leaf ∈ info.leaves)
    (internalKey : ByteArray) (outputParity : Bool) :
    taprootControlMerkleRoot
      { leafVersion := 0xc0, internalKey, outputParity, merklePath := leaf.merklePath }
      (tapleafHash leaf.script 0xc0) = info.merkleRoot :=
  (DescriptorTree.compile_paths compiled).2 leaf member |>.1

/-- Every leaf returned by the output compiler reconstructs its advertised
Merkle root with at most 128 siblings, each exactly 32 bytes. -/
theorem compileOutputDescriptor_taprootPaths
    {key : PubKey} {tree : DescriptorTree} {result : CompiledDescriptor}
    (compiled : compileOutputDescriptor (.tr key (some tree)) = .ok result) :
    ∀ leaf ∈ result.taprootLeaves,
      result.taprootMerkleRoot = some
        (leaf.merklePath.foldl tapbranchHash (tapleafHash leaf.script 0xc0)) ∧
      leaf.merklePath.length ≤ 128 ∧
      ∀ sibling ∈ leaf.merklePath, sibling.size = 32 := by
  simp only [compileOutputDescriptor, bind, Except.bind] at compiled
  split at compiled
  · cases compiled
  · cases treeEq : tree.compile with
    | error error => simp [treeEq, Functor.map, Except.map] at compiled
    | ok info =>
        simp only [treeEq, Functor.map, Except.map] at compiled
        split at compiled
        · simp only [pure, Except.pure, Except.ok.injEq] at compiled
          subst result
          intro leaf member
          simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.mem_map] at member
          obtain ⟨original, member, rfl⟩ := member
          obtain ⟨rootEq, bound, sizes⟩ :=
            (DescriptorTree.compile_paths treeEq).2 original member
          exact ⟨congrArg some rootEq.symm, bound, sizes⟩
        · cases compiled

/-- Every serialized leaf control block from a successfully compiled Taproot
tree passes the existing commitment verifier against the compiled output key
and recovers the advertised Merkle root. This establishes agreement between
the executable compiler and verifier, without a claim of curve correctness. -/
theorem compileOutputDescriptor_taprootCommitments
    {key : PubKey} {tree : DescriptorTree} {result : CompiledDescriptor}
    (compiled : compileOutputDescriptor (.tr key (some tree)) = .ok result) :
    ∃ outputKey root,
      result.taprootOutputKey = some outputKey ∧ result.taprootMerkleRoot = some root ∧
      ∀ leaf ∈ result.taprootLeaves,
        verifyTaprootControlBlock outputKey leaf.script leaf.controlBlock =
          .ok {
            leafVersion := 0xc0
            leafHash := tapleafHash leaf.script 0xc0
            merkleRoot := root } := by
  simp only [compileOutputDescriptor, bind, Except.bind] at compiled
  split at compiled
  · cases compiled
  · rename_i internalBytes internalEq
    cases treeEq : tree.compile with
    | error error => simp [treeEq, Functor.map, Except.map] at compiled
    | ok info =>
        simp only [treeEq, Functor.map, Except.map] at compiled
        split at compiled
        · rename_i point tweakEq
          simp only [pure, Except.pure, Except.ok.injEq] at compiled
          subst result
          refine ⟨_, info.merkleRoot, rfl, rfl, ?_⟩
          intro leaf member
          simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil,
            List.append_nil, List.mem_map] at member
          obtain ⟨original, member, rfl⟩ := member
          obtain ⟨rootEq, depth, sizes⟩ :=
            (DescriptorTree.compile_paths treeEq).2 original member
          have pointBound := (taprootTweakPoint_bounds tweakEq).2
          have encoded := decodeBE_fixedWidth 32 point.1
            (Nat.lt_trans pointBound (by decide))
          have verified := verifyTaprootControlBlock_serialized internalBytes
            ⟨(List.range 32).toArray.map (fun i => UInt8.ofNat (point.1 / 256 ^ (31 - i)))⟩
            original.script original.merklePath point depth sizes
            (by change ((List.range 32).toArray.map _).size = 32; simp) encoded
            (by simpa only [rootEq, Option.map_some, Option.getD_some] using tweakEq)
          rw [rootEq] at verified
          exact verified
        · cases compiled

end LeanMiniscript.Miniscript
