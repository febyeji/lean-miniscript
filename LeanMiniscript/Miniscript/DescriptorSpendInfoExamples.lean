import LeanMiniscript.Miniscript.DescriptorParser

namespace LeanMiniscript.Miniscript.DescriptorSpendInfoExamples

open LeanMiniscript.Bitcoin
open LeanMiniscript.Script

private def keyText :=
  "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"

private def verifiesLeaf (output root : ByteArray) (leaf : TaprootLeafSpendInfo) : Bool :=
  match parseTaprootControlBlock leaf.controlBlock,
      verifyTaprootControlBlock output leaf.script leaf.controlBlock with
  | .ok control, .ok commitment =>
      control.leafVersion == 0xc0 && control.merklePath == leaf.merklePath &&
      leaf.controlBlock.size == 33 + 32 * leaf.merklePath.length &&
      commitment.leafVersion == 0xc0 &&
      commitment.leafHash == tapleafHash leaf.script 0xc0 && commitment.merkleRoot == root
  | _, _ => false

private def verifiesLeaves (result : CompiledDescriptor) : Bool :=
  match result.taprootOutputKey, result.taprootMerkleRoot with
  | some output, some root =>
      !result.taprootLeaves.isEmpty && result.taprootLeaves.all (verifiesLeaf output root)
  | _, _ => false

-- Exact controls from BIP341 wallet vectors 1, 2, 5, and 6, pinned by the
-- existing OutputDescriptorExamples and TaprootControlBlockExamples fixtures.
-- https://github.com/bitcoin/bips/blob/442e9628b3dcca1b65f0df8af2308f8260e00caa/bip-0341/wallet-test-vectors.json
-- These cover both output parities, single leaves, and asymmetric trees.
private def walletSpendVectors : List (String × List String) := [
  ("tr(187791b6f712a8ea41c8ecdd0ee77fab3e85263b37e1ec18a3651926b3a6cf27,pk(d85a959b0290bf19bb89ed43c916be835475d013da4b362117393e25a48229b8))",
    ["c1187791b6f712a8ea41c8ecdd0ee77fab3e85263b37e1ec18a3651926b3a6cf27"]),
  ("tr(93478e9488f956df2396be2ce6c5cced75f900dfa18e7dabd2428aae78451820,pk(b617298552a72ade070667e86ca63b8f5789a9fe8731ef91202a91c9f3459007))",
    ["c093478e9488f956df2396be2ce6c5cced75f900dfa18e7dabd2428aae78451820"]),
  ("tr(e0dfe2300b0dd746a3f8674dfd4525623639042569d829c7f0eed9602d263e6f,{pk(72ea6adcf1d371dea8fba1035a09f3d24ed5a059799bae114084130ee5898e69),{pk(2352d137f2f3ab38d1eaa976758873377fa5ebb817372c71e2c542313d4abda8),pk(7337c0dd4253cb86f2c43a2351aadd82cccb12a172cd120452b9bb8324f2186a)}})",
    ["c0e0dfe2300b0dd746a3f8674dfd4525623639042569d829c7f0eed9602d263e6fffe578e9ea769027e4f5a3de40732f75a88a6353a09d767ddeb66accef85e553",
     "c0e0dfe2300b0dd746a3f8674dfd4525623639042569d829c7f0eed9602d263e6f9e31407bffa15fefbf5090b149d53959ecdf3f62b1246780238c24501d5ceaf62645a02e0aac1fe69d69755733a9b7621b694bb5b5cde2bbfc94066ed62b9817",
     "c0e0dfe2300b0dd746a3f8674dfd4525623639042569d829c7f0eed9602d263e6fba982a91d4fc552163cb1c0da03676102d5b7a014304c01f0c77b2b8e888de1c2645a02e0aac1fe69d69755733a9b7621b694bb5b5cde2bbfc94066ed62b9817"]),
  ("tr(55adf4e8967fbd2e29f20ac896e60c3b0f1d5b0efa9d34941b5958c7b0a0312d,{pk(71981521ad9fc9036687364118fb6ccd2035b96a423c59c5430e98310a11abe2),{pk(d5094d2dbe9b76e2c245a2b89b6006888952e2faa6a149ae318d69e520617748),pk(c440b462ad48c7a77f94cd4532d8f2119dcebbd7c9764557e62726419b08ad4c)}})",
    ["c155adf4e8967fbd2e29f20ac896e60c3b0f1d5b0efa9d34941b5958c7b0a0312d3cd369a528b326bc9d2133cbd2ac21451acb31681a410434672c8e34fe757e91",
     "c155adf4e8967fbd2e29f20ac896e60c3b0f1d5b0efa9d34941b5958c7b0a0312dd7485025fceb78b9ed667db36ed8b8dc7b1f0b307ac167fa516fe4352b9f4ef7f154e8e8e17c31d3462d7132589ed29353c6fafdb884c5a6e04ea938834f0d9d",
     "c155adf4e8967fbd2e29f20ac896e60c3b0f1d5b0efa9d34941b5958c7b0a0312d737ed1fe30bc42b8022d717b44f0d93516617af64a64753b7a06bf16b26cd711f154e8e8e17c31d3462d7132589ed29353c6fafdb884c5a6e04ea938834f0d9d"])
]

example : walletSpendVectors.all (fun (descriptor, controls) =>
    match deriveOutputDescriptor descriptor with
    | .error _ => false
    | .ok result => verifiesLeaves result &&
        result.taprootLeaves.map (fun leaf => byteArrayHex leaf.controlBlock) == controls) = true := by
  native_decide

-- Duplicate scripts retain their tree positions, including distinct paths.
example : (match deriveOutputDescriptor ("tr(" ++ keyText ++ ",{1,{0,1}})") with
    | .ok result => verifiesLeaves result &&
        result.taprootLeaves.map (fun leaf => byteArrayHex leaf.script) == ["51", "00", "51"] &&
        result.taprootLeaves.map (fun leaf => leaf.merklePath.length) == [1, 2, 2] &&
        (result.taprootLeaves.map (fun leaf => byteArrayHex leaf.controlBlock)).eraseDups.length == 3
    | .error _ => false) = true := by native_decide

-- Equal sibling hashes still produce two entries with identical controls.
example : (match deriveOutputDescriptor ("tr(" ++ keyText ++ ",{1,1})") with
    | .ok result => verifiesLeaves result &&
        result.taprootLeaves.length == 2 &&
        result.taprootLeaves.map (fun leaf => leaf.merklePath.length) == [1, 1] &&
        (result.taprootLeaves.map (fun leaf => byteArrayHex leaf.controlBlock)).eraseDups.length == 1
    | .error _ => false) = true := by native_decide

-- Distinct surface forms can have identical bytes. Preserve both the original
-- expression and each occurrence's position when generating spending data.
example : (match resolveDescriptorKey none keyText with
    | .error _ => false
    | .ok key =>
        let tree := DescriptorTree.branch (.leaf (.pk key))
          (.branch (.leaf (.core (.c (.pk_k key)))) (.leaf (.pk key)))
        match compileOutputDescriptor (.tr key (some tree)) with
        | .error _ => false
        | .ok result => match result.taprootLeaves with
          | [first, second, third] =>
              (match first.fragment, second.fragment, third.fragment with
                | .pk a, .core (.c (.pk_k b)), .pk c => a == key && b == key && c == key
                | _, _, _ => false) &&
              first.script == second.script && second.script == third.script &&
              result.taprootLeaves.map (fun leaf => leaf.merklePath.length) == [1, 2, 2] &&
              result.taprootLeaves.all (fun leaf =>
                (serializeScript (compileSurfaceConcrete leaf.fragment)).toOption == some leaf.script)
          | _ => false) = true := by native_decide

-- A hash-key leaf uses concrete HASH160 in the bytes retained with its source.
example : (match resolveDescriptorKey none keyText with
    | .error _ => false
    | .ok key => match compileOutputDescriptor (.tr key (some (.leaf (.pkh key)))) with
      | .error _ => false
      | .ok result => match result.taprootLeaves with
        | [leaf] =>
            (match leaf.fragment with
              | .pkh sourceKey => sourceKey == key
              | _ => false) &&
            leaf.script == ByteArray.mk #[0x76, 0xa9, 0x14] ++
              LeanHash160.hash160 key.bytes ++ ByteArray.mk #[0x88, 0xac]
        | _ => false) = true := by native_decide

-- Output wrappers without script-path leaves expose an empty list.
example : [s!"tr({keyText})", s!"wsh(pk(02{keyText}))",
    s!"sh(wsh(pk(02{keyText})))"].all (fun text =>
      match deriveOutputDescriptor text with
      | .ok result => result.taprootLeaves.isEmpty
      | .error _ => false) = true := by native_decide

-- Compressed internal keys of either parity normalize to the same x-only key.
example : ["", "02", "03"].all (fun keyPrefix =>
    match deriveOutputDescriptor s!"tr({keyPrefix}{keyText},1)" with
    | .ok result => verifiesLeaves result && result.taprootLeaves.all (fun leaf =>
        byteArrayHex (leaf.controlBlock.extract 1 33) == keyText)
    | .error _ => false) = true := by native_decide

private def flip (bytes : ByteArray) (index : Nat) : ByteArray :=
  ⟨bytes.data.set! index (bytes[index]! ^^^ 1)⟩

-- Generated proofs fail after parity, sibling, script, or output mutation.
-- Reversing the depth-two path also fails, detecting root-to-leaf ordering.
example : (match deriveOutputDescriptor
    ("tr(" ++ keyText ++ ",{1,{0,pk(" ++ keyText ++ ")}})") with
    | .ok result => match result.taprootOutputKey, result.taprootLeaves with
      | some output, [_, _, leaf] =>
          let control := leaf.controlBlock
          let changed := [
            verifyTaprootControlBlock output leaf.script (flip control 0),
            verifyTaprootControlBlock output leaf.script (flip control 33),
            verifyTaprootControlBlock output (flip leaf.script 1) control,
            verifyTaprootControlBlock (flip output 0) leaf.script control,
            verifyTaprootControlBlock output leaf.script
              (control.extract 0 33 ++ control.extract 65 97 ++ control.extract 33 65)]
          verifiesLeaves result && changed.all (fun result => match result with
            | .error .commitmentMismatch => true
            | _ => false)
      | _, _ => false
    | .error _ => false) = true := by native_decide

private def chain : Nat → DescriptorTree
  | 0 => .leaf (.core .one)
  | n + 1 => .branch (chain n) (.leaf (.core .zero))

private def chainOutput (depth : Nat) : Except String CompiledDescriptor := do
  let key ← resolveDescriptorKey none keyText
  compileOutputDescriptor (.tr key (some (chain depth)))

-- The deepest generated control reaches the 4,129-byte boundary. Check every
-- path's size and root, and verify the deepest control through the wire parser.
example : (match chainOutput 128 with
    | .ok result => match result.taprootOutputKey, result.taprootMerkleRoot, result.taprootLeaves with
      | some output, some root, first :: rest =>
          rest.length == 128 && first.merklePath.length == 128 &&
          first.controlBlock.size == 4129 && verifiesLeaf output root first &&
          (first :: rest).all (fun leaf =>
            leaf.merklePath.length ≤ 128 &&
            leaf.controlBlock.size == 33 + 32 * leaf.merklePath.length &&
            leaf.merklePath.foldl tapbranchHash (tapleafHash leaf.script 0xc0) == root)
      | _, _, _ => false
    | .error _ => false) = true := by native_decide

example : (chainOutput 129).isOk = false := by native_decide

end LeanMiniscript.Miniscript.DescriptorSpendInfoExamples
