import LeanMiniscript.Miniscript.OutputDescriptor

namespace LeanMiniscript.Miniscript.OutputDescriptorExamples

open LeanMiniscript.Miniscript

private def digit (byte : UInt8) : Nat :=
  if byte.toNat ≤ 57 then byte.toNat - 48 else byte.toNat - 87
private def decodeHex : List UInt8 → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest
  | _ => []
private def hex (text : String) : ByteArray :=
  ⟨(decodeHex text.toUTF8.data.toList).toArray⟩
private def key (text : String) : PubKey := PubKey.ofBytes (hex text)
private def leaf (text : String) : DescriptorTree := .leaf (.pk (key text))

private def matchesTaproot (descriptor : OutputDescriptor) (script : String)
    (root : Option String) : Bool :=
  match compileOutputDescriptor descriptor with
  | .error _ => false
  | .ok result =>
      result.scriptPubKey == hex script &&
      result.taprootOutputKey == some ((hex script).extract 2 34) &&
      result.taprootMerkleRoot == root.map hex &&
      result.redeemScript.isNone && result.witnessScript.isNone

-- Official BIP341 wallet scriptPubKey vectors 0, 1, 2, 5 and 6. These are the
-- vectors whose leaves are version 0xc0 pk() scripts supported by this AST.
-- https://github.com/bitcoin/bips/blob/442e9628b3dcca1b65f0df8af2308f8260e00caa/bip-0341/wallet-test-vectors.json
example : matchesTaproot
    (.tr (key "d6889cb081036e0faefa3a35157ad71086b123b2b144b649798b494c300a961d")
      none)
    "512053a1f6e454df1aa2776a2814a721372d6258050de330b3c6d10ee8f4e0dda343"
    none = true := by native_decide

example : matchesTaproot
    (.tr (key "187791b6f712a8ea41c8ecdd0ee77fab3e85263b37e1ec18a3651926b3a6cf27")
      (some (leaf "d85a959b0290bf19bb89ed43c916be835475d013da4b362117393e25a48229b8")))
    "5120147c9c57132f6e7ecddba9800bb0c4449251c92a1e60371ee77557b6620f3ea3"
    (some "5b75adecf53548f3ec6ad7d78383bf84cc57b55a3127c72b9a2481752dd88b21") = true := by native_decide

example : matchesTaproot
    (.tr (key "93478e9488f956df2396be2ce6c5cced75f900dfa18e7dabd2428aae78451820")
      (some (leaf "b617298552a72ade070667e86ca63b8f5789a9fe8731ef91202a91c9f3459007")))
    "5120e4d810fd50586274face62b8a807eb9719cef49c04177cc6b76a9a4251d5450e"
    (some "c525714a7f49c28aedbbba78c005931a81c234b2f6c99a73e4d06082adc8bf2b") = true := by native_decide

example : matchesTaproot
    (.tr (key "e0dfe2300b0dd746a3f8674dfd4525623639042569d829c7f0eed9602d263e6f")
      (some (.branch (leaf "72ea6adcf1d371dea8fba1035a09f3d24ed5a059799bae114084130ee5898e69") (.branch (leaf "2352d137f2f3ab38d1eaa976758873377fa5ebb817372c71e2c542313d4abda8") (leaf "7337c0dd4253cb86f2c43a2351aadd82cccb12a172cd120452b9bb8324f2186a")))))
    "512091b64d5324723a985170e4dc5a0f84c041804f2cd12660fa5dec09fc21783605"
    (some "ccbd66c6f7e8fdab47b3a486f59d28262be857f30d4773f2d5ea47f7761ce0e2") = true := by native_decide

example : matchesTaproot
    (.tr (key "55adf4e8967fbd2e29f20ac896e60c3b0f1d5b0efa9d34941b5958c7b0a0312d")
      (some (.branch (leaf "71981521ad9fc9036687364118fb6ccd2035b96a423c59c5430e98310a11abe2") (.branch (leaf "d5094d2dbe9b76e2c245a2b89b6006888952e2faa6a149ae318d69e520617748") (leaf "c440b462ad48c7a77f94cd4532d8f2119dcebbd7c9764557e62726419b08ad4c")))))
    "512075169f4001aa68f15bbed28b218df1d0a62cbbcf1188c6665110c293c907b831"
    (some "2f6b2c5397b6d68ca18e09a3f05161668ffe93a988582d55c6f07bd5b3329def") = true := by native_decide
-- BIP386 fixed-key output vectors, including implicit compressed-to-x-only
-- conversion of either parity. The output is tweaked even without a tree.
-- https://github.com/bitcoin/bips/blob/442e9628b3dcca1b65f0df8af2308f8260e00caa/bip-0386.mediawiki
private def bip386Key : String :=
  "a34b99f22c790c4e36b2b3c2c35a36db06226e41c692fc82b8b56ac1c540c5bd"
private def bip386Output : String :=
  "512077aab6e066f8a7419c5ab714c12c67d25007ed55a43cadcacb4d7a970a093f11"
example : [bip386Key, "02" ++ bip386Key, "03" ++ bip386Key].all
    (fun text => matchesTaproot (.tr (key text) none) bip386Output none) = true := by
  native_decide

private def compressed : PubKey :=
  key "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
private def xOnly : PubKey := PubKey.ofBytes (compressed.bytes.extract 1 33)
private def uncompressed : PubKey := key
  "0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8"

private def matchesWsh (wrapped : Bool) (fragment : SurfaceFragment)
    (script program outer : String) : Bool :=
  match compileOutputDescriptor (if wrapped then .shWsh fragment else .wsh fragment) with
  | .error _ => false
  | .ok result =>
      result.scriptPubKey == hex (if wrapped then outer else program) &&
      result.witnessScript == some (hex script) &&
      result.redeemScript == (if wrapped then some (hex program) else none) &&
      result.taprootOutputKey.isNone && result.taprootMerkleRoot.isNone

-- Expected hashes were independently computed with Python hashlib SHA256 and
-- RIPEMD160, from these literal witness scripts.
example : [false, true].all (fun wrapped => matchesWsh wrapped (.pk compressed)
    "210279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798ac"
    "00201863143c14c5166804bd19203356da136c985678cd4d27a1b8c6329604903262"
    "a914e4300531190587e3880d4c3004f5355d88ff928d87") = true := by native_decide
example : [false, true].all (fun wrapped => matchesWsh wrapped (.pkh compressed)
    "76a914751e76e8199196d454941c45d1b3a323f1433bd688ac"
    "00203f4ae1eb3e75f3578491811d27eb59e23a512cf90c73b13c6acd4499f7c4d28b"
    "a914d7c1e6f8f430d9563ed6ca46ca74f6d1e3b96e0e87") = true := by native_decide

-- Direct constructors must satisfy the same fragment and key checks as text.
private def rejected (descriptor : OutputDescriptor) : Bool :=
  !(compileOutputDescriptor descriptor).isOk
private def badX : PubKey := key
  "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"
private def badCompressed : PubKey := PubKey.ofBytes (ByteArray.mk #[2] ++ badX.bytes)

example : [
    OutputDescriptor.wsh (.core (.pk_k compressed)), -- Root K
    .wsh (.core (.v (.c (.pk_k compressed)))),       -- Root V
    .wsh (.core (.a (.c (.pk_k compressed)))),       -- Root W
    .wsh (.core (.and_v .one .one)),                -- Ill-typed connective
    .shWsh (.core (.pk_k compressed)),
    .wsh (.pk xOnly),
    .wsh (.pk uncompressed),
    .wsh (.pk badCompressed),
    .wsh (.pkh badCompressed),
    .wsh (.core (.multi 1 [badCompressed])),
    .wsh (.core (.multi_a 1 [xOnly])),
    .wsh (.core (.sha256 (Hash256.ofBytes (hex "00")))),
    .wsh (.core (.older 0)),
    .tr uncompressed none,
    .tr badX none,
    .tr badCompressed none,
    .tr xOnly (some (.leaf (.core (.pk_k xOnly)))),
    .tr xOnly (some (.leaf (.pk compressed))),
    .tr xOnly (some (.leaf (.pk badX))),
    .tr xOnly (some (.leaf (.pkh badX))),
    .tr xOnly (some (.leaf (.core (.multi_a 1 [badX])))),
    .tr xOnly (some (.leaf (.core (.multi 1 [compressed]))))
  ].all rejected = true := by native_decide

private def rootOf (tree : DescriptorTree) : Option ByteArray :=
  match compileOutputDescriptor (.tr xOnly (some tree)) with
  | .ok result => result.taprootMerkleRoot
  | .error _ => none
private def a : DescriptorTree := .leaf (.core .one)
private def b : DescriptorTree := .leaf (.core .zero)
private def c : DescriptorTree := .leaf (.pk xOnly)

-- Each branch sorts its children by hash; the descriptor's grouping remains.
example : rootOf (.branch a (.branch b c)) = rootOf (.branch (.branch c b) a) := by
  native_decide
example : (rootOf (.branch a (.branch b c)) != rootOf (.branch (.branch a b) c)) = true := by
  native_decide
example : (compileOutputDescriptor (.tr xOnly (some (.leaf (.pkh xOnly))))).isOk = true := by
  native_decide

private def chain : Nat → DescriptorTree
  | 0 => a
  | n + 1 => .branch (chain n) a
example : (compileOutputDescriptor (.tr xOnly (some (chain 128)))).isOk = true := by
  native_decide
example : rejected (.tr xOnly (some (chain 129))) = true := by native_decide

end LeanMiniscript.Miniscript.OutputDescriptorExamples
