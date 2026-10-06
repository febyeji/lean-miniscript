import LeanMiniscript.Bitcoin.BIP32

namespace LeanMiniscript.Bitcoin.BIP32

/-! Independent review regressions. SHA512/HMAC expectations were computed with
Python's hashlib/hmac; BIP32 expectations use a separate Python implementation
with OpenSSL-backed secp256k1 public-key derivation and standard-library HMAC.
These examples exercise padding boundaries, version bytes and index limits. -/

private def digit (byte : UInt8) : Nat :=
  if byte.toNat ≤ 57 then byte.toNat - 48 else byte.toNat - 87
private def decodeHex : List UInt8 → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest
  | _ => []
private def hex (text : String) : ByteArray := ⟨(decodeHex text.toUTF8.data.toList).toArray⟩
private def pattern (size : Nat) : ByteArray :=
  ⟨((List.range size).map (fun i => UInt8.ofNat (i * 17 + 3))).toArray⟩
private def fails {α : Type} (result : Except String α) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true
private def stringResult (result : Except String String) (expected : String) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

private def shaBoundaries : Array (Nat × String) := #[
  (0, "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"),
  (1, "e45bf5817ddf94aa2f7a407071f0eedc6beb98f768b4cd33d1176d44d1563a45a5d7212290eb7670c6786b13591aedac86478993895e8b24e612014abaa6ba04"),
  (111, "d10298baa041e1461b6680a3542e350b5da77316a4df3680d0583a7f9c9edc9fbf3817e0387ac7df68aed78fb5634ded691889ba66aa682a9c6085b8f97f7d20"),
  (112, "ab96b474771218e6795fc011d3e2b80b9cf1a31bd267a9c8373e1cd92a9a314d32df0cc0c891871dcced9eaec7ba90e3571948a129d5fc96aba225b8f15daea4"),
  (113, "f7e9fbb607438cf98ddc8d866c1cc788ac96cfbba9abcfe554a207b73782879be8217da8c68a6fa4a5dc36454288c31a23a5245ddd8847f97875173762a5aed5"),
  (127, "6c06aae9306473040c3f3566ec91934ff387a72aa55a2967a9c2977506ac1ac91dd480aef85ce5de41e5917c1f907df14ebf91d144b9aea711097e1a15d7bc92"),
  (128, "4d5618155f746968d0485e9b9093977b17e0e81520b1a9cfb2539fe22e2fd76b49508302e8ab9083b29261562556ddc8017a5c89ce53d02fa13eb95bded120d7"),
  (129, "129437ffcead15e9c0cfddfc2fed5d5d16069deaff871c17239ee321da9e7d000ae1b94411c306bacda4dfa618108ef3494db2eed6068f14556a27dbcb547c4a"),
  (239, "e6e048eed64967c52d2d10ad924498a1e96c58a09a6a18ea2d8082a22d812838abdcf82aa099959e744cca86675083967cc36ed700da88d1054206e415aee0ab"),
  (240, "4ff44aa6ef270cd490a32cb2b121793e530da3e9012fa4cb82abad042988f578391217a2c21f3577a3c4cf98eb68526abbe2d7edccda32e1b6324e4b7847f8b6"),
  (255, "80d7ea1d7b2e0e01103c2b5da1005d288aedc835866f6bb6cdb86460f5ba8497e37ab0dac6a25df44008040c58ca49399644e39d0da2b62f3c600bf327ce89d8"),
  (256, "c39b6adc272336d4f76d051ff89597c58530dfc1b004bb185009332fd3ce78e5c02043e0606fbaac9d87bdb7c813aaba4d0fae99d1a8f5b77326f31ed50cdd49"),
  (257, "5698c08ee09e042bd2cc4b430babaab7391b8b51f89c52e271fac913cb60fcac10698003f93940088b6defa61d92855c5e835759583b8ece6bba5ec73ec04a06"),
  (1000, "7245940365247792079b55ce293bbf74cb2a43a06fcbc03a8c433642484bb300f235f46b20c99d6a39725a97936aa54b091c4a51f945f7b087459f709d852c59")]

example : shaBoundaries.size = 14 := by native_decide
example : shaBoundaries.all (fun (size, expected) =>
    SHA512.hash (pattern size) == hex expected) = true := by native_decide

private def hmacBoundaries : Array (Nat × Nat × String) := #[
  (0, 0, "b936cee86c9f87aa5d3c6f2e84cb5a4239a5fe50480a6ec66b70ab5b1f4ac6730c6c515421b327ec1d69402e53dfb49ad7381eb067b338fd7b0cb22247225d47"),
  (0, 111, "8f4c43b22c27d33b24a2ca85c99b9315a46f80afb1fab53bd5ee5b14314b6a01130f763f99a0e0a2f8d6ee374120bc4103b155e83beb09e6ccd7102e762d8ccb"),
  (0, 112, "d130e86298d1ca68a365537d7d382fda0e084fb58338ba093425799f5552fefd144076a3735ed008138d20a99eeda3459b96b241e8c053dbdf5498b4d1cc8db0"),
  (0, 127, "0c639d132d8c41b3e4ee0c2d4cc8af4a1798f205f191c556f403e347648eb419b7f27f69bffb16863157cec327e74347d5731ffeb507a89e403c9bad24c118b1"),
  (0, 128, "646f81cc30544c4746885ae75301e7bc3215f99ae6a871101708ee3fc078e9b9ac210b28f3c149e680f88ed371bf44b0d61945d3937b54e2d275b62506c3f1e0"),
  (0, 129, "49d9e014d536fd74adbdb3b9e4b5b4bbd28477e18f516b65fcb403dcbb5931635d4c3173390f842a3bc3cadae5af75b4f10ed84bfddd86d952e6a215ca1f9877"),
  (1, 0, "c0090857ec6d9dfbb1637a4a2cca76750f183b9c85c692b95f1711cc1a6aba56713d06d36b43b195cb796104daf01fdcfe0548f25f5c6b367c7daa55cd747d0d"),
  (1, 111, "f58912b4089957c3febb96e835e03184885f36c667bede526404b670daa3cf7a6ebe668ab54906d02ab5218e6517f50decf4a92ff5c06ac84bd14d60c9f17e94"),
  (1, 112, "1d28b048b377b6647e484bcb7baa9b78d501640356e0a4234797d75ae88d4d69261c261ecea818dc93e79651d527630ee480ee4e734f189793248671f6c062a0"),
  (1, 127, "26e13834caaea20b677c3ce040af1c9ec7fa70327ff350737f663a978b25b7ff5f6db3bb9e0579035af71280572e6a731bfa3facdff39767e41d587ae88f7807"),
  (1, 128, "78238d18a164b73544e1ecc5a9587a8833eabdc23a0841624a8b37e256debb8b04d24251293a5e62f0c822732f6bb90d4b5aec0796ab5a8d6ea8589afa81c4e5"),
  (1, 129, "b8866f51b3d34a1ac8127127ecbf0081086058747f2b81a1e4d85168139e47a01faa58495716c31cc43c015ccd2189684d02dd850d496899fb8a3d05f2f2fbb9"),
  (127, 0, "090420e80a97c4c1288ccfbf8968e90e49daff726c778941d96b1a91ae1980d92454931ac80482906b48543d8f48a488c56ff480a36dac559ee812f4323af879"),
  (127, 111, "e3bd523ab9bc0d2aaa7c2a31d682ad2b25322ef5552e51cce4622ceb9d954ed8ec57d88af0840815a81b17ebe964e1cb8ec6b0226e3817e2ba46f09a9277255b"),
  (127, 112, "3e364b2d009c88e2ef60b7576a522895bda12462208053fd40604371706c3c79a924f1c42e1592303e74ef020f9e6c8e2c0e4ee558ec32b0ff7f54e13b3e1e66"),
  (127, 127, "66c0eb4bbe7de7bf7dd412a7c8aae3bea3dc03b2ab03e32b1c7f531e32e815db6dbb3b98cc7e8bde7d1a8364cb6b67df19a6019c0b5dfa9ec8e1762c6b342dd2"),
  (127, 128, "2a2830f4a2f22706ef4e865aa4f9ebcfd1eb7b073ba23a044ba6033403cff67870c2d9921313efedabfc211c37d2d2f6f6de37a13a1b2dfffee51da9905a7ab6"),
  (127, 129, "fb6e9fd92ce1c36586060cec0e3ee15b59347b84c3265d7bce2ad394bbcc0251c9eea0dca46fdad2065f4c702dc7d4bae383cc903075210e03edacce2d6f5590"),
  (128, 0, "5caa30f44bc57e6f6051331a58f9f64e40338c16c62ce2a15586f7f9399bece27962e68443f276f73eae1a7545793b52d75c5b22db5131b5c0a8867b67735ee6"),
  (128, 111, "ab1ba76ce7be21addb0eeb2971902351e62006d21fbbd6571ac9acc53869404a7e9051ac83e67be81f37b2631e3d075911edfe270dd1c33b216eb20775357ba9"),
  (128, 112, "c5f8e5de74fc384b649337c06b8352390b33a337f19deb6c7e56d40655ee126d58d3637b00c016d6f5b3c28715b7a76c5d6daba35cd9f7c101b2c780df8fd218"),
  (128, 127, "c0f458b273dbf68ab87de33df6b4f25dd52cbb54aba06ad949c8dabb84387820c75f56150bf4a5dd6770b0539f7738b947518446725c93fea421c356f2702430"),
  (128, 128, "7259a42fa7e2da204441d4b7be336c06605978222fe7520f894efdb05611c407865d8ed2d1120ad6899ffc0f0cb270ede718403357a7efc8b9a7cac721e5f15f"),
  (128, 129, "5926c13c274ea7690f16a4cd6a754303c54c60aef68db4fca26274c38cdebc4a6904921d77526eaf96df88e525487b18f0c04797e35da1c7ddafba3be72c2351"),
  (129, 0, "b547d0848dd895e21b1ad99314969ce21c6f1dbc9f07ff12aa03efc5c876caf9f69d004a3e87f314b4165dcd8eacdbe593f678b4c73e1ed3164342f601576cc1"),
  (129, 111, "5a1a5ceec71b2b26c8467d1f72a6e9e722c686eb8c2688eb7110f2b940255e6b7c317aa3e3fac06ca091bb8fe693dd4202f6f199c3ba47645fe6252b0978da36"),
  (129, 112, "8df0858ceb5f6b00040137c1504e646a071d5b2586be6ad0c48532089932ef7ca6523267846c23b8538d90b9f64e6ba09b94b2dcf62a8565046688bd7325e23f"),
  (129, 127, "9748165160deb4c8ab3040cf45c7d4077799f688bfa2e253023e2f9dc2df22a0e1e1a22687aec43ec98690e00a6775ff878b78b0f6ff0093717ddbf6f7a75de0"),
  (129, 128, "fd316e9145d7daced22c87f819e4816090b34ff12f30e141c1192cf5b01e7d4e7f07da4a52e26d937672f6dea965703b533f5329633d79a05cce0eb277c78b44"),
  (129, 129, "9edfa232c36c8d885788df19142381b1eb85ebfdbaeee75a09dcd14c7a8e535fee7716eaa1c7e2033f9a075eeb087f044a267b7d1e84328ceaba77ca0468e740"),
  (200, 0, "346ad4825b2146f9955099f3b5d7157d7196ab3b6f341ca671ae301a02bfb61c098cca5b83b3b72652c51864d54d1840eedd78b49639316c2aa5721b38f5b1e2"),
  (200, 111, "69025cbe4ff399eafb3e2daf4e94f3408c19e52b26c8e898eb49139b230c17bae11118e0b7ca9bfa100527acc2bffa0ae1250c2a274558d3061e564b658b0fc2"),
  (200, 112, "0fbad2f3adead798f18df09e8119e053eab5bd327e0e4d2cd685fdde878fd7248f6b9e81af64234e294c6bb2af09177ef1794fd0e5cb64aca27b83fce3d0f0a9"),
  (200, 127, "3e11a525b163427b22a5e9d7e33f4c01ac23b330c856055ada5e123bbc524acf6ef73988c4b1303299accf71e32db99b2256149bd5270cecbbb361fbf0fd84f7"),
  (200, 128, "af380ff13fa97f914a581f53dcb198936f121327434652cb95c23e96259a580e12034bb0425719e7fe2cd929be5d22c64cb80efba72602871a882ee1042ff5e4"),
  (200, 129, "8ee911cce2d32796d90954e1adc110e82fae659ba6efe4598b9bbd929c3801abafd0c8a337bb271bd32909da9b8048a7cbc1fb5d3cbe84ca28c8f48fe884dd3b")]

example : hmacBoundaries.size = 36 := by native_decide
example : hmacBoundaries.all (fun (keySize, messageSize, expected) =>
    SHA512.hmac (pattern keySize) (pattern messageSize) == hex expected) = true := by native_decide

private def edgeVectors : Array (String × List Nat × KeyEncoding.Network × String × String) := #[
  ("031425364758697a8b9cadbecfe0f102132435465768798a9bacbdcedff00112", [0], .mainnet, "xprv9uAATLtQLMHoMTid8PiGssaJvCzR2Eq2R6aBsVtVmD5YPo9riBYL1S2YBsH4PSyKaH5dTvXm4VxJhByUXQdeYSCiCQ3rBcugLgKzV7P72Dg", "xpub689WrrRJAir6Zwo6ERFHF1X3UEpuRhYsnKVnftJ7KYcXGbV1FiraZEM239drC7y1kVHbuzXQgSgrJaHv8mUBZ9kBktvPtSM7KbxmKMVKXjb"),
  ("031425364758697a8b9cadbecfe0f102132435465768798a9bacbdcedff00112", [2147483647], .mainnet, "xprv9uAATLtYg1pmVkr3HPAU7jAZX8ZL8hschidhGhLYkRV2TZSH3ExFfcSZpYs8fJH5FSE1QMLC1mRgYmfuifhuZr7mcSmoSWPriXQ1tt2z7Ps", "xpub689WrrRSWPP4iEvWPQhUUs7J5APpYAbU4wZJ55kAJm21LMmRanGWDQm3frhniepszqXNFLimUeDWUujbSLgncAibctMf2422kSsWtGG7Y1a"),
  ("031425364758697a8b9cadbecfe0f102132435465768798a9bacbdcedff00112", [2147483648], .mainnet, "xprv9uAATLtYg1pmYU9xvbYHo87KNesmBpCyP7TZpK7jbNHKMMyTdw4JjNRDhQhSC9yX9RTdqdxhrKgy2DxACvGHvNg8yXUR3WALr3v6ynYEMMB", "xpub689WrrRSWPP4kxES2d5JAG43vgiFbGvpkLPAchXM9hpJEAJcBUNZHAjhYeBAE3A3Qh6G1Loh7are4iXaCFpv8xd4EhfBwkCs889cKjAU6qa"),
  ("031425364758697a8b9cadbecfe0f102132435465768798a9bacbdcedff00112", [4294967295], .mainnet, "xprv9uAATLth1gMjfkAnGi7Kkfuub7aua4F43Ts2cDfCxiNGZV27vPca4b6gH1178QwJSM5zCf7L6yAraBNhmTyYLnhNsBndyAsueSSKQ8Keu85", "xpub689WrrRar3v2tEFFNjeL7ore99RPyWxuQgndQc4pX3uFSHMGTvvpcPRA8K8kWw4v8BadB4xr59gPEDQiRRro5ScfmYgDWUoYYXsvuc3pVnS"),
  ("031425364758697a8b9cadbecfe0f102132435465768798a9bacbdcedff00112", [4294967295, 2147483647], .mainnet, "xprv9x5Q7So7D3sunzTWcVFW7SokuAfqAYJNPtUtL7gqwjRPtRJoiyTQoucjwLPdX8uetXAh7kBCSvgBsk3wH8i6ieLfGFbxBEPMVRV1CfqRGwP", "xpub6B4kWxL13RSD1UXyiWnWUakVTCWKa12Dm7QV8W6TW4xNmDdxGWmfMhwDndgetTuxTh9EGuv7MJ4KFu3aUhYuvsHLzd33kxHXbPr1QAeJBgM"),
  ("031425364758697a8b9cadbecfe0f102132435465768798a9bacbdcedff00112", [0, 2147483647, 42], .mainnet, "xprv9z39gysHsxaikbakL5tfV3id9C5y942UDWAx1KiV43kCmszxve9QAgDVojkXMsuohYLECJ4VHgXtFzt1kcstQiHL2E9mAeEcKMnpGR9VqXQ", "xpub6D2W6VQBiL91y5fDS7RfrBfMhDvTYWkKaj6Yoi86cPHBegL7UBTeiUXyf15XJgnNfhbjeMpdNvAEVMm2Kzzc1zpEfxm8NtaA4baWg1zyY6z"),
  ("031425364758697a8b9cadbecfe0f102132435465768798a9bacbdcedff00112233445566778899aabbccddeef00112233445566778899aabbccddeeff102132", [0], .testnet, "tprv8dFgfpBn3UHFqS94myfg3X62GAdFQPNjvV8J179sWVmxB5uXGPsaTR9R1MprDb9AY9e267jZr3KvEmAw4fDuzC7SSqiKkTXp6JT3dZNwm8v", "tpubD9wipEE2BqxviuArfdLGSvk8qC9BZiZeVnj5HdCAvmaM1aAHtnhAdumHBW223rz9DrUDKYCWGrUjhHUxYdRK1p9d8wtLP5MLRZP9cSAnKaQ"),
  ("031425364758697a8b9cadbecfe0f102132435465768798a9bacbdcedff00112233445566778899aabbccddeef00112233445566778899aabbccddeeff102132", [2147483647], .testnet, "tprv8dFgfpBvP8pDyi1ryQP8YvLbdrmuV9LbuAUpXzvbjAYcRjaBBmmCm94pRKic3W6vKFE5Vj75b7dALokBQgm3gsCUyjwdhyi9Qaa3xoPf5HE", "tpubD9wipEEAXWVtsB3es43ixKziCtHqeUXWUU5bpWxu9SM1GDpwpAanwdggbUG9sDAydqE3rGi5bbMMCbNrTQKcyPMuXN64GJ6e1WQFvaES6bX"),
  ("031425364758697a8b9cadbecfe0f102132435465768798a9bacbdcedff00112233445566778899aabbccddeef00112233445566778899aabbccddeeff102132", [2147483648], .testnet, "tprv8dFgfpBvP8pE1FLKG5sdFShhNEVCbN7ddgRp4jTzhHsqHrsJkTyj3qq5YHruSW3FumXU6KAxD8mge2mRuW2CRZte5vVxpqPyNhVY3gSe2Qk", "tpubD9wipEEAXWVttiN79jYDerMowG18khJYCz2bMFWJ7ZgE8M85NroKELSwiQco25EV8wgW2urKmNEyRKxLPEK1qKxPbYBFoXR7hFusyWnHNeA"),
  ("031425364758697a8b9cadbecfe0f102132435465768798a9bacbdcedff00112233445566778899aabbccddeef00112233445566778899aabbccddeeff102132", [4294967295], .testnet, "tprv8dFgfpC4ioMC8T91xWAZcudQxVgzhFSiAfCYgoy2Sfj4L1VdYeD7tFyHgwxcZkwzKtHZttThJqyiDxppP9db4GmSuq2Pki9CbQfcsdcoZoJ", "tpubD9wipEEJsB2s1vAor9qA2KHXXXCvradcjxoKyL1KrwXTAVkQB32i4kb9s7oCUsKb2E9mG64X7ziriHxXaD7ZTDZgj2tpMnxkcbn7uvwRHCX"),
  ("031425364758697a8b9cadbecfe0f102132435465768798a9bacbdcedff00112233445566778899aabbccddeef00112233445566778899aabbccddeeff102132", [4294967295, 2147483647], .testnet, "tprv8dqy9Wt5buKGbJHjS2BTmd2pXoJKqo2Ea51AffTWZ1pefn3bRVF3SEKsNEASCP5rnT38YXrh5Jg8sewMbetTdveNHN2P7JC4VVMZYFnvFtb", "tpubDAY1HvvKkGzwUmKXKfr4B2gw6ppG18D99NbwxBVoyHd3WGJN3t4dciwjYMq3xhsFrMsjXXEao7V57srkedCBn6Do9iJLojtkmShwSyYnhMw"),
  ("031425364758697a8b9cadbecfe0f102132435465768798a9bacbdcedff00112233445566778899aabbccddeef00112233445566778899aabbccddeeff102132", [0, 2147483647, 42], .testnet, "tprv8gHY9GjZNP8EZrUPNWfwkdmsAjshec9yYRSHCdViE8putKQT73z7RJfCRcj7M1mh35pjAVrd2MknzmM4HfH5TG9uNk4sKoyqGB9wD6P6hoe", "tpubDCyaHgmoWkouTKWBGALYA3RyjmPdowLt7j34V9Y1eQdJiofDjSohboH4bo5YD8BbaVTVdbi4ybM9NSgAGGyVwVE7cK4TphhsheR3fLk7r17")]

private def checkEdge (seed : String) (path : List Nat) (network : KeyEncoding.Network)
    (privateText publicText : String) : Bool :=
  match fromSeed (hex seed) network with
  | .error _ => false
  | .ok master =>
    let derived := derivePath master path
    let privateResult := stringResult (derived >>= serialize) privateText
    let publicResult := stringResult (derived >>= neuter >>= serialize) publicText
    let publicPath := if path.all (· < 0x80000000) then
      stringResult (neuter master >>= fun key => derivePath key path >>= serialize) publicText
      else true
    privateResult && publicResult && publicPath &&
      stringResult (parse privateText >>= serialize) privateText &&
      stringResult (parse publicText >>= serialize) publicText

example : edgeVectors.size = 12 := by native_decide
example : edgeVectors.all (fun (seed, path, network, privateText, publicText) =>
    checkEdge seed path network privateText publicText) = true := by native_decide

private def knownMaster : ExtendedKey := {
  network := .mainnet, depth := 0, parentFingerprint := ⟨#[0, 0, 0, 0]⟩,
  childNumber := 0, chainCode := pattern 32,
  material := .secret (hex "0000000000000000000000000000000000000000000000000000000000000001") }

-- Validate caller-constructed keys at every operation, including an empty path.
private def invalidConstructed : Array ExtendedKey := #[
  { knownMaster with depth := 256 },
  { knownMaster with parentFingerprint := ByteArray.empty },
  { knownMaster with parentFingerprint := ⟨#[0, 0, 0, 1]⟩ },
  { knownMaster with childNumber := 1 },
  { knownMaster with depth := 1, childNumber := 0x100000000 },
  { knownMaster with chainCode := pattern 31 },
  { knownMaster with material := .secret (⟨(List.replicate 32 0).toArray⟩) },
  { knownMaster with material := .publicKey (hex "0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8") },
  { knownMaster with material := .publicKey (hex "02fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f") }]
example : invalidConstructed.all (fun key => fails (publicKey key) && fails (serialize key) &&
    fails (neuter key) && fails (deriveChild key 0) && fails (derivePath key [])) = true :=
  by native_decide
example : fails (deriveChild knownMaster 0x100000000) = true := by native_decide
example : fails (neuter knownMaster >>= fun key => deriveChild key 0x80000000) = true :=
  by native_decide
example : fails (neuter knownMaster >>= fun key => deriveChild key 0xffffffff) = true :=
  by native_decide
example : fails (deriveChild { knownMaster with depth := 255 } 0) = true := by native_decide
example : (match deriveChild { knownMaster with depth := 254 } 0 with
    | .error _ => false
    | .ok child => child.depth == 255 && fails (deriveChild child 0)) = true := by native_decide
example : #[0, 15, 65].all (fun size => fails (fromSeed (pattern size))) = true := by native_decide

end LeanMiniscript.Bitcoin.BIP32
