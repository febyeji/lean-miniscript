import LeanMiniscript.Bitcoin.KeyEncoding

namespace LeanMiniscript.Bitcoin.KeyEncoding

private def digit (byte : UInt8) : Nat :=
  if byte.toNat ≤ 57 then byte.toNat - 48
  else if byte.toNat ≤ 70 then byte.toNat - 55 else byte.toNat - 87
private def decodeHex : List UInt8 → List UInt8
  | a :: b :: rest => UInt8.ofNat (16 * digit a + digit b) :: decodeHex rest
  | _ => []
private def hex (text : String) : ByteArray := ⟨(decodeHex text.toUTF8.data.toList).toArray⟩
private def succeedsWith (result : Except String ByteArray) (expected : ByteArray) : Bool :=
  match result with
  | .ok bytes => bytes == expected
  | .error _ => false
private def fails {α : Type} (result : Except String α) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

/-! Bitcoin Core vectors pinned at 9be056a8a72b624dae9623b2f7bded92c2a21c91:
https://github.com/bitcoin/bitcoin/tree/9be056a8a72b624dae9623b2f7bded92c2a21c91/src/test/data
base58_encode_decode.json SHA256: 20d51011f49339714c28b9244cc5238f4c78bb9206dc8fc61500aed6fc2682ca
key_io_valid.json SHA256: 90bd1d35d12763e0d00c5400b2c9fe551e532a821e1e466c20cad3aced70a7fe
key_io_invalid.json SHA256: c3ca74ddad7c01faaca7c26063537feb73ff2be03eb7fc83a42a655d2979261d
The public keys associated with Core's secret-key vectors were independently
computed with Python cryptography's OpenSSL-backed secp256k1 implementation. -/

private def rawVectors : Array (String × String) := #[
  ("", ""),
  ("61", "2g"),
  ("626262", "a3gV"),
  ("636363", "aPEr"),
  ("73696d706c792061206c6f6e6720737472696e67", "2cFupjhnEsSn59qHXstmK2ffpLv2"),
  ("00eb15231dfceb60925886b67d065299925915aeb172c06647", "1NS17iag9jJgTHD1VXjvLCEnZuQ3rJDE9L"),
  ("516b6fcd0f", "ABnLTmg"),
  ("bf4f89001e670274dd", "3SEo3LWLoPntC"),
  ("572e4794", "3EFU7m"),
  ("ecac89cad93923c02321", "EJDM8drfXA6uyA"),
  ("10c8511e", "Rt5zm"),
  ("00000000000000000000", "1111111111"),
  ("00000000000000000000000000000000000000000000000000000000000000000000000000000000", "1111111111111111111111111111111111111111"),
  ("00000000000000000000000000000000000000000000000000000000000000000000000000000001", "1111111111111111111111111111111111111112"),
  ("0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ec39d04c37e71e5d591881f6", "111111111111111111111111111111111111111111111111111111111111111111111111111111111111115TYzLYH1udmLdzCLM"),
  ("000111d38e5fc9071ffcd20b4a763cc9ae4f252bb4e48fd66a835e252ada93ff480d6dd43dc62a641155a5", "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"),
  ("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff", "1cWB5HCBdLjAuqGGReWE3R3CguuwSjw6RHn39s2yuDRTS5NsBgNiFpWgAnEx6VQi8csexkgYw3mdYrMHr8x9i7aEwP8kZ7vccXWqKDvGv3u1GxFKPuAkn8JCPPGDMf3vMMnbzm6Nh9zh1gcNsMvH3ZNLmP5fSG6DGbbi2tuwMWPthr4boWwCxf7ewSgNQeacyozhKDDQQ1qL5fQFUW52QKUZDZ5fw3KXNQJMcNTcaB723LchjeKun7MuGW5qyCBZYzA1KjofN1gYBV3NqyhQJ3Ns746GNuf9N2pQPmHz4xpnSrrfCvy6TVVz5d4PdrjeshsWQwpZsZGzvbdAdN8MKV5QsBDY"),
  ("271F359E", "zzzzy"),
  ("271F359F", "zzzzz"),
  ("271F35A0", "211111"),
  ("271F35A1", "211112")]

example : rawVectors.size = 21 := by native_decide
example : rawVectors.all (fun (bytes, encoded) =>
    encodeBase58 (hex bytes) == encoded && succeedsWith (decodeBase58 encoded) (hex bytes)) = true :=
  by native_decide

private def wifVectors : Array (String × String × Network × Bool × String) := #[
  ("5JuW2AMDYu4xVwRG9DZW18VbzQrGcd5RCgb99sS6ehJsNQXu5b9", "8f8943bf956de595665c38ffff23827e17c10cdc1c27a028caae6c9810626198", .mainnet, false, "04e2afefc080e25af9ae8d2f9d3108672eb25b42f1514196a2ff597b0d168895651909f99683db29c4d9d58e58a69eea1522a584b6d0bcda584a178e7383ba5490"),
  ("L5nJeqKmpHp4P7F8ZYyjwc5a7P4d8EabuGAzfGJk7yC1BJyzNaEd", "ff778740f88ddcf102aeb81daee289c044c4a4571c4b6f287400f4b8e0b843f8", .mainnet, true, "0295fa435f2d74f73b4baaec28115df0b32e0f1b10a340ade948c56a647fe92cdc"),
  ("92ZdE5HoLafywnTBbzPxbvRmp75pSfzvdU3XaZGh1cToipgdHVh", "80c32d81e91bdea04cd7a3819b32275fc3298af4c7ec87eb0099527d041ced5c", .testnet, false, "045e4f9467ad1d314e7270d66628dc3775af375aefae221445d453b4487b04ed218d68a65052c188c103f4f0bf5e1152a799e1ec12d864c53af7a363d9c5a81841"),
  ("cV83kKisF3RQSvXbUCm9ox3kaz5JjEUBWcx8tNydfGJcyeUxuH47", "e0fcd4ce4e3d0e3de091f21415bb7cd011fac288c42020a879f28c2a4387df9b", .testnet, true, "02ee1266376e264684abcec3e23784d71d4baa6e3f0a916bdec6073ea8ef03a51e"),
  ("92QuSnywrhsV7WPZChTgSQA23uSmj9MCEEno1eRBDG9sg8M29cX", "6cf636ed8ac1bab033b64f66feaba65f70e684731e3f39105605968d3a963801", .testnet, false, "04069ba5a268d5f8f3d5ca0554d91077eac94ed9eac83aded61309ae33dcbb8e0628f750c57b247a2371aa086e38705d906d108d5580c654947a92ca32939983ed"),
  ("cND53Dhp8eCZqG2ghe8YhSCGesXZ8fE5PGD1khrqNvEi4RBoXhEK", "12b5a10f3a11e708dc5412833c47ab7c368a21b9efe19293793ec879ce683018", .testnet, true, "0307f5771802fab42edffb2896c13d0834c04c637f12a75efb913b0aaf28f7e490"),
  ("91mn1wYKEB1zyof1VFm8tMtocZx1oBrKKRCu9GCpgZvPmBLEJjp", "18a86e5a6c6977ddba0daca7fba5190f67ba56ccdc1b3f31308972236c2e4776", .testnet, false, "0431929c2a2801729da4c7aa0bfd43cdd1313636d66712ee41eb3499e7fdc8718333fa18e6cc64f3f7e7343ee8f83c29a0bb02a864437344b396f3dd3c70c2107d"),
  ("cPisAUdLvqqAr6MYtXnrWvgvyUAwuNyuTvZkDGw6miPhZdaiSDNH", "3fdfec1371cedcdb8c190ca6ff8ad603f817edc0d93c2a687c7b36dd66e70f2a", .testnet, true, "03ea647ff30012df9a561c6941ee1dba66559ffa835f653d75e5bb5c7a33630337"),
  ("5HsL2nZuEebU5nM3RxNVQD9GcAnvNMahqQskf4fkqHe54zwd14e", "06e8649790a90615a46d22dd762e0c42615336745356c2e16147c0f3d46b40d5", .mainnet, false, "046bb95c214a7f2ed0069dfc117f62b5e54026b89faa66e0249d0687ff60d82e737be211e10710df1cdd91d1a99667d16dbcd9794a263c8503a95d03efddf4edbb"),
  ("KwuVvu6hsuEMHrfFWJQV64tRrWX3QzqHH18JuAHYqYV6dqBvNKxd", "147804bf8a0dfff35939a611c7f5a60ac107f33f33d6059f273d2079ab1d90f2", .mainnet, true, "0388ce2529c809f21008959fd3b2697f6f7cf5a116acd7a93f3b1c369aab0c7a3a"),
  ("921M1RNxghFcsVGqAJksQVbSgx36Yz4u6vebfz1wDujNvgNt93B", "3777b341c45e2a9b9bf6bfb71dc7d129f64f1b9406ed4f93ade8f56065f1b732", .testnet, false, "0476f45c6bf6bb5c975b6a9c47ea6c304a66cf70b6883ae49b056359dba29e136c6b8a60199bd69cdff4a90a60554b273653fe2222d0771513050f232b674ddb0c"),
  ("cNEnbfF2fcxmmCLWqMAaq6fxJvVkwMbyU3kCbpQznz4Z1j6TZDGb", "1397b0d4a03e1ab2c54dd9af99ce1ecbfb90c80a58886da95e1181a55703d96b", .testnet, true, "034f1641088921947a8ce957afe4057c9d739b9c6ec7ed2b421216a9a2be461690"),
  ("93BcpCMKPmFCuY8bqS4k3HFrhJ1Afxi4uSsEeJFvX86GYW7PC7W", "d27d1b6ef55ca2e4d475b5276f2dbb85f7a6459dceeb89c67b776fd3bb974452", .testnet, false, "04c0e513a8f56be8353af81ba8cd6a99f0eb13fb380d7ebc15cbe23029198519bd9483cda9ba5c3e4595f214a145df288284d419c8818eab15d06c5b5c318a8e51"),
  ("cUtwbyxoL1owPxUafgH2meEpydeywjhnTYv2mJaFHHchz39AaEgy", "da3ed4ef1647e1733ec076919cab6156077ed9532e7c365acc425747e198b3e1", .testnet, true, "03e1ce1e2c95fb2f97182d8550699b0ad870b6133cc70fbf2914c0c4a4164d3c1e"),
  ("927zPWny2SiNaUmHF5NnGQXQWDwbByfFzXGgu88j91ZoutSosvE", "468e0284f230153db8687d8ec23db079a5b67d72ca04174b3867b13e4ea9945e", .testnet, false, "04cfac43a4861acec124171c93694c8dbed49307f0d96ace32ac93ed50c6aab681096fd1629ee1f0d5775304c66bb632877249bcc04df192f0733011366497782b"),
  ("cRez45VGSp5EXNqm89K3NJJPSKKapJg5Kbw3atxr2337x2gtgYed", "798d87586cffbe8c545ab374454e403b1eb831501ebe89f3c3b02f3137bd7b46", .testnet, true, "0395b310f9ef4a6d24bd8034afed8f2f9f7b44b553325cea93be8fa0a3c7de92ea")]

example : wifVectors.size = 16 := by native_decide
example : wifVectors.all (fun (text, secret, network, compressed, publicKey) =>
    match decodeWIF text with
    | .error _ => false
    | .ok key => key.secret == hex secret && key.network == network &&
        key.compressed == compressed &&
        succeedsWith (publicKeyFromSecret key.secret key.compressed) (hex publicKey) &&
        validatePublicKey (hex publicKey) &&
        encodeBase58Check (⟨#[if network == .mainnet then 0x80 else 0xef]⟩ ++
          hex secret ++ if compressed then ⟨#[1]⟩ else ByteArray.empty) == text) = true :=
  by native_decide

private def invalidCoreKeys : Array String := #[
  "",
  "x",
  "1GAdfviErV2Ew95FPtZyikz2qGP3gyCB6Hyu94sedAkPpA523m3fQwps9YKUZkKgQckGPKhRsFR",
  "37G2kMDLpmWVhimxRdzwNfE8JFvWXnJYnVcXeeGrek2qumdJuK7XArcVVpRtLLjRra3t64BEPF2",
  "giymtio7u7oqWtmC9YnvAEKkLF3JQpAdkEFkVJKYrVDfaLbhaDpX1ihfF2vZmya1i61fwLPC3YQ",
  "8iVk9nLM3nYwRuwypjy9NK5rsuZH7BbrQRZ1pgcQmvMnjAgRXD",
  "cPTVQ1hbo4qdoysf6Jx5GthqucNmdfqt6J2pZRFeXv8Ep7Kmjqud",
  "cQbR2Ny85XFBzUMx3Ed6HsTLw2pVruSgPvt5AofnBUnhiv86gYeW",
  "2UB3iG3VJbX2TRrMwm6ssWskgvU9VjFBYSqCzwqkrihCwo7mg4mtS4WuGZgxTKuxf5A3EcotYEymz",
  "cQe12pqwPR6ExtZKfrKf1q4b3CTh1Qi7MwuvMvzs79nWXDvESfBJ",
  "tc1qeul5g2xfkvdkrhcfmdursv73ad64jnkjl9c40f",
  "bt1pq65rzej5glw3ra79gav6fqnx4haa0z257qr3mc8cggkefahmgvyseufhc0",
  "tb13hty4qmumlwpp6chxjvcyzza4duqgtmxw3xhm3u9ahj4nyhtwz8eq7ynrj4",
  "bcrt1r2qxpwuge",
  "bc10uexgzna2dpfk0vjt35srz6a27ps6m0l89jweznt83n2sqn2fx4hvn9ym5af8wut34sfrqhk3",
  "tb1qum6uh0pt4q253qaf520929737v63w5gf",
  "bcrt1q888ryfgxpvl0k7vum8zpyar2u2sexvdhkf38ue37yknmqq0ycrwpl3w48y",
  "bc1qdsuzmn04k2z8vryw8l4dj8m5ygqgnne5n",
  "tb1qlj8es50nc8j8r8xshrjgzmw5azx89efghmw8ju6zcqla0g6xcnrstsjz7k",
  "bcrt1qzwmyj0z924g7fzs5yvnrkc43y76RVyr2lh5t4r",
  "bc1qpu6d26mrulzetu4jqhd7rsunv9aqru26f5c4j8",
  "tb1qun6d26ufh77ghny6u5u8cwz9da7qwc6k4wkuceae9tth06eqlw0syupl4w",
  "bcrt1qj7g2jps453kj9htk9cxyyc2nxe69x4kzzmth7v",
  "bc1p702xksx4z3uqf0u2phllxkfe5cgu0adxptqs0uelx0tqt8e885sqryes2l",
  "tb1z7gmh0v6pc30z4xum76lmw8w86yswrlmw",
  "bcrt1sjsrw6nun4h502cr97xmnyyuhkr22q0s6efrgtu",
  "2UVPFpGYnLHJezFzjUo42our6PMEoozzRdM",
  "2MygHQjE1U33q3LSC53p69YqFjP8PihumJAF",
  "KzNbAQ4mexfAxa6RKBzHQqfoTycaeWpv2p",
  "2jDPrDfAKihCGPbPD9ztY8TswAia4V8Bc6vx",
  "4VQUNG1hG64QFtaNyQZQWDdwpxB275Pwb3tvyPt2HDxB8Mi2MgH8Tz3AC83YYiz9LydsLNXEZJLHY",
  "39TKsUQ5QpEL1wowc6GMUqak94ijirPuP69ooV3xsFmiKQX2dau",
  "2UEJjT3dSdwc8dAo7oedPzznXceXCEsBbDfAvSymqpqDrkZMv7JBEUpLyhkghioYAWC9W4sKysry",
  "7VmMEkphxCFSV1y659Th4dkk6x6bJS5eQvbt8rzUYKQyd6ACgwQ4vXHtXKFUwP2kW3XULipnHJdZ7",
  "tc1qdlapns4zkn03juf2k9xwwpct209suj6mgcd9gh",
  "bt1psa5eptk29c4jc9yumeseat3a0l5e2fpmw635za2p4gpwdnthueysxga9je",
  "tb13w8c43lykfj3lvm9sgp6dsnfjla3d57cm83seykunf0ltxjc9lt2q4efm4d",
  "bcrt1rjqr2tdkm",
  "bc10lyxwnxa70l270e6fcmxr4x7dtgu2yvy7gzkurwxy4zhdvgaqrrn6pfg2flyhqzy5t5se8yu3",
  "TB1QFDFM763VXVSUNZHQLPWC0Q8FG5LJX6ZN",
  "bcrt1q60chha7wfwlau4kdr4mlvyeyc8mnnh9dhxk05e0hmrxcuhghefj36uwyha",
  "bc1gmk9yu",
  "tb1ly0q7p",
  "bcrt1qdwttaw38uf42wxw40kwk3u8nguyTQH3hx6jmqp",
  "bc1qtsvlht6730n04f2mpaj5vv8hrledn5n5ug8c79",
  "tb1dclvmr",
  "bcrt1q3fqvctqu48wsvggrt09vj0yk2gzzcscdp4h98u",
  "bc1prklpq7tjcawg89cmwwqr3u5apwav36xa4zz56ady7crsllm6mpnqts7p86",
  "tb1zkm58zyhxz3ffkfgsyprflg543slsl4c4",
  "bcrt1snzr5kaypnfhpnjanrhd20fhqcjxm3hfh7dw9fu",
  "2GgnYKqBGuA2Mm5GnrPsMTZR81xPhNtgMYoFUZngZGiobhCuUpCaTriUHRcgFreEekNdPAR17q8d",
  "AZEah8d1EK362okRBS66e8SvdtYkrE8tsX",
  "gep8xr77FyPW6zYP15RiV9W8nL6w2HyHB16cUDakfyDceMA6ZzUdhJjk2LPuLYHnLkBqkRTTi6z",
  "2NDNP7GY59tTJPZTpbkprhM9SR99Nn5rUs7",
  "2Csgzy2T287YAjeU5tFtt1nPshBZAUFQi4WtgaWyZGKSBNnKXHy2Tmxo8QK4Mfdds977ShcDWC5o",
  "Kwjk3Vy6sdXMQDGWJzaWmqFxUNtWZCX1q4F4Kpt8jNNUoWJUUaTY",
  "Svj8kk98bAS9V4L2crmxakbhmnPm3cJ1tJ4Je4yVzDreU8eSTFURS1SPYv5oWEQD8Q9VBDvx5uF",
  "KNYsv6v9GtkGeD4WdQnBEJCrPKQm91PTxAbCfXr66LEd4JDmhPWC",
  "2UJ2H2xvAeXmFKfQwMyDoSdQTTPFMNCT3SsoUafBWKzoGP3NsUK1buEgQZG38viyD53jgMdpqfT7",
  "6aLMfayKF4TW4ecn5SEc8FExpyJA2peKxYRGZhes6tQ4NTTzuGy",
  "7VP4FmcebU2thJns9MnXde7LWfuqR5vMizrAuUoq2GcJjzTyA4RHFcPVdZL8PLg1SbpSFdJrvLXoY5",
  "tc1q5qdvt99uc92jyz663dtdpfpv6nr67ahmgwcpq2",
  "bt1peu3ppd7x796sjjenp09r8cs22rhylqm9lhggk72qp8q22vzft0wq2a0x6j",
  "tb1323z3lnz7dl3kd0nsuh6xy4he9almzl67anxgg3xdzkaxc9rwntlqdhdzd7",
  "bcrt1r2gc42sky",
  "bc10fd889x4hd54tqu2ewg9t4hhft2wl7m6x50av4uswzw46xe6as0xmltfg7vrjfkvm459vld7w",
  "TB1QZY7V0F2AT3308YGGNGN66ULJTCN3RY6F",
  "bcrt1qjg3cwht92znyw0l4r5rtctmls337nrc7g0ry9drjxmlecjd3atl3fake7c",
  "bc1qmgf8xt8xkecl79k04mma3lz34gqep7hg4",
  "TB1Q3F9WGNXE9ZMTTMDN5VKVKHYZ8Y0LCV72YV7V5LSXTJXEYHNHEHASLYL0TZ"]

example : invalidCoreKeys.size = 70 := by native_decide
example : invalidCoreKeys.all (fun text => fails (decodeWIF text)) = true := by native_decide

private def generatorCompressed : ByteArray :=
  hex "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
private def generatorUncompressed : ByteArray :=
  hex "0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8"
private def scalarOne : ByteArray := hex "0000000000000000000000000000000000000000000000000000000000000001"
private def scalarZero : ByteArray := hex "0000000000000000000000000000000000000000000000000000000000000000"
private def scalarOrder : ByteArray := hex "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141"
private def scalarLast : ByteArray := hex "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364140"

-- Known independent checksum vector plus explicit leading-zero payloads.
example : succeedsWith (decodeBase58Check "1111111111111111111114oLvT2") (hex "000000000000000000000000000000000000000000") = true := by native_decide
example : encodeBase58Check (hex "000000000000000000000000000000000000000000") = "1111111111111111111114oLvT2" := by native_decide
example : #[ByteArray.empty, hex "00", hex "000001", hex "ff"].all (fun payload =>
    succeedsWith (decodeBase58Check (encodeBase58Check payload)) payload) = true := by native_decide
example : #["", "1", "111", "1111", "1111111111111111111114oLvT3", "0", "O", "I", "l",
    " 1111111111111111111114oLvT2", "1111111111111111111114oLvT2 ", "é", "1\n1"].all
    (fun text => fails (decodeBase58Check text)) = true := by native_decide

-- Checksum-valid malformed payloads must still fail WIF semantic validation.
example : #[⟨#[0x80]⟩ ++ scalarZero, ⟨#[0x80]⟩ ++ scalarOrder,
    ⟨#[0x80]⟩ ++ scalarOne ++ ⟨#[2]⟩, ⟨#[0x80]⟩ ++ scalarOne ++ ⟨#[1, 0]⟩,
    ⟨#[0]⟩ ++ scalarOne, ⟨#[0xef]⟩ ++ scalarOne.extract 0 31].all
    (fun payload => fails (decodeWIF (encodeBase58Check payload))) = true := by native_decide
example : #[scalarZero, scalarOrder, scalarOne.extract 0 31, scalarOne.push 0].all
    (fun secret => fails (publicKeyFromSecret secret)) = true := by native_decide
example : succeedsWith (publicKeyFromSecret scalarOne) generatorCompressed = true := by native_decide
example : succeedsWith (publicKeyFromSecret scalarOne false) generatorUncompressed = true := by native_decide
example : succeedsWith (publicKeyFromSecret scalarLast) (generatorCompressed.set! 0 3) = true := by native_decide

-- SEC encodings check actual curve membership, canonical fields and prefixes.
example : validatePublicKey generatorCompressed = true := by native_decide
example : validatePublicKey (generatorCompressed.set! 0 3) = true := by native_decide
example : validatePublicKey generatorUncompressed = true := by native_decide
example : #[ByteArray.empty, generatorCompressed.extract 0 32, generatorCompressed.push 0,
    generatorCompressed.set! 0 4, generatorUncompressed.set! 0 6,
    generatorUncompressed.set! 0 7, generatorUncompressed.set! 64 0,
    hex "02fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f",
    ⟨#[2]⟩ ++ scalarZero, ⟨#[4]⟩ ++ scalarZero ++ scalarZero,
    ⟨#[4]⟩ ++ generatorCompressed.extract 1 33 ++
      hex "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"].all
    (fun key => !validatePublicKey key) = true := by native_decide

end LeanMiniscript.Bitcoin.KeyEncoding
