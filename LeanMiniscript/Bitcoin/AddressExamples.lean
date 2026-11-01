import LeanMiniscript.TestSupport.Hex
import LeanMiniscript.Bitcoin.Address

namespace LeanMiniscript.Bitcoin.Address

open LeanMiniscript.TestSupport (hex)

private def decodesTo (address script : String) : Bool :=
  match scriptPubKey address with
  | .ok bytes => bytes == hex script
  | .error _ => false

private def rejected (address : String) : Bool :=
  match scriptPubKey address with
  | .ok _ => false
  | .error _ => true

/-! Segwit address vectors from BIP350's "Test vectors for v0-v16 native
segregated witness addresses", which repeats BIP173's v0 vectors and adds
Bech32m vectors for versions 1 to 16:
https://github.com/bitcoin/bips/blob/master/bip-0350.mediawiki#test-vectors-for-v0-v16-native-segregated-witness-addresses -/

private def validSegwit : Array (String × String) := #[
  ("BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4",
   "0014751e76e8199196d454941c45d1b3a323f1433bd6"),
  ("tb1qrp33g0q5c5txsp9arysrx4k6zdkfs4nce4xj0gdcccefvpysxf3q0sl5k7",
   "00201863143c14c5166804bd19203356da136c985678cd4d27a1b8c6329604903262"),
  ("bc1pw508d6qejxtdg4y5r3zarvary0c5xw7kw508d6qejxtdg4y5r3zarvary0c5xw7kt5nd6y",
   "5128751e76e8199196d454941c45d1b3a323f1433bd6751e76e8199196d454941c45d1b3a323f1433bd6"),
  ("BC1SW50QGDZ25J", "6002751e"),
  ("bc1zw508d6qejxtdg4y5r3zarvaryvaxxpcs", "5210751e76e8199196d454941c45d1b3a323"),
  ("tb1qqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesrxh6hy",
   "0020000000c4a5cad46221b2a187905e5266362b99d5e91c6ce24d165dab93e86433"),
  ("tb1pqqqqp399et2xygdj5xreqhjjvcmzhxw4aywxecjdzew6hylgvsesf3hn0c",
   "5120000000c4a5cad46221b2a187905e5266362b99d5e91c6ce24d165dab93e86433"),
  ("bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0",
   "512079be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")]

example : validSegwit.all (fun (address, script) => decodesTo address script) = true := by
  native_decide

/-- BIP350 invalid addresses: unknown prefix, wrong checksum variant for the
version, invalid character, version 17, invalid program lengths, mixed case,
excess or nonzero padding, and an empty data section. -/
private def invalidSegwit : Array String := #[
  "tc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq5zuyut",
  "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqh2y7hd",
  "tb1z0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqglt7rf",
  "BC1S0XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ54WELL",
  "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kemeawh",
  "tb1q0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq24jc47",
  "bc1p38j9r5y49hruaue7wxjce0updqjuyyx0kh56v8s25huc6995vvpql3jow4",
  "BC130XLXVLHEMJA6C4DQV22UAPCTQUPFHLXM9H8Z3K2E72Q4K9HCZ7VQ7ZWS8R",
  "bc1pw5dgrnzv",
  "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v8n0nx0muaewav253zgeav",
  "BC1QR508D6QEJXTDG4Y5R3ZARVARYV98GJ9P",
  "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vq47Zagq",
  "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7v07qwwzcrf",
  "tb1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vpggkg4j",
  "bc1gmk9yu"]

example : invalidSegwit.all rejected = true := by native_decide

/-- The Bech32 and Bech32m checksum constants select the variant. -/
example : (match decodeBech32 "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0" with
    | .ok (hrp, _, variant) => hrp == "bc" && variant == .bech32m
    | .error _ => false) = true := by native_decide

example : (match decodeBech32 "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4" with
    | .ok (hrp, _, variant) => hrp == "bc" && variant == .bech32
    | .error _ => false) = true := by native_decide

/-! Base58Check addresses for HASH160 of the compressed generator point
`751e76e8199196d454941c45d1b3a323f1433bd6`, on mainnet and testnet. -/

example : decodesTo "1BgGZ9tcN4rm9KBzDn7KprQz87SZ26SAMH"
    "76a914751e76e8199196d454941c45d1b3a323f1433bd688ac" = true := by native_decide

example : decodesTo "mrCDrCybB6J1vRfbwM5hemdJz73FwDBC8r"
    "76a914751e76e8199196d454941c45d1b3a323f1433bd688ac" = true := by native_decide

/-- A WIF secret key is valid Base58Check with the wrong payload size. -/
example : rejected "L4rK1yDtCWekvXuE6oXD9jCYfFNV2cWRpVuPLBcCU2z8TrisoyY1" = true := by
  native_decide

/-- A Base58Check payload with an unknown version byte. -/
example : rejected (KeyEncoding.encodeBase58Check
    (⟨#[0x30]⟩ ++ hex "751e76e8199196d454941c45d1b3a323f1433bd6")) = true := by
  native_decide

end LeanMiniscript.Bitcoin.Address
