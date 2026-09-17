import LeanHash160

namespace LeanMiniscript.Bitcoin

/-- Domain-separated SHA256 shared by BIP340 and Taproot commitment/signing hashes. -/
def taggedHash (tag : String) (message : ByteArray) : ByteArray :=
  let tagHash := LeanHash160.SHA256.hash tag.toUTF8
  LeanHash160.SHA256.hash (tagHash ++ tagHash ++ message)

end LeanMiniscript.Bitcoin
