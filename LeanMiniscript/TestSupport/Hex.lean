import LeanMiniscript.Script.Assembly

namespace LeanMiniscript.TestSupport

/-- Decode trusted, even-length fixture hex in either letter case.
Out-of-contract input decodes to no bytes. -/
def hex (text : String) : ByteArray :=
  match LeanMiniscript.Script.decodeHexChars? text.toList with
  | some bytes => ⟨bytes.toArray⟩
  | none => ⟨#[]⟩

end LeanMiniscript.TestSupport
