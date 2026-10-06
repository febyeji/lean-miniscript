import LeanMiniscript.Script.Assembly
import LeanMiniscript.Script.Codec.Deserialization

/-!
Bitcoin Core's textual Script fixture syntax. A `0x...` token inserts
raw bytes, while quoted strings and integers compile to Script pushes.
-/

namespace LeanMiniscript.Extraction

open LeanMiniscript.Script

/-- Failures while translating Bitcoin Core's textual Script fixture syntax. -/
inductive CoreScriptSourceError where
  | unterminatedQuote
  | quoteInsideToken
  | invalidHex (token : String)
  | oddHexLength (token : String)
  | unsupportedToken (token : String)
  | serialization (error : SerializationError)
  | truncatedPushLength (offset width remaining : Nat)
  | truncatedPushData (offset expected remaining : Nat)
  | unsupportedOpcode (offset : Nat) (byte : UInt8)
  | decoderFuelExhausted (offset : Nat)
  deriving Repr, DecidableEq

/-- Preserve the fixture importer's public error categories while delegating
    byte decoding to the shared Script deserializer. -/
def CoreScriptSourceError.ofDeserialization :
    DeserializationError → CoreScriptSourceError
  | .truncatedPushLength offset width remaining =>
      .truncatedPushLength offset width remaining
  | .truncatedPushData offset expected remaining =>
      .truncatedPushData offset expected remaining
  | .unsupportedOpcode offset byte => .unsupportedOpcode offset byte

private inductive CoreSourceToken where
  | word (text : String)
  | quoted (text : String)

private def flushWord (wordRev : List Char)
    (tokensRev : List CoreSourceToken) : List CoreSourceToken :=
  match wordRev with
  | [] => tokensRev
  | _ => .word (String.ofList wordRev.reverse) :: tokensRev

private def tokenizeCoreSourceAux : List Char → List Char →
    List CoreSourceToken → Bool →
    Except CoreScriptSourceError (List CoreSourceToken)
  | [], _, _, true => .error .unterminatedQuote
  | [], wordRev, tokensRev, false => .ok (flushWord wordRev tokensRev).reverse
  | char :: rest, charsRev, tokensRev, true =>
      if char = '\'' then
        tokenizeCoreSourceAux rest []
          (.quoted (String.ofList charsRev.reverse) :: tokensRev) false
      else
        tokenizeCoreSourceAux rest (char :: charsRev) tokensRev true
  | char :: rest, wordRev, tokensRev, false =>
      if char.isWhitespace then
        tokenizeCoreSourceAux rest [] (flushWord wordRev tokensRev) false
      else if char = '\'' then
        match wordRev with
        | _ :: _ => .error .quoteInsideToken
        | [] => tokenizeCoreSourceAux rest [] tokensRev true
      else
        tokenizeCoreSourceAux rest (char :: wordRev) tokensRev false

private def tokenizeCoreSource (source : String) :
    Except CoreScriptSourceError (List CoreSourceToken) :=
  tokenizeCoreSourceAux source.toList [] [] false

private def hexNibble? : Char → Option Nat
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | 'a' | 'A' => some 10
  | 'b' | 'B' => some 11
  | 'c' | 'C' => some 12
  | 'd' | 'D' => some 13
  | 'e' | 'E' => some 14
  | 'f' | 'F' => some 15
  | _ => none

private def decodeHexChars (token : String) : List Char →
    Except CoreScriptSourceError (List UInt8)
  | [] => .ok []
  | [_] => .error (.oddHexLength token)
  | high :: low :: rest => do
      let highNibble ← match hexNibble? high with
        | some value => pure value
        | none => throw (.invalidHex token)
      let lowNibble ← match hexNibble? low with
        | some value => pure value
        | none => throw (.invalidHex token)
      return UInt8.ofNat (16 * highNibble + lowNibble) ::
        (← decodeHexChars token rest)

private def decodeRawHexToken (token : String) :
    Except CoreScriptSourceError ByteArray :=
  match token.toList with
  | '0' :: 'x' :: digits =>
      return ⟨(← decodeHexChars token digits).toArray⟩
  | '0' :: 'X' :: digits =>
      return ⟨(← decodeHexChars token digits).toArray⟩
  | _ => .error (.invalidHex token)

/-- Map the modeled opcode names used by Bitcoin Core fixture sources. -/
def opcodeFromCoreName? (name : String) : Option Opcode :=
  opcodeFromAssembly? name

/-- Decode raw Script bytes emitted by a Core fixture token, rejecting every
    opcode outside the modeled subset with its byte offset. -/
def deserializeCoreScriptBytes (bytes : ByteArray) :
    Except CoreScriptSourceError Script :=
  (deserializeScript bytes).mapError CoreScriptSourceError.ofDeserialization

/-- Legacy-only source aliases compile to their literal bytes, while the
shared Script AST continues to reject the corresponding unmodeled opcodes. -/
private def coreLegacyOpcodeByteFromName? : String → Option UInt8
  | "SHA1" => some 0xa7
  | "CODESEPARATOR" => some 0xab
  | "RESERVED" => some 0x50
  | "VER" => some 0x62
  | "VERIF" => some 0x65
  | "VERNOTIF" => some 0x66
  | "CAT" => some 0x7e
  | "SUBSTR" => some 0x7f
  | "LEFT" => some 0x80
  | "RIGHT" => some 0x81
  | "INVERT" => some 0x83
  | "AND" => some 0x84
  | "OR" => some 0x85
  | "XOR" => some 0x86
  | "RESERVED1" => some 0x89
  | "RESERVED2" => some 0x8a
  | "2MUL" => some 0x8d
  | "2DIV" => some 0x8e
  | "MUL" => some 0x95
  | "DIV" => some 0x96
  | "MOD" => some 0x97
  | "LSHIFT" => some 0x98
  | "RSHIFT" => some 0x99
  | _ => none

private def compileCoreToken : CoreSourceToken →
    Except CoreScriptSourceError ByteArray
  | .quoted text => (serializePushData text.toUTF8).mapError .serialization
  | .word token =>
      match token.toList with
      | '0' :: 'x' :: _ => decodeRawHexToken token
      | '0' :: 'X' :: _ => decodeRawHexToken token
      | _ =>
          match token.toInt? with
          | some number => (serializePushNum number).mapError .serialization
          | none =>
              match opcodeFromCoreName? token with
              | some opcode => .ok ⟨#[opcodeByte opcode]⟩
              | none =>
                  match coreLegacyOpcodeByteFromName? token with
                  | some byte => .ok ⟨#[byte]⟩
                  | none => .error (.unsupportedToken token)

/-- Compile Core's fixture tokens to the exact byte stream that its test
    utility feeds to the Script interpreter. -/
def coreScriptSourceBytes (source : String) :
    Except CoreScriptSourceError ByteArray := do
  let tokens ← tokenizeCoreSource source
  tokens.foldlM (fun bytes token => do
    let next ← compileCoreToken token
    pure (bytes ++ next)) ByteArray.empty

/-- Translate Bitcoin Core fixture source through its serialized-byte
    boundary into the modeled Script AST. -/
def parseCoreScriptSource (source : String) :
    Except CoreScriptSourceError Script := do
  let bytes ← coreScriptSourceBytes source
  deserializeCoreScriptBytes bytes

end LeanMiniscript.Extraction
