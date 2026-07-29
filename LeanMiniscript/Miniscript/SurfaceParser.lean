import LeanMiniscript.Miniscript.SurfaceNormalize
import LeanMiniscript.Miniscript.ValidationDecidable

namespace LeanMiniscript.Miniscript

/-!
# Context-aware surface parser

Parsing is split into two boundaries:

1. a generic tokenizer and raw expression parser, which reports syntax and
   arity errors without knowing about keys; and
2. elaboration into `SurfaceFragment`, which resolves key tokens, decodes hash
   literals, and checks the selected P2WSH or Tapscript context.

Descriptor decoding and derivation remain outside this module. Callers provide
the key resolver used at the elaboration boundary.
-/

/-- Resolve one textual key token to public-key bytes. Context normalization
    happens after resolution, and the error string is preserved in
    `SurfaceParseError`. -/
abbrev KeyResolver := String → Except String PubKey

/-- Structured failures produced by the surface text boundary. -/
inductive SurfaceParseError where
  | emptyInput
  | unexpectedEnd (expected : String)
  | unexpectedToken (position : Nat) (expected found : String)
  | trailingInput (position : Nat) (found : String)
  | unknownFragment (position : Nat) (name : String)
  | unknownWrapper (position : Nat) (name : String)
  | invalidArity (position : Nat) (name expected : String) (actual : Nat)
  | expectedAtom (position : Nat) (role : String)
  | invalidNumber (position : Nat) (text : String)
  | invalidHex (position : Nat) (role text : String)
  | invalidHashLength (position : Nat) (role : String) (expected actual : Nat)
  | keyResolution (position : Nat) (token message : String)
  | keyContext (position : Nat) (token : String) (context : ScriptContext)
  | contextMismatch (position : Nat) (fragment : String) (context : ScriptContext)
  | validationFailed (context : ScriptContext)
  deriving Repr, DecidableEq, BEq, Inhabited

private inductive SurfaceTokenKind where
  | atom (value : String)
  | leftParen
  | rightParen
  | comma
  | colon
  deriving Repr

private structure SurfaceToken where
  kind : SurfaceTokenKind
  position : Nat
  deriving Repr

private inductive RawSurfaceExpr where
  | atom (position : Nat) (value : String)
  | wrapper (position : Nat) (name : String) (inner : RawSurfaceExpr)
  | call (position : Nat) (name : String) (arguments : List RawSurfaceExpr)
  deriving Repr, Inhabited

private def isSurfaceSpace : Char → Bool
  | ' ' | '\t' | '\n' | '\r' => true
  | _ => false

private def isSurfacePunctuation : Char → Bool
  | '(' | ')' | ',' | ':' => true
  | _ => false

private def finishTokenizedAtom (position : Nat) (reversed : List Char)
    (tail : List SurfaceToken) : List SurfaceToken :=
  match reversed with
  | [] => tail
  | _ =>
      ⟨.atom (String.ofList reversed.reverse), position⟩ :: tail

private def tokenizeChars (position atomPosition : Nat)
    (reversedAtom : List Char) : List Char → List SurfaceToken
  | [] => finishTokenizedAtom atomPosition reversedAtom []
  | char :: rest =>
      if isSurfaceSpace char then
        finishTokenizedAtom atomPosition reversedAtom
          (tokenizeChars (position + 1) (position + 1) [] rest)
      else
        match char with
        | '(' =>
            finishTokenizedAtom atomPosition reversedAtom
              (⟨.leftParen, position⟩ ::
                tokenizeChars (position + 1) (position + 1) [] rest)
        | ')' =>
            finishTokenizedAtom atomPosition reversedAtom
              (⟨.rightParen, position⟩ ::
                tokenizeChars (position + 1) (position + 1) [] rest)
        | ',' =>
            finishTokenizedAtom atomPosition reversedAtom
              (⟨.comma, position⟩ ::
                tokenizeChars (position + 1) (position + 1) [] rest)
        | ':' =>
            finishTokenizedAtom atomPosition reversedAtom
              (⟨.colon, position⟩ ::
                tokenizeChars (position + 1) (position + 1) [] rest)
        | _ =>
            let start :=
              if reversedAtom.isEmpty then position else atomPosition
            tokenizeChars (position + 1) start (char :: reversedAtom) rest

private def tokenizeSurface (input : String) : List SurfaceToken :=
  tokenizeChars 0 0 [] input.toList

private def tokenText (token : SurfaceToken) : String :=
  match token.kind with
  | .atom value => value
  | .leftParen => "("
  | .rightParen => ")"
  | .comma => ","
  | .colon => ":"

private abbrev RawParseResult :=
  Except SurfaceParseError (RawSurfaceExpr × List SurfaceToken)

private abbrev RawArgumentsResult :=
  Except SurfaceParseError (List RawSurfaceExpr × List SurfaceToken)

mutual
  private def parseRawFuel : Nat → List SurfaceToken → RawParseResult
    | 0, _ => .error (.unexpectedEnd "a fragment within the parser budget")
    | _ + 1, [] => .error (.unexpectedEnd "a Miniscript fragment")
    | fuel + 1, token :: rest =>
        match token.kind with
        | .atom name =>
            match rest with
            | next :: remaining =>
                match next.kind with
                | .colon => do
                    let (inner, tail) ← parseRawFuel fuel remaining
                    pure (.wrapper token.position name inner, tail)
                | .leftParen => do
                    let (arguments, tail) ← parseRawArgumentsFuel fuel remaining
                    pure (.call token.position name arguments, tail)
                | _ => pure (.atom token.position name, rest)
            | [] => pure (.atom token.position name, [])
        | _ =>
            .error (.unexpectedToken token.position
              "a fragment name, wrapper, 0, or 1" (tokenText token))

  private def parseRawArgumentsFuel :
      Nat → List SurfaceToken → RawArgumentsResult
    | 0, _ => .error (.unexpectedEnd "arguments within the parser budget")
    | _ + 1, [] => .error (.unexpectedEnd "an argument or )")
    | fuel + 1, token :: rest =>
        match token.kind with
        | .rightParen => pure ([], rest)
        | _ => do
            let (first, remaining) ← parseRawFuel fuel (token :: rest)
            parseMoreRawArgumentsFuel [first] fuel remaining

  private def parseMoreRawArgumentsFuel
      (reversed : List RawSurfaceExpr) :
      Nat → List SurfaceToken → RawArgumentsResult
    | 0, _ => .error (.unexpectedEnd "more arguments within the parser budget")
    | _ + 1, [] => .error (.unexpectedEnd ", or )")
    | fuel + 1, token :: rest =>
        match token.kind with
        | .rightParen => pure (reversed.reverse, rest)
        | .comma => do
            let (next, remaining) ← parseRawFuel fuel rest
            parseMoreRawArgumentsFuel (next :: reversed) fuel remaining
        | _ =>
            .error (.unexpectedToken token.position ", or )" (tokenText token))
end

private def parseRaw (tokens : List SurfaceToken) : RawParseResult :=
  parseRawFuel (tokens.length + 1) tokens

private def unaryArgument (position : Nat) (name : String) :
    List RawSurfaceExpr → Except SurfaceParseError RawSurfaceExpr
  | [argument] => pure argument
  | arguments =>
      .error (.invalidArity position name "exactly 1 argument" arguments.length)

private def binaryArguments (position : Nat) (name : String) :
    List RawSurfaceExpr →
      Except SurfaceParseError (RawSurfaceExpr × RawSurfaceExpr)
  | [x, y] => pure (x, y)
  | arguments =>
      .error (.invalidArity position name "exactly 2 arguments" arguments.length)

private def ternaryArguments (position : Nat) (name : String) :
    List RawSurfaceExpr →
      Except SurfaceParseError (RawSurfaceExpr × RawSurfaceExpr × RawSurfaceExpr)
  | [x, y, z] => pure (x, y, z)
  | arguments =>
      .error (.invalidArity position name "exactly 3 arguments" arguments.length)

private def variadicArguments (position : Nat) (name : String) :
    List RawSurfaceExpr →
      Except SurfaceParseError (RawSurfaceExpr × List RawSurfaceExpr)
  | first :: rest =>
      if rest.isEmpty then
        .error (.invalidArity position name
          "a threshold and at least 1 item" 1)
      else
        pure (first, rest)
  | [] =>
      .error (.invalidArity position name
        "a threshold and at least 1 item" 0)

private def rawAtom (role : String) :
    RawSurfaceExpr → Except SurfaceParseError (Nat × String)
  | .atom position value => pure (position, value)
  | .wrapper position _ _ | .call position _ _ =>
      .error (.expectedAtom position role)

private def parseNatRaw (role : String)
    (raw : RawSurfaceExpr) : Except SurfaceParseError Nat := do
  let (position, text) ← rawAtom role raw
  match text.toNat? with
  | some value => pure value
  | none => .error (.invalidNumber position text)

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

private def decodeHexChars? : List Char → Option (List UInt8)
  | [] => some []
  | high :: low :: rest => do
      let highValue ← hexNibble? high
      let lowValue ← hexNibble? low
      let tail ← decodeHexChars? rest
      pure (UInt8.ofNat (highValue * 16 + lowValue) :: tail)
  | [_] => none

private def decodeHex? (text : String) : Option ByteArray := do
  let bytes ← decodeHexChars? text.toList
  pure ⟨bytes.toArray⟩

/-- Default key resolver for canonical lowercase or uppercase hexadecimal key
    tokens. Context-specific length checks remain in `parseSurface`. -/
def resolveHexKey (token : String) : Except String PubKey :=
  match decodeHex? token with
  | some bytes => pure (PubKey.ofBytes bytes)
  | none => .error "expected an even-length hexadecimal public key"

private def parseHashBytes (role : String) (expectedLength : Nat)
    (raw : RawSurfaceExpr) : Except SurfaceParseError ByteArray := do
  let (position, text) ← rawAtom role raw
  match decodeHex? text with
  | none => .error (.invalidHex position role text)
  | some bytes =>
      if bytes.size = expectedLength then
        pure bytes
      else
        .error (.invalidHashLength position role expectedLength bytes.size)

/-- Normalize resolved key bytes to the representation embedded in Script.
    BIP 386 permits compressed key expressions under `tr()`, but their
    33-byte serialization must become a 32-byte x-only Tapscript key. -/
private def normalizeKeyForContext
    (context : ScriptContext) (key : PubKey) : Option PubKey :=
  match context with
  | .p2wsh =>
      if key.size = 33 then some key else none
  | .tapscript =>
      if key.size = 32 then
        some key
      else if key.size = 33 then
        let keyPrefix := key.bytes.get! 0
        if keyPrefix = 0x02 || keyPrefix = 0x03 then
          some (PubKey.ofBytes (key.bytes.extract 1 33))
        else
          none
      else
        none

private def resolveKeyRaw (context : ScriptContext) (resolver : KeyResolver)
    (raw : RawSurfaceExpr) : Except SurfaceParseError PubKey := do
  let (position, token) ← rawAtom "a key token" raw
  match resolver token with
  | .error message => .error (.keyResolution position token message)
  | .ok key =>
      match normalizeKeyForContext context key with
      | some normalized => pure normalized
      | none => .error (.keyContext position token context)

private def validateSurface (context : ScriptContext)
    (fragment : SurfaceFragment) : Except SurfaceParseError SurfaceFragment :=
  if _ : fragment.WellFormed context then
    pure fragment
  else
    .error (.validationFailed context)

private def applyWrapper (position : Nat) (wrapper : Char)
    (fragment : SurfaceFragment) : Except SurfaceParseError SurfaceFragment :=
  match wrapper with
  | 'a' => pure (.core (.a (desugar fragment)))
  | 's' => pure (.core (.s (desugar fragment)))
  | 'c' => pure (.core (.c (desugar fragment)))
  | 'd' => pure (.core (.d (desugar fragment)))
  | 'v' => pure (.core (.v (desugar fragment)))
  | 'j' => pure (.core (.j (desugar fragment)))
  | 'n' => pure (.core (.n (desugar fragment)))
  | 't' => pure (.t fragment)
  | 'l' => pure (.l fragment)
  | 'u' => pure (.u fragment)
  | unknown =>
      .error (.unknownWrapper position (String.ofList [unknown]))

private def applyWrapperChain (position : Nat) (name : String)
    (inner : SurfaceFragment) : Except SurfaceParseError SurfaceFragment :=
  name.toList.foldrM (applyWrapper position) inner

private def elaborateRawFuel (context : ScriptContext)
    (resolver : KeyResolver) :
      Nat → RawSurfaceExpr → Except SurfaceParseError SurfaceFragment
  | 0, _ =>
      .error (.unexpectedEnd "a fragment within the elaboration budget")
  | _ + 1, .atom position value =>
      if value = "0" then
        pure (.core .zero)
      else if value = "1" then
        pure (.core .one)
      else
        .error (.unknownFragment position value)
  | fuel + 1, .wrapper position name inner => do
      let fragment ← elaborateRawFuel context resolver fuel inner
      applyWrapperChain position name fragment
  | fuel + 1, .call position name arguments => do
      if name = "pk" then
        let argument ← unaryArgument position name arguments
        let key ← resolveKeyRaw context resolver argument
        pure (.pk key)
      else if name = "pkh" then
        let argument ← unaryArgument position name arguments
        let key ← resolveKeyRaw context resolver argument
        pure (.pkh key)
      else if name = "pk_k" then
        let argument ← unaryArgument position name arguments
        let key ← resolveKeyRaw context resolver argument
        pure (.core (.pk_k key))
      else if name = "pk_h" then
        let argument ← unaryArgument position name arguments
        let key ← resolveKeyRaw context resolver argument
        pure (.core (.pk_h key))
      else if name = "older" then
        let argument ← unaryArgument position name arguments
        pure (.core (.older (← parseNatRaw "a relative timelock" argument)))
      else if name = "after" then
        let argument ← unaryArgument position name arguments
        pure (.core (.after (← parseNatRaw "an absolute timelock" argument)))
      else if name = "sha256" then
        let argument ← unaryArgument position name arguments
        let bytes ← parseHashBytes "sha256" 32 argument
        pure (.core (.sha256 (Hash256.ofBytes bytes)))
      else if name = "hash256" then
        let argument ← unaryArgument position name arguments
        let bytes ← parseHashBytes "hash256" 32 argument
        pure (.core (.hash256 (Hash256.ofBytes bytes)))
      else if name = "ripemd160" then
        let argument ← unaryArgument position name arguments
        let bytes ← parseHashBytes "ripemd160" 20 argument
        pure (.core (.ripemd160 (Hash160.ofBytes bytes)))
      else if name = "hash160" then
        let argument ← unaryArgument position name arguments
        let bytes ← parseHashBytes "hash160" 20 argument
        pure (.core (.hash160 (Hash160.ofBytes bytes)))
      else if name = "and_n" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.and_n x y)
      else if name = "and_v" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.core (.and_v (desugar x) (desugar y)))
      else if name = "and_b" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.core (.and_b (desugar x) (desugar y)))
      else if name = "or_b" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.core (.or_b (desugar x) (desugar y)))
      else if name = "or_c" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.core (.or_c (desugar x) (desugar y)))
      else if name = "or_d" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.core (.or_d (desugar x) (desugar y)))
      else if name = "or_i" then
        let (xRaw, yRaw) ← binaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        pure (.core (.or_i (desugar x) (desugar y)))
      else if name = "andor" then
        let (xRaw, yRaw, zRaw) ← ternaryArguments position name arguments
        let x ← elaborateRawFuel context resolver fuel xRaw
        let y ← elaborateRawFuel context resolver fuel yRaw
        let z ← elaborateRawFuel context resolver fuel zRaw
        pure (.core (.andor (desugar x) (desugar y) (desugar z)))
      else if name = "thresh" then
        let (thresholdRaw, fragmentRaws) ←
          variadicArguments position name arguments
        let threshold ← parseNatRaw "a threshold" thresholdRaw
        let fragments ←
          fragmentRaws.mapM (elaborateRawFuel context resolver fuel)
        pure (.core (.thresh threshold (fragments.map desugar)))
      else if name = "multi" then
        let (thresholdRaw, keyRaws) ←
          variadicArguments position name arguments
        match context with
        | .tapscript =>
            .error (.contextMismatch position name context)
        | .p2wsh =>
            let threshold ← parseNatRaw "a threshold" thresholdRaw
            let keys ← keyRaws.mapM (resolveKeyRaw context resolver)
            pure (.core (.multi threshold keys))
      else if name = "multi_a" then
        let (thresholdRaw, keyRaws) ←
          variadicArguments position name arguments
        match context with
        | .p2wsh =>
            .error (.contextMismatch position name context)
        | .tapscript =>
            let threshold ← parseNatRaw "a threshold" thresholdRaw
            let keys ← keyRaws.mapM (resolveKeyRaw context resolver)
            pure (.core (.multi_a threshold keys))
      else
        .error (.unknownFragment position name)

/-- Parse one supported Miniscript expression, resolve its keys, normalize its
    surface spelling, and reject fragments invalid in the selected context. -/
def parseSurface (context : ScriptContext) (resolver : KeyResolver)
    (input : String) : Except SurfaceParseError SurfaceFragment := do
  let tokens := tokenizeSurface input
  if tokens.isEmpty then
    .error .emptyInput
  else
    let (raw, remaining) ← parseRaw tokens
    match remaining with
    | token :: _ =>
        .error (.trailingInput token.position (tokenText token))
    | [] =>
        let fragment ←
          elaborateRawFuel context resolver (tokens.length + 1) raw
        validateSurface context (normalizeSurface fragment)

/-- Parse canonical surface text whose key tokens are raw hexadecimal public
    keys. -/
def parseSurfaceHex (context : ScriptContext) (input : String) :
    Except SurfaceParseError SurfaceFragment :=
  parseSurface context resolveHexKey input

end LeanMiniscript.Miniscript
