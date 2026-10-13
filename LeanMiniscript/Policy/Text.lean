import LeanMiniscript.Policy.Syntax
import LeanMiniscript.Miniscript.SurfaceParser

/-!
# Policy text

Policy text follows rust-miniscript's concrete policy syntax:

* `UNSATISFIABLE`, `TRIVIAL`;
* `pk(KEY)`, `after(N)`, `older(N)`;
* `sha256(H)`, `hash256(H)`, `ripemd160(H)`, `hash160(H)`;
* `and(X,Y)`, `or(X,Y)` with optional `N@` branch weights such as
  `or(99@pk(A),1@pk(B))`, and `thresh(k,X1,...,Xn)`.

The printer reuses the position-free `SurfaceText.Expr` grammar, and the parser
reuses the Miniscript tokenizer, recursion-depth scan, and raw expression
parser. `@` is an ordinary atom character for that tokenizer, so a weighted
branch arrives as a call or atom whose head name carries the `N@` prefix. Key
tokens are resolved by a caller-supplied `KeyResolver`; policies are
context-free, so context key normalization happens at compilation.
-/

namespace LeanMiniscript.Policy

open LeanMiniscript.Miniscript
open LeanMiniscript.Miniscript.SurfaceParser
open LeanMiniscript.Script (byteArrayHex)

/-! ## Printing -/

/-- Prefix the head name of a canonical expression with a branch weight. The
    default weight `1` is omitted. -/
def weightedExpr (weight : Nat) (expr : SurfaceText.Expr) : SurfaceText.Expr :=
  if weight = 1 then expr
  else
    match expr with
    | .atom value => .atom (toString weight ++ "@" ++ value)
    | .wrapper name inner => .wrapper (toString weight ++ "@" ++ name) inner
    | .call name arguments => .call (toString weight ++ "@" ++ name) arguments

namespace Policy

mutual
  /-- Canonical text expression for a policy with a caller-chosen key
      rendering. -/
  def toExprWith (renderKey : PubKey → String) : Policy → SurfaceText.Expr
    | .unsatisfiable => .atom "UNSATISFIABLE"
    | .trivial => .atom "TRIVIAL"
    | .key pubKey => .call "pk" [.atom (renderKey pubKey)]
    | .after n => .call "after" [.atom (toString n)]
    | .older n => .call "older" [.atom (toString n)]
    | .sha256 hash => .call "sha256" [.atom (byteArrayHex hash.bytes)]
    | .hash256 hash => .call "hash256" [.atom (byteArrayHex hash.bytes)]
    | .ripemd160 hash => .call "ripemd160" [.atom (byteArrayHex hash.bytes)]
    | .hash160 hash => .call "hash160" [.atom (byteArrayHex hash.bytes)]
    | .and left right =>
        .call "and" [toExprWith renderKey left, toExprWith renderKey right]
    | .or leftWeight left rightWeight right =>
        .call "or"
          [weightedExpr leftWeight (toExprWith renderKey left),
            weightedExpr rightWeight (toExprWith renderKey right)]
    | .thresh k subs =>
        .call "thresh" (.atom (toString k) :: listToExprWith renderKey subs)

  /-- Canonical text expressions for a list of policies. -/
  def listToExprWith (renderKey : PubKey → String) :
      List Policy → List SurfaceText.Expr
    | [] => []
    | sub :: subs => toExprWith renderKey sub :: listToExprWith renderKey subs
end

end Policy

/-- Render a policy with a caller-chosen key rendering. -/
def prettyPolicyWith (renderKey : PubKey → String) (policy : Policy) : String :=
  (policy.toExprWith renderKey).render

/-- Render a policy with canonical lowercase hexadecimal keys. -/
def prettyPolicy (policy : Policy) : String :=
  prettyPolicyWith prettyPubKey policy

/-! ## Parsing -/

/-- Split a character list at the first occurrence of `separator`. -/
def splitAtChar (separator : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | char :: chars =>
      if char = separator then some ([], chars)
      else (splitAtChar separator chars).map fun (before, after) =>
        (char :: before, after)

/-- Split `N@rest` at the first `@`. -/
def splitWeight (name : String) : Option (String × String) :=
  (splitAtChar '@' name.toList).map fun (weight, rest) =>
    (String.ofList weight, String.ofList rest)

/-- Remove an optional `N@` weight from the head of an `or` branch. -/
def stripWeight (position : Nat) (name : String) :
    Except SurfaceParseError (Nat × String) :=
  match splitWeight name with
  | none => pure (1, name)
  | some (weight, rest) =>
      match weight.toNat? with
      | some value => pure (value, rest)
      | none => .error (.invalidNumber position weight)

/-- Remove an optional branch weight from a raw `or` argument. -/
def stripRawWeight :
    RawSurfaceExpr → Except SurfaceParseError (Nat × RawSurfaceExpr)
  | .atom position value => do
      let (weight, rest) ← stripWeight position value
      pure (weight, .atom position rest)
  | .call position name arguments => do
      let (weight, rest) ← stripWeight position name
      pure (weight, .call position rest arguments)
  | raw@(.wrapper _ _ _) => pure (1, raw)

/-- Resolve one policy key token without context normalization. -/
def resolvePolicyKeyRaw (resolver : KeyResolver)
    (raw : RawSurfaceExpr) : Except SurfaceParseError PubKey := do
  let (position, token) ← rawAtom "a key token" raw
  match resolver token with
  | .error message => .error (.keyResolution position token message)
  | .ok key => pure key

/-- Elaborate a raw expression into a policy. The fuel only makes recursion
    structural; the public parser supplies the token count plus one. -/
def elaboratePolicyFuel (resolver : KeyResolver) :
    Nat → RawSurfaceExpr → Except SurfaceParseError Policy
  | 0, _ => .error (.unexpectedEnd "a policy within the elaboration budget")
  | _ + 1, .atom position value =>
      if value = "UNSATISFIABLE" then pure .unsatisfiable
      else if value = "TRIVIAL" then pure .trivial
      else .error (.unknownFragment position value)
  | _ + 1, .wrapper position name _ =>
      .error (.unknownWrapper position name)
  | fuel + 1, .call position name arguments => do
      if name = "pk" then
        let argument ← unaryArgument position name arguments
        pure (.key (← resolvePolicyKeyRaw resolver argument))
      else if name = "after" then
        let argument ← unaryArgument position name arguments
        pure (.after (← parseNatRaw "an absolute timelock" argument))
      else if name = "older" then
        let argument ← unaryArgument position name arguments
        pure (.older (← parseNatRaw "a relative timelock" argument))
      else if name = "sha256" then
        let argument ← unaryArgument position name arguments
        pure (.sha256 (Hash256.ofBytes (← parseHashBytes "sha256" 32 argument)))
      else if name = "hash256" then
        let argument ← unaryArgument position name arguments
        pure (.hash256 (Hash256.ofBytes (← parseHashBytes "hash256" 32 argument)))
      else if name = "ripemd160" then
        let argument ← unaryArgument position name arguments
        pure (.ripemd160
          (Hash160.ofBytes (← parseHashBytes "ripemd160" 20 argument)))
      else if name = "hash160" then
        let argument ← unaryArgument position name arguments
        pure (.hash160 (Hash160.ofBytes (← parseHashBytes "hash160" 20 argument)))
      else if name = "and" then
        let (leftRaw, rightRaw) ← binaryArguments position name arguments
        let left ← elaboratePolicyFuel resolver fuel leftRaw
        let right ← elaboratePolicyFuel resolver fuel rightRaw
        pure (.and left right)
      else if name = "or" then
        let (leftRaw, rightRaw) ← binaryArguments position name arguments
        let (leftWeight, leftRaw) ← stripRawWeight leftRaw
        let (rightWeight, rightRaw) ← stripRawWeight rightRaw
        let left ← elaboratePolicyFuel resolver fuel leftRaw
        let right ← elaboratePolicyFuel resolver fuel rightRaw
        pure (.or leftWeight left rightWeight right)
      else if name = "thresh" then
        let (thresholdRaw, subRaws) ← variadicArguments position name arguments
        let threshold ← parseNatRaw "a threshold" thresholdRaw
        let subs ← subRaws.mapM (elaboratePolicyFuel resolver fuel)
        pure (.thresh threshold subs)
      else
        .error (.unknownFragment position name)

/-- Whether policy text stays within the shared parser recursion boundary. -/
def policyTextWithinRecursionLimit (input : String) : Bool :=
  tokensWithinSurfaceRecursionLimit (tokenizeSurface input)

/-- Parse policy text, resolving keys with the supplied resolver. -/
def parsePolicy (resolver : KeyResolver) (input : String) :
    Except SurfaceParseError Policy := do
  let tokens := tokenizeSurface input
  if tokens.isEmpty then
    .error .emptyInput
  else if !tokensWithinSurfaceRecursionLimit tokens then
    .error (.maxRecursionDepthExceeded maxSurfaceRecursionDepth)
  else
    let (raw, remaining) ← parseRaw tokens
    match remaining with
    | token :: _ =>
        .error (.trailingInput token.position (tokenText token))
    | [] => elaboratePolicyFuel resolver (tokens.length + 1) raw

/-- Parse policy text whose key tokens are 32- or 33-byte hexadecimal keys. -/
def parsePolicyHex (input : String) : Except SurfaceParseError Policy :=
  parsePolicy resolveHexKey input

end LeanMiniscript.Policy
