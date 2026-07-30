import LeanMiniscript.Miniscript.SurfaceNormalize
import LeanMiniscript.Script.Assembly

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- Render a resolved public key as a canonical lowercase hexadecimal token. -/
def prettyPubKey (key : PubKey) : String :=
  byteArrayHex key.bytes

private def prependWrappers (wrappers body : String) : String :=
  if wrappers.isEmpty then body else wrappers ++ ":" ++ body

/-- Render a core fragment while accumulating consecutive BIP 379 wrapper
    letters. The specification uses one colon after the complete wrapper chain:
    `dv:older(144)`, not `d:v:older(144)`. -/
private def prettyCoreWithWrappers (renderKey : PubKey → String) :
    String → CoreFragment → String
  | wrappers, .zero => prependWrappers wrappers "0"
  | wrappers, .one => prependWrappers wrappers "1"
  | wrappers, .c (.pk_k key) =>
      prependWrappers wrappers ("pk(" ++ renderKey key ++ ")")
  | wrappers, .c (.pk_h key) =>
      prependWrappers wrappers ("pkh(" ++ renderKey key ++ ")")
  | wrappers, .pk_k key =>
      prependWrappers wrappers ("pk_k(" ++ renderKey key ++ ")")
  | wrappers, .pk_h key =>
      prependWrappers wrappers ("pk_h(" ++ renderKey key ++ ")")
  | wrappers, .older n =>
      prependWrappers wrappers ("older(" ++ toString n ++ ")")
  | wrappers, .after n =>
      prependWrappers wrappers ("after(" ++ toString n ++ ")")
  | wrappers, .sha256 hash =>
      prependWrappers wrappers ("sha256(" ++ byteArrayHex hash.bytes ++ ")")
  | wrappers, .hash256 hash =>
      prependWrappers wrappers ("hash256(" ++ byteArrayHex hash.bytes ++ ")")
  | wrappers, .ripemd160 hash =>
      prependWrappers wrappers ("ripemd160(" ++ byteArrayHex hash.bytes ++ ")")
  | wrappers, .hash160 hash =>
      prependWrappers wrappers ("hash160(" ++ byteArrayHex hash.bytes ++ ")")
  | wrappers, .andor x y .zero =>
      prependWrappers wrappers
        ("and_n(" ++ prettyCoreWithWrappers renderKey "" x ++ "," ++
          prettyCoreWithWrappers renderKey "" y ++ ")")
  | wrappers, .and_v x .one =>
      prettyCoreWithWrappers renderKey (wrappers ++ "t") x
  | wrappers, .or_i .zero x =>
      prettyCoreWithWrappers renderKey (wrappers ++ "l") x
  | wrappers, .or_i x .zero =>
      prettyCoreWithWrappers renderKey (wrappers ++ "u") x
  | wrappers, .and_v x y =>
      prependWrappers wrappers
        ("and_v(" ++ prettyCoreWithWrappers renderKey "" x ++ "," ++
          prettyCoreWithWrappers renderKey "" y ++ ")")
  | wrappers, .and_b x y =>
      prependWrappers wrappers
        ("and_b(" ++ prettyCoreWithWrappers renderKey "" x ++ "," ++
          prettyCoreWithWrappers renderKey "" y ++ ")")
  | wrappers, .or_b x y =>
      prependWrappers wrappers
        ("or_b(" ++ prettyCoreWithWrappers renderKey "" x ++ "," ++
          prettyCoreWithWrappers renderKey "" y ++ ")")
  | wrappers, .or_c x y =>
      prependWrappers wrappers
        ("or_c(" ++ prettyCoreWithWrappers renderKey "" x ++ "," ++
          prettyCoreWithWrappers renderKey "" y ++ ")")
  | wrappers, .or_d x y =>
      prependWrappers wrappers
        ("or_d(" ++ prettyCoreWithWrappers renderKey "" x ++ "," ++
          prettyCoreWithWrappers renderKey "" y ++ ")")
  | wrappers, .or_i x y =>
      prependWrappers wrappers
        ("or_i(" ++ prettyCoreWithWrappers renderKey "" x ++ "," ++
          prettyCoreWithWrappers renderKey "" y ++ ")")
  | wrappers, .andor x y z =>
      prependWrappers wrappers
        ("andor(" ++ prettyCoreWithWrappers renderKey "" x ++ "," ++
          prettyCoreWithWrappers renderKey "" y ++ "," ++
          prettyCoreWithWrappers renderKey "" z ++ ")")
  | wrappers, .a x => prettyCoreWithWrappers renderKey (wrappers ++ "a") x
  | wrappers, .s x => prettyCoreWithWrappers renderKey (wrappers ++ "s") x
  | wrappers, .c x => prettyCoreWithWrappers renderKey (wrappers ++ "c") x
  | wrappers, .d x => prettyCoreWithWrappers renderKey (wrappers ++ "d") x
  | wrappers, .v x => prettyCoreWithWrappers renderKey (wrappers ++ "v") x
  | wrappers, .j x => prettyCoreWithWrappers renderKey (wrappers ++ "j") x
  | wrappers, .n x => prettyCoreWithWrappers renderKey (wrappers ++ "n") x
  | wrappers, .thresh k fragments =>
      prependWrappers wrappers
        ("thresh(" ++ toString k ++ "," ++
          String.intercalate ","
            (fragments.map (prettyCoreWithWrappers renderKey "")) ++ ")")
  | wrappers, .multi k keys =>
      prependWrappers wrappers
        ("multi(" ++ toString k ++ "," ++
          String.intercalate "," (keys.map renderKey) ++ ")")
  | wrappers, .multi_a k keys =>
      prependWrappers wrappers
        ("multi_a(" ++ toString k ++ "," ++
          String.intercalate "," (keys.map renderKey) ++ ")")

/-- Render a core fragment using BIP 379 function and wrapper spelling.
    `renderKey` makes the descriptor/key-expression presentation boundary
    explicit for callers that need something other than raw hexadecimal keys.
    It must return one token without whitespace or `(`, `)`, `,`, or `:`. -/
def prettyCoreWith (renderKey : PubKey → String) (fragment : CoreFragment) :
    String :=
  prettyCoreWithWrappers renderKey "" fragment

private def prettyNormalizedSurfaceWithWrappers
    (renderKey : PubKey → String) : String → SurfaceFragment → String
  | wrappers, .core fragment =>
      prettyCoreWithWrappers renderKey wrappers fragment
  | wrappers, .pk key =>
      prependWrappers wrappers ("pk(" ++ renderKey key ++ ")")
  | wrappers, .pkh key =>
      prependWrappers wrappers ("pkh(" ++ renderKey key ++ ")")
  | wrappers, .and_n x y =>
      prependWrappers wrappers
        ("and_n(" ++ prettyNormalizedSurfaceWithWrappers renderKey "" x ++ "," ++
          prettyNormalizedSurfaceWithWrappers renderKey "" y ++ ")")
  | wrappers, .t x =>
      prettyNormalizedSurfaceWithWrappers renderKey (wrappers ++ "t") x
  | wrappers, .l x =>
      prettyNormalizedSurfaceWithWrappers renderKey (wrappers ++ "l") x
  | wrappers, .u x =>
      prettyNormalizedSurfaceWithWrappers renderKey (wrappers ++ "u") x

/-- Render canonical surface text with a caller-supplied key presentation.
    The renderer has the same single-token contract as `prettyCoreWith`. -/
def prettySurfaceWith (renderKey : PubKey → String) (fragment : SurfaceFragment) :
    String :=
  prettyNormalizedSurfaceWithWrappers renderKey "" (normalizeSurface fragment)

/-- Render canonical surface text using lowercase hexadecimal public keys. -/
def prettySurface (fragment : SurfaceFragment) : String :=
  prettySurfaceWith prettyPubKey fragment

end LeanMiniscript.Miniscript
