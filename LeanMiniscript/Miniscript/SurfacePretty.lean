import LeanMiniscript.Miniscript.SurfaceNormalize
import LeanMiniscript.Script.Assembly

namespace LeanMiniscript.Miniscript

open LeanMiniscript.Script

/-- Render a resolved public key as a canonical lowercase hexadecimal token. -/
def prettyPubKey (key : PubKey) : String :=
  byteArrayHex key.bytes

namespace SurfaceText

/-!
`Expr` is the proof-facing canonical text grammar shared by the surface
printer and its round-trip proof. It deliberately contains no source
positions: the parser continues to attach those while tokenizing user input.
-/

/-- Whitespace recognized by the surface text grammar. -/
def isSpace : Char → Bool
  | ' ' | '\t' | '\n' | '\r' => true
  | _ => false

/-- Punctuation that terminates an atom in the surface text grammar. -/
def isPunctuation : Char → Bool
  | '(' | ')' | ',' | ':' => true
  | _ => false

/-- A nonempty token containing neither surface whitespace nor punctuation. -/
def AtomSafe (value : String) : Prop :=
  value.toList ≠ [] ∧
    ∀ char ∈ value.toList, isSpace char = false ∧ isPunctuation char = false

/-- Position-free canonical surface text before rendering to `String`. -/
inductive Expr where
  | atom (value : String)
  | wrapper (name : String) (inner : Expr)
  | call (name : String) (arguments : List Expr)
  deriving Repr

/-- Position-free lexical units used by canonical surface text. -/
inductive Lexeme where
  | atom (value : String)
  | leftParen
  | rightParen
  | comma
  | colon
  deriving Repr

/-- Render one canonical lexical unit. -/
def Lexeme.render : Lexeme → String
  | .atom value => value
  | .leftParen => "("
  | .rightParen => ")"
  | .comma => ","
  | .colon => ":"

/-- Characters emitted by one canonical lexical unit. -/
def Lexeme.chars : Lexeme → List Char
  | .atom value => value.toList
  | .leftParen => ['(']
  | .rightParen => [')']
  | .comma => [',']
  | .colon => [':']

mutual
  /-- Flatten a canonical expression into lexical units. -/
  def Expr.lexemes : Expr → List Lexeme
    | .atom value => [.atom value]
    | .wrapper name inner => .atom name :: .colon :: inner.lexemes
    | .call name arguments =>
        .atom name :: .leftParen :: argumentLexemes arguments ++ [.rightParen]

  /-- Flatten canonical call arguments, inserting commas between them. -/
  def argumentLexemes : List Expr → List Lexeme
    | [] => []
    | [argument] => argument.lexemes
    | argument :: arguments =>
        argument.lexemes ++ .comma :: argumentLexemes arguments
end

/-- Every canonical expression emits at least one lexical unit. -/
theorem Expr.lexemes_ne_nil (expr : Expr) : expr.lexemes ≠ [] := by
  cases expr <;> simp [Expr.lexemes]

/-- Every canonical expression begins with an atom naming the fragment or
    containing the complete leaf value. -/
theorem Expr.lexemes_eq_atom_cons (expr : Expr) :
    ∃ value tail, expr.lexemes = .atom value :: tail := by
  cases expr <;> simp [Expr.lexemes]

/-- Render a canonical text expression without optional whitespace. -/
def Expr.render (expr : Expr) : String :=
  String.ofList (expr.lexemes.flatMap Lexeme.chars)

/-- Every atom occurring in a canonical expression is safe for tokenization. -/
def Expr.AtomsSafe : Expr → Prop
  | .atom value => AtomSafe value
  | .wrapper name inner => AtomSafe name ∧ inner.AtomsSafe
  | .call name arguments =>
      AtomSafe name ∧ ∀ argument ∈ arguments, argument.AtomsSafe

/-- Attach an accumulated wrapper chain to a canonical expression. -/
def prependWrappers (wrappers : String) (body : Expr) : Expr :=
  if wrappers.isEmpty then body else .wrapper wrappers body

/-- Build the canonical proof-facing text expression for a core fragment while
    accumulating consecutive BIP 379 wrapper letters. -/
def coreExprWithWrappers (renderKey : PubKey → String) :
    String → CoreFragment → Expr
  | wrappers, .zero => prependWrappers wrappers (.atom "0")
  | wrappers, .one => prependWrappers wrappers (.atom "1")
  | wrappers, .c (.pk_k key) =>
      prependWrappers wrappers (.call "pk" [.atom (renderKey key)])
  | wrappers, .c (.pk_h key) =>
      prependWrappers wrappers (.call "pkh" [.atom (renderKey key)])
  | wrappers, .pk_k key =>
      prependWrappers wrappers (.call "pk_k" [.atom (renderKey key)])
  | wrappers, .pk_h key =>
      prependWrappers wrappers (.call "pk_h" [.atom (renderKey key)])
  | wrappers, .older n =>
      prependWrappers wrappers (.call "older" [.atom (toString n)])
  | wrappers, .after n =>
      prependWrappers wrappers (.call "after" [.atom (toString n)])
  | wrappers, .sha256 hash =>
      prependWrappers wrappers
        (.call "sha256" [.atom (byteArrayHex hash.bytes)])
  | wrappers, .hash256 hash =>
      prependWrappers wrappers
        (.call "hash256" [.atom (byteArrayHex hash.bytes)])
  | wrappers, .ripemd160 hash =>
      prependWrappers wrappers
        (.call "ripemd160" [.atom (byteArrayHex hash.bytes)])
  | wrappers, .hash160 hash =>
      prependWrappers wrappers
        (.call "hash160" [.atom (byteArrayHex hash.bytes)])
  | wrappers, .andor x y .zero =>
      prependWrappers wrappers
        (.call "and_n"
          [coreExprWithWrappers renderKey "" x,
            coreExprWithWrappers renderKey "" y])
  | wrappers, .and_v x .one =>
      coreExprWithWrappers renderKey (wrappers ++ "t") x
  | wrappers, .or_i .zero x =>
      coreExprWithWrappers renderKey (wrappers ++ "l") x
  | wrappers, .or_i x .zero =>
      coreExprWithWrappers renderKey (wrappers ++ "u") x
  | wrappers, .and_v x y =>
      prependWrappers wrappers
        (.call "and_v"
          [coreExprWithWrappers renderKey "" x,
            coreExprWithWrappers renderKey "" y])
  | wrappers, .and_b x y =>
      prependWrappers wrappers
        (.call "and_b"
          [coreExprWithWrappers renderKey "" x,
            coreExprWithWrappers renderKey "" y])
  | wrappers, .or_b x y =>
      prependWrappers wrappers
        (.call "or_b"
          [coreExprWithWrappers renderKey "" x,
            coreExprWithWrappers renderKey "" y])
  | wrappers, .or_c x y =>
      prependWrappers wrappers
        (.call "or_c"
          [coreExprWithWrappers renderKey "" x,
            coreExprWithWrappers renderKey "" y])
  | wrappers, .or_d x y =>
      prependWrappers wrappers
        (.call "or_d"
          [coreExprWithWrappers renderKey "" x,
            coreExprWithWrappers renderKey "" y])
  | wrappers, .or_i x y =>
      prependWrappers wrappers
        (.call "or_i"
          [coreExprWithWrappers renderKey "" x,
            coreExprWithWrappers renderKey "" y])
  | wrappers, .andor x y z =>
      prependWrappers wrappers
        (.call "andor"
          [coreExprWithWrappers renderKey "" x,
            coreExprWithWrappers renderKey "" y,
            coreExprWithWrappers renderKey "" z])
  | wrappers, .a x => coreExprWithWrappers renderKey (wrappers ++ "a") x
  | wrappers, .s x => coreExprWithWrappers renderKey (wrappers ++ "s") x
  | wrappers, .c x => coreExprWithWrappers renderKey (wrappers ++ "c") x
  | wrappers, .d x => coreExprWithWrappers renderKey (wrappers ++ "d") x
  | wrappers, .v x => coreExprWithWrappers renderKey (wrappers ++ "v") x
  | wrappers, .j x => coreExprWithWrappers renderKey (wrappers ++ "j") x
  | wrappers, .n x => coreExprWithWrappers renderKey (wrappers ++ "n") x
  | wrappers, .thresh k fragments =>
      prependWrappers wrappers
        (.call "thresh"
          (.atom (toString k) ::
            fragments.map (coreExprWithWrappers renderKey "")))
  | wrappers, .multi k keys =>
      prependWrappers wrappers
        (.call "multi"
          (.atom (toString k) :: keys.map (fun key => .atom (renderKey key))))
  | wrappers, .multi_a k keys =>
      prependWrappers wrappers
        (.call "multi_a"
          (.atom (toString k) :: keys.map (fun key => .atom (renderKey key))))

/-- Render a core fragment while accumulating consecutive BIP 379 wrapper
    letters. The specification uses one colon after the complete wrapper chain:
    `dv:older(144)`, not `d:v:older(144)`. -/
def prettyCoreWithWrappers (renderKey : PubKey → String)
    (wrappers : String) (fragment : CoreFragment) : String :=
  (coreExprWithWrappers renderKey wrappers fragment).render

/-- Render a core fragment using BIP 379 function and wrapper spelling.
    `renderKey` makes the descriptor/key-expression presentation boundary
    explicit for callers that need something other than raw hexadecimal keys.
    It must return one token without whitespace or `(`, `)`, `,`, or `:`. -/
def prettyCoreWith (renderKey : PubKey → String) (fragment : CoreFragment) :
    String :=
  prettyCoreWithWrappers renderKey "" fragment

/-- Build the canonical proof-facing text expression for normalized surface
    syntax while accumulating consecutive wrapper letters. -/
def normalizedExprWithWrappers (renderKey : PubKey → String) :
    String → SurfaceFragment → Expr
  | wrappers, .core fragment =>
      coreExprWithWrappers renderKey wrappers fragment
  | wrappers, .pk key =>
      prependWrappers wrappers (.call "pk" [.atom (renderKey key)])
  | wrappers, .pkh key =>
      prependWrappers wrappers (.call "pkh" [.atom (renderKey key)])
  | wrappers, .and_n x y =>
      prependWrappers wrappers
        (.call "and_n"
          [normalizedExprWithWrappers renderKey "" x,
            normalizedExprWithWrappers renderKey "" y])
  | wrappers, .t x =>
      normalizedExprWithWrappers renderKey (wrappers ++ "t") x
  | wrappers, .l x =>
      normalizedExprWithWrappers renderKey (wrappers ++ "l") x
  | wrappers, .u x =>
      normalizedExprWithWrappers renderKey (wrappers ++ "u") x

/-- Render normalized surface syntax from the proof-facing text expression. -/
def prettyNormalizedSurfaceWithWrappers
    (renderKey : PubKey → String) (wrappers : String)
    (fragment : SurfaceFragment) : String :=
  (normalizedExprWithWrappers renderKey wrappers fragment).render

/-- Core-shape recognition and the canonical surface-expression builder agree
    on the exact proof-facing syntax tree. -/
theorem normalizedExpr_normalizeCoreAsSurface
    (renderKey : PubKey → String) (wrappers : String)
    (fragment : CoreFragment) :
    normalizedExprWithWrappers renderKey wrappers
        (normalizeCoreAsSurface fragment) =
      coreExprWithWrappers renderKey wrappers fragment := by
  cases fragment with
  | c inner =>
      cases inner <;>
        simp [normalizeCoreAsSurface, normalizedExprWithWrappers,
          coreExprWithWrappers]
  | andor first second third =>
      have hFirst := normalizedExpr_normalizeCoreAsSurface renderKey "" first
      have hSecond := normalizedExpr_normalizeCoreAsSurface renderKey "" second
      cases third <;>
        simp_all [normalizeCoreAsSurface, normalizedExprWithWrappers,
          coreExprWithWrappers]
  | and_v first second =>
      have hFirst := normalizedExpr_normalizeCoreAsSurface renderKey
        (wrappers ++ "t") first
      cases second <;>
        simp_all [normalizeCoreAsSurface, normalizedExprWithWrappers,
          coreExprWithWrappers]
  | or_i first second =>
      have hFirst := normalizedExpr_normalizeCoreAsSurface renderKey
        (wrappers ++ "u") first
      have hSecond := normalizedExpr_normalizeCoreAsSurface renderKey
        (wrappers ++ "l") second
      cases first <;> cases second <;>
        simp_all [normalizeCoreAsSurface, normalizedExprWithWrappers,
          coreExprWithWrappers]
  | _ => rfl
termination_by structural fragment

end SurfaceText

/-- Render a core fragment using BIP 379 function and wrapper spelling. -/
def prettyCoreWith (renderKey : PubKey → String) (fragment : CoreFragment) :
    String :=
  SurfaceText.prettyCoreWith renderKey fragment

/-- Render canonical surface text with a caller-supplied key presentation.
    The renderer has the same single-token contract as `prettyCoreWith`. -/
def prettySurfaceWith (renderKey : PubKey → String) (fragment : SurfaceFragment) :
    String :=
  SurfaceText.prettyNormalizedSurfaceWithWrappers
    renderKey "" (normalizeSurface fragment)

/-- Render canonical surface text using lowercase hexadecimal public keys. -/
def prettySurface (fragment : SurfaceFragment) : String :=
  prettySurfaceWith prettyPubKey fragment

end LeanMiniscript.Miniscript
