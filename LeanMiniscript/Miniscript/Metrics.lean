import LeanMiniscript.Miniscript.Syntax

namespace LeanMiniscript.Miniscript

namespace CoreFragment

mutual
  /-- Number of core Miniscript AST nodes. -/
  def nodeCount : CoreFragment → Nat
    | .zero => 1
    | .one => 1
    | .pk_k _ => 1
    | .pk_h _ => 1
    | .older _ => 1
    | .after _ => 1
    | .sha256 _ => 1
    | .hash256 _ => 1
    | .ripemd160 _ => 1
    | .hash160 _ => 1
    | .and_v x y => 1 + nodeCount x + nodeCount y
    | .and_b x y => 1 + nodeCount x + nodeCount y
    | .or_b x y => 1 + nodeCount x + nodeCount y
    | .or_c x y => 1 + nodeCount x + nodeCount y
    | .or_d x y => 1 + nodeCount x + nodeCount y
    | .or_i x y => 1 + nodeCount x + nodeCount y
    | .andor x y z => 1 + nodeCount x + nodeCount y + nodeCount z
    | .a x => 1 + nodeCount x
    | .s x => 1 + nodeCount x
    | .c x => 1 + nodeCount x
    | .d x => 1 + nodeCount x
    | .v x => 1 + nodeCount x
    | .j x => 1 + nodeCount x
    | .n x => 1 + nodeCount x
    | .thresh _ fragments => 1 + listNodeCount fragments
    | .multi _ _ => 1
    | .multi_a _ _ => 1

  /-- Number of core Miniscript AST nodes in a list. -/
  def listNodeCount : List CoreFragment → Nat
    | [] => 0
    | fragment :: fragments => nodeCount fragment + listNodeCount fragments
end

mutual
  /-- Maximum nesting depth of a core Miniscript AST. -/
  def depth : CoreFragment → Nat
    | .zero => 1
    | .one => 1
    | .pk_k _ => 1
    | .pk_h _ => 1
    | .older _ => 1
    | .after _ => 1
    | .sha256 _ => 1
    | .hash256 _ => 1
    | .ripemd160 _ => 1
    | .hash160 _ => 1
    | .and_v x y => 1 + max (depth x) (depth y)
    | .and_b x y => 1 + max (depth x) (depth y)
    | .or_b x y => 1 + max (depth x) (depth y)
    | .or_c x y => 1 + max (depth x) (depth y)
    | .or_d x y => 1 + max (depth x) (depth y)
    | .or_i x y => 1 + max (depth x) (depth y)
    | .andor x y z => 1 + max (depth x) (max (depth y) (depth z))
    | .a x => 1 + depth x
    | .s x => 1 + depth x
    | .c x => 1 + depth x
    | .d x => 1 + depth x
    | .v x => 1 + depth x
    | .j x => 1 + depth x
    | .n x => 1 + depth x
    | .thresh _ fragments => 1 + listDepth fragments
    | .multi _ _ => 1
    | .multi_a _ _ => 1

  /-- Maximum nesting depth in a list of core Miniscript ASTs. -/
  def listDepth : List CoreFragment → Nat
    | [] => 0
    | fragment :: fragments => max (depth fragment) (listDepth fragments)
end

end CoreFragment

namespace SurfaceFragment

/-- Number of surface Miniscript AST nodes before desugaring. -/
def nodeCount : SurfaceFragment → Nat
  | .core fragment => 1 + fragment.nodeCount
  | .pk _ => 1
  | .pkh _ => 1
  | .and_n x y => 1 + nodeCount x + nodeCount y
  | .t x => 1 + nodeCount x
  | .l x => 1 + nodeCount x
  | .u x => 1 + nodeCount x

/-- Maximum nesting depth of a surface Miniscript AST before desugaring. -/
def depth : SurfaceFragment → Nat
  | .core fragment => 1 + fragment.depth
  | .pk _ => 1
  | .pkh _ => 1
  | .and_n x y => 1 + max (depth x) (depth y)
  | .t x => 1 + depth x
  | .l x => 1 + depth x
  | .u x => 1 + depth x

end SurfaceFragment

end LeanMiniscript.Miniscript
