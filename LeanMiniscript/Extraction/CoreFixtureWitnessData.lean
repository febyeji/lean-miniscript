import Lean.Data.Json

namespace LeanMiniscript.Extraction

open Lean

/-- Unresolved witness elements retain Core's hex and dynamic template syntax.
The final JSON array entry is the crediting output's amount in BTC. -/
structure CoreFixtureWitnessSource where
  elements : List String := []
  amount : UInt64 := 0
  deriving Repr

/-- Convert an exact JSON decimal to satoshis, with Core's eight-decimal
precision and MoneyRange bounds. No floating-point rounding is involved. -/
def coreFixtureAmount (value : Json) : Except String UInt64 := do
  let number ← value.getNum?
  if number.mantissa < 0 then throw "negative fixture amount"
  let magnitude := number.mantissa.natAbs
  if magnitude = 0 then return 0
  let satoshis ← if number.exponent ≤ 8 then
      pure (magnitude * 10 ^ (8 - number.exponent))
    else do
      -- Reject tiny nonzero values before constructing an unbounded power.
      if number.exponent - 8 > (toString magnitude).length then
        throw "fixture amount has fractional satoshis"
      let divisor := 10 ^ (number.exponent - 8)
      if magnitude % divisor ≠ 0 then
        throw "fixture amount has fractional satoshis"
      pure (magnitude / divisor)
  if satoshis > 2100000000000000 then throw "fixture amount exceeds MoneyRange"
  return UInt64.ofNat satoshis

/-- Decode the optional witness array without discarding malformed elements
or its amount. Template expansion is a separate byte-producing operation. -/
def parseCoreFixtureWitnessSource (witness : Option Json) :
    Except String CoreFixtureWitnessSource := do
  match witness with
  | none => return {}
  | some (.arr values) =>
      if values.isEmpty then throw "witness array is missing its amount"
      let amount ← coreFixtureAmount values[values.size - 1]!
      let elements ← (values.toList.take (values.size - 1)).mapM Json.getStr?
      return { elements, amount }
  | some _ => throw "witness field must be an array"

end LeanMiniscript.Extraction
