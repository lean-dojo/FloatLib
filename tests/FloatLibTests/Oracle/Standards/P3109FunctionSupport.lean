module

public import FloatLib.Floats.Formats.P3109.Functions.Runtime
public import FloatLib.Floats.Formats.P3109.Functions.Recommended.Runtime

/-! Shared corpus policies and exact-expression observations for scalar and block functions. -/

open FloatLib.Numerics FloatLib.Floats
open Formats.P3109

namespace P3109FunctionSupport

/-- Deterministic policies and all stochastic words at widths zero through two. -/
public def modes : Array RoundingMode := Id.run do
  let mut result := #[.towardZero, .up, .down, .nearestAway, .nearest, .toOdd]
  for width in [:3] do
    for word in [:2 ^ width] do
      let random := RandomBits.ofNat width word
      result := result ++ #[.stochasticA random, .stochasticB random, .stochasticC random]
  return result

/-- The chapter 4 unary operations in the order used by the corpus. -/
public def operations : Array Functions.Unary :=
  #[.log, .log2, .logOnePlus, .exp, .exp2, .expMinusOne,
    .sin, .cos, .tan, .arcSin, .arcCos, .arcTan,
    .sinh, .cosh, .tanh, .arcSinh, .arcCosh, .arcTanh,
    .sinPi, .cosPi, .tanPi, .arcSinPi, .arcCosPi, .arcTanPi, .softplus]

/-- Report spellings in the same order as `operations`. -/
public def names : Array String :=
  #["Log", "Log2", "LogOnePlus", "Exp", "Exp2", "ExpMinusOne",
    "Sin", "Cos", "Tan", "ArcSin", "ArcCos", "ArcTan",
    "Sinh", "Cosh", "Tanh", "ArcSinh", "ArcCosh", "ArcTanh",
    "SinPi", "CosPi", "TanPi", "ArcSinPi", "ArcCosPi", "ArcTanPi", "Softplus"]

/-- The format parameters written in each comparison row. -/
public def descriptor (format : Format) : String :=
  s!"{format.bitWidth},{format.precision},{format.signedness == .signed},\
      {format.domain == .extended}"

/-- Compare the public nearest-even code with the cached exact expression, then emit all
policies. -/
public def observe (stdout : IO.FS.Stream) (format : Format) (heading : String)
    (expression : NumericalValue FunctionExpr) (publicCode : Nat) : IO Unit := do
  let prepared := expression.map (fun expr => expr.prepare 8)
  let mut row := heading
  for mode in modes do
    for saturation in [SaturationMode.finite, .propagate, .none] do
      let datum := format.saturate saturation mode (prepared.map (fun compare =>
        ComparisonRounding.rounded format mode compare.compare))
      let code := (BitVec.ofNat format.bitWidth
        (Format.Internal.encodeDatumNat format datum)).toNat
      let publicPolicy := match mode, saturation with
        | .nearest, .none => true
        | _, _ => false
      if publicPolicy && code != publicCode then
        throw (IO.userError s!"public/cached mismatch: {heading}, {publicCode}, {code}")
      row := row ++ s!",{code}"
  stdout.putStrLn row


end P3109FunctionSupport
