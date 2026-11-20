module

import FloatLibTests.Oracle.Standards.P3109FunctionSupport

/-!
P3109 interim report v4.1 §§4.10.9–4.10.13, 4.10.15–4.10.16, and the functions of
IEEE 754-2019 §9.2 that the report does not list: those with one operand, `Pow` and
`Powr` with an exponent of an independent descriptor, and `Pown`, `Rootn` and
`Compound` with the integers from -3 to 3. Exhaustive small source words,
independent destination descriptors, all modes and supplied random words through two
bits. Finite expression caches are shared across policies. A public operation is
checked against that path on each input.
-/

open FloatLib.Numerics FloatLib.Floats
open Formats.P3109 P3109FunctionSupport

def publicFunctions {source : Format} :
    Array (ExecFloat.P3109 source → (target : Format) → ExecFloat.P3109 target) :=
  #[fun x f => ExecFloat.P3109.Log x f,
    fun x f => ExecFloat.P3109.Log2 x f,
    fun x f => ExecFloat.P3109.LogOnePlus x f,
    fun x f => ExecFloat.P3109.Exp x f,
    fun x f => ExecFloat.P3109.Exp2 x f,
    fun x f => ExecFloat.P3109.ExpMinusOne x f,
    fun x f => ExecFloat.P3109.Sin x f,
    fun x f => ExecFloat.P3109.Cos x f,
    fun x f => ExecFloat.P3109.Tan x f,
    fun x f => ExecFloat.P3109.ArcSin x f,
    fun x f => ExecFloat.P3109.ArcCos x f,
    fun x f => ExecFloat.P3109.ArcTan x f,
    fun x f => ExecFloat.P3109.Sinh x f,
    fun x f => ExecFloat.P3109.Cosh x f,
    fun x f => ExecFloat.P3109.Tanh x f,
    fun x f => ExecFloat.P3109.ArcSinh x f,
    fun x f => ExecFloat.P3109.ArcCosh x f,
    fun x f => ExecFloat.P3109.ArcTanh x f,
    fun x f => ExecFloat.P3109.SinPi x f,
    fun x f => ExecFloat.P3109.CosPi x f,
    fun x f => ExecFloat.P3109.TanPi x f,
    fun x f => ExecFloat.P3109.ArcSinPi x f,
    fun x f => ExecFloat.P3109.ArcCosPi x f,
    fun x f => ExecFloat.P3109.ArcTanPi x f,
    fun x f => ExecFloat.P3109.Softplus x f]

/-- The functions of IEEE 754-2019 §9.2 with one operand that the report does not list: the
name, the closed expression and the public operation. -/
def recommendedFunctions {source : Format} :
    Array (String × (NumericalValue Rat → NumericalValue FunctionExpr) ×
      (ExecFloat.P3109 source → (target : Format) → ExecFloat.P3109 target)) :=
  #[("Exp10", Functions.exponential 10 (by decide) false, fun x f => ExecFloat.P3109.Exp10 x f),
    ("Exp2MinusOne", Functions.exponential 2 (by decide) true,
      fun x f => ExecFloat.P3109.Exp2MinusOne x f),
    ("Exp10MinusOne", Functions.exponential 10 (by decide) true,
      fun x f => ExecFloat.P3109.Exp10MinusOne x f),
    ("Log10", Functions.logarithmIn 10 (by decide) 0, fun x f => ExecFloat.P3109.Log10 x f),
    ("Log2OnePlus", Functions.logarithmIn 2 (by decide) 1,
      fun x f => ExecFloat.P3109.Log2OnePlus x f),
    ("Log10OnePlus", Functions.logarithmIn 10 (by decide) 1,
      fun x f => ExecFloat.P3109.Log10OnePlus x f),
    ("Cbrt", Functions.root 3, fun x f => ExecFloat.P3109.Cbrt x f)]


/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main (arguments : List String) : IO Unit := do
  let first := arguments[0]?.bind String.toNat? |>.getD 3
  let last := arguments[1]?.bind String.toNat? |>.getD (first + 1)
  let stdout ← IO.getStdout
  for width in [first:last] do
    for precision in [1:width + 1] do
      for signedness in [Signedness.signed, .unsigned] do
        for domain in [Domain.finite, .extended] do
          if let some source := Format.ofParameters? width precision signedness domain then
            -- Each source word is tested both in its own descriptor and in a
            -- different precision/domain, without an intermediate conversion.
            for target in [source, Format.binary8p3se] do
              stdout.putStrLn s!"F,{descriptor source},{descriptor target}"
              for word in [:2 ^ width] do
                let input : ExecFloat.P3109 source := ExecFloat.P3109.ofNatBits word
                for (operation, (name, call)) in
                    operations.zip (names.zip (publicFunctions (source := source))) do
                  let expression := Functions.unary operation input.toClosedRat
                  let publicCode := (call input target).toNatBits
                  observe stdout target s!"U,{word},{name}" expression publicCode
                for (name, expression, call) in recommendedFunctions (source := source) do
                  observe stdout target s!"U,{word},{name}" (expression input.toClosedRat)
                    (call input target).toNatBits
              -- Exhaust the first operand and select second-operand boundaries
              -- in an independent descriptor.
              if width ≤ 4 then
                let other := Format.binary8p3se
                for yWord in [:2 ^ width] do
                  let y : ExecFloat.P3109 source := ExecFloat.P3109.ofNatBits yWord
                  for xWord in [0, 1, 32, 63, 64, 65, 96, 127, 128, 129, 192, 255] do
                    let x : ExecFloat.P3109 other := ExecFloat.P3109.ofNatBits xWord
                    for scaled in [false, true] do
                      let expression := Functions.arcTan2 scaled y.toClosedRat x.toClosedRat
                      let output := if scaled then ExecFloat.P3109.ArcTan2Pi y x target
                        else ExecFloat.P3109.ArcTan2 y x target
                      observe stdout target s!"B,{yWord},{xWord},{scaled}"
                        expression output.toNatBits
                -- The powers: an exponent of an independent descriptor, and integer
                -- exponents and degrees.
                for xWord in [:2 ^ width] do
                  let x : ExecFloat.P3109 source := ExecFloat.P3109.ofNatBits xWord
                  for yWord in [0, 1, 32, 63, 64, 65, 96, 127, 128, 129, 192, 255] do
                    let y : ExecFloat.P3109 other := ExecFloat.P3109.ofNatBits yWord
                    observe stdout target s!"P,{xWord},{yWord},Pow"
                      (Functions.power x.toClosedRat y.toClosedRat)
                      (ExecFloat.P3109.Pow x y target).toNatBits
                    observe stdout target s!"P,{xWord},{yWord},Powr"
                      (Functions.positivePower x.toClosedRat y.toClosedRat)
                      (ExecFloat.P3109.Powr x y target).toNatBits
                  for n in ([-3, -2, -1, 0, 1, 2, 3] : List Int) do
                    observe stdout target s!"I,{xWord},{n},Pown"
                      (Functions.integerPower n x.toClosedRat)
                      (ExecFloat.P3109.Pown x n target).toNatBits
                    observe stdout target s!"I,{xWord},{n},Rootn"
                      (Functions.root n x.toClosedRat)
                      (ExecFloat.P3109.Rootn x n target).toNatBits
                    observe stdout target s!"I,{xWord},{n},Compound"
                      (Functions.compound n x.toClosedRat)
                      (ExecFloat.P3109.Compound x n target).toNatBits
