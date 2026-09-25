/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Mul.Runtime

/-!
# Unary binary squaring kernels

Squaring decodes one operand and passes its exact significand product to the existing
multiplication rounders. Finite results have positive sign, including an underflowed zero.
Declined inputs use multiplication, retaining its complete exceptional-value policy.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.SquareBackend

/-- Square finite scalar fields using multiplication's exact product and scale coordinates. -/
@[inline] def finite? {fmt : FloatFormat} (x : Model fmt) : Option (Model fmt) :=
  FiniteKernel.withFinite? x fun _ exponent mantissa =>
    some <| FiniteKernel.mulFields fmt false exponent mantissa false exponent mantissa

/-- Width-generic squaring with one finite decode and the multiplication exceptional policy. -/
@[specialize fmt] def generic {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  match finite? x with
  | some result => result
  | none => MulBackend.generic x x

/-- Binary32 finite squaring, including zero and subnormal inputs and outputs. -/
@[inline] def binary32? (x : NativeBinary32.Value) : Option NativeBinary32.Value :=
  let bits := NativeBinary32.toUInt32 x
  let exponent := NativeBinary32.expField bits
  if exponent == 0xff then
    none
  else
    let mantissa :=
      NativeBinary32.finiteMantissa exponent (NativeBinary32.fracField bits)
    let scale := NativeBinary32.finiteScale exponent
    some <| NativeBinary32.ofUInt32 <|
      NativeBinary32.roundProduct false (mantissa * mantissa) (scale + scale)

/-- One-word normal squaring with the multiplication decline sentinel. -/
@[inline] def smallWord {fmt : FloatFormat} (x : Model fmt) : UInt64 :=
  let bits := NativeSmallWord.toWord x
  let exponent := NativeSmallWord.exponentField fmt bits
  if exponent == 0 || exponent == NativeSmallWord.exponentMask fmt then
    NativeSmallWordMul.declineWord
  else
    let mantissa :=
      NativeSmallWord.fractionField fmt bits ||| NativeSmallWord.hiddenBit fmt
    NativeSmallWordMul.roundNormalProductWord fmt false
      exponent exponent mantissa mantissa

/-- Two-word normal squaring from one decoded machine word. -/
@[inline] def twoWord? {fmt : FloatFormat} (x : Model fmt) : Option (Model fmt) :=
  let bits := NativeSmallWord.toWord x
  let exponent := NativeSmallWord.exponentField fmt bits
  if exponent == 0 || exponent == NativeSmallWord.exponentMask fmt then
    none
  else
    let mantissa :=
      NativeSmallWord.fractionField fmt bits ||| NativeSmallWord.hiddenBit fmt
    NativeTwoWordMul.roundNormalProduct? fmt false exponent exponent mantissa mantissa

/-- Fixed-pair normal squaring from one decoded pair of machine words. -/
@[specialize fmt] def pair? {fmt : FloatFormat} (x : Model fmt) : Option (Model fmt) :=
  let words := NativePair.toWords x
  let exponent := NativePair.expField fmt words.hi
  if exponent == 0 || exponent == NativePair.expAllOnes fmt then
    none
  else
    let mantissa :=
      NativePair.normalMantissa fmt (NativePair.fracHigh fmt words.hi) words.lo
    NativePair.roundNormalLimb? false exponent exponent mantissa mantissa

/-- Structural squaring dispatch, with exact arbitrary-width multiplication as its fallback. -/
@[specialize fmt] def dispatch {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  if h32 : FloatFormat.IsBinary32 fmt then
    let hcarrier := congrArg Model (FloatFormat.eq_binary32_of_isBinary32 h32)
    let x32 : NativeBinary32.Value := Eq.mp hcarrier x
    match binary32? x32 with
    | some result => Eq.mpr hcarrier result
    | none => generic x
  else if h64 : FloatFormat.IsBinary64 fmt then
    match twoWord? x with
    | some result => result
    | none =>
        let hcarrier := congrArg Model (FloatFormat.eq_binary64_of_isBinary64 h64)
        let x64 : NativeBinary64.Value := Eq.mp hcarrier x
        match NativeBinary64.mulNormalLimb? x64 x64 with
        | some result => Eq.mpr hcarrier result
        | none => generic x
  else if _hpair : NativePair.Eligible fmt then
    match pair? x with
    | some result => result
    | none => generic x
  else if _hsmall : NativeSmallWordMul.Eligible fmt then
    let result := smallWord x
    if result == NativeSmallWordMul.declineWord then
      generic x
    else
      NativeSmallWord.ofWord result
  else if _htwoWord : NativeTwoWordMul.Eligible fmt then
    match twoWord? x with
    | some result => result
    | none => generic x
  else
    generic x

end FloatLib.Floats.Formats.BinaryInterchange.Model.SquareBackend
