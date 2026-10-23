/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Finite.Runtime
public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Runtime
import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Compiler

/-!
# Native one-word square root for small IEEE formats

A positive finite input is `mantissa * 2 ^ (scale - (bias + fracWidth - 1))`. Scaling the mantissa
to a radicand of `2 * fracWidth + 1` or `2 * fracWidth + 2` bits gives a floor square root with
exactly `fracWidth + 1` bits, so the root and its remainder fit one machine word. Since a square
root is never a midpoint, comparing the remainder with the root decides nearest rounding. This is
the binary32 kernel with the format's bias and fraction width as parameters.

Formats whose radicand exceeds one word, or whose bias is too small for every square root to be
normal, use the descriptor-generic kernel. `Sqrt.Proof` has the proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordSqrt

/--
Formats served by the one-word kernel: one-word IEEE storage, a radicand below `2 ^ 64`, and a bias
for which the square root of every finite value is normal.
-/
def Eligible (fmt : FloatFormat) : Prop :=
  NativeSmallWord.StorageEligible fmt ∧ 2 * fmt.fracWidth + 2 ≤ 64 ∧
    fmt.fracWidth + 1 ≤ fmt.bias

@[inline] instance (fmt : FloatFormat) : Decidable (Eligible fmt) :=
  if h : NativeSmallWord.StorageEligible fmt ∧ 2 * fmt.fracWidth + 2 ≤ 64 ∧
      fmt.fracWidth + 1 ≤ fmt.bias then isTrue h else isFalse h

/--
Square root of `mantissa * 2 ^ (scale - (bias + fracWidth - 1))` for a nonzero mantissa below
`2 ^ (fracWidth + 1)` and a scale of a finite value, packed as storage bits.

`numerator / 2` is the biased exponent of the root before rounding, and the shift makes the
radicand's leading-bit position `2 * fracWidth` or `2 * fracWidth + 1`, matching its parity.
-/
@[inline] def sqrtPositiveCore (fmt : FloatFormat) (mantissa scale : UInt64) : UInt64 :=
  let fracWidth := UInt64.ofNat fmt.fracWidth
  let leading := FloatLib.Numerics.FixedWord.log2Word mantissa
  let numerator := leading + scale + (NativeSmallWord.biasWord fmt + 1 - fracWidth)
  let shift := numerator % 2 + 2 * fracWidth - leading
  let scaled := mantissa <<< shift
  let root := FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrt scaled
  let remainder := scaled - root * root
  let rounded := if remainder ≤ root then root else root + 1
  let carry := rounded == NativeSmallWord.carryBit fmt
  let exponent := numerator / 2 + if carry then 1 else 0
  let roundedMantissa := if carry then NativeSmallWord.hiddenBit fmt else rounded
  NativeSmallWord.packFields fmt false exponent
    (roundedMantissa - NativeSmallWord.hiddenBit fmt)

/--
Square root of a positive, finite, nonzero value: the one-word kernel for eligible formats and the
shared finite kernel otherwise. The evidence is erased by compilation.
-/
@[inline] def sqrtPositive {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt)
    (x : Model fmt)
    (hfinite : isFinite x = true)
    (hnonzero : isZero x = false)
    (hpositive : signBit x = false) : Model fmt :=
  if Eligible fmt then
    let bits := NativeSmallWord.toWord x
    let exponent := NativeSmallWord.exponentField fmt bits
    let fraction := NativeSmallWord.fractionField fmt bits
    NativeSmallWord.ofWord <| sqrtPositiveCore fmt
      (NativeSmallWordFinite.finiteMantissa fmt exponent fraction)
      (if exponent == 0 then 0 else exponent - 1)
  else
    NativeSmallWordFinite.sqrtPositive heligible x hfinite hnonzero hpositive

end Model.NativeSmallWordSqrt
end FloatLib.Floats.Formats.BinaryInterchange
