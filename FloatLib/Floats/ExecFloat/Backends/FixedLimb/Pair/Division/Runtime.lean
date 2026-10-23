/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.FixedLimb.Pair.Core.Runtime
public import FloatLib.Kernels.FixedWord.CertifiedDivision.Runtime

/-!
# Two-word division runtime

A radix-`2^32` quotient candidate is checked with an independent Euclidean certificate. A
rejected candidate is replaced by the fixed-word restoring result, whose equality to the logical
divider is proved in `CertifiedDivision.Proof`. The selected quotient and remainder are then
rounded and packed. This module holds only the partial kernel for eligible two-word layouts, and
the dispatcher handles every case outside its normal finite range.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair

/--
Try certified fixed-word division for two normal operands given by their storage words, returning
the storage words of an accepted quotient. Two-word carriers call this form, so an accepted
quotient never becomes a model value.
-/
@[inline] def divNormalWords? (fmt : FloatFormat)
    (xWords yWords : FloatLib.Numerics.FixedWord.UInt128) :
    Option FloatLib.Numerics.FixedWord.UInt128 :=
  let xExponent := expField fmt xWords.hi
  let yExponent := expField fmt yWords.hi
  if xExponent == 0 || xExponent == expAllOnes fmt ||
      yExponent == 0 || yExponent == expAllOnes fmt then
    none
  else
    let num := normalMantissa fmt (fracHigh fmt xWords.hi) xWords.lo
    let den := normalMantissa fmt (fracHigh fmt yWords.hi) yWords.lo
    let less := FloatLib.Numerics.FixedWord.UInt128.less num den
    let rationalExponent : Int := if less then -1 else 0
    let totalExponent :=
      rationalExponent +
        (Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat)
    if totalExponent < fmt.ieeeMinNormalExponent then
      none
    else
      let candidateShift :
          FloatLib.Numerics.FixedWord.CertifiedDivision.CandidateShift :=
        if less then .extra else .exact
      let shift := candidateShift.toNat fmt.fracWidth
      let candidate :=
        FloatLib.Numerics.FixedWord.CertifiedDivision.checkedCandidate
          fmt.fracWidth num den candidateShift
      let rounded :=
        FloatLib.Numerics.FixedWord.CertifiedDivision.roundQuotient
          den candidate.quotient candidate.remainder
      let carry := isCarry fmt rounded
      let resultExponent : Int :=
        Int.ofNat xExponent.toNat - Int.ofNat yExponent.toNat +
          Int.ofNat (fmt.bias + fmt.fracWidth) - Int.ofNat shift + if carry then 1 else 0
      if resultExponent ≤ 0 || Int.ofNat fmt.expAllOnesNat ≤ resultExponent then
        none
      else
        some <| packNormalWords fmt
          (Bool.xor (signBit fmt xWords.hi) (signBit fmt yWords.hi))
          (UInt64.ofNat resultExponent.toNat) (normalizeCarry fmt carry rounded)

/--
`divNormalWords?` on the storage words of two model values, as a model value.

Descriptor specialization follows the pattern described in `Dispatch.Add.Runtime`.
-/
@[specialize fmt] def divNormal? {fmt : FloatFormat} (x y : Model fmt) : Option (Model fmt) :=
  (divNormalWords? fmt (toWords x) (toWords y)).map (ofWords fmt)

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativePair
