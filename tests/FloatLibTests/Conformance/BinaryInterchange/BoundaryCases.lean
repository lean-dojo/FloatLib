/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange

/-!
# Descriptor and interval boundary regressions

These cases check declared exponent biases, overflow during integral conversion, composition
of intervals with infinite endpoints, and the binary32 constants of the standard model. Each
expected result is checked by the kernel. Configured examples also exercise the same `ExecFloat`
operations used by numerical programs.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.BoundaryCases

open FloatLib

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

private abbrev Narrow := ExecFloat.Binary 2 1 (bias := 2)
private abbrev NarrowFinite := ExecFloat.Binary 2 1 (encoding := .finite) (bias := 3)

-- The ceiling is two, outside these descriptors' finite range.
example : (ExecFloat.Binary.roundToIntegralExactWithStatus (1.5 : Narrow)
    .towardPositiveInfinity).2.overflow = true := by decide +kernel

example : (ExecFloat.Binary.roundToIntegralExactWithStatus (1.5 : NarrowFinite)
    .towardPositiveInfinity).2.overflow = true := by decide +kernel

example : ExecFloat.Binary.toRat?
    (ExecFloat.Binary.roundToIntegral (1.5 : Narrow) .towardNegativeInfinity) = some 1 := by
  decide +kernel

-- The configured operation and its proof use the same value and rounding argument.
example (value : Narrow) (rounding : Model.IEEERoundingMode) :
    ExecFloat.Binary.toModel (ExecFloat.Binary.roundToIntegral value rounding) =
      Model.roundToIntegral (ExecFloat.Binary.toModel value) rounding :=
  ExecFloat.Binary.toModel_roundToIntegral value rounding

example : Model.roundRatWithRounding FloatFormat.e4m3fnuz .nearestEven false 1 1024 =
    Model.ofNatBits (fmt := FloatFormat.e4m3fnuz) 1 := by decide

-- The rounded-real grid retains the same least subnormal as the executable decoder.
example : Model.roundAt FloatFormat.e4m3fnuz (1 / 1024) = 1 / 1024 := by
  let value := Model.ofNatBits (fmt := FloatFormat.e4m3fnuz) 1
  have hvalue : value.toReal = (1 / 1024 : ℝ) := by
    have hdecode : Model.toDyadic? value = some ⟨false, 1, -10⟩ := by decide
    rw [Model.toReal_eq, hdecode]
    norm_num [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand,
      Formats.Flocq.bpow, Numerics.Radix.toReal, Numerics.binaryRadix]
  simpa only [hvalue] using Model.roundAt_toReal_eq value (by decide)

private def crossingZero : Model.Interval FloatFormat.binary16 :=
  ⟨Model.negOne _, Model.posOne _⟩

private def quotient : Model.Interval FloatFormat.binary16 :=
  Model.Interval.div (Model.Interval.point (Model.posOne _)) crossingZero

example : Model.Interval.mul quotient (Model.Interval.point (Model.posZero _)) =
    Model.Interval.whole FloatFormat.binary16 := by decide

example : Model.Interval.ValidExtended
    (Model.Interval.mul quotient (Model.Interval.point (Model.posZero _))) :=
  Model.Interval.mul_validExtended _ _ (by decide)

example (x : EReal) : Model.Interval.ERealMem
    (Model.Interval.mul quotient (Model.Interval.point (Model.posZero _))) x := by
  have h : Model.Interval.mul quotient (Model.Interval.point (Model.posZero _)) =
      Model.Interval.whole FloatFormat.binary16 := by decide
  rw [h]
  exact Model.Interval.eRealMem_whole _ (by decide) x

example : Model.Interval.abs quotient =
    ⟨Model.posZero FloatFormat.binary16, Model.posInf FloatFormat.binary16⟩ := by decide

-- A proof about this pipeline never needs to establish that the intermediate sum is finite.
example {fmt : FloatFormat} (A B : Model.Interval fmt) (hfmt : fmt.isIEEE = true)
    (hA : Model.Interval.Valid A) (hB : Model.Interval.Valid B)
    {x y : ℝ} (hx : Model.Interval.RealMem A x) (hy : Model.Interval.RealMem B y) :
    Model.Interval.ERealMem
      (Model.Interval.relu (Model.Interval.abs (Model.Interval.neg (Model.Interval.add A B))))
      ((|x + y| : ℝ) : EReal) := by
  have hsum := Model.Interval.add_sound A B hfmt hA hB hx hy
  have hsumValid := Model.Interval.add_validExtended A B hfmt
  have hneg := Model.Interval.neg_sound_extended _ hsumValid hsum
  have hnegValid := Model.Interval.neg_validExtended _ hsumValid
  have habs := Model.Interval.abs_sound_extended _ hnegValid hneg
  have habsValid := Model.Interval.abs_validExtended _ hnegValid
  simpa only [abs_neg, max_eq_left (abs_nonneg (x + y))] using
    Model.Interval.relu_sound_extended _ habsValid habs

/-- The standard-model unit roundoff of binary32 is `2^(-24)`. -/
theorem binary32_unitRoundoffAt :
    Model.unitRoundoffAt FloatFormat.binary32 = 2 ^ (-24 : ℤ) := by
  rw [Model.unitRoundoffAt_eq]
  norm_num [FloatFormat.binary32]

/-- The standard-model underflow allowance of binary32 is half its subnormal spacing, `2^(-150)`. -/
theorem binary32_underflowErrorAt :
    Model.underflowErrorAt FloatFormat.binary32 = 2 ^ (-150 : ℤ) := by
  rw [Model.underflowErrorAt_eq]
  have h : FloatFormat.minSubnormalExponent FloatFormat.binary32 = -149 := by decide
  rw [h]
  norm_num

example (x : ℝ) :
    ∃ δ η : ℝ, Model.roundAt FloatFormat.binary32 x = x * (1 + δ) + η ∧
      |δ| ≤ 2 ^ (-24 : ℤ) ∧ |η| ≤ 2 ^ (-150 : ℤ) ∧ δ * η = 0 := by
  simpa only [binary32_unitRoundoffAt, binary32_underflowErrorAt] using
    Model.roundAt_standardModel FloatFormat.binary32 x

-- Directed rounding doubles both constants.
example (x : ℝ) :
    ∃ δ η : ℝ, Model.roundAtDown FloatFormat.binary32 x = x * (1 + δ) + η ∧
      |δ| ≤ 2 ^ (-23 : ℤ) ∧ |η| ≤ 2 ^ (-149 : ℤ) ∧ δ * η = 0 := by
  obtain ⟨δ, η, h, hδ, hη, hδη⟩ := Model.roundAtDown_standardModel FloatFormat.binary32 x
  rw [binary32_unitRoundoffAt] at hδ
  rw [binary32_underflowErrorAt] at hη
  exact ⟨δ, η, h, by norm_num at hδ ⊢; linarith, by norm_num at hη ⊢; linarith, hδη⟩

-- Finite binary32 addition has no underflow term.
example (x y : Model FloatFormat.binary32) (hx : Model.isFinite x = true)
    (hy : Model.isFinite y = true) (hout : Model.isFinite (Model.add x y) = true) :
    ∃ δ : ℝ, Model.toReal (Model.add x y) = (Model.toReal x + Model.toReal y) * (1 + δ) ∧
      |δ| ≤ 2 ^ (-24 : ℤ) := by
  simpa only [binary32_unitRoundoffAt] using
    Model.toReal_add_eq_mul_one_add x y (by decide) hx hy hout

end FloatLibTests.Conformance.BinaryInterchange.BoundaryCases
