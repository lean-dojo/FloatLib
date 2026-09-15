/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange

/-!
# Descriptor and interval boundary regressions

These cases check declared exponent biases, overflow during integral conversion, and composition
of intervals with infinite endpoints. Each expected result is checked by the kernel. Configured
examples also exercise the same `ExecFloat` operations used by numerical programs.
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

end FloatLibTests.Conformance.BinaryInterchange.BoundaryCases
