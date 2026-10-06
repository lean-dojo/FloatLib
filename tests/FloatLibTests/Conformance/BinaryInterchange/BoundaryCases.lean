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

-- E2M3 cannot represent the nearest integer 8: its finite boundary is 7.5.
example : (Model.roundToIntegralExactWithStatus
    (Model.ofNatBits (fmt := .e2m3) 31) .nearestEven).value.toNatBits = 31 := by
  decide +kernel

example : (Model.roundToIntegralExactWithStatus
    (Model.ofNatBits (fmt := .e2m3) 31) .nearestEven).status.overflow = true := by
  decide +kernel

private abbrev Narrow := ExecFloat.Binary 2 1 (bias := 2)
private abbrev NarrowFinite := ExecFloat.Binary 2 1 (encoding := .finite) (bias := 3)

-- The E5M2 subnormal code 2 is 2^(-15). Its integer exponent must remain -15,
-- although that exponent cannot be represented exactly by an E5M2 floating result.
example : Model.binaryExponentInt (Model.ofNatBits (fmt := .e5m2) 2) =
    ⟨-15, {}⟩ := by decide +kernel

example : (Model.binaryExponentWithStatus (Model.ofNatBits (fmt := .e5m2) 2)).status.inexact =
    true := by decide +kernel

example : (Model.binaryExponentInt (Model.posZero .binary32)).status.invalid = true := by
  decide +kernel

example : (Model.binaryExponentInt (Model.posZero .binary32)).value <
    -2 * |Model.logBBound .binary32| := by decide +kernel

example : (Model.binaryExponentInt (Model.posInf .binary32)).value >
    2 * |Model.logBBound .binary32| := by decide +kernel

example : (Model.binaryExponentInt (Model.canonicalNaN .binary32)).status.invalid = true := by
  decide +kernel

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

private abbrev IntegralNarrow := FloatFormat.ieee 2 3

-- This IEEE-shaped custom layout does not satisfy the standard interchange range bound.
example : ¬ (IntegralNarrow.fracWidth : Int) ≤ IntegralNarrow.maxNormalExponent := by
  decide +kernel

/-- Every finite E2M3 input can be truncated without the interchange range bound. -/
theorem truncation_custom_range (value : Model (FloatFormat.ieee 2 3))
    (hfinite : Model.isFinite value = true) :
    Model.isFinite (Model.roundToIntegral value .towardZero) = true :=
  Model.isFinite_roundToIntegral_towardZero (by decide) value hfinite

/-- The broader truncation theorem computes 3.75 to 3 in the narrow-range descriptor. -/
theorem truncation_custom_value :
    Model.toReal (Model.roundToIntegral
      (Model.ofNatBits (fmt := FloatFormat.ieee 2 3) 23) .towardZero) = 3 := by
  let value := Model.ofNatBits (fmt := IntegralNarrow) 23
  have hd : Model.toDyadic? value = some ⟨false, 15, -2⟩ := by
    dsimp [value]
    rfl
  have hvalue : Model.toReal value = (15 / 4 : ℝ) := by
    norm_num [Model.toReal_eq, hd, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]
  change Model.toReal (Model.roundToIntegral value .towardZero) = 3
  rw [Model.toReal_roundToIntegral_towardZero_of_isFinite (by decide) value (by decide), hvalue]
  norm_num

example : (Model.roundToIntegralExactWithStatus
    (Model.ofNatBits (fmt := IntegralNarrow) 23) .towardZero).status.overflow = false :=
  Model.roundToIntegralExactWithStatus_towardZero_overflow_eq_false (by decide) _ (by decide)

-- Nearest rounding still overflows here; its range guard cannot be dropped wholesale.
example : Model.isInf (Model.roundToIntegral
    (Model.ofNatBits (fmt := IntegralNarrow) 23) .nearestEven) = true := by
  decide +kernel

example : (Model.roundToIntegral
    (Model.ofNatBits (fmt := IntegralNarrow) 55) .towardZero).toNatBits = 52 := by
  decide +kernel

example : (Model.roundToIntegral (Model.negZero .binary64) .towardZero).toNatBits =
    0x8000000000000000 := by decide +kernel

/-- Zero numerators use the common rational-rounding theorem for either stored sign. -/
theorem scaled_rational_zero (sign : Bool) (denominator : Nat) (hd : denominator ≠ 0)
    (exponent : Int) :
    Model.toReal (Model.roundRatScaled FloatFormat.binary64 sign 0 denominator exponent) =
      Model.roundAt FloatFormat.binary64
        (Model.signedScaledRatToReal sign 0 denominator exponent) := by
  apply Model.toReal_roundRatScaled_eq_roundAt_of_isFinite _ _ _ _ _ (by decide) hd
  rw [Model.roundRatScaled_num_zero _ _ _ _ hd]
  exact Model.isFinite_eq_true_of_isZero_eq_true _ (Model.isZero_zero _ _)

example : (Model.roundRatScaled FloatFormat.binary64 true 0 3 (-1074)).toNatBits =
    0x8000000000000000 := by decide +kernel

example : Model.isNaN (Model.roundRatScaled FloatFormat.binary64 false 0 0 0) = true := by
  decide +kernel

/-- Sterbenz exactness covers negative nearby operands through the public same-sign theorem. -/
theorem sterbenz_negative :
    Model.toReal (Model.sub (Model.ofNatBits (fmt := .binary64) 0xbff8000000000000)
      (Model.negOne .binary64)) = (-1 / 2 : ℝ) := by
  let x := Model.ofNatBits (fmt := .binary64) 0xbff8000000000000
  let y := Model.negOne FloatFormat.binary64
  have hd : Model.toDyadic? x = some ⟨true, 3 * 2 ^ 51, -52⟩ := by
    dsimp [x]
    rfl
  have hx : Model.toReal x = (-3 / 2 : ℝ) := by
    norm_num [Model.toReal_eq, hd, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]
  have hy : Model.toReal y = -1 := Model.toReal_negOne _
  have hsub := Model.toReal_sub_eq_of_sterbenz_of_same_sign (x := x) (y := y)
    (by decide) (by decide) (by decide)
    (by rw [hx, hy]; norm_num) (by rw [hx, hy]; norm_num) (by rw [hx, hy]; norm_num)
  change Model.toReal (Model.sub x y) = (-1 / 2 : ℝ)
  rw [hsub, hx, hy]
  norm_num

example : (Model.sub (Model.ofNatBits (fmt := .binary16) 0x8002)
    (Model.ofNatBits (fmt := .binary16) 0x8001)).toNatBits = 0x8001 := by
  decide +kernel

example : Model.toReal (Model.sub (Model.negZero .binary64) (Model.posZero .binary64)) = 0 := by
  have hfmt : FloatFormat.binary64.isIEEE = true := by decide
  rw [Model.toReal_sub_eq_of_sterbenz_of_same_sign
    (x := Model.negZero .binary64) (y := Model.posZero .binary64)
    hfmt (by decide) (by decide)
    (by simp [hfmt]) (by simp [hfmt]) (by simp [hfmt])]
  simp [hfmt]

-- FNUZ is a finite-with-NaN encoding with a different bias from the IEEE layout.
example : FloatFormat.e4m3fnuz.isIEEE = false := by decide +kernel

/-- A finite FNUZ source uses the common exact widening contract for an IEEE destination. -/
theorem cast_fnuz_source :
    Model.toReal (Model.cast FloatFormat.e4m3fnuz FloatFormat.binary32
      (Model.ofNatBits (fmt := .e4m3fnuz) 68)) =
      Model.toReal (Model.ofNatBits (fmt := .e4m3fnuz) 68) :=
  Model.cast_exact_of_gridExtension_of_isIEEE_destination _ (by decide)
    (by decide) (by decide) (by decide) (by decide)

example : (Model.cast FloatFormat.e4m3fnuz (FloatFormat.ieee 4 3)
    (Model.ofNatBits (fmt := .e4m3fnuz) 68)).toNatBits = 60 := by decide +kernel

example : (Model.cast FloatFormat.e4m3fn (FloatFormat.ieee 4 3)
    (Model.ofNatBits (fmt := .e4m3fn) 60)).toNatBits = 60 := by decide +kernel

/-- Opposite finite terms cancel through the common sum rounding bridge. -/
theorem sum_cancellation_real :
    Model.toReal (Model.sumWithStatus FloatFormat.binary64
      #[Model.posOne .binary32, Model.negOne .binary32] .nearestEven).value = 0 := by
  have hsum : Model.Reduction.Semantics.finiteSum
      [Model.posOne FloatFormat.binary32, Model.negOne FloatFormat.binary32] = 0 := by
    decide +kernel
  rw [Model.Reduction.sumWithStatus_value_toReal_eq_roundAt_of_finite _ _ (by decide)]
  · change Model.roundAt FloatFormat.binary64
      (Model.Reduction.Semantics.finiteSum
        [Model.posOne FloatFormat.binary32, Model.negOne FloatFormat.binary32] : ℝ) = 0
    rw [hsum]
    simp
  · intro value hvalue
    change value ∈ [Model.posOne FloatFormat.binary32, Model.negOne FloatFormat.binary32]
      at hvalue
    simp at hvalue
    rcases hvalue with rfl | rfl <;> decide +kernel
  · decide +kernel

/-- A cancelling product sum succeeds and uses the common real-rounding theorem at zero. -/
theorem dot_cancellation_real :
    ∃ outcome : Model.IEEEOutcome FloatFormat.binary64,
      Model.dotWithStatus FloatFormat.binary64
          #[Model.posOne .binary32, Model.posOne .binary32]
          #[Model.posOne .binary32, Model.negOne .binary32] .nearestEven = .ok outcome ∧
        Model.toReal outcome.value = Model.roundAt FloatFormat.binary64 (0 : ℝ) := by
  let outcome : Model.IEEEOutcome FloatFormat.binary64 := { value := Model.posZero .binary64, status := {} }
  have houtcome : Model.dotWithStatus FloatFormat.binary64
      #[Model.posOne .binary32, Model.posOne .binary32]
      #[Model.posOne .binary32, Model.negOne .binary32] .nearestEven = .ok outcome := by
    dsimp [outcome]
    decide +kernel
  refine ⟨outcome, houtcome, ?_⟩
  simpa using Model.Reduction.dotWithStatus_value_toReal_eq_roundAt_of_finite
    _ _ _ 0 outcome (by decide) (by decide)
    (by
      intro position hposition
      have h : position = 0 ∨ position = 1 := by
        change position < 2 at hposition
        omega
      rcases h with rfl | rfl <;> decide +kernel +revert)
    (by
      intro position hposition
      have h : position = 0 ∨ position = 1 := by
        change position < 2 at hposition
        omega
      rcases h with rfl | rfl <;> decide +kernel +revert)
    (by decide +kernel) houtcome (by dsimp [outcome]; decide +kernel)

/-- Normalized rational conversion supplies both enclosure endpoints without a nonzero premise. -/
theorem rational_directed_enclosure (fmt : FloatFormat) (q : Rat) (hfmt : fmt.isIEEE = true) :
    ((q : ℝ) : EReal) ∈ Set.Icc
      (Model.toEReal (Model.roundRatQDown fmt q))
      (Model.toEReal (Model.roundRatQUp fmt q)) :=
  ⟨Model.toEReal_roundRatQDown_le fmt q hfmt, Model.le_toEReal_roundRatQUp fmt q hfmt⟩

example : (Model.roundRatQUp FloatFormat.binary16 ((1 : Rat) / 2 ^ 25)).toNatBits = 1 := by
  decide +kernel

example : (Model.roundRatQUp FloatFormat.binary16 (-(1 : Rat) / 2 ^ 25)).toNatBits = 0x8000 := by
  decide +kernel

example : Model.isInf (Model.roundRatQUp FloatFormat.binary16 65536) = true := by
  decide +kernel

end FloatLibTests.Conformance.BinaryInterchange.BoundaryCases
