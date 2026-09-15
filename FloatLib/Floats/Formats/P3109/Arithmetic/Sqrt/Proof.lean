/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Scaling
public import FloatLib.Floats.Formats.P3109.Projection.Correctness

/-!
# Real semantics and executable refinement of P3109 square root

The reference rounder takes the floor of a real square root and compares that root with the
report's exact rounding thresholds. The executable rounder computes the same result using
natural-number square roots and products. Neither implementation first projects a rational
approximation of the root.

The final decoding theorem composes this equality with the existing report saturation and
encoding theorem. Reciprocal square root and hypotenuse reuse the same rounder after forming
their exact rational radicands.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

/-- The report's upper-candidate decision expressed using the real square root. -/
noncomputable def sqrtRoundAwayReal (format : Format) (mode : RoundingMode)
    (quantum : Int) (numerator denominator lower : Nat) : Bool :=
  let root := Real.sqrt ((numerator : Real) / denominator)
  sqrtRoundDecision format mode quantum lower (decide (root = lower))
    (fun scale threshold => compare root ((threshold : Real) / scale))

/-- Exact integer threshold tests implement real square-root rounding in every supplied mode. -/
theorem sqrtRoundAway_eq_real (format : Format) (mode : RoundingMode)
    (quantum : Int) (numerator denominator lower : Nat) (hd : 0 < denominator) :
    sqrtRoundAway format mode quantum numerator denominator lower =
      sqrtRoundAwayReal format mode quantum numerator denominator lower := by
  have hexact :
      Real.sqrt ((numerator : Real) / denominator) = lower ↔
        numerator = denominator * lower ^ 2 := by
    simpa using sqrt_eq_threshold_iff numerator denominator 1 lower hd (by decide)
  have hcompare := compareSqrt_eq_real numerator denominator
  unfold sqrtRoundAway sqrtRoundAwayReal
  simp only [hexact]
  cases mode <;>
    simp [sqrtRoundDecision, hcompare, hd]

/--
Reference precision rounding takes the floor and threshold comparisons of a real root.
As in the executable precision helper, the radicand magnitude is used; the closed operation
rejects negative inputs before calling this helper.
-/
noncomputable def roundSqrtRealToPrecision (format : Format) (mode : RoundingMode)
    (radicand : Rat) : FloatLib.Numerics.Dyadic :=
  if radicand.num.natAbs == 0 then .zero
  else
    let quantum := sqrtQuantum format radicand.num.natAbs radicand.den
    let scaled :=
      RationalBinary.scaleByPowerOfTwo radicand.num.natAbs radicand.den (-2 * quantum)
    let lower := ⌊Real.sqrt ((scaled.1 : Real) / scaled.2)⌋₊
    let rounded :=
      if sqrtRoundAwayReal format mode quantum scaled.1 scaled.2 lower then lower + 1 else lower
    if rounded == 0 then .zero else ⟨false, rounded, quantum⟩

/-- The executable precision rounder equals the rounder defined with the actual real root. -/
theorem roundSqrtRatToPrecision_eq_real (format : Format) (mode : RoundingMode)
    (radicand : Rat) :
    roundSqrtRatToPrecision format mode radicand =
      roundSqrtRealToPrecision format mode radicand := by
  unfold roundSqrtRatToPrecision roundSqrtRealToPrecision
  split
  · rfl
  · have hd := Nat.pos_of_ne_zero
      (RationalBinary.scaleByPowerOfTwo_snd_ne_zero
        radicand.num.natAbs radicand.den
        (-2 * sqrtQuantum format radicand.num.natAbs radicand.den) radicand.den_nz)
    simp only [floor_real_sqrt _ _ hd, sqrtRoundAway_eq_real _ _ _ _ _ _ hd]

/-- Closed square-root reference, followed by the supplied report saturation policy. -/
noncomputable def sqrtRealValue (format : Format) (policy : ProjectionPolicy)
    (value : NumericalValue Rat) : NumericalValue FloatLib.Numerics.Dyadic :=
  format.saturate policy.saturation policy.rounding
    (match value with
    | .exceptional _ | .infinity true => .exceptional (.nan)
    | .infinity false => .infinity false
    | .finite value =>
        if value < 0 then .exceptional (.nan)
        else .finite (roundSqrtRealToPrecision format policy.rounding value))

/-- Closed executable square root refines the real-root reference for every input and policy. -/
theorem sqrtValue_eq_real (format : Format) (policy : ProjectionPolicy)
    (value : NumericalValue Rat) :
    sqrtValue format policy value = sqrtRealValue format policy value := by
  cases value with
  | finite value =>
      simp [sqrtValue, sqrtRounded, sqrtRealValue, roundSqrtRatToPrecision_eq_real]
  | infinity negative => cases negative <;> rfl
  | exceptional _ => rfl

/-- Encoding and decoding preserves the single rounded and saturated square-root datum. -/
theorem sameDatum_decode_sqrtCode (format : Format) (policy : ProjectionPolicy)
    (value : NumericalValue Rat) :
    Format.SameDatum (format.decode (sqrtCode format policy value))
      (sqrtValue format policy value) := by
  unfold sqrtCode sqrtValue
  apply format.sameDatum_decode_encodeSaturate
  cases value with
  | finite value =>
      by_cases hnegative : value < 0 <;>
        simp [sqrtRounded, hnegative, roundSqrtRatToPrecision_fitsPrecisionGrid]
  | infinity negative => cases negative <;> trivial
  | exceptional _ => trivial

/-- Reciprocal square root uses the same real value as reciprocal of the positive square root. -/
theorem sqrt_recip_real (value : Rat) :
    Real.sqrt ((1 / value : Rat) : Real) = 1 / Real.sqrt (value : Real) := by
  simp [one_div, Real.sqrt_inv]

/-- The finite hypotenuse radicand is the real sum of squares and is nonnegative. -/
theorem hypotRadicand_finite_real (left right : Rat) :
    ((left * left + right * right : Rat) : Real) = (left : Real) ^ 2 + (right : Real) ^ 2 ∧
      0 ≤ left * left + right * right := by
  constructor
  · simp [pow_two]
  · exact add_nonneg (mul_self_nonneg left) (mul_self_nonneg right)

end FloatLib.Floats.Formats.P3109.Arithmetic

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {source leftFormat rightFormat : Format}

/-- Decoding the square-root projector returns the real-root report reference. -/
theorem decode_projectSqrt (destination : Format) (policy : ProjectionPolicy)
    (value : NumericalValue Rat) :
    Format.SameDatum (decode (projectSqrt destination policy value))
      (Arithmetic.sqrtRealValue destination policy value) := by
  change Format.SameDatum
    (destination.decode (Arithmetic.sqrtCode destination policy value)) _
  rw [← Arithmetic.sqrtValue_eq_real]
  exact Arithmetic.sameDatum_decode_sqrtCode destination policy value

/-- Mixed-format square root evaluates the source value and rounds once into the destination. -/
theorem decode_sqrtTo (destination : Format) (policy : ProjectionPolicy)
    (value : ExecFloat.P3109 source) :
    Format.SameDatum (decode (sqrtTo destination policy value))
      (Arithmetic.sqrtRealValue destination policy value.toClosedRat) :=
  decode_projectSqrt destination policy value.toClosedRat

/-- Reciprocal square root projects the root of the exact reciprocal, with its report domain. -/
theorem decode_rsqrtTo (destination : Format) (policy : ProjectionPolicy)
    (value : ExecFloat.P3109 source) :
    Format.SameDatum (decode (rsqrtTo destination policy value))
      (Arithmetic.sqrtRealValue destination policy
        (Arithmetic.rsqrtRadicand value.toClosedRat)) :=
  decode_projectSqrt destination policy _

/-- Hypotenuse projects the root of the exact sum of squares without intermediate overflow. -/
theorem decode_hypotTo (destination : Format) (policy : ProjectionPolicy)
    (left : ExecFloat.P3109 leftFormat) (right : ExecFloat.P3109 rightFormat) :
    Format.SameDatum (decode (hypotTo destination policy left right))
      (Arithmetic.sqrtRealValue destination policy
        (Arithmetic.hypotRadicand left.toClosedRat right.toClosedRat)) :=
  decode_projectSqrt destination policy _

end FloatLib.Floats.ExecFloat.P3109
