/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Proof

/-!
# Correctness of finite constants

The format-generic encodings of positive and negative one are finite normal values and decode to
the corresponding real constants. These facts are useful for powers, reciprocals, and executable
interval constructors.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

private theorem isFinite_oneFields (fmt : FloatFormat) (sign : Bool) :
    isFinite (ofFields fmt sign fmt.exponentBias 0) = true := by
  rw [isFinite_ofFields fmt sign fmt.exponentBias 0
    fmt.exponentBias_lt_two_pow (Nat.two_pow_pos fmt.fracWidth)]
  cases hencoding : fmt.encoding
  · have hbound :
        fmt.exponentBias ≤
          FloatFormat.Encoding.maxFiniteExponent .ieee fmt.expWidth := by
      simpa only [hencoding] using fmt.exponentBias_le_maxFinite
    change fmt.exponentBias ≤ 2 ^ fmt.expWidth - 2 at hbound
    apply bne_iff_ne.mpr
    unfold FloatFormat.expAllOnesNat
    have hfour := fmt.four_le_two_pow_expWidth
    have hstep : 2 ^ fmt.expWidth - 2 < 2 ^ fmt.expWidth - 1 := by omega
    exact Nat.ne_of_lt (hbound.trans_lt hstep)
  · have hmask : (0 : Nat) ≠ fmt.fracMaskNat :=
      (FloatFormat.fracMaskNat_pos fmt).ne
    simp [hmask]
  · have hbias : fmt.exponentBias ≠ 0 := Nat.ne_of_gt fmt.exponentBias_pos
    cases sign <;> simp [hbias]
  · rfl

/-- Positive one is finite in every supported format. -/
@[simp] theorem isFinite_posOne (fmt : FloatFormat) :
    isFinite (posOne fmt) = true := by
  exact isFinite_oneFields fmt false

/-- Negative one is finite in every supported format. -/
@[simp] theorem isFinite_negOne (fmt : FloatFormat) :
    isFinite (negOne fmt) = true := by
  exact isFinite_oneFields fmt true

/-- The unit fields with either sign denote `1` or `-1`. -/
private theorem toReal_oneFields (fmt : FloatFormat) (sign : Bool) :
    toReal (ofFields fmt sign fmt.exponentBias 0) = if sign then -1 else 1 := by
  rw [toReal_eq, toDyadic?_ofFields_of_isFinite fmt sign fmt.exponentBias 0
    fmt.exponentBias_lt_two_pow (Nat.two_pow_pos fmt.fracWidth)
    (isFinite_oneFields fmt sign)]
  cases sign <;>
    simp [fmt.exponentBias_pos.ne', Numerics.Dyadic.toReal,
      Numerics.Dyadic.signedSignificand, pow2_eq_two_pow, zpow_neg]

/-- Positive one denotes the real number `1` in every supported format. -/
@[simp] theorem toReal_posOne (fmt : FloatFormat) :
    toReal (posOne fmt) = 1 :=
  toReal_oneFields fmt false

/-- Negative one denotes the real number `-1` in every supported format. -/
@[simp] theorem toReal_negOne (fmt : FloatFormat) :
    toReal (negOne fmt) = -1 :=
  toReal_oneFields fmt true

end Model
end FloatLib.Floats.Formats.BinaryInterchange
