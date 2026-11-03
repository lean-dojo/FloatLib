/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Scaling.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Direction
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Minimal

/-!
# Scaling accuracy and cohort independence of exponent queries

The accuracy bounds use the delivered rational value and the public overflow
flag. Exact cohort selection also applies when the original shifted quantum is
outside the format range but another member of its cohort is representable.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Without overflow, the quantum of the rounded scaled value is at most the format's largest
quantum. -/
theorem scale_quantum_le_of_no_overflow (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int)
    (hfinite : (scale f mode (.finite s c q) n).status.overflow = false) :
    (roundedPair f mode s ((c : ℚ) * (10 : ℚ) ^ (q + n))).2 ≤ f.maxQuantum := by
  by_contra h
  have he := (projectMagnitude_overflow_iff f mode s
    ((c : ℚ) * (10 : ℚ) ^ (q + n)) (q + n)).mpr (by omega)
  rw [← scale_finite] at he
  simp [hfinite] at he

private theorem scale_magnitude_nonneg (c : Nat) (q n : Int) :
    0 ≤ (c : ℚ) * (10 : ℚ) ^ (q + n) :=
  mul_nonneg (Nat.cast_nonneg _) (zpow_pos (by norm_num) _).le

/-- The signed shifted magnitude that `scale` projects is the input value times `10 ^ n`. -/
private theorem scale_signed_value (s : Bool) (c : Nat) (q n : Int) :
    (if s then -((c : ℚ) * (10 : ℚ) ^ (q + n)) else (c : ℚ) * (10 : ℚ) ^ (q + n)) =
      Datum.finiteValue s c q * (10 : ℚ) ^ n := by
  cases s <;> simp [Datum.finiteValue, scale_exact_magnitude, mul_assoc]

/-- Both nearest directions deliver at most half a unit of error on the selected grid. -/
theorem scale_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearest ∨ mode = .nearestAway)
    (s : Bool) (c : Nat) (q n : Int)
    (hfinite : (scale f mode (.finite s c q) n).status.overflow = false) :
    ∃ v, (scale f mode (.finite s c q) n).value.toRat? = some v ∧
      |v - Datum.finiteValue s c q * (10 : ℚ) ^ n| ≤
        (10 : ℚ) ^ roundingQuantum f ((c : ℚ) * (10 : ℚ) ^ (q + n)) / 2 := by
  have h := projectMagnitude_error_le_half f mode hm s (scale_magnitude_nonneg c q n) (q + n)
    (scale_quantum_le_of_no_overflow f mode s c q n hfinite)
  rwa [scale_signed_value, ← scale_finite] at h

/-- Every rounding direction delivers an error smaller than one selected grid unit. -/
theorem scale_error_lt_one (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int)
    (hfinite : (scale f mode (.finite s c q) n).status.overflow = false) :
    ∃ v, (scale f mode (.finite s c q) n).value.toRat? = some v ∧
      |v - Datum.finiteValue s c q * (10 : ℚ) ^ n| <
        (10 : ℚ) ^ roundingQuantum f ((c : ℚ) * (10 : ℚ) ^ (q + n)) := by
  have h := projectMagnitude_error_lt_one f mode s (scale_magnitude_nonneg c q n) (q + n)
    (scale_quantum_le_of_no_overflow f mode s c q n hfinite)
  rwa [scale_signed_value, ← scale_finite] at h

/-- Rounding toward positive, a nonoverflowing scaling of a finite datum is finite and at least the
exact scaled value. -/
theorem le_scale_up (f : Format) (s : Bool) (c : Nat) (q n : Int)
    (hfinite : (scale f .up (.finite s c q) n).status.overflow = false) :
    ∃ v, (scale f .up (.finite s c q) n).value.toRat? = some v ∧
      Datum.finiteValue s c q * (10 : ℚ) ^ n ≤ v := by
  have h := projectMagnitude_up_le f s (scale_magnitude_nonneg c q n) (q + n)
    (scale_quantum_le_of_no_overflow f .up s c q n hfinite)
  rwa [scale_signed_value, ← scale_finite] at h

/-- Rounding toward negative, a nonoverflowing scaling of a finite datum is finite and at most the
exact scaled value. -/
theorem scale_down_le (f : Format) (s : Bool) (c : Nat) (q n : Int)
    (hfinite : (scale f .down (.finite s c q) n).status.overflow = false) :
    ∃ v, (scale f .down (.finite s c q) n).value.toRat? = some v ∧
      v ≤ Datum.finiteValue s c q * (10 : ℚ) ^ n := by
  have h := projectMagnitude_down_le f s (scale_magnitude_nonneg c q n) (q + n)
    (scale_quantum_le_of_no_overflow f .down s c q n hfinite)
  rwa [scale_signed_value, ← scale_finite] at h

/-- Exactness does not require the source's shifted representation itself to be in range. -/
theorem scale_exact_status_of_representable (f : Format) (mode : RoundingMode)
    (s : Bool) (c e : Nat) (q n t : Int) (he : (Datum.finite s e t).Valid f)
    (hv : (c : ℚ) * (10 : ℚ) ^ (q + n) = (e : ℚ) * (10 : ℚ) ^ t) :
    (scale f mode (.finite s c q) n).status = {} := by
  simpa only [scale_finite, hv] using projectMagnitude_exact_status f mode s e t (q + n) he

/-- Inexact finite results, including directed overflow deliveries, use the least quantum. -/
theorem scale_inexact_quantum_minimal (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q n : Int)
    (hinexact : (scale f mode (.finite s c q) n).status.inexact = true)
    (d : Nat) (r : Int) (hout : (scale f mode (.finite s c q) n).value = .finite s d r)
    (a : Nat) (b : Int) (ha : (Datum.finite s a b).Valid f)
    (he : (d : ℚ) * (10 : ℚ) ^ r = (a : ℚ) * (10 : ℚ) ^ b) : r ≤ b := by
  rw [scale_finite] at hinexact hout
  exact projectMagnitude_inexact_quantum_minimal f mode s _ (q + n) hinexact d r hout a b ha he

/-- A nonzero magnitude no larger than another has a radix exponent no larger. -/
private theorem decimalExponent_le_of_magnitude_le (f g : Format) (s t : Bool) (c d : Nat)
    (q r : Int) (hc : c ≠ 0) (hd : d ≠ 0)
    (he : (c : ℚ) * (10 : ℚ) ^ q ≤ (d : ℚ) * (10 : ℚ) ^ r) :
    (decimalExponent f (.finite s c q)).value ≤ (decimalExponent g (.finite t d r)).value := by
  have hx := decimalExponent_bounds f s c q hc
  have hy := decimalExponent_bounds g t d r hd
  by_contra h
  have hp : (10 : ℚ) ^ ((decimalExponent g (.finite t d r)).value + 1) ≤
      (10 : ℚ) ^ (decimalExponent f (.finite s c q)).value :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  linarith [hx.1, hy.2]

/-- Equal nonzero magnitudes have the same radix exponent, irrespective of cohort or sign. The
second coefficient is nonzero because the magnitudes agree. -/
theorem decimalExponent_eq_of_equal_magnitude (f g : Format) (s t : Bool) (c d : Nat) (q r : Int)
    (hc : c ≠ 0) (he : (c : ℚ) * (10 : ℚ) ^ q = (d : ℚ) * (10 : ℚ) ^ r) :
    (decimalExponent f (.finite s c q)).value = (decimalExponent g (.finite t d r)).value := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp [hc, (zpow_pos (by norm_num : (0 : ℚ) < 10) q).ne'] at he
  exact le_antisymm (decimalExponent_le_of_magnitude_le f g s t c d q r hc hd he.le)
    (decimalExponent_le_of_magnitude_le g f t s d c r q hd hc he.ge)

/-- `logB` of either zero, at any quantum, is the negative sentinel and raises invalid. -/
@[simp] theorem decimalExponent_zero (f : Format) (s : Bool) (q : Int) :
    decimalExponent f (.finite s 0 q) =
      { value := -decimalExponentSentinel f, status := { invalid := true } } :=
  rfl

/-- `logB` of either infinity is the positive sentinel and raises invalid. -/
@[simp] theorem decimalExponent_infinity (f : Format) (s : Bool) :
    decimalExponent f (.infinity s) =
      { value := decimalExponentSentinel f, status := { invalid := true } } := rfl

/-- `logB` of any NaN, quiet or signaling, is the positive sentinel and raises invalid. -/
@[simp] theorem decimalExponent_nan (f : Format) (s t : Bool) (p : Nat) :
    decimalExponent f (.nan s t p) =
      { value := decimalExponentSentinel f, status := { invalid := true } } := rfl

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
