/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Runtime
public import Mathlib.Basic.Real.Basic
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Logarithm

/-!
# Shared exponent selection for concrete OCP MX blocks

The selected exponent is the binade exponent of the largest input magnitude minus the largest
element power-of-two exponent. E8M0 bounds every scale that reaches element quantization.
The binade theorem reuses the format-independent proof of the executable rational logarithm.
-/

public section

namespace FloatLib.Floats.Formats.OCP.MX

open FloatLib.Numerics

/-- Every finite E8M0 scale has a bounded exponent. -/
theorem E8M0.exponent?_bounds {scale : E8M0} {exponent : Int}
    (h : scale.exponent? = some exponent) : -127 ≤ exponent ∧ exponent ≤ 127 := by
  have hbits := scale.isLt
  unfold E8M0.exponent? E8M0.isNaN E8M0.bias at h
  split at h
  · contradiction
  · rename_i hfinite
    simp only [Option.some.injEq] at h
    simp only [beq_iff_eq] at hfinite
    subst exponent
    change scale.toNat < 256 at hbits
    simp only [Int.ofNat_eq_natCast]
    omega

/-- Saturating E8M0 encoding decodes to the clamped mathematical exponent. -/
@[simp] theorem E8M0.exponent?_ofExponentSaturating (exponent : Int) :
    (E8M0.ofExponentSaturating exponent).exponent? =
      some (max (-127) (min 127 exponent)) := by
  let clamped := max (-127) (min 127 exponent)
  have hlo : -127 ≤ clamped := le_max_left _ _
  have hhi : clamped ≤ 127 := max_le (by norm_num) (min_le_left _ _)
  have hcode : (clamped + 127).toNat < 256 := by omega
  have hnotnan : (clamped + 127).toNat ≠ 255 := by omega
  change (if (BitVec.ofNat 8 (clamped + 127).toNat).toNat == 255 then none
    else some ((BitVec.ofNat 8 (clamped + 127).toNat).toNat - (127 : Int))) = some clamped
  simp only [BitVec.toNat_ofNat, show 2 ^ 8 = 256 by decide, Nat.mod_eq_of_lt hcode]
  simp [hnotnan, Int.toNat_of_nonneg (by omega : 0 ≤ clamped + 127)]

namespace Standard

private theorem le_fold_max (values : List SignedRat) (initial : Rat) :
    initial ≤ values.foldl (fun largest value => max largest |value.value|) initial := by
  induction values generalizing initial with
  | nil => exact le_rfl
  | cons head tail ih =>
    exact (le_max_left initial |head.value|).trans (ih _)

/-- The largest input magnitude is nonnegative, including the all-zero block. -/
theorem maxMagnitude_nonneg (input : Vector SignedRat 32) : 0 ≤ maxMagnitude input :=
  le_fold_max input.toList 0

private theorem abs_le_fold_max {value : SignedRat} {values : List SignedRat}
    (h : value ∈ values) (initial : Rat) :
    |value.value| ≤ values.foldl (fun largest value => max largest |value.value|) initial := by
  induction values generalizing initial with
  | nil => contradiction
  | cons head tail ih =>
    rcases List.mem_cons.mp h with rfl | htail
    · exact (le_max_right initial |value.value|).trans (le_fold_max tail _)
    · exact ih htail _

/-- Every lane is bounded by the magnitude used for standard scale selection. -/
theorem abs_le_maxMagnitude (input : Vector SignedRat 32) (lane : Fin 32) :
    |input[lane.val].value| ≤ maxMagnitude input :=
  abs_le_fold_max (Vector.mem_toList_iff.mpr (Vector.getElem_mem lane.isLt)) 0

/--
For a nonzero input block, the requested scale positions the largest magnitude between the
element's largest positive power of two and twice that value, before E8M0 range handling.
-/
theorem requestedExponent_bounds (profile : Profile) (input : Vector SignedRat 32)
    (hnonzero : maxMagnitude input ≠ 0) :
    (2 : Real) ^ (requestedExponent profile input + profile.maxPowerExponent) ≤
        (maxMagnitude input : Real) ∧
      (maxMagnitude input : Real) <
        (2 : Real) ^ (requestedExponent profile input + profile.maxPowerExponent + 1) := by
  let largest := maxMagnitude input
  have hpos : 0 < largest := lt_of_le_of_ne (maxMagnitude_nonneg input) (Ne.symm hnonzero)
  have hnum : largest.num.natAbs ≠ 0 := by
    simpa only [Int.natAbs_ne_zero] using (Rat.num_pos.mpr hpos).ne'
  have hratio : (largest.num.natAbs : Real) / largest.den = (largest : Real) := by
    rw [Nat.cast_natAbs, abs_of_pos (by exact_mod_cast Rat.num_pos.mpr hpos)]
    exact (Rat.cast_def largest).symm
  have hbounds := BinaryInterchange.Model.floorLog2_bounds
    largest.num.natAbs largest.den hnum (Nat.ne_of_gt largest.den_pos)
  change (2 : Real) ^ _ ≤ _ ∧ _ < (2 : Real) ^ _ at hbounds
  rw [hratio] at hbounds
  simpa only [requestedExponent, ite_eq_right hnonzero, sub_add_cancel, largest] using hbounds

/-- Out-of-range upper scales propagate a block NaN instead of constructing an invalid exponent. -/
theorem selectScale_exponent?_of_overflow (profile : Profile) (input : Vector SignedRat 32)
    (h : 127 < requestedExponent profile input) :
    (selectScale profile input).exponent? = none := by
  simp only [selectScale, ite_eq_left h]
  rfl

/-- Finite scale selection clamps only at the lower E8M0 boundary. -/
theorem selectScale_exponent?_of_le (profile : Profile) (input : Vector SignedRat 32)
    (h : requestedExponent profile input ≤ 127) :
    (selectScale profile input).exponent? =
      some (max (-127) (requestedExponent profile input)) := by
  simp [selectScale, not_lt.mpr h, min_eq_right h]

end Standard
end FloatLib.Floats.Formats.OCP.MX
