/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Classification.Classes
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Classification.Semantics

/-!
# Exact semantic classification of binary data

The field-based classifier refines the complete exact interpretation for every descriptor.
Finite classes depend on numerical zero and the normal threshold, retaining the sign of zero.
Infinity signs and NaN signaling status come from the same exact interpretation.

This entry point also exports all ten predicate characterizations, real/rational threshold
theorems, the finite-class partition, and canonical stored-field reconstruction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

variable {fmt : FloatFormat}

/-- Finite classification agrees with exact numerical zero, magnitude, and the decoded sign. -/
theorem classify_of_toDyadic {x : Model fmt} {d : Numerics.Dyadic}
    (hx : toDyadic? x = some d) :
    classify x =
      if d.toRat = 0 then
        if d.negative then .negativeZero else .positiveZero
      else if |d.toRat| < (2 : ℚ) ^ fmt.minNormalExponent then
        if d.negative then .negativeSubnormal else .positiveSubnormal
      else
        if d.negative then .negativeNormal else .positiveNormal := by
  have hn := isNaN_eq_false_of_toDyadic?_some hx
  have hi := isInf_eq_false_of_toDyadic?_some hx
  have hs := sign_eq_signBit_of_toDyadic?_some hx
  have hz := isZero_iff_toRat_eq_zero hx
  have hsub := isSubnormal_iff_abs_toRat hx
  simp only [abs_pos] at hsub
  by_cases hzero : d.toRat = 0 <;>
    simp [classify, hn, hi, hz, hsub, ← hs, hzero]

/-- Classification is determined by the complete exact value and the declared normal threshold.
The NaN sign and payload do not affect its signaling/quiet class. -/
theorem classify_eq_match_exactValue (x : Model fmt) :
    classify x =
      match exactValue x with
      | .nan _ signaling _ => if signaling then .signalingNaN else .quietNaN
      | .infinity sign => if sign then .negativeInfinity else .positiveInfinity
      | .finite d =>
          if d.toRat = 0 then
            if d.negative then .negativeZero else .positiveZero
          else if |d.toRat| < (2 : ℚ) ^ fmt.minNormalExponent then
            if d.negative then .negativeSubnormal else .positiveSubnormal
          else
            if d.negative then .negativeNormal else .positiveNormal := by
  cases hd : toDyadic? x with
  | some d =>
      simpa only [exactValue, hd] using classify_of_toDyadic hd
  | none =>
      cases hi : isInf x
      · have hn : isNaN x = true := by
          apply Bool.eq_true_of_not_eq_false
          intro hnan
          obtain ⟨d, hdecode⟩ := exists_toDyadic?_of_isFinite
            (isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnan hi)
          simp [hd] at hdecode
        simp [classify, exactValue, hd, hi, hn]
      · have hn := isNaN_eq_false_of_isInf_eq_true x hi
        simp [classify, exactValue, hd, hi, hn]

/-- Equal complete exact values have equal classes, without any IEEE-policy restriction. -/
theorem classify_eq_of_exactValue_eq {x y : Model fmt}
    (h : exactValue x = exactValue y) : classify x = classify y := by
  rw [classify_eq_match_exactValue, classify_eq_match_exactValue, h]

end FloatLib.Floats.Formats.BinaryInterchange.Model
