/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Classification.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics
import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Proof

/-!
# Binary classification predicates

The finite classes partition every descriptor's finite values. In particular, subnormal
fields remain finite under every exceptional-value policy, whereas zero fields alone do not
imply zero in FNUZ. The finite hypothesis in `isZero_iff_fields_of_isFinite` excludes its NaN.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

variable {fmt : FloatFormat}

/-- For a finite value, zero means that both magnitude fields vanish. -/
theorem isZero_iff_fields_of_isFinite {x : Model fmt} (hx : isFinite x = true) :
    isZero x = true ↔ expField x = 0 ∧ fracField x = 0 := by
  have hf := isFinite_ofFields fmt (signBit x) (expField x) (fracField x)
    (expField_lt_pow2 x) (fracField_lt_pow2 x)
  have hz := isZero_ofFields fmt (signBit x) (expField x) (fracField x)
    (expField_lt_pow2 x) (fracField_lt_pow2 x)
  rw [ofFields_signBit_expField_fracField, hx] at hf
  rw [ofFields_signBit_expField_fracField] at hz
  rw [hz]
  cases he : fmt.encoding <;> cases hs : signBit x <;>
    by_cases hezero : expField x = 0 <;> by_cases hfzero : fracField x = 0 <;>
    simp [he, hs, hezero, hfzero] at hf ⊢

/-- Every subnormal field pattern is finite, including under the FNUZ policy. -/
theorem isFinite_of_isSubnormal {x : Model fmt} (hx : isSubnormal x = true) :
    isFinite x = true := by
  obtain ⟨he, hf⟩ : expField x = 0 ∧ fracField x ≠ 0 := by
    simpa [isSubnormal] using hx
  have hd := toDyadic?_ofFields_subnormal fmt (signBit x) (fracField x)
    hf (fracField_lt_pow2 x)
  rw [← he, ofFields_signBit_expField_fracField] at hd
  exact isFinite_eq_true_of_toDyadic?_some hd

/-- The normal predicate uses the descriptor's finiteness policy and nonzero exponent. -/
theorem isNormal_iff_fields (x : Model fmt) :
    isNormal x = true ↔ isFinite x = true ∧ expField x ≠ 0 := by
  simp [isNormal]

/-- Normal values are exactly the finite values that are neither zero nor subnormal. -/
theorem isNormal_iff (x : Model fmt) :
    isNormal x = true ↔
      isFinite x = true ∧ isZero x = false ∧ isSubnormal x = false := by
  rw [isNormal_iff_fields]
  constructor
  · rintro ⟨hf, he⟩
    refine ⟨hf, Bool.eq_false_iff.mpr ?_, ?_⟩
    · intro hz
      exact he ((isZero_iff_fields_of_isFinite hf).mp hz).1
    · simp [isSubnormal, he]
  · rintro ⟨hf, hz, hs⟩
    refine ⟨hf, ?_⟩
    intro he
    have hfrac : fracField x = 0 := by
      simpa [isSubnormal, he] using hs
    have := (isZero_iff_fields_of_isFinite hf).mpr ⟨he, hfrac⟩
    simp [hz] at this

/-- Finiteness is the union of zero, subnormal, and normal classification. -/
theorem isFinite_eq_zero_or_subnormal_or_normal (x : Model fmt) :
    isFinite x = (isZero x || isSubnormal x || isNormal x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true]
  constructor
  · intro hf
    cases hz : isZero x
    · cases hs : isSubnormal x
      · exact Or.inr ((isNormal_iff x).mpr ⟨hf, hz, hs⟩)
      · exact Or.inl (Or.inr rfl)
    · exact Or.inl (Or.inl rfl)
  · rintro ((hz | hs) | hn)
    · exact isFinite_eq_true_of_isZero_eq_true x hz
    · exact isFinite_of_isSubnormal hs
    · exact ((isNormal_iff x).mp hn).1

/-- Zero and subnormal classification are disjoint. -/
theorem isSubnormal_eq_false_of_isZero {x : Model fmt} (hx : isZero x = true) :
    isSubnormal x = false := by
  have hf := isFinite_eq_true_of_isZero_eq_true x hx
  obtain ⟨he, hfrac⟩ := (isZero_iff_fields_of_isFinite hf).mp hx
  simp [isSubnormal, he, hfrac]

/-- Signaling and quiet NaNs partition NaNs under every supported encoding policy. -/
theorem isQNaN_eq_nan_and_not_signaling (x : Model fmt) :
    isQNaN x = (isNaN x && !isSNaN x) := by
  cases he : fmt.encoding <;>
    simp [isQNaN, isSNaN, he, IEEE.isQNaN, IEEE.isSNaN] <;>
    cases hn : IEEE.isNaN x <;> simp [isNaN, he, hn]
  rfl

/-- Every signaling NaN is a NaN. Non-IEEE policies have no signaling NaNs. -/
theorem isNaN_of_isSNaN {x : Model fmt} (hx : isSNaN x = true) :
    isNaN x = true := by
  cases hn : isNaN x
  · have := isSNaN_eq_false_of_isNaN_eq_false x hn
    simp [hx] at this
  · rfl

/-- Every exact-width binary datum is canonical, including every NaN payload. -/
@[simp] theorem isCanonical_eq_true (x : Model fmt) : isCanonical x = true := rfl

/-- Canonical classification agrees with exact reconstruction of all stored fields.
This reconstruction preserves signaling bits and payloads as well as finite data. -/
theorem isCanonical_iff_fields_roundtrip (x : Model fmt) :
    isCanonical x = true ↔ ofFields fmt (signBit x) (expField x) (fracField x) = x := by
  simp [ofFields_signBit_expField_fracField]

end FloatLib.Floats.Formats.BinaryInterchange.Model
