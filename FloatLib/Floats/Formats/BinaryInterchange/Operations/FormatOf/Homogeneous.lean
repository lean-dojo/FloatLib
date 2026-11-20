/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Reference
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Decode
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact

/-!
# The formatOf operations in one format

The arithmetic of IEEE 754-2019 §5.4.1 is formatOf arithmetic: operands of any formats and one
rounding into the destination. When the operands and the destination have one format, the
operation is the homogeneous operation of that format. This module proves it for every operand,
finite or not, in every rounding direction and for every format descriptor:

* `formatOfAddition_eq_add`, `formatOfSubtraction_eq_sub`, `formatOfMultiplication_eq_mul`,
  `formatOfDivision_eq_div` and `formatOfFusedMultiplyAdd_eq_fma`: the whole outcome, the value
  with its exception flags and its ternary value, is the outcome of `Model.add`, `sub`, `mul`,
  `div` and `fma` with `status := true` in the same direction. That covers the signed zeros, the
  infinity or the NaN of a division by zero, the exact infinities, the NaN that NaN operands
  select (a signaling one before a quiet one and the left before the right, quieted), and
  `invalid` for a signaling NaN, for infinities of opposite signs added, for zero times infinity
  and for infinity divided by infinity.

* `formatOfAddition_value_eq_add`, `formatOfSubtraction_value_eq_sub`,
  `formatOfMultiplication_value_eq_mul`, `formatOfDivision_value_eq_div` and
  `formatOfFusedMultiplyAdd_value_eq_fma`: the delivered values, which are `Model.add`, `sub`,
  `mul`, `div` and `fma` in the same direction.

So every theorem of the homogeneous operations in a direction (the directed enclosures of
`DirectedSemantics`, the kernel path, the theorems on the flags) applies to the formatOf
operations in one format.

`dyadicRoundingOutcome_zero` is the step for an exact zero result, which the formatOf operations
deliver without consulting the rounding: a zero delivered for an exact zero raises no flag.
`Factor.ofValue_self` is the step for the special cases: an operand read in its own format is
finite, or a NaN that is delivered quieted (`cast_quietNaN_self`), or an infinity, which only
the IEEE encoding has and which is the overflow result of its sign
(`eq_nativeOverflow_of_isInfinite`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Reduction.Internal (Factor)

variable {fmt : FloatFormat}

/-! ## An exact zero -/

/--
A zero delivered for an exact result that is zero raises no flag and has the ternary value
`.eq`, in every direction and for every format descriptor.
-/
theorem dyadicRoundingOutcome_zero (fmt : FloatFormat) (mode : IEEERoundingMode)
    {exact : Numerics.Dyadic} (hexact : exact.significand = 0) (sign : Bool) :
    dyadicRoundingOutcome fmt mode exact (zero fmt sign) =
      { value := zero fmt sign, status := .clear, ternary := .eq } := by
  have hfinite : isFinite (zero fmt sign) = true :=
    isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt sign)
  have hreal : toReal (zero fmt sign) = exact.toReal := by
    rw [toReal_zero, (Dyadic.toReal_eq_zero_iff exact).mpr hexact]
  have hmagnitude : ({ exact with negative := false } : Numerics.Dyadic).toReal = 0 :=
    (Dyadic.toReal_eq_zero_iff _).mpr hexact
  have hmidpoint : cmpDyadic { exact with negative := false } (overflowMidpoint fmt) = .lt := by
    rw [cmpDyadic_eq_compare, hmagnitude]
    exact compare_lt_iff_lt.mpr
      (Dyadic.toReal_pos_of_negative_eq_false rfl (by simp [overflowMidpoint]))
  have hlimit : cmpDyadic { exact with negative := false } (overflowLimit fmt) = .lt := by
    rw [cmpDyadic_eq_compare, hmagnitude]
    exact compare_lt_iff_lt.mpr
      (Dyadic.toReal_pos_of_negative_eq_false rfl (by simp [overflowLimit]))
  have hmaximum : (cmpDyadic { exact with negative := false } (maxFiniteDyadic fmt) == .gt) =
      false := by
    rw [beq_eq_false_iff_ne, cmpDyadic_eq_compare, hmagnitude]
    intro h
    exact absurd (compare_gt_iff_gt.mp h)
      (not_lt.mpr (Dyadic.toReal_nonneg_of_negative_eq_false rfl))
  have hoverflow : dyadicRoundingOverflows fmt mode exact = false := by
    cases mode <;>
      simp [dyadicRoundingOverflows, dyadicNearestEvenOverflows, dyadicNearestAwayOverflows,
        dyadicTruncationOverflows, dyadicMagnitudeOverflows, hmidpoint, hlimit, hmaximum]
  have hcompare (d : Numerics.Dyadic) (hd : d.significand = 0) : cmpDyadic exact d = .eq := by
    rw [cmpDyadic_eq_compare, compare_eq_iff_eq, (Dyadic.toReal_eq_zero_iff exact).mpr hexact,
      (Dyadic.toReal_eq_zero_iff d).mpr hd]
  have hternary : dyadicTernary exact (zero fmt sign) = .eq :=
    (dyadicTernary_eq_eq_iff exact hfinite).mpr hreal
  unfold dyadicRoundingOutcome dyadicRoundingStatus
  simp [hoverflow, hfinite, hcompare ⟨sign && fmt.supportsSignedZero, 0, 0⟩ rfl, hternary,
    Numerics.IEEEStatus.clear]

/-! ## Operands of the destination format -/

/-- Quieting a quieted value changes nothing. -/
theorem quietNaN_quietNaN (x : Model fmt) : quietNaN (quietNaN x) = quietNaN x := by
  by_cases hnan : isNaN x = true
  · have hquiet : isNaN (quietNaN x) = true := by rw [isNaN_quietNaN, hnan]
    have hbits : (quietNaN (quietNaN x)).toNatBits = (quietNaN x).toNatBits := by
      rw [KernelPath.quietNaN_bits _ hquiet, KernelPath.quietNaN_bits x hnan, Nat.or_assoc,
        Nat.or_self]
    rw [← ofNatBits_toNatBits (quietNaN (quietNaN x)), hbits, ofNatBits_toNatBits]
  · have hfalse : isNaN x = false := by simpa using hnan
    rw [quietNaN_eq_self_of_isNaN_eq_false x hfalse, quietNaN_eq_self_of_isNaN_eq_false x hfalse]

/-- A cast within one format returns a quieted NaN unchanged. -/
theorem cast_quietNaN_self {x : Model fmt} (hnan : isNaN x = true) :
    cast fmt fmt (quietNaN x) = quietNaN x := by
  have hquiet : isNaN (quietNaN x) = true := by rw [isNaN_quietNaN, hnan]
  rw [cast_of_isNaN _ hquiet, propagatedNaN_eq_quietNaN _ hquiet, quietNaN_quietNaN]

/-- The overflow result of the IEEE encoding is an infinity. -/
theorem isInfinite_nativeOverflow (hencoding : fmt.encoding = .ieee) (negative : Bool) :
    isInfinite (nativeOverflow fmt negative) = true := by
  have hsupports : fmt.supportsInfinity = true := by
    simp [FloatFormat.supportsInfinity, hencoding]
  cases negative <;> simp [nativeOverflow, hencoding, hsupports]

/-- The overflow result of the IEEE encoding has the sign it was asked for. -/
theorem signBit_nativeOverflow (hencoding : fmt.encoding = .ieee) (negative : Bool) :
    signBit (nativeOverflow fmt negative) = negative := by
  cases negative <;> simp [nativeOverflow, hencoding]

/-- An exact infinity delivered as the overflow result of the IEEE encoding is exact. -/
theorem exactInfinityTernary_nativeOverflow (hencoding : fmt.encoding = .ieee)
    (negative : Bool) :
    exactInfinityTernary negative (nativeOverflow fmt negative) = .eq := by
  simp [exactInfinityTernary, isInfinite_nativeOverflow hencoding,
    signBit_nativeOverflow hencoding]

/-- Only the IEEE encoding has infinities, and an infinity is the overflow result of its sign. -/
theorem eq_nativeOverflow_of_isInfinite {x : Model fmt} (hx : isInfinite x = true) :
    fmt.encoding = .ieee ∧ x = nativeOverflow fmt (signBit x) := by
  have hencoding : fmt.encoding = .ieee := by
    cases h : fmt.encoding <;> simp [isInfinite, h] at hx ⊢
  have hfields : expField x = fmt.expAllOnesNat ∧ fracField x = 0 := by
    simpa [isInfinite, hencoding, IEEE.isInfinite] using hx
  refine ⟨hencoding, ?_⟩
  cases hsign : signBit x
  · have hvalue : nativeOverflow fmt false = posInf fmt := by simp [nativeOverflow, hencoding]
    rw [hvalue, ← ofFields_signBit_expField_fracField x,
      ← ofFields_signBit_expField_fracField (posInf fmt), hsign, hfields.1, hfields.2,
      signBit_posInf, posInf_eq_ofModel_infinity, expField_ofModel_infinity,
      fracField_ofModel_infinity]
  · have hvalue : nativeOverflow fmt true = negInf fmt := by simp [nativeOverflow, hencoding]
    rw [hvalue, ← ofFields_signBit_expField_fracField x,
      ← ofFields_signBit_expField_fracField (negInf fmt), hsign, hfields.1, hfields.2,
      signBit_negInf, negInf_eq_ofModel_infinity, expField_ofModel_infinity,
      fracField_ofModel_infinity]

namespace Reduction.Internal

/--
What the formatOf operations read of an operand of the destination format. The operand is
finite, with its exact dyadic and its sign; or a NaN, which is delivered quieted; or an infinity,
which only the IEEE encoding has and which is the overflow result of its sign.
-/
theorem Factor.ofValue_self (x : Model fmt) :
    (∃ d negative, toDyadic? x = some d ∧ (Factor.ofValue x : Factor fmt) = .finite d ∧
        d.negative = negative ∧ signBit x = negative ∧ isZero x = (d.significand == 0) ∧
        isFinite x = true ∧ isNaN x = false ∧ isSignaling x = false ∧ isInfinite x = false) ∨
      (∃ signaling, toDyadic? x = none ∧
        (Factor.ofValue x : Factor fmt) = .nan (quietNaN x) signaling ∧
        isSignaling x = signaling ∧ isFinite x = false ∧ isNaN x = true ∧
        isInfinite x = false ∧ isZero x = false) ∨
      (∃ negative, fmt.encoding = .ieee ∧ x = nativeOverflow fmt negative ∧
        toDyadic? x = none ∧ (Factor.ofValue x : Factor fmt) = .infinity negative ∧
        signBit x = negative ∧ isFinite x = false ∧ isNaN x = false ∧ isSignaling x = false ∧
        isInfinite x = true ∧ isZero x = false) := by
  by_cases hnan : isNaN x = true
  · have hdecode := toDyadic?_eq_none_of_isNaN hnan
    refine .inr (.inl ⟨isSignaling x, hdecode, ?_, rfl, isFinite_eq_false_of_isNaN hnan, hnan,
      ?_, ?_⟩)
    · simp [Factor.ofValue, hdecode, hnan, cast_quietNaN_self hnan]
    · cases hinf : isInfinite x
      · rfl
      · rw [isNaN_eq_false_of_isInfinite_eq_true x hinf] at hnan
        exact absurd hnan (by decide)
    · cases hzero : isZero x
      · rfl
      · rw [toDyadic?_eq_zero_of_isZero_eq_true x hzero] at hdecode
        exact absurd hdecode (by simp)
  · have hnanFalse : isNaN x = false := by simpa using hnan
    have hsignaling := isSignaling_eq_false_of_isNaN_eq_false x hnanFalse
    by_cases hinf : isInfinite x = true
    · obtain ⟨hencoding, hx⟩ := eq_nativeOverflow_of_isInfinite hinf
      have hdecode := toDyadic?_eq_none_of_isInfinite_eq_true hinf
      have hfinite : isFinite x = false := by
        cases hfinite : isFinite x
        · rfl
        · rw [isInfinite_eq_false_of_isFinite_eq_true x hfinite] at hinf
          exact absurd hinf (by decide)
      refine .inr (.inr ⟨signBit x, hencoding, hx, hdecode, ?_, rfl, hfinite, hnanFalse,
        hsignaling, hinf, isZero_eq_false_of_isInfinite_eq_true x hinf⟩)
      simp [Factor.ofValue, hdecode, hnanFalse]
    · have hinfFalse : isInfinite x = false := by simpa using hinf
      have hfinite :=
        isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x hnanFalse hinfFalse
      obtain ⟨d, hd, hsign, -⟩ := KernelPath.toDyadic?_of_isFinite x hfinite
      exact .inl ⟨d, signBit x, hd, Factor.ofValue_of_toDyadic?_eq_some hd, hsign, rfl,
        isZero_eq_beq_zero_of_toDyadic?_some hd, hfinite, hnanFalse, hsignaling, hinfFalse⟩

/--
The NaN that two operands of the destination format select is the sum and the product of their
factors and the outcome of their division, with `invalid` when one of them was signaling.
-/
theorem Factor.of_chooseNaN2 {x y nan : Model fmt} (h : chooseNaN2 x y = some nan)
    (mode : IEEERoundingMode) :
    Factor.add (Factor.ofValue x : Factor fmt) (Factor.ofValue y) =
        .nan nan (isSignaling x || isSignaling y) ∧
      Factor.mul (Factor.ofValue x : Factor fmt) (Factor.ofValue y) =
        .nan nan (isSignaling x || isSignaling y) ∧
      formatOfDivision fmt x y mode = outcomeWithInvalid nan (isSignaling x || isSignaling y) ∧
      ((isInfinite x || isInfinite y) && (isZero x || isZero y)) = false := by
  unfold chooseNaN2 at h
  rcases Factor.ofValue_self x with ⟨dx, bx, _, hfx, _, _, hzx, _, hnx, hgx, hix⟩ |
      ⟨sx, _, hfx, hgx, _, hnx, hix, hzx⟩ |
      ⟨bx, _, rfl, _, hfx, _, _, hnx, hgx, hix, hzx⟩ <;>
    rcases Factor.ofValue_self y with ⟨dy, by', _, hfy, _, _, hzy, _, hny, hgy, hiy⟩ |
      ⟨sy, _, hfy, hgy, _, hny, hiy, hzy⟩ |
      ⟨by', _, rfl, _, hfy, _, _, hny, hgy, hiy, hzy⟩
  all_goals first
    | (cases sx <;> cases sy <;>
        simp_all [Factor.add, Factor.mul, Factor.deliver, formatOfDivision])
    | (cases sx <;> simp_all [Factor.add, Factor.mul, Factor.deliver, formatOfDivision])
    | (cases sy <;> simp_all [Factor.add, Factor.mul, Factor.deliver, formatOfDivision])
    | simp_all

/-- The product of two factors of the destination format, one of them infinite and none a NaN:
invalid when the other is a zero, and otherwise the infinity with the product of the signs. -/
theorem Factor.mul_of_isInfinite {x y : Model fmt} (hnx : isNaN x = false)
    (hny : isNaN y = false) (hinfinite : (isInfinite x || isInfinite y) = true) :
    fmt.encoding = .ieee ∧
      Factor.mul (Factor.ofValue x : Factor fmt) (Factor.ofValue y) =
        if (isZero x || isZero y) = true then .invalid
        else .infinity (Bool.xor (signBit x) (signBit y)) := by
  rcases Factor.ofValue_self x with ⟨dx, bx, -, hfx, hbx, hsx, hzx, -, -, -, hix⟩ |
      ⟨sx, -, -, -, -, hnan, -⟩ |
      ⟨bx, hencoding, rfl, hdx, hfx, hsx, hx, -, hgx, hix, hzx⟩
  · rcases Factor.ofValue_self y with ⟨dy, by', -, -, -, -, -, -, -, -, hiy⟩ |
        ⟨sy, -, -, -, -, hnan, -⟩ |
        ⟨by', hencoding, rfl, hdy, hfy, hsy, hy, -, hgy, hiy, hzy⟩
    · simp [hix, hiy] at hinfinite
    · rw [hny] at hnan
      exact absurd hnan (by decide)
    · refine ⟨hencoding, ?_⟩
      by_cases hzero : dx.significand = 0 <;> cases bx <;> cases by' <;>
        simp [Factor.mul, hfx, hfy, hzx, hzy, hsx, hsy, hbx, hzero]
  · rw [hnx] at hnan
    exact absurd hnan (by decide)
  · refine ⟨hencoding, ?_⟩
    rcases Factor.ofValue_self y with ⟨dy, by', -, hfy, hby, hsy, hzy, -, -, -, -⟩ |
        ⟨sy, -, -, -, -, hnan, -⟩ |
        ⟨by', -, rfl, hdy, hfy, hsy, hy, -, hgy, hiy, hzy⟩
    · by_cases hzero : dy.significand = 0 <;> cases bx <;> cases by' <;>
        simp [Factor.mul, hfx, hfy, hzx, hzy, hsx, hsy, hby, hzero]
    · rw [hny] at hnan
      exact absurd hnan (by decide)
    · cases bx <;> cases by' <;> simp [Factor.mul, hfx, hfy, hzx, hzy, hsx, hsy]

end Reduction.Internal

/-- The NaN that three operands select, from the NaN that the first two select. -/
theorem chooseNaN3_of_chooseNaN2 {x y nan : Model fmt} (h : chooseNaN2 x y = some nan)
    (z : Model fmt) :
    chooseNaN3 x y z =
      if (isSignaling x || isSignaling y) = true then some nan
      else if isSignaling z = true then some (quietNaN z) else some nan := by
  unfold chooseNaN2 at h
  unfold chooseNaN3
  cases hsx : isSignaling x <;> cases hsy : isSignaling y <;> cases hsz : isSignaling z <;>
    cases hnx : isNaN x <;> cases hny : isNaN y <;> simp_all

/-! ## The outcome for finite operands -/

/-- `formatOfAddition_eq_add` for finite operands. -/
private theorem formatOfAddition_eq_add_of_isFinite (x y : Model fmt) (mode : IEEERoundingMode)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    formatOfAddition fmt x y mode = add x y (mode := mode) (status := true) := by
  obtain ⟨dx, hdx, hsx, -⟩ := KernelPath.toDyadic?_of_isFinite x hx
  obtain ⟨dy, hdy, hsy, -⟩ := KernelPath.toDyadic?_of_isFinite y hy
  rw [formatOfAddition_of_toDyadic?_eq_some hdx hdy mode, ← Internal.Status.add_eq]
  unfold Internal.Status.add
  simp only [hdx, hdy]
  rw [Internal.Directed.add_eq, KernelPath.add_of_finite mode x y dx dy hdx hdy]
  unfold KernelPath.roundedSum zeroForExactSum Factor.deliver
  by_cases hzero : (addDyadic dx dy).significand = 0
  · simp [hzero, hsx, hsy, dyadicRoundingOutcome_zero]
  · simp [hzero]

/-- `formatOfMultiplication_eq_mul` for finite operands. -/
private theorem formatOfMultiplication_eq_mul_of_isFinite (x y : Model fmt)
    (mode : IEEERoundingMode) (hx : isFinite x = true) (hy : isFinite y = true) :
    formatOfMultiplication fmt x y mode = mul x y (mode := mode) (status := true) := by
  obtain ⟨dx, hdx, hsx, -⟩ := KernelPath.toDyadic?_of_isFinite x hx
  obtain ⟨dy, hdy, hsy, -⟩ := KernelPath.toDyadic?_of_isFinite y hy
  rw [formatOfMultiplication_of_toDyadic?_eq_some hdx hdy mode, ← Internal.Status.mul_eq]
  unfold Internal.Status.mul
  simp only [hdx, hdy]
  rw [Internal.Directed.mul_eq, KernelPath.mul_of_finite mode x y dx dy hdx hdy]
  unfold Factor.deliver
  by_cases hzero : dx.significand * dy.significand = 0
  · simp only [hzero, beq_self_eq_true, ↓reduceIte]
    rw [Internal.Directed.roundDyadic_zero, dyadicRoundingOutcome_zero fmt mode rfl, hsx, hsy]
  · simp [hzero]

/-- `formatOfFusedMultiplyAdd_eq_fma` for finite operands. -/
private theorem formatOfFusedMultiplyAdd_eq_fma_of_isFinite (x y z : Model fmt)
    (mode : IEEERoundingMode) (hx : isFinite x = true) (hy : isFinite y = true)
    (hz : isFinite z = true) :
    formatOfFusedMultiplyAdd fmt x y z mode = fma x y z (mode := mode) (status := true) := by
  obtain ⟨dx, hdx, hsx, -⟩ := KernelPath.toDyadic?_of_isFinite x hx
  obtain ⟨dy, hdy, hsy, -⟩ := KernelPath.toDyadic?_of_isFinite y hy
  obtain ⟨dz, hdz, hsz, -⟩ := KernelPath.toDyadic?_of_isFinite z hz
  rw [formatOfFusedMultiplyAdd_of_toDyadic?_eq_some hdx hdy hdz mode, ← Internal.Status.fma_eq]
  unfold Internal.Status.fma
  simp only [hdx, hdy, hdz]
  rw [Internal.Directed.fma_eq, KernelPath.fma_of_finite mode x y z dx dy dz hdx hdy hdz]
  unfold KernelPath.roundedSum zeroForExactSum Factor.deliver
  simp only [hsx, hsy, hsz]
  by_cases hzero : (addDyadic ⟨Bool.xor (signBit x) (signBit y),
      dx.significand * dy.significand, dx.exponent + dy.exponent⟩ dz).significand = 0
  · simp [hzero, dyadicRoundingOutcome_zero]
  · simp [hzero]

/-- `formatOfDivision_eq_div` for finite operands. -/
private theorem formatOfDivision_eq_div_of_isFinite (x y : Model fmt) (mode : IEEERoundingMode)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    formatOfDivision fmt x y mode = div x y (mode := mode) (status := true) := by
  obtain ⟨dx, hdx, hsx, -⟩ := KernelPath.toDyadic?_of_isFinite x hx
  obtain ⟨dy, hdy, hsy, -⟩ := KernelPath.toDyadic?_of_isFinite y hy
  rw [← Internal.Status.div_eq]
  simp [formatOfDivision, Internal.Status.div, Factor.ofValue_of_toDyadic?_eq_some hdx,
    Factor.ofValue_of_toDyadic?_eq_some hdy, hdx, hdy, hsx, hsy]

/-! ## The homogeneous operations at operands that are not finite -/

/-- Two operands that are not both finite do not both have a dyadic value. -/
private theorem not_decode_of_not_finite {x y : Model fmt}
    (h : isFinite x = false ∨ isFinite y = false) {dx dy : Numerics.Dyadic}
    (hdx : toDyadic? x = some dx) (hdy : toDyadic? y = some dy) : False := by
  rcases h with h | h
  · rw [isFinite_eq_true_of_toDyadic?_some hdx] at h
    exact absurd h (by decide)
  · rw [isFinite_eq_true_of_toDyadic?_some hdy] at h
    exact absurd h (by decide)

/-- One of two operands is not finite when they are not both finite. -/
private theorem not_finite_of_not_and {x y : Model fmt}
    (h : ¬(isFinite x = true ∧ isFinite y = true)) :
    isFinite x = false ∨ isFinite y = false := by
  cases hx : isFinite x
  · exact .inl rfl
  · cases hy : isFinite y
    · exact .inr rfl
    · exact absurd ⟨hx, hy⟩ h

/-- `Model.add` with its flags when an operand is not finite. -/
private theorem add_status_of_not_finite (x y : Model fmt) (mode : IEEERoundingMode)
    (h : isFinite x = false ∨ isFinite y = false) :
    add x y (mode := mode) (status := true) =
      outcomeWithInvalid
        ((chooseNaN2 x y).getD
          (if isInfinite x then
            if isInfinite y then
              if signBit x == signBit y then x else invalidResult fmt
            else x
          else if isInfinite y then y
          else invalidResult fmt))
        (isSignaling x || isSignaling y ||
          (!(isNaN x || isNaN y) && (isInfinite x && isInfinite y && signBit x != signBit y))) := by
  have hspec : Spec.add x y =
      (chooseNaN2 x y).getD
        (if isInfinite x then
          if isInfinite y then
            if signBit x == signBit y then x else invalidResult fmt
          else x
        else if isInfinite y then y
        else invalidResult fmt) := by
    unfold Spec.add
    cases hdx : toDyadic? x <;> cases hdy : toDyadic? y
    case some.some dx dy => exact (not_decode_of_not_finite h hdx hdy).elim
    all_goals cases chooseNaN2 x y <;> rfl
  rw [← Internal.Status.add_eq, ← hspec, ← KernelPath.add_of_nonFinite mode x y h,
    ← Internal.Directed.add_eq]
  unfold Internal.Status.add
  cases hdx : toDyadic? x <;> cases hdy : toDyadic? y
  case some.some dx dy => exact (not_decode_of_not_finite h hdx hdy).elim
  all_goals rfl

/-- `Model.mul` with its flags when an operand is not finite. -/
private theorem mul_status_of_not_finite (x y : Model fmt) (mode : IEEERoundingMode)
    (h : isFinite x = false ∨ isFinite y = false) :
    mul x y (mode := mode) (status := true) =
      outcomeWithInvalid
        ((chooseNaN2 x y).getD
          (if isInfinite x then
            if isZero y then invalidResult fmt
            else nativeOverflow fmt (signBit x != signBit y)
          else if isInfinite y then
            if isZero x then invalidResult fmt
            else nativeOverflow fmt (signBit x != signBit y)
          else invalidResult fmt))
        (isSignaling x || isSignaling y ||
          (!(isNaN x || isNaN y) &&
            ((isInfinite x && isZero y) || (isInfinite y && isZero x)))) := by
  have hspec : Spec.mul x y =
      (chooseNaN2 x y).getD
        (if isInfinite x then
          if isZero y then invalidResult fmt
          else nativeOverflow fmt (signBit x != signBit y)
        else if isInfinite y then
          if isZero x then invalidResult fmt
          else nativeOverflow fmt (signBit x != signBit y)
        else invalidResult fmt) := by
    unfold Spec.mul
    cases hdx : toDyadic? x <;> cases hdy : toDyadic? y
    case some.some dx dy => exact (not_decode_of_not_finite h hdx hdy).elim
    all_goals cases chooseNaN2 x y <;> rfl
  rw [← Internal.Status.mul_eq, ← hspec, ← KernelPath.mul_of_nonFinite mode x y h,
    ← Internal.Directed.mul_eq]
  unfold Internal.Status.mul
  cases hdx : toDyadic? x <;> cases hdy : toDyadic? y
  case some.some dx dy => exact (not_decode_of_not_finite h hdx hdy).elim
  all_goals rfl

/-- `Model.div` with its flags when an operand is not finite. -/
private theorem div_status_of_not_finite (x y : Model fmt) (mode : IEEERoundingMode)
    (h : isFinite x = false ∨ isFinite y = false) :
    div x y (mode := mode) (status := true) =
      outcomeWithInvalid (Spec.divSpecial x y)
        (isSignaling x || isSignaling y ||
          (!(isNaN x || isNaN y) && (isInfinite x && isInfinite y))) := by
  have hspec : Spec.div x y = Spec.divSpecial x y := by
    unfold Spec.div
    cases hdx : toDyadic? x <;> cases hdy : toDyadic? y
    case some.some dx dy => exact (not_decode_of_not_finite h hdx hdy).elim
    all_goals rfl
  rw [← Internal.Status.div_eq, ← hspec, ← KernelPath.div_of_nonFinite mode x y h,
    ← Internal.Directed.div_eq]
  unfold Internal.Status.div
  cases hdx : toDyadic? x <;> cases hdy : toDyadic? y
  case some.some dx dy => exact (not_decode_of_not_finite h hdx hdy).elim
  all_goals rfl

/-- `Model.fma` with its flags when an operand is not finite. -/
private theorem fma_status_of_not_finite (x y z : Model fmt) (mode : IEEERoundingMode)
    (h : isFinite x = false ∨ isFinite y = false ∨ isFinite z = false) :
    fma x y z (mode := mode) (status := true) =
      outcomeWithInvalid (Spec.fma x y z)
        (isSignaling x || isSignaling y || isSignaling z ||
          ((isInfinite x || isInfinite y) && (isZero x || isZero y)) ||
          (!(isNaN x || isNaN y || isNaN z) &&
            ((isInfinite x || isInfinite y) && !(isZero x || isZero y) && isInfinite z &&
              signBit z != Bool.xor (signBit x) (signBit y)))) := by
  rw [← Internal.Status.fma_eq, ← KernelPath.fma_of_nonFinite mode x y z h,
    ← Internal.Directed.fma_eq]
  unfold Internal.Status.fma
  cases hdx : toDyadic? x <;> cases hdy : toDyadic? y <;> cases hdz : toDyadic? z
  case some.some.some dx dy dz =>
    rcases h with h | h | h
    · rw [isFinite_eq_true_of_toDyadic?_some hdx] at h
      exact absurd h (by decide)
    · rw [isFinite_eq_true_of_toDyadic?_some hdy] at h
      exact absurd h (by decide)
    · rw [isFinite_eq_true_of_toDyadic?_some hdz] at h
      exact absurd h (by decide)
  all_goals rfl

/-! ## The outcome -/

/--
In one format, `formatOfAddition` is `Model.add` with its flags and its ternary value, in every
rounding direction and for every operand: finite, infinite or NaN.
-/
theorem formatOfAddition_eq_add (x y : Model fmt) (mode : IEEERoundingMode) :
    formatOfAddition fmt x y mode = add x y (mode := mode) (status := true) := by
  by_cases hfinite : isFinite x = true ∧ isFinite y = true
  · exact formatOfAddition_eq_add_of_isFinite x y mode hfinite.1 hfinite.2
  rw [add_status_of_not_finite x y mode (not_finite_of_not_and hfinite)]
  unfold formatOfAddition
  cases hchoose : chooseNaN2 x y with
  | some nan =>
      have hnan : (isNaN x || isNaN y) = true := by
        by_contra hnone
        rw [(chooseNaN2_eq_none_iff x y).mpr (by simpa using hnone)] at hchoose
        exact absurd hchoose (by simp)
      rw [(Factor.of_chooseNaN2 hchoose mode).1]
      simp [Factor.deliver, hnan]
  | none =>
      obtain ⟨hnx, hny⟩ := (chooseNaN2_eq_none_iff x y).mp hchoose
      rcases Factor.ofValue_self x with ⟨dx, bx, -, hfx, -, -, -, hx, -, hgx, hix⟩ |
          ⟨sx, -, -, -, -, hnan, -⟩ |
          ⟨bx, hencoding, rfl, hdx, hfx, hsx, hx, -, hgx, hix, hzx⟩
      · rcases Factor.ofValue_self y with ⟨dy, by', -, -, -, -, -, hy, -, -, -⟩ |
            ⟨sy, -, -, -, -, hnan, -⟩ |
            ⟨by', hencoding, rfl, -, hfy, -, -, -, hgy, hiy, -⟩
        · exact absurd ⟨hx, hy⟩ hfinite
        · rw [hny] at hnan
          exact absurd hnan (by decide)
        · simp [Factor.add, Factor.deliver, outcomeWithInvalid,
            exactInfinityTernary_nativeOverflow hencoding, hfx, hfy, hnx, hny, hgx, hgy, hix,
            hiy]
      · rw [hnx] at hnan
        exact absurd hnan (by decide)
      · rcases Factor.ofValue_self y with ⟨dy, by', -, hfy, -, -, -, -, -, hgy, hiy⟩ |
            ⟨sy, -, -, -, -, hnan, -⟩ |
            ⟨by', -, rfl, hdy, hfy, hsy, hy, -, hgy, hiy, hzy⟩
        · simp [Factor.add, Factor.deliver, outcomeWithInvalid,
            exactInfinityTernary_nativeOverflow hencoding, hfx, hfy, hnx, hny, hgx, hgy, hix,
            hiy]
        · rw [hny] at hnan
          exact absurd hnan (by decide)
        · cases bx <;> cases by' <;>
            simp [Factor.add, Factor.deliver, outcomeWithInvalid,
              exactInfinityTernary_nativeOverflow hencoding, hfx, hfy, hnx, hny, hgx, hgy, hix,
              hiy, hsx, hsy]

/--
In one format, `formatOfSubtraction` is `Model.sub` with its flags and its ternary value, in
every rounding direction and for every operand.
-/
theorem formatOfSubtraction_eq_sub (x y : Model fmt) (mode : IEEERoundingMode) :
    formatOfSubtraction fmt x y mode = sub x y (mode := mode) (status := true) :=
  formatOfAddition_eq_add x (neg y) mode

/--
In one format, `formatOfMultiplication` is `Model.mul` with its flags and its ternary value, in
every rounding direction and for every operand: finite, infinite or NaN.
-/
theorem formatOfMultiplication_eq_mul (x y : Model fmt) (mode : IEEERoundingMode) :
    formatOfMultiplication fmt x y mode = mul x y (mode := mode) (status := true) := by
  by_cases hfinite : isFinite x = true ∧ isFinite y = true
  · exact formatOfMultiplication_eq_mul_of_isFinite x y mode hfinite.1 hfinite.2
  rw [mul_status_of_not_finite x y mode (not_finite_of_not_and hfinite)]
  unfold formatOfMultiplication
  cases hchoose : chooseNaN2 x y with
  | some nan =>
      have hnan : (isNaN x || isNaN y) = true := by
        by_contra hnone
        rw [(chooseNaN2_eq_none_iff x y).mpr (by simpa using hnone)] at hchoose
        exact absurd hchoose (by simp)
      rw [(Factor.of_chooseNaN2 hchoose mode).2.1]
      simp [Factor.deliver, hnan]
  | none =>
      obtain ⟨hnx, hny⟩ := (chooseNaN2_eq_none_iff x y).mp hchoose
      rcases Factor.ofValue_self x with ⟨dx, bx, -, hfx, hbx, hsx, hzx, hx, -, hgx, hix⟩ |
          ⟨sx, -, -, -, -, hnan, -⟩ |
          ⟨bx, hencoding, rfl, hdx, hfx, hsx, hx, -, hgx, hix, hzx⟩
      · rcases Factor.ofValue_self y with ⟨dy, by', -, -, -, -, -, hy, -, -, -⟩ |
            ⟨sy, -, -, -, -, hnan, -⟩ |
            ⟨by', hencoding, rfl, hdy, hfy, hsy, hy, -, hgy, hiy, hzy⟩
        · exact absurd ⟨hx, hy⟩ hfinite
        · rw [hny] at hnan
          exact absurd hnan (by decide)
        · by_cases hzero : dx.significand = 0 <;> cases bx <;> cases by' <;>
            simp [Factor.mul, Factor.deliver, outcomeWithInvalid,
              exactInfinityTernary_nativeOverflow hencoding, hfx, hfy, hnx, hny, hgx, hgy, hix,
              hiy, hzx, hzy, hsx, hsy, hbx, hzero]
      · rw [hnx] at hnan
        exact absurd hnan (by decide)
      · rcases Factor.ofValue_self y with ⟨dy, by', -, hfy, hby, hsy, hzy, -, -, hgy, hiy⟩ |
            ⟨sy, -, -, -, -, hnan, -⟩ |
            ⟨by', -, rfl, hdy, hfy, hsy, hy, -, hgy, hiy, hzy⟩
        · by_cases hzero : dy.significand = 0 <;> cases bx <;> cases by' <;>
            simp [Factor.mul, Factor.deliver, outcomeWithInvalid,
              exactInfinityTernary_nativeOverflow hencoding, hfx, hfy, hnx, hny, hgx, hgy, hix,
              hiy, hzx, hzy, hsx, hsy, hby, hzero]
        · rw [hny] at hnan
          exact absurd hnan (by decide)
        · cases bx <;> cases by' <;>
            simp [Factor.mul, Factor.deliver, outcomeWithInvalid,
              exactInfinityTernary_nativeOverflow hencoding, hfx, hfy, hnx, hny, hgx, hgy, hix,
              hiy, hzx, hzy, hsx, hsy]

/--
In one format, `formatOfDivision` is `Model.div` with its flags and its ternary value, in every
rounding direction and for every operand: a zero divisor with `divideByZero` or `invalid`,
infinite operands and NaN operands included.
-/
theorem formatOfDivision_eq_div (x y : Model fmt) (mode : IEEERoundingMode) :
    formatOfDivision fmt x y mode = div x y (mode := mode) (status := true) := by
  by_cases hfinite : isFinite x = true ∧ isFinite y = true
  · exact formatOfDivision_eq_div_of_isFinite x y mode hfinite.1 hfinite.2
  rw [div_status_of_not_finite x y mode (not_finite_of_not_and hfinite)]
  unfold Spec.divSpecial
  cases hchoose : chooseNaN2 x y with
  | some nan =>
      have hnan : (isNaN x || isNaN y) = true := by
        by_contra hnone
        rw [(chooseNaN2_eq_none_iff x y).mpr (by simpa using hnone)] at hchoose
        exact absurd hchoose (by simp)
      rw [(Factor.of_chooseNaN2 hchoose mode).2.2.1]
      simp [hnan]
  | none =>
      obtain ⟨hnx, hny⟩ := (chooseNaN2_eq_none_iff x y).mp hchoose
      unfold formatOfDivision
      rcases Factor.ofValue_self x with ⟨dx, bx, -, hfx, -, hsx, -, hx, -, hgx, hix⟩ |
          ⟨sx, -, -, -, -, hnan, -⟩ |
          ⟨bx, hencoding, rfl, -, hfx, hsx, -, -, hgx, hix, -⟩
      · rcases Factor.ofValue_self y with ⟨dy, by', -, -, -, -, -, hy, -, -, -⟩ |
            ⟨sy, -, -, -, -, hnan, -⟩ |
            ⟨by', -, rfl, -, hfy, hsy, -, -, hgy, hiy, -⟩
        · exact absurd ⟨hx, hy⟩ hfinite
        · rw [hny] at hnan
          exact absurd hnan (by decide)
        · simp [outcomeWithInvalid, Numerics.IEEEStatus.clear, hfx, hfy, hnx, hny, hgx, hgy, hix,
            hiy, hsx, hsy]
      · rw [hnx] at hnan
        exact absurd hnan (by decide)
      · rcases Factor.ofValue_self y with ⟨dy, by', -, hfy, -, hsy, -, -, -, hgy, hiy⟩ |
            ⟨sy, -, -, -, -, hnan, -⟩ |
            ⟨by', -, rfl, -, hfy, -, -, -, hgy, hiy, -⟩
        · simp [Factor.deliver, outcomeWithInvalid,
            exactInfinityTernary_nativeOverflow hencoding, hfx, hfy, hnx, hny, hgx, hgy, hix,
            hiy, hsx, hsy]
        · rw [hny] at hnan
          exact absurd hnan (by decide)
        · simp [Factor.deliver, outcomeWithInvalid, hfx, hfy, hnx, hny, hgx, hgy, hix, hiy]

/--
In one format, `formatOfFusedMultiplyAdd` is `Model.fma` with its flags and its ternary value,
in every rounding direction and for every operand: finite, infinite or NaN.
-/
theorem formatOfFusedMultiplyAdd_eq_fma (x y z : Model fmt) (mode : IEEERoundingMode) :
    formatOfFusedMultiplyAdd fmt x y z mode = fma x y z (mode := mode) (status := true) := by
  by_cases hfinite : isFinite x = true ∧ isFinite y = true ∧ isFinite z = true
  · exact formatOfFusedMultiplyAdd_eq_fma_of_isFinite x y z mode hfinite.1 hfinite.2.1
      hfinite.2.2
  have hsome : isFinite x = false ∨ isFinite y = false ∨ isFinite z = false := by
    cases hx : isFinite x
    · exact .inl rfl
    · cases hy : isFinite y
      · exact .inr (.inl rfl)
      · cases hz : isFinite z
        · exact .inr (.inr rfl)
        · exact absurd ⟨hx, hy, hz⟩ hfinite
  rw [fma_status_of_not_finite x y z mode hsome]
  unfold formatOfFusedMultiplyAdd Spec.fma
  cases hchoose : chooseNaN2 x y with
  | some nan =>
      have hnan : (isNaN x || isNaN y) = true := by
        by_contra hnone
        rw [(chooseNaN2_eq_none_iff x y).mpr (by simpa using hnone)] at hchoose
        exact absurd hchoose (by simp)
      obtain ⟨-, hproduct, -, hinvalid⟩ := Factor.of_chooseNaN2 hchoose mode
      rw [hproduct, chooseNaN3_of_chooseNaN2 hchoose z, hinvalid]
      rcases Factor.ofValue_self z with ⟨dz, bz, -, hfz, -, -, -, -, -, hgz, -⟩ |
          ⟨sz, -, hfz, hgz, -, -, -, -⟩ |
          ⟨bz, -, rfl, -, hfz, -, -, -, hgz, -, -⟩
      · cases (isSignaling x || isSignaling y) <;>
          simp [Factor.add, Factor.deliver, hfz, hgz, hnan]
      · cases (isSignaling x || isSignaling y) <;> cases sz <;>
          simp [Factor.add, Factor.deliver, hfz, hgz, hnan]
      · cases (isSignaling x || isSignaling y) <;>
          simp [Factor.add, Factor.deliver, hfz, hgz, hnan]
  | none =>
      obtain ⟨hnx, hny⟩ := (chooseNaN2_eq_none_iff x y).mp hchoose
      have hgx := isSignaling_eq_false_of_isNaN_eq_false x hnx
      have hgy := isSignaling_eq_false_of_isNaN_eq_false y hny
      unfold chooseNaN3
      cases hinfinite : (isInfinite x || isInfinite y)
      · have hix : isInfinite x = false := by
          cases h : isInfinite x <;> simp [h] at hinfinite ⊢
        have hiy : isInfinite y = false := by
          cases h : isInfinite y <;> simp [h] at hinfinite ⊢
        have hx := isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x hnx hix
        have hy := isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false y hny hiy
        obtain ⟨dx, hdx, -⟩ := KernelPath.toDyadic?_of_isFinite x hx
        obtain ⟨dy, hdy, -⟩ := KernelPath.toDyadic?_of_isFinite y hy
        rw [Factor.ofValue_of_toDyadic?_eq_some hdx, Factor.ofValue_of_toDyadic?_eq_some hdy]
        rcases Factor.ofValue_self z with ⟨dz, bz, -, -, -, -, -, hz, -, -, -⟩ |
            ⟨sz, -, hfz, hgz, -, hnz, hiz, -⟩ |
            ⟨bz, hencoding, rfl, -, hfz, -, -, hnz, hgz, hiz, -⟩
        · exact absurd ⟨hx, hy, hz⟩ hfinite
        · cases sz <;>
            simp [Factor.mul, Factor.add, Factor.deliver, hfz, hgz, hnz, hiz, hnx, hny, hgx,
              hgy]
        · simp [Factor.mul, Factor.add, Factor.deliver, outcomeWithInvalid,
            exactInfinityTernary_nativeOverflow hencoding, hfz, hgz, hnz, hiz, hnx, hny, hgx,
            hgy]
      · obtain ⟨hencoding, hproduct⟩ := Factor.mul_of_isInfinite hnx hny hinfinite
        rw [hproduct]
        cases hzero : (isZero x || isZero y)
        · generalize Bool.xor (signBit x) (signBit y) = negative
          rcases Factor.ofValue_self z with
              ⟨dz, bz, -, hfz, -, -, -, -, hnz, hgz, hiz⟩ |
              ⟨sz, -, hfz, hgz, -, hnz, hiz, -⟩ |
              ⟨bz, -, rfl, hdz, hfz, hsz, hz, hnz, hgz, hiz, hzz⟩
          · simp [Factor.add, Factor.deliver, outcomeWithInvalid,
              exactInfinityTernary_nativeOverflow hencoding, hfz, hgz, hnz, hiz, hnx, hny, hgx,
              hgy]
          · cases sz <;>
              simp [Factor.add, Factor.deliver, hfz, hgz, hnz, hiz, hnx, hny, hgx, hgy]
          · cases negative <;> cases bz <;>
              simp [Factor.add, Factor.deliver, outcomeWithInvalid,
                exactInfinityTernary_nativeOverflow hencoding, hfz, hgz, hnz, hiz, hnx, hny,
                hgx, hgy, hsz]
        · rcases Factor.ofValue_self z with
              ⟨dz, bz, -, hfz, -, -, -, -, hnz, hgz, hiz⟩ |
              ⟨sz, -, hfz, hgz, -, hnz, hiz, -⟩ |
              ⟨bz, -, rfl, -, hfz, -, -, hnz, hgz, hiz, -⟩
          · simp [Factor.add, Factor.deliver, hfz, hgz, hnz, hiz, hnx, hny, hgx, hgy]
          · cases sz <;> simp [hfz, hgz, hnz, hiz, hnx, hny, hgx, hgy]
          · simp [Factor.add, Factor.deliver, hfz, hgz, hnz, hiz, hnx, hny, hgx, hgy]

/-! ## The value -/

/--
In one format, `formatOfAddition` delivers `Model.add`, in every rounding direction and for
every operand.
-/
theorem formatOfAddition_value_eq_add (x y : Model fmt) (mode : IEEERoundingMode) :
    (formatOfAddition fmt x y mode).value = add x y (mode := mode) := by
  rw [formatOfAddition_eq_add, value_add]

/--
In one format, `formatOfSubtraction` delivers `Model.sub`, in every rounding direction and for
every operand.
-/
theorem formatOfSubtraction_value_eq_sub (x y : Model fmt) (mode : IEEERoundingMode) :
    (formatOfSubtraction fmt x y mode).value = sub x y (mode := mode) := by
  rw [formatOfSubtraction_eq_sub, value_sub]

/--
In one format, `formatOfMultiplication` delivers `Model.mul`, in every rounding direction and
for every operand, a zero product with the product of the signs.
-/
theorem formatOfMultiplication_value_eq_mul (x y : Model fmt) (mode : IEEERoundingMode) :
    (formatOfMultiplication fmt x y mode).value = mul x y (mode := mode) := by
  rw [formatOfMultiplication_eq_mul, value_mul]

/--
In one format, `formatOfFusedMultiplyAdd` delivers `Model.fma`, in every rounding direction and
for every operand.
-/
theorem formatOfFusedMultiplyAdd_value_eq_fma (x y z : Model fmt) (mode : IEEERoundingMode) :
    (formatOfFusedMultiplyAdd fmt x y z mode).value = fma x y z (mode := mode) := by
  rw [formatOfFusedMultiplyAdd_eq_fma, value_fma]

/--
In one format, `formatOfDivision` delivers `Model.div`, in every rounding direction and for
every operand: the rounded quotient, the signed zero of a zero dividend, the infinity of a
division by zero and the default NaN of zero divided by zero.
-/
theorem formatOfDivision_value_eq_div (x y : Model fmt) (mode : IEEERoundingMode) :
    (formatOfDivision fmt x y mode).value = div x y (mode := mode) := by
  rw [formatOfDivision_eq_div, value_div]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
