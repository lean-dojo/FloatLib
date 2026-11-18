/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Special
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Sum

/-!
# The reference operations in every rounding direction, by operand class

The reference `Model.add x y (mode := mode)` and its siblings are the dispatched nearest-even
kernels for `mode = .nearest` and the directed kernels `Model.Internal.Directed.*` otherwise. The
kernel-path proofs need them in one shape for all six directions:

* for finite operands, one rounding of the exact result (`add_of_finite`, `mul_of_finite`,
  `fma_of_finite`): `roundedSum` for sums, `Model.Internal.Directed.roundDyadic` for products;
  `sub_eq_add_neg` reduces subtraction to addition;
* for an operand that is not finite, the nearest-even specification `Model.Spec.*`, whose NaN
  and infinity rules do not depend on the direction (`add_of_nonFinite`, `mul_of_nonFinite`,
  `fma_of_nonFinite`);
* for the square root, the operand classes (`sqrt_cases`) and the root `positiveRoot` of a
  positive finite value (`sqrt_of_positive`).

Every statement holds for every format descriptor.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

variable {fmt : FloatFormat}

/-- With a non-finite operand and no NaN, one of two operands is an infinity. -/
private theorem isInfinite_of_nonFinite {x : Model fmt} (hnan : Model.isNaN x = false)
    (hfinite : Model.isFinite x = false) : Model.isInfinite x = true := by
  cases hinf : Model.isInfinite x
  · rw [Model.isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x hnan hinf] at hfinite
    exact absurd hfinite (by decide)
  · rfl

/-- A NaN selection either selects a NaN or selects none. -/
private theorem selection_cases (selected : Option (Model fmt)) :
    (∃ nan, selected = some nan) ∨ selected = none := by
  cases selected
  · exact Or.inr rfl
  · exact Or.inl ⟨_, rfl⟩

/-! ## Addition and subtraction -/

/-- The sum of two finite values in any direction: one rounding of the exact sum. -/
theorem add_of_finite (mode : Model.IEEERoundingMode) (x y : Model fmt)
    (dx dy : Numerics.Dyadic) (hx : Model.toDyadic? x = some dx)
    (hy : Model.toDyadic? y = some dy) :
    Model.add x y (mode := mode) = roundedSum fmt mode dx dy := by
  rw [← Model.Internal.Directed.add_eq]
  cases mode
  case nearest =>
    rw [roundedSum_nearest]
    refine (Model.Proof.add_eq_spec x y).trans ?_
    simp only [Model.Spec.add, hx, hy]
  all_goals
    have hsel : Model.chooseNaN2 x y = none :=
      (Model.chooseNaN2_eq_none_iff x y).2
        ⟨Model.isNaN_eq_false_of_toDyadic?_some hx, Model.isNaN_eq_false_of_toDyadic?_some hy⟩
    have hinfx := Model.isInfinite_eq_false_of_toDyadic?_some hx
    have hinfy := Model.isInfinite_eq_false_of_toDyadic?_some hy
    simp only [Model.Internal.Directed.add]
    rw [Model.withNaNSelection_of_none _ _ hsel]
    simp only [hinfx, hinfy, Bool.false_eq_true, dite_false,
      Model.finiteDyadic_eq_of_toDyadic _ hx, Model.finiteDyadic_eq_of_toDyadic _ hy]
    rfl

/--
The sum with an operand that is not finite does not depend on the direction: it is the
nearest-even specification.
-/
theorem add_of_nonFinite (mode : Model.IEEERoundingMode) (x y : Model fmt)
    (h : Model.isFinite x = false ∨ Model.isFinite y = false) :
    Model.add x y (mode := mode) = Model.Spec.add x y := by
  rw [← Model.Internal.Directed.add_eq]
  cases mode
  case nearest => exact Model.Proof.add_eq_spec x y
  all_goals
    have hspec : Model.Spec.add x y =
        (match Model.chooseNaN2 x y with
          | some nan => nan
          | none =>
              if Model.isInfinite x then
                if Model.isInfinite y then
                  if Model.signBit x == Model.signBit y then x else Model.invalidResult fmt
                else x
              else if Model.isInfinite y then y
              else Model.invalidResult fmt) := by
      unfold Model.Spec.add
      rcases h with h | h
      · rw [toDyadic?_eq_none_of_isFinite_eq_false x h]
        cases Model.toDyadic? y <;> rfl
      · rw [toDyadic?_eq_none_of_isFinite_eq_false y h]
        cases Model.toDyadic? x <;> rfl
    rw [hspec]
    simp only [Model.Internal.Directed.add]
    obtain ⟨nan, hsel⟩ | hsel := selection_cases (Model.chooseNaN2 x y)
    · rw [Model.withNaNSelection_of_some _ _ nan hsel, hsel]
    · rw [Model.withNaNSelection_of_none _ _ hsel]
      simp only [hsel]
      have hnan := (Model.chooseNaN2_eq_none_iff x y).1 hsel
      by_cases hxInf : Model.isInfinite x = true
      · simp only [hxInf, dite_true, ite_true]
      · by_cases hyInf : Model.isInfinite y = true
        · simp only [hxInf, hyInf, dite_true, dite_false, ite_true, ite_false,
            Bool.false_eq_true]
        · exfalso
          rcases h with h | h
          · exact hxInf (isInfinite_of_nonFinite hnan.1 h)
          · exact hyInf (isInfinite_of_nonFinite hnan.2 h)

/-- Subtraction in any direction is addition of the negated second operand. -/
theorem sub_eq_add_neg (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    Model.sub x y (mode := mode) = Model.add x (Model.neg y) (mode := mode) := by
  rw [← Model.Internal.Directed.sub_eq, ← Model.Internal.Directed.add_eq]
  rfl

/-! ## Division -/

/--
The quotient with an operand that is not finite does not depend on the direction: it is the
nearest-even specification.
-/
theorem div_of_nonFinite (mode : Model.IEEERoundingMode) (x y : Model fmt)
    (h : Model.isFinite x = false ∨ Model.isFinite y = false) :
    Model.div x y (mode := mode) = Model.Spec.div x y := by
  rw [← Model.Internal.Directed.div_eq]
  cases mode
  case nearest => exact Model.Proof.div_eq_spec x y
  all_goals
    have hspec : Model.Spec.div x y = Model.Spec.divSpecial x y := by
      unfold Model.Spec.div
      rcases h with h | h
      · rw [toDyadic?_eq_none_of_isFinite_eq_false x h]
      · rw [toDyadic?_eq_none_of_isFinite_eq_false y h]
        cases Model.toDyadic? x <;> rfl
    rw [hspec]
    unfold Model.Spec.divSpecial
    simp only [Model.Internal.Directed.div]
    obtain ⟨nan, hsel⟩ | hsel := selection_cases (Model.chooseNaN2 x y)
    · rw [Model.withNaNSelection_of_some _ _ nan hsel, hsel]
    · rw [Model.withNaNSelection_of_none _ _ hsel]
      simp only [hsel]
      have hnan := (Model.chooseNaN2_eq_none_iff x y).1 hsel
      by_cases hxInf : Model.isInfinite x = true
      · simp only [hxInf, dite_true, ite_true]
      · by_cases hyInf : Model.isInfinite y = true
        · simp only [hxInf, hyInf, dite_true, dite_false, ite_true, ite_false,
            Bool.false_eq_true]
        · exfalso
          rcases h with h | h
          · exact hxInf (isInfinite_of_nonFinite hnan.1 h)
          · exact hyInf (isInfinite_of_nonFinite hnan.2 h)

/--
The quotient of two finite values in any direction: the invalid result or the overflow result for
a zero divisor, the signed zero for a zero dividend, and otherwise one rounding of the exact
quotient.
-/
theorem div_of_finite (mode : Model.IEEERoundingMode) (x y : Model fmt)
    (dx dy : Numerics.Dyadic) (hx : Model.toDyadic? x = some dx)
    (hy : Model.toDyadic? y = some dy) :
    Model.div x y (mode := mode) =
      if dy.significand = 0 then
        if dx.significand = 0 then Model.invalidResult fmt
        else Model.nativeOverflow fmt (Bool.xor dx.negative dy.negative)
      else if dx.significand = 0 then Model.zero fmt (Bool.xor dx.negative dy.negative)
      else Model.Internal.Directed.roundRatScaled fmt mode (Bool.xor dx.negative dy.negative)
        dx.significand dy.significand (dx.exponent - dy.exponent) := by
  rw [← Model.Internal.Directed.div_eq]
  cases mode
  case nearest =>
    refine (Model.Proof.div_eq_spec x y).trans ?_
    simp only [Model.Spec.div, hx, hy, beq_iff_eq]
    rfl
  all_goals
    have hsel : Model.chooseNaN2 x y = none :=
      (Model.chooseNaN2_eq_none_iff x y).2
        ⟨Model.isNaN_eq_false_of_toDyadic?_some hx, Model.isNaN_eq_false_of_toDyadic?_some hy⟩
    have hinfx := Model.isInfinite_eq_false_of_toDyadic?_some hx
    have hinfy := Model.isInfinite_eq_false_of_toDyadic?_some hy
    have hzerox := Model.isZero_eq_beq_zero_of_toDyadic?_some hx
    have hzeroy := Model.isZero_eq_beq_zero_of_toDyadic?_some hy
    have hfinx : Model.isFinite x = true := by
      rw [← Model.toDyadic?_isSome_eq_isFinite, hx]
      rfl
    have hfiny : Model.isFinite y = true := by
      rw [← Model.toDyadic?_isSome_eq_isFinite, hy]
      rfl
    obtain ⟨dx', hdx', hnx, -⟩ := toDyadic?_of_isFinite x hfinx
    obtain rfl : dx' = dx := Option.some.inj (hdx'.symm.trans hx)
    obtain ⟨dy', hdy', hny, -⟩ := toDyadic?_of_isFinite y hfiny
    obtain rfl : dy' = dy := Option.some.inj (hdy'.symm.trans hy)
    have hsign : (Model.signBit x != Model.signBit y) = Bool.xor dx'.negative dy'.negative := by
      rw [hnx, hny]
    simp only [Model.Internal.Directed.div, Model.withNaNSelection_of_none _ _ hsel, hinfx,
      hinfy, hzerox, hzeroy, hsign, Bool.false_eq_true, dite_false, beq_iff_eq,
      Model.finiteDyadic_eq_of_toDyadic _ hx, Model.finiteDyadic_eq_of_toDyadic _ hy]

/-! ## Square root -/

/--
The reference root of a positive finite dyadic in the direction `mode`: the nearest-even root in
both nearest directions (an exact square root is never a tie), and otherwise the directed
rounding of an endpoint of the enclosure `Model.sqrtDyadicBracket`, the upper one when the
result rounds up.
-/
def positiveRoot (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (d : Numerics.Dyadic) :
    Model fmt :=
  match mode with
  | .nearest | .nearestAway => Model.FiniteSqrt.sqrtPositiveDyadic fmt d.significand d.exponent
  | .up | .away => Model.roundDyadicUp fmt (Model.sqrtDyadicBracket fmt d).upper
  | .towardZero | .down => Model.roundDyadicDown fmt (Model.sqrtDyadicBracket fmt d).lower

/--
The square root in any direction, by operand class: a NaN is selected, the positive infinity and
the zeros are returned, the negative infinity and a negative value are invalid, and a positive
finite value keeps its root.
-/
theorem sqrt_cases (mode : Model.IEEERoundingMode) (x : Model fmt) :
    Model.sqrt x (mode := mode) =
      (Model.chooseNaN1 x).getD
        (if Model.isInfinite x then
          if Model.signBit x then Model.invalidResult fmt else Model.nativeOverflow fmt false
        else if Model.isZero x then x
        else if Model.signBit x then Model.invalidResult fmt
        else Model.sqrt x (mode := mode)) := by
  have hspec : Model.Spec.sqrt x =
      (Model.chooseNaN1 x).getD
        (if Model.isInfinite x then
          if Model.signBit x then Model.invalidResult fmt else Model.nativeOverflow fmt false
        else if Model.isZero x then x
        else if Model.signBit x then Model.invalidResult fmt
        else Model.Spec.sqrt x) := by
    cases hc : Model.chooseNaN1 x
    · cases hi : Model.isInfinite x <;> cases hz : Model.isZero x <;> cases hs : Model.signBit x <;>
        simp [Model.Spec.sqrt, hc, hi, hz, hs]
    · simp [Model.Spec.sqrt, hc]
  have hnearest : Model.sqrt x (mode := .nearest) = Model.Spec.sqrt x :=
    Model.Proof.sqrt_eq_spec x
  have hnearestAway : Model.sqrt x (mode := .nearestAway) = Model.Spec.sqrt x :=
    Model.Proof.sqrt_eq_spec x
  cases mode
  case nearest => rw [hnearest]; exact hspec
  case nearestAway => rw [hnearestAway]; exact hspec
  all_goals
    rw [← Model.Internal.Directed.sqrt_eq]
    obtain ⟨nan, hsel⟩ | hsel := selection_cases (Model.chooseNaN1 x)
    · rw [hsel, Option.getD_some]
      simp only [Model.Internal.Directed.sqrt]
      exact Model.withNaNSelection_of_some _ _ nan hsel
    · rw [hsel, Option.getD_none]
      by_cases hinf : Model.isInfinite x = true
      · rw [ite_eq_left hinf]
        simp only [Model.Internal.Directed.sqrt]
        rw [Model.withNaNSelection_of_none _ _ hsel]
        simp only [hinf, dite_true]
      · rw [ite_eq_right hinf]
        by_cases hzero : Model.isZero x = true
        · rw [ite_eq_left hzero]
          simp only [Model.Internal.Directed.sqrt]
          rw [Model.withNaNSelection_of_none _ _ hsel]
          simp only [hinf, hzero, dite_false, ite_true, Bool.false_eq_true]
        · rw [ite_eq_right hzero]
          by_cases hsign : Model.signBit x = true
          · rw [ite_eq_left hsign]
            simp only [Model.Internal.Directed.sqrt]
            rw [Model.withNaNSelection_of_none _ _ hsel]
            simp only [hinf, hzero, hsign, dite_false, ite_true, ite_false, Bool.false_eq_true]
          · rw [ite_eq_right hsign]

/--
The square root of a positive finite value in any direction: the root `positiveRoot` of its
exact value.
-/
theorem sqrt_of_positive (mode : Model.IEEERoundingMode) (x : Model fmt) (d : Numerics.Dyadic)
    (hd : Model.toDyadic? x = some d) (hzero : Model.isZero x = false)
    (hsign : Model.signBit x = false) :
    Model.sqrt x (mode := mode) = positiveRoot fmt mode d := by
  have hnan := Model.isNaN_eq_false_of_toDyadic?_some hd
  have hinf := Model.isInfinite_eq_false_of_toDyadic?_some hd
  have hspec : Model.Spec.sqrt x =
      Model.FiniteSqrt.sqrtPositiveDyadic fmt d.significand d.exponent := by
    simp [Model.Spec.sqrt, Model.chooseNaN1, hnan, hinf, hzero, hsign, hd]
  have hnearest : Model.sqrt x (mode := .nearest) = Model.Spec.sqrt x :=
    Model.Proof.sqrt_eq_spec x
  have hnearestAway : Model.sqrt x (mode := .nearestAway) = Model.Spec.sqrt x :=
    Model.Proof.sqrt_eq_spec x
  cases mode
  case nearest => rw [hnearest, hspec]; rfl
  case nearestAway => rw [hnearestAway, hspec]; rfl
  all_goals
    have hsel : Model.chooseNaN1 x = none := (Model.chooseNaN1_eq_none_iff x).2 hnan
    rw [← Model.Internal.Directed.sqrt_eq]
    simp only [Model.Internal.Directed.sqrt]
    rw [Model.withNaNSelection_of_none _ _ hsel]
    simp only [hinf, hzero, hsign, Bool.false_eq_true, dite_false, ite_false,
      Model.finiteDyadic_eq_of_toDyadic _ hd]
    rfl

/-! ## Multiplication -/

/-- The product of two finite values in any direction: one rounding of the exact product. -/
theorem mul_of_finite (mode : Model.IEEERoundingMode) (x y : Model fmt)
    (dx dy : Numerics.Dyadic) (hx : Model.toDyadic? x = some dx)
    (hy : Model.toDyadic? y = some dy) :
    Model.mul x y (mode := mode) =
      Model.Internal.Directed.roundDyadic fmt mode
        ⟨Bool.xor dx.negative dy.negative, dx.significand * dy.significand,
          dx.exponent + dy.exponent⟩ := by
  rw [← Model.Internal.Directed.mul_eq]
  cases mode
  case nearest =>
    refine (Model.Proof.mul_eq_spec x y).trans ?_
    simp only [Model.Spec.mul, hx, hy]
    by_cases hzero : dx.significand = 0 ∨ dy.significand = 0
    · have hproduct : dx.significand * dy.significand = 0 := by
        rcases hzero with h | h <;> simp [h]
      have hcond : (dx.significand == 0 || dy.significand == 0) = true := by
        rcases hzero with h | h <;> simp [h]
      rw [hproduct, hcond, ite_eq_left rfl]
      exact (roundDyadic_zero fmt .nearest _ _).symm
    · have hcond : (dx.significand == 0 || dy.significand == 0) = false := by
        rw [Bool.or_eq_false_iff]
        constructor <;> simp only [beq_eq_false_iff_ne, ne_eq] <;> intro h
        · exact hzero (Or.inl h)
        · exact hzero (Or.inr h)
      rw [hcond]
      rfl
  all_goals
    have hsel : Model.chooseNaN2 x y = none :=
      (Model.chooseNaN2_eq_none_iff x y).2
        ⟨Model.isNaN_eq_false_of_toDyadic?_some hx, Model.isNaN_eq_false_of_toDyadic?_some hy⟩
    have hinfx := Model.isInfinite_eq_false_of_toDyadic?_some hx
    have hinfy := Model.isInfinite_eq_false_of_toDyadic?_some hy
    simp only [Model.Internal.Directed.mul]
    rw [Model.withNaNSelection_of_none _ _ hsel]
    simp only [hinfx, hinfy, Bool.false_eq_true, dite_false,
      Model.finiteDyadic_eq_of_toDyadic _ hx, Model.finiteDyadic_eq_of_toDyadic _ hy]

/--
The product with an operand that is not finite does not depend on the direction: it is the
nearest-even specification.
-/
theorem mul_of_nonFinite (mode : Model.IEEERoundingMode) (x y : Model fmt)
    (h : Model.isFinite x = false ∨ Model.isFinite y = false) :
    Model.mul x y (mode := mode) = Model.Spec.mul x y := by
  rw [← Model.Internal.Directed.mul_eq]
  cases mode
  case nearest => exact Model.Proof.mul_eq_spec x y
  all_goals
    have hspec : Model.Spec.mul x y =
        (match Model.chooseNaN2 x y with
          | some nan => nan
          | none =>
              if Model.isInfinite x then
                if Model.isZero y then Model.invalidResult fmt
                else Model.nativeOverflow fmt (Model.signBit x != Model.signBit y)
              else if Model.isInfinite y then
                if Model.isZero x then Model.invalidResult fmt
                else Model.nativeOverflow fmt (Model.signBit x != Model.signBit y)
              else Model.invalidResult fmt) := by
      unfold Model.Spec.mul
      rcases h with h | h
      · rw [toDyadic?_eq_none_of_isFinite_eq_false x h]
        cases Model.toDyadic? y <;> rfl
      · rw [toDyadic?_eq_none_of_isFinite_eq_false y h]
        cases Model.toDyadic? x <;> rfl
    rw [hspec]
    simp only [Model.Internal.Directed.mul]
    obtain ⟨nan, hsel⟩ | hsel := selection_cases (Model.chooseNaN2 x y)
    · rw [Model.withNaNSelection_of_some _ _ nan hsel, hsel]
    · rw [Model.withNaNSelection_of_none _ _ hsel]
      simp only [hsel]
      have hnan := (Model.chooseNaN2_eq_none_iff x y).1 hsel
      by_cases hxInf : Model.isInfinite x = true
      · simp only [hxInf, dite_true, ite_true]
      · by_cases hyInf : Model.isInfinite y = true
        · simp only [hxInf, hyInf, dite_true, dite_false, ite_true, ite_false,
            Bool.false_eq_true]
        · exfalso
          rcases h with h | h
          · exact hxInf (isInfinite_of_nonFinite hnan.1 h)
          · exact hyInf (isInfinite_of_nonFinite hnan.2 h)

/-! ## Fused multiply-add -/

/-- The nearest-even fused multiply-add of three finite values: one rounding of the exact result. -/
theorem spec_fma_of_isFinite (x y z : Model fmt)
    (dx dy dz : Numerics.Dyadic) (hx : Model.toDyadic? x = some dx)
    (hy : Model.toDyadic? y = some dy) (hz : Model.toDyadic? z = some dz) :
    Model.Spec.fma x y z =
      Model.roundDyadic fmt
        (Model.addDyadic
          ⟨Bool.xor dx.negative dy.negative, dx.significand * dy.significand,
            dx.exponent + dy.exponent⟩ dz) := by
  have hnanx := Model.isNaN_eq_false_of_toDyadic?_some hx
  have hnany := Model.isNaN_eq_false_of_toDyadic?_some hy
  have hnanz := Model.isNaN_eq_false_of_toDyadic?_some hz
  have hsx := Model.isSignaling_eq_false_of_toDyadic?_some hx
  have hsy := Model.isSignaling_eq_false_of_toDyadic?_some hy
  have hsz := Model.isSignaling_eq_false_of_toDyadic?_some hz
  have hix := Model.isInfinite_eq_false_of_toDyadic?_some hx
  have hiy := Model.isInfinite_eq_false_of_toDyadic?_some hy
  have hiz := Model.isInfinite_eq_false_of_toDyadic?_some hz
  simp [Model.Spec.fma, Model.chooseNaN3, hnanx, hnany, hnanz, hsx, hsy, hsz, hix, hiy, hiz,
    hx, hy, hz]

/--
The fused multiply-add of three finite values in any direction: one rounding of the exact
`x * y + z`.
-/
theorem fma_of_finite (mode : Model.IEEERoundingMode) (x y z : Model fmt)
    (dx dy dz : Numerics.Dyadic) (hx : Model.toDyadic? x = some dx)
    (hy : Model.toDyadic? y = some dy) (hz : Model.toDyadic? z = some dz) :
    Model.fma x y z (mode := mode) =
      roundedSum fmt mode
        ⟨Bool.xor dx.negative dy.negative, dx.significand * dy.significand,
          dx.exponent + dy.exponent⟩ dz := by
  rw [← Model.Internal.Directed.fma_eq]
  cases mode
  case nearest =>
    rw [roundedSum_nearest]
    exact (Model.Proof.fma_eq_spec x y z).trans (spec_fma_of_isFinite x y z dx dy dz hx hy hz)
  all_goals
    have hsel : Model.chooseNaN3 x y z = none :=
      (Model.chooseNaN3_eq_none_iff x y z).2
        ⟨Model.isNaN_eq_false_of_toDyadic?_some hx, Model.isNaN_eq_false_of_toDyadic?_some hy,
          Model.isNaN_eq_false_of_toDyadic?_some hz⟩
    have hinfx := Model.isInfinite_eq_false_of_toDyadic?_some hx
    have hinfy := Model.isInfinite_eq_false_of_toDyadic?_some hy
    have hinfz := Model.isInfinite_eq_false_of_toDyadic?_some hz
    simp only [Model.Internal.Directed.fma]
    rw [Model.withNaNSelection_of_none _ _ hsel]
    simp only [hinfx, hinfy, hinfz, Bool.or_self, Bool.false_eq_true, dite_false,
      Model.finiteDyadic_eq_of_toDyadic _ hx, Model.finiteDyadic_eq_of_toDyadic _ hy,
      Model.finiteDyadic_eq_of_toDyadic _ hz]
    rfl

/--
The fused multiply-add with an operand that is not finite does not depend on the direction: it
is the nearest-even specification.
-/
theorem fma_of_nonFinite (mode : Model.IEEERoundingMode) (x y z : Model fmt)
    (h : Model.isFinite x = false ∨ Model.isFinite y = false ∨ Model.isFinite z = false) :
    Model.fma x y z (mode := mode) = Model.Spec.fma x y z := by
  rw [← Model.Internal.Directed.fma_eq]
  cases mode
  case nearest => exact Model.Proof.fma_eq_spec x y z
  all_goals
    have hspec : Model.Spec.fma x y z =
        (match Model.chooseNaN3 x y z with
          | some nan => nan
          | none =>
              if Model.isInfinite x || Model.isInfinite y then
                if Model.isZero x || Model.isZero y then Model.invalidResult fmt
                else if Model.isInfinite z then
                  if Model.signBit z != Bool.xor (Model.signBit x) (Model.signBit y) then
                    Model.invalidResult fmt
                  else Model.nativeOverflow fmt (Bool.xor (Model.signBit x) (Model.signBit y))
                else Model.nativeOverflow fmt (Bool.xor (Model.signBit x) (Model.signBit y))
              else if Model.isInfinite z then z
              else Model.invalidResult fmt) := by
      unfold Model.Spec.fma
      rcases h with h | h | h
      · rw [toDyadic?_eq_none_of_isFinite_eq_false x h]
        cases Model.toDyadic? y <;> cases Model.toDyadic? z <;>
          cases Model.chooseNaN3 x y z <;> rfl
      · rw [toDyadic?_eq_none_of_isFinite_eq_false y h]
        cases Model.toDyadic? x <;> cases Model.toDyadic? z <;>
          cases Model.chooseNaN3 x y z <;> rfl
      · rw [toDyadic?_eq_none_of_isFinite_eq_false z h]
        cases Model.toDyadic? x <;> cases Model.toDyadic? y <;>
          cases Model.chooseNaN3 x y z <;> rfl
    rw [hspec]
    simp only [Model.Internal.Directed.fma]
    obtain ⟨nan, hsel⟩ | hsel := selection_cases (Model.chooseNaN3 x y z)
    · rw [Model.withNaNSelection_of_some _ _ nan hsel, hsel]
    · rw [Model.withNaNSelection_of_none _ _ hsel]
      simp only [hsel]
      have hnan := (Model.chooseNaN3_eq_none_iff x y z).1 hsel
      by_cases hxyInf : (Model.isInfinite x || Model.isInfinite y) = true
      · simp only [hxyInf, dite_true, ite_true]
      · by_cases hzInf : Model.isInfinite z = true
        · simp only [hxyInf, hzInf, dite_true, dite_false, ite_true, ite_false,
            Bool.false_eq_true]
        · exfalso
          have hxInf : ¬ Model.isInfinite x = true := fun hx => hxyInf (by simp [hx])
          have hyInf : ¬ Model.isInfinite y = true := fun hy => hxyInf (by simp [hy])
          rcases h with h | h | h
          · exact hxInf (isInfinite_of_nonFinite hnan.1 h)
          · exact hyInf (isInfinite_of_nonFinite hnan.2.1 h)
          · exact hzInf (isInfinite_of_nonFinite hnan.2.2 h)

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
