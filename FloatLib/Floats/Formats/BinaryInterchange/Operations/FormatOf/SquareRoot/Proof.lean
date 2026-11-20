/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.SquareRoot.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.Homogeneous
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Comparison.Directions
public import FloatLib.Floats.Formats.Posit.Algebraic.Root.Proof

import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Extrema

/-!
# The formatOf square root is correctly rounded in every direction

For every destination descriptor (a conventional IEEE one, a format without an infinity such as
OCP E4M3, a format with one zero such as ONNX E4M3FNUZ, or a format in which every encoding is
finite), each rounding direction and a finite positive operand of any binary format with the
exact value `q`, `formatOfSquareRoot` meets the contract `RoundsTo` for `sqrt q`
(`formatOfSquareRoot_roundsTo`): the result is finite and denotes `roundAt destination (sqrt q)
mode` when that is at most the largest finite magnitude of the destination, it is the overflow
result of the direction otherwise, and in a format with signed zeros its sign bit is clear. To
nearest-even a finite result is `roundAt destination (sqrt q)` (`toReal_formatOfSquareRoot`),
`inexact` is raised exactly when the finite result is not `sqrt q`, in every direction
(`formatOfSquareRoot_inexact_iff`), and in one IEEE format the value to nearest-even is
`Model.sqrt` (`formatOfSquareRoot_value_eq_sqrt`).

The special cases are equations for every destination and every operand format:
`formatOfSquareRoot_of_isZero`, `formatOfSquareRoot_of_negative`,
`formatOfSquareRoot_of_isNaN` and `formatOfSquareRoot_of_isInfinite`. In one format they are
the outcomes of `Model.sqrt` with its flags and its ternary value, in every direction and for
every format descriptor (`formatOfSquareRoot_eq_sqrt`): at a NaN, a zero, an infinity and a
negative number.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Numerics
open Reduction.Internal (Factor)
open ComparisonRounding

variable {destination source : FloatFormat}

/-- A finite positive operand is the finite factor of a positive dyadic with a clear sign. -/
private theorem exists_exact_of_toRat?_pos {x : Model source} {q : ℚ}
    (hq : toRat? x = some q) (hpos : 0 < q) :
    ∃ exact : Numerics.Dyadic, toDyadic? x = some exact ∧ exact.toRat = q ∧
      (exact.significand == 0) = false ∧ exact.negative = false := by
  obtain ⟨exact, hexact, hvalue⟩ := Option.map_eq_some_iff.mp hq
  have hsignificand : exact.significand ≠ 0 := by
    intro h
    have := (Numerics.Dyadic.toRat_eq_zero_iff exact).mpr h
    rw [hvalue] at this
    exact hpos.ne' this
  refine ⟨exact, hexact, hvalue, by simpa using hsignificand, ?_⟩
  cases hnegative : exact.negative with
  | false => rfl
  | true =>
      have := Numerics.Dyadic.toRat_neg_of_significand_ne_zero exact hsignificand hnegative
      rw [hvalue] at this
      exact absurd hpos (not_lt.mpr this.le)

/-- At a finite positive operand the formatOf square root is one rounding of the root that the
comparisons of squares locate. -/
theorem formatOfSquareRoot_of_toRat?_pos {x : Model source} {q : ℚ}
    (hq : toRat? x = some q) (hpos : 0 < q) (mode : IEEERoundingMode) :
    formatOfSquareRoot destination x mode =
      ComparisonRounding.deliver destination (Posit.Model.RootRounding.compareRoot q 2) mode := by
  obtain ⟨exact, hexact, hvalue, hsignificand, hnegative⟩ := exists_exact_of_toRat?_pos hq hpos
  simp [formatOfSquareRoot, Factor.ofValue_of_toDyadic?_eq_some hexact, hsignificand, hnegative,
    hvalue]

/-- The comparisons of squares order the square root of a nonnegative rational. -/
theorem compareRoot_two_eq_real {q : ℚ} (hq : 0 ≤ q) (candidate : ℚ) :
    Posit.Model.RootRounding.compareRoot q 2 candidate =
      cmp (Real.sqrt q) (candidate : ℝ) :=
  Posit.Model.RootRounding.compareRoot_eq_real q 2 (Real.sqrt q) (Real.sqrt_nonneg _)
    (by decide) (Real.sq_sqrt (by exact_mod_cast hq)) candidate

/--
**The formatOf square root is correctly rounded in every direction.** For every destination
descriptor and each rounding direction `mode` and a finite positive operand of any binary
format with the exact value `q`: the result is finite and denotes `roundAt destination (sqrt q)
mode` when that value is at most the largest finite magnitude of the destination, it is the
overflow result of the direction otherwise, and in a format with signed zeros its sign bit is
clear.
-/
theorem formatOfSquareRoot_roundsTo {mode : IEEERoundingMode}
    {x : Model source} {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q) :
    RoundsTo destination mode (Real.sqrt q) false
      (formatOfSquareRoot destination x mode).value := by
  have hroot : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hpos)
  rw [formatOfSquareRoot_of_toRat?_pos hq hpos]
  have h := deliver_roundsTo (fmt := destination) (mode := mode) _ hroot.ne'
    (compareRoot_two_eq_real hpos.le) (Hint.sound_none _) (Hint.signed_none _)
  rwa [decide_eq_false (not_lt.mpr hroot.le)] at h

/--
**To nearest-even the formatOf square root is the rounded root.** For a conventional IEEE
destination and a finite positive operand with the exact value `q`, a finite result denotes
`roundAt destination (sqrt q)`.
-/
theorem toReal_formatOfSquareRoot (hdestination : destination.isIEEE = true) {x : Model source}
    {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q)
    (hfinite : isFinite (formatOfSquareRoot destination x).value = true) :
    toReal (formatOfSquareRoot destination x).value = roundAt destination (Real.sqrt q) := by
  rw [formatOfSquareRoot_of_toRat?_pos hq hpos] at hfinite ⊢
  exact toReal_deliver hdestination _ _ (compareRoot_two_eq_real hpos.le) (Hint.sound_none _)
    hfinite

/--
For a finite positive operand with the exact value `q` and every rounding direction, the
formatOf square root raises `inexact` exactly when its finite result is not `sqrt q`.
-/
theorem formatOfSquareRoot_inexact_iff {x : Model source} {q : ℚ} (hq : toRat? x = some q)
    (hpos : 0 < q) (mode : IEEERoundingMode)
    (hfinite : isFinite (formatOfSquareRoot destination x mode).value = true) :
    (formatOfSquareRoot destination x mode).status.inexact = true ↔
      toReal (formatOfSquareRoot destination x mode).value ≠ Real.sqrt q := by
  rw [formatOfSquareRoot_of_toRat?_pos hq hpos] at hfinite ⊢
  exact deliver_inexact_iff _ _ (compareRoot_two_eq_real hpos.le) mode (Hint.sound_none _)
    hfinite

/-- The formatOf square root of a zero is the zero of the operand's sign, without a flag, in
every direction. -/
theorem formatOfSquareRoot_of_isZero {x : Model source} (hzero : isZero x = true)
    (mode : IEEERoundingMode) :
    formatOfSquareRoot destination x mode =
      { value := zero destination (signBit x), status := .clear, ternary := .eq } := by
  have hdecode := toDyadic?_eq_zero_of_isZero_eq_true x hzero
  simp [formatOfSquareRoot, Factor.ofValue_of_toDyadic?_eq_some hdecode]

/-- The formatOf square root of a NaN is that NaN quieted and converted into the destination,
with `invalid` when it was signaling. -/
theorem formatOfSquareRoot_of_isNaN {x : Model source} (hnan : isNaN x = true)
    (mode : IEEERoundingMode) :
    formatOfSquareRoot destination x mode =
      outcomeWithInvalid (cast source destination (quietNaN x)) (isSignaling x) := by
  have hdecode : toDyadic? x = none :=
    toDyadic?_eq_none_of_isFinite_eq_false (isFinite_eq_false_of_isNaN hnan)
  simp [formatOfSquareRoot, Factor.ofValue, hdecode, hnan, Factor.deliver]

/--
In one conventional IEEE format and for a finite positive operand, the formatOf square root to
nearest-even delivers `Model.sqrt`.
-/
theorem formatOfSquareRoot_value_eq_sqrt {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {x : Model fmt} {q : ℚ} (hq : toRat? x = some q) (hpos : 0 < q) :
    (formatOfSquareRoot fmt x).value = sqrt x := by
  have hfinite := Algebraic.isFinite_of_toRat?_eq_some hq
  have hreal := Algebraic.toReal_of_toRat?_eq_some hq
  have hsign : signBit x = false := by
    cases hbit : signBit x with
    | false => rfl
    | true =>
        have hnonneg : (0 : ℝ) ≤ toReal x := by
          rw [hreal]
          exact_mod_cast hpos.le
        rcases isZero_or_signBit_eq_false_of_toReal_nonneg x hfinite hnonneg with hzero | hclear
        · have := toReal_eq_zero_of_isZero x hzero
          rw [hreal] at this
          exact absurd (by exact_mod_cast this) hpos.ne'
        · rw [hbit] at hclear
          exact absurd hclear (by decide)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hpos
  have hsqrt := toReal_sqrt_eq_roundAt x hfmt hfinite (.inr hsign)
  rw [hreal] at hsqrt
  have hsqrtFinite := isFinite_sqrt_of_isFinite x hfmt hfinite (.inr hsign)
  have hrange : |roundAt fmt (Real.sqrt q)| ≤ toReal (posMaxFinite fmt) := by
    rw [← hsqrt]
    exact abs_toReal_le_posMaxFinite_of_isFinite _ hsqrtFinite
  obtain ⟨-, hresult⟩ :=
    (formatOfSquareRoot_roundsTo (destination := fmt) (mode := .nearest) hq hpos).finite hrange
  -- The rounded root is not zero: it is at least the smaller of the operand and one.
  have hne : roundAt fmt (Real.sqrt q) ≠ 0 := by
    rcases le_total (q : ℝ) 1 with hle | hge
    · have hbelow : (q : ℝ) ≤ Real.sqrt q := (Real.le_sqrt' hq0).mpr (by nlinarith)
      have h := roundAt_mono fmt hbelow
      rw [← hreal, roundAt_toReal_eq x hfinite, hreal] at h
      exact (hq0.trans_le h).ne'
    · have habove : (1 : ℝ) ≤ Real.sqrt q := Real.one_le_sqrt.mpr hge
      have h := roundAt_mono fmt habove
      rw [roundAt_one] at h
      exact (zero_lt_one.trans_le h).ne'
  exact eq_of_toReal_eq_of_nonzero (hresult.trans hsqrt.symm) (by rw [hresult]; exact hne)

/--
The formatOf square root of an infinity, in every direction: the infinity of the destination
for the positive one, without a flag, and the default NaN with `invalid` for the negative one.
-/
theorem formatOfSquareRoot_of_isInfinite {x : Model source} (hinfinite : isInfinite x = true)
    (mode : IEEERoundingMode) :
    formatOfSquareRoot destination x mode =
      if signBit x = true then outcomeWithInvalid (invalidResult destination) true
      else
        { value := nativeOverflow destination false, status := .clear
          ternary := exactInfinityTernary false (nativeOverflow destination false) } := by
  have hdecode := toDyadic?_eq_none_of_isInfinite_eq_true hinfinite
  have hnan := isNaN_eq_false_of_isInfinite_eq_true x hinfinite
  cases hsign : signBit x <;>
    simp [formatOfSquareRoot, Factor.ofValue, hdecode, hnan, hsign, Factor.deliver]

/-- The formatOf square root of a negative finite number that is not a zero is the default NaN
with `invalid`, in every direction. -/
theorem formatOfSquareRoot_of_negative {x : Model source} (hfinite : isFinite x = true)
    (hzero : isZero x = false) (hsign : signBit x = true) (mode : IEEERoundingMode) :
    formatOfSquareRoot destination x mode =
      outcomeWithInvalid (invalidResult destination) true := by
  obtain ⟨exact, hexact, hnegative, -⟩ := KernelPath.toDyadic?_of_isFinite x hfinite
  have hsignificand : (exact.significand == 0) = false := by
    rw [← isZero_eq_beq_zero_of_toDyadic?_some hexact, hzero]
  simp [formatOfSquareRoot, Factor.ofValue_of_toDyadic?_eq_some hexact, hsignificand, hnegative,
    hsign]

/--
In one format, the formatOf square root of an operand that is not a positive finite number is
`Model.sqrt` with its flags and its ternary value, in every rounding direction and for every
format descriptor: a NaN, a zero, an infinity and a negative number.
-/
theorem formatOfSquareRoot_eq_sqrt {fmt : FloatFormat} {x : Model fmt} (mode : IEEERoundingMode)
    (h : isFinite x = false ∨ isZero x = true ∨ signBit x = true) :
    formatOfSquareRoot fmt x mode = sqrt x (mode := mode) (status := true) := by
  by_cases hnan : isNaN x = true
  · rw [formatOfSquareRoot_of_isNaN hnan, cast_quietNaN_self hnan, sqrt_status_of_isNaN mode hnan,
      KernelPath.sqrt_cases]
    simp [chooseNaN1, hnan]
  have hnanFalse : isNaN x = false := by simpa using hnan
  by_cases hzero : isZero x = true
  · have hinfinite := isInfinite_eq_false_of_isFinite_eq_true x
      (isFinite_eq_true_of_isZero_eq_true x hzero)
    rw [formatOfSquareRoot_of_isZero hzero, sqrt_status_of_isZero mode hzero,
      KernelPath.sqrt_cases]
    simp [chooseNaN1, hnanFalse, hinfinite, hzero, outcomeWithInvalid,
      KernelPath.zero_signBit_of_isZero x hzero]
  have hzeroFalse : isZero x = false := by simpa using hzero
  by_cases hinfinite : isInfinite x = true
  · obtain ⟨hencoding, -⟩ := eq_nativeOverflow_of_isInfinite hinfinite
    rw [formatOfSquareRoot_of_isInfinite hinfinite]
    cases hsign : signBit x
    · rw [sqrt_status_of_isInfinite mode hinfinite hsign, KernelPath.sqrt_cases]
      simp [chooseNaN1, hnanFalse, hinfinite, hsign, outcomeWithInvalid,
        exactInfinityTernary_nativeOverflow hencoding]
    · rw [sqrt_status_of_signBit mode hnanFalse hzeroFalse hsign, KernelPath.sqrt_cases]
      simp [chooseNaN1, hnanFalse, hinfinite, hsign]
  have hinfiniteFalse : isInfinite x = false := by simpa using hinfinite
  have hfinite :=
    isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x hnanFalse hinfiniteFalse
  have hsign : signBit x = true := by
    rcases h with h | h | h
    · rw [hfinite] at h
      exact absurd h (by decide)
    · rw [hzeroFalse] at h
      exact absurd h (by decide)
    · exact h
  rw [formatOfSquareRoot_of_negative hfinite hzeroFalse hsign,
    sqrt_status_of_signBit mode hnanFalse hzeroFalse hsign, KernelPath.sqrt_cases]
  simp [chooseNaN1, hnanFalse, hinfiniteFalse, hzeroFalse, hsign]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
