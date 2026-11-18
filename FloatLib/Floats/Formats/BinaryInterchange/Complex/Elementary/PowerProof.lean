/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Power
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.LogarithmProof
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.AlgebraicProof
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.ExponentialProof
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.DirectedEnclosureProof
public import FloatLib.Numerics.Enclosure.Rational.Converges
public import FloatLib.Numerics.Exact.Product.FactorsProof
public import FloatLib.Numerics.Exact.RationalPower.Proof
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# A certified complex power is correctly rounded

For every IEEE binary format, every rounding direction, every finite base other than zero and
every finite exponent, a result of `ExecComplex.pow` that `powCertified` accepts is the exact
power with each part rounded once (`pow_eq`).

The exact power `powExact z w` is Mathlib's `toComplex z ^ toComplex w`, which is
`exp (log z * w)`, where the imaginary sign bit of the base is clear, and
`conj (conj z ^ conj w)` elsewhere, so that a base `x - 0 i` with `x < 0` is below the branch
cut. The proof writes both parts as `exp (c L - d θ) cos (d L + c θ)` and
`exp (c L - d θ) sin (d L + c θ)` with `L = log |z|` and the angle `θ` (`powExact_eq`), and
treats the certified cases of `powRat` in turn: the exact powers of a complex rational root
(`gaussRatPow?_spec`, with `gaussZPow_spec` for the integer power and `gaussRoot?_spec` for the
principal `2 ^ k`-th root), the powers that stay on an axis (`axisComparators_spec`), and the
parts decided by an enclosure (`contains_powEnclosure?` with
`Model.AlgebraicRounding.roundReal_eq_of_zivRound?`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open FloatLib.Numerics
open ProductComparison (Trig cos_int_mul_pi_div_two sin_int_mul_pi_div_two)
open Model.AlgebraicRounding (roundRat zivRound? roundSigned_eq_roundReal roundRat_eq_roundReal
  roundReal_eq_of_zivRound?)

variable {fmt : FloatFormat}

/-- The angle of the base `x + i y`, or of its conjugate with `negative`. -/
noncomputable def powAngle (x y : ℝ) (negative : Bool) : ℝ :=
  if negative then -Complex.arg ⟨x, y⟩ else Complex.arg ⟨x, y⟩

/--
A part of the power `(x + i y) ^ (c + i d)`, or of the power of the conjugate base with
`negative`: `exp (c L - d θ) cos (d L + c θ)` or `exp (c L - d θ) sin (d L + c θ)`.
-/
noncomputable def powPartValue (trig : Trig) (x y c d : ℝ) (negative : Bool) : ℝ :=
  Real.exp (c * (Complex.log ⟨x, y⟩).re - d * powAngle x y negative) *
    trig.eval (d * (Complex.log ⟨x, y⟩).re + c * powAngle x y negative)

/-- The parts of a complex power with a nonzero base. -/
theorem cpow_mk {ζ : ℂ} (hζ : ζ ≠ 0) (c d : ℝ) :
    ζ ^ (⟨c, d⟩ : ℂ) =
      ⟨Real.exp (c * (Complex.log ζ).re - d * ζ.arg) *
          Real.cos (d * (Complex.log ζ).re + c * ζ.arg),
        Real.exp (c * (Complex.log ζ).re - d * ζ.arg) *
          Real.sin (d * (Complex.log ζ).re + c * ζ.arg)⟩ := by
  rw [Complex.cpow_def_of_ne_zero hζ]
  apply Complex.ext
  · rw [Complex.exp_re]
    simp only [Complex.mul_re, Complex.mul_im, Complex.log_im]
    congr 2 <;> ring
  · rw [Complex.exp_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.log_im]
    congr 2 <;> ring

/--
The exact result of `cpow` at a finite nonzero base: Mathlib's complex power where the imaginary
sign bit of the base is clear, and `conj (conj z ^ conj w)` elsewhere. A zero imaginary part has
the sign bit of the imaginary part of the base.
-/
noncomputable def powExact (z w : ExecComplex fmt) : Exact :=
  if Model.signBit z.im then
    (⟨toComplex (ExecComplex.conj z) ^ toComplex (ExecComplex.conj w), false, false⟩ : Exact).conj
  else ⟨toComplex z ^ toComplex w, false, false⟩

/-- The exact power in terms of the logarithm and the angle of the base. -/
theorem powExact_eq {z w : ExecComplex fmt} (hz : isFinite z = true) (hw : isFinite w = true)
    {x y c d : ℝ} (hbase : (if Model.signBit z.im then starRingEnd ℂ (toComplex z)
      else toComplex z) = ⟨x, y⟩) (hne : (⟨x, y⟩ : ℂ) ≠ 0) (hexponent : toComplex w = ⟨c, d⟩) :
    powExact z w = ⟨⟨powPartValue .cos x y c d (Model.signBit z.im),
      powPartValue .sin x y c d (Model.signBit z.im)⟩, false, Model.signBit z.im⟩ := by
  unfold powExact
  cases hsign : Model.signBit z.im with
  | false =>
      rw [hsign] at hbase
      simp only [Bool.false_eq_true, ↓reduceIte] at hbase ⊢
      rw [hbase, hexponent, cpow_mk hne]
      simp [powPartValue, powAngle, Trig.eval]
  | true =>
      rw [hsign] at hbase
      simp only [↓reduceIte] at hbase ⊢
      rw [toComplex_conj z hz, toComplex_conj w hw, hbase, hexponent,
        show starRingEnd ℂ (⟨c, d⟩ : ℂ) = ⟨c, -d⟩ from rfl, cpow_mk hne]
      simp only [Exact.conj, powPartValue, powAngle, Trig.eval, ↓reduceIte, Bool.not_false]
      congr 1
      apply Complex.ext
      · simp only [Complex.conj_re]
        rw [show d * (Complex.log ⟨x, y⟩).re + c * -Complex.arg ⟨x, y⟩ =
          -(-d * (Complex.log ⟨x, y⟩).re + c * Complex.arg ⟨x, y⟩) by ring, Real.cos_neg]
        congr 2
        ring
      · simp only [Complex.conj_im]
        rw [show d * (Complex.log ⟨x, y⟩).re + c * -Complex.arg ⟨x, y⟩ =
          -(-d * (Complex.log ⟨x, y⟩).re + c * Complex.arg ⟨x, y⟩) by ring, Real.sin_neg,
          mul_neg]
        congr 3
        ring

/-! ## Exact integer powers -/

/-- `gaussPow` is the natural power of the complex rational. -/
theorem gaussPow_spec (x y : Rat) (n : Nat) :
    (⟨(x : ℝ), (y : ℝ)⟩ : ℂ) ^ n =
      ⟨((gaussPow x y n).1 : ℝ), ((gaussPow x y n).2 : ℝ)⟩ := by
  induction n with
  | zero => apply Complex.ext <;> simp [gaussPow]
  | succ n ih =>
      rw [pow_succ, ih]
      apply Complex.ext <;> simp [gaussPow, Complex.mul_re, Complex.mul_im]

/-- `gaussZPow` is the integer power of the complex rational. -/
theorem gaussZPow_spec (x y : Rat) (n : Int) :
    (⟨(x : ℝ), (y : ℝ)⟩ : ℂ) ^ n =
      ⟨((gaussZPow x y n).1 : ℝ), ((gaussZPow x y n).2 : ℝ)⟩ := by
  unfold gaussZPow
  split
  · rename_i hn
    have h := gaussPow_spec x y n.natAbs
    rwa [← zpow_natCast, Int.natAbs_of_nonneg hn] at h
  · rename_i hn
    have hneg : n = -(n.natAbs : ℤ) := by omega
    conv_lhs => rw [hneg]
    rw [zpow_neg, zpow_natCast, gaussPow_spec]
    apply Complex.ext <;> simp [Complex.inv_re, Complex.inv_im, Complex.normSq_mk]

/-! ## Exact roots -/

/-- A complex number of the closed first quadrant is the principal square root of its square. -/
theorem cpow_inv_two_of_sq {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hre : a * a - b * b = x)
    (him : 2 * a * b = y) : (⟨x, y⟩ : ℂ) ^ (2⁻¹ : ℂ) = ⟨a, b⟩ := by
  have hsq : (⟨x, y⟩ : ℂ) = (⟨a, b⟩ : ℂ) ^ 2 := by
    apply Complex.ext <;> simp [sq, ← hre, ← him]
    ring
  rw [hsq]
  exact sq_cpow_inv_two ha (Or.inr hb)

/-- A root that `gaussSqrt?` returns is the principal square root of the complex rational. -/
theorem gaussSqrt?_spec {x y : Rat} {root : Rat × Rat} (h : gaussSqrt? x y = some root) :
    (⟨(x : ℝ), (y : ℝ)⟩ : ℂ) ^ (2⁻¹ : ℂ) = ⟨(root.1 : ℝ), (root.2 : ℝ)⟩ := by
  unfold gaussSqrt? at h
  dsimp only at h
  split at h
  · rename_i hcheck
    obtain ⟨ha, hb, hre, him⟩ := hcheck
    rw [← Option.some.inj h]
    exact cpow_inv_two_of_sq (by exact_mod_cast ha) (by exact_mod_cast hb)
      (by exact_mod_cast hre) (by exact_mod_cast him)
  · simp at h

/-- A root that `gaussRoot?` returns is the principal `2 ^ k`-th root of the complex rational. -/
theorem gaussRoot?_spec : ∀ (k : Nat) {x y : Rat} {root : Rat × Rat},
    gaussRoot? x y k = some root →
      (⟨(x : ℝ), (y : ℝ)⟩ : ℂ) ^ (((2 : ℂ) ^ k)⁻¹) = ⟨(root.1 : ℝ), (root.2 : ℝ)⟩
  | 0, x, y, root, h => by
      rw [← Option.some.inj h]
      simp
  | k + 1, x, y, root, h => by
      obtain ⟨first, hfirst, hrest⟩ := Option.bind_eq_some_iff.mp h
      have him : (Complex.log ⟨(x : ℝ), (y : ℝ)⟩ * (2⁻¹ : ℂ)).im =
          Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ / 2 := by
        rw [show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.im_mul_ofReal,
          Complex.log_im]
        ring
      rw [← gaussRoot?_spec k hrest, ← gaussSqrt?_spec hfirst, pow_succ, mul_inv, mul_comm,
        Complex.cpow_mul]
      · rw [him]
        linarith [Complex.neg_pi_lt_arg ⟨(x : ℝ), (y : ℝ)⟩, Real.pi_pos]
      · rw [him]
        linarith [Complex.arg_le_pi ⟨(x : ℝ), (y : ℝ)⟩, Real.pi_pos]

/-- A power that `gaussRatPow?` returns is the principal power of the complex rational. -/
theorem gaussRatPow?_spec {x y c : Rat} {power : Rat × Rat}
    (h : gaussRatPow? x y c = some power) :
    (⟨(x : ℝ), (y : ℝ)⟩ : ℂ) ^ ((c : ℝ) : ℂ) = ⟨(power.1 : ℝ), (power.2 : ℝ)⟩ := by
  unfold gaussRatPow? at h
  split at h
  · rename_i hden
    obtain ⟨root, hroot, hpower⟩ := Option.bind_eq_some_iff.mp h
    split at hpower
    · have hcast : ((c.den : ℕ) : ℂ) = (2 : ℂ) ^ c.den.log2 := by
        have := congrArg (Nat.cast : ℕ → ℂ) hden
        simpa using this
      rw [← Option.some.inj hpower, ← gaussZPow_spec, ← gaussRoot?_spec _ hroot,
        ← Complex.cpow_int_mul]
      congr 1
      rw [Complex.ofReal_ratCast, Rat.cast_def, hcast, div_eq_mul_inv]
    · simp at hpower
  · simp at h

/-! ## Powers that stay on an axis -/

/--
`axisComparators r c m` compare the parts of `r ^ c * i ^ m`, which are `r ^ c cos (m π / 2)` and
`r ^ c sin (m π / 2)`, with every rational, for a nonnegative `r`.
-/
theorem axisComparators_spec {r : Rat} (hr : 0 ≤ r) (c : Rat) (m : Int) (boundary : Rat) :
    (axisComparators r c m).1 boundary =
        cmp ((r : ℝ) ^ (c : ℝ) * Real.cos (m * (Real.pi / 2))) (boundary : ℝ) ∧
      (axisComparators r c m).2 boundary =
        cmp ((r : ℝ) ^ (c : ℝ) * Real.sin (m * (Real.pi / 2))) (boundary : ℝ) := by
  have hpower (t : Rat) := RationalPower.compare_eq_real r c t hr
  have hzero : cmp (0 : Rat) boundary = cmp (0 : ℝ) (boundary : ℝ) := by
    simp only [cmp, cmpUsing, Rat.cast_pos, Rat.cast_lt_zero]
  have hnegated : (RationalPower.compare r c (-boundary)).swap =
      cmp (-((r : ℝ) ^ (c : ℝ))) (boundary : ℝ) := by
    rw [hpower, cmp_swap]
    push_cast
    simp only [cmp, cmpUsing, neg_lt, lt_neg]
  rw [cos_int_mul_pi_div_two, sin_int_mul_pi_div_two]
  unfold axisComparators
  have hlower := Int.emod_nonneg m (by norm_num : (4 : ℤ) ≠ 0)
  obtain h | h | h | h : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  · simp [h, hpower, hzero]
  · simp [h, hpower, hzero]
  · simp [h, hnegated, hzero]
  · simp [h, hnegated, hzero]

/-- The modulus of a complex number on an axis is the sum of the moduli of its parts. -/
theorem norm_mk_of_axis {x y : ℝ} (h : x = 0 ∨ y = 0) : ‖(⟨x, y⟩ : ℂ)‖ = |x| + |y| := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  rcases h with rfl | rfl
  · simp [Real.sqrt_sq_eq_abs]
  · simp [Real.sqrt_sq_eq_abs]

/-- The angle of a nonzero base on an axis, with a nonnegative imaginary part, is `axisTurns`
quarter turns. -/
theorem powAngle_of_axis {x y : Rat} (hne : ¬(x = 0 ∧ y = 0)) (hy : 0 ≤ y) (h : x = 0 ∨ y = 0)
    (negative : Bool) :
    powAngle x y negative = (axisTurns x y negative : ℝ) * (Real.pi / 2) := by
  have harg : Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ =
      ((if y = 0 then (if 0 < x then 0 else 2) else 1 : ℤ) : ℝ) * (Real.pi / 2) := by
    by_cases hy0 : y = 0
    · subst hy0
      have hx0 : x ≠ 0 := fun hx => hne ⟨hx, rfl⟩
      by_cases hx : 0 < x
      · simp only [↓reduceIte, hx, Int.cast_zero, zero_mul]
        exact Complex.arg_eq_zero_iff.mpr
          ⟨show (0 : ℝ) ≤ (x : ℝ) by exact_mod_cast hx.le, by simp⟩
      · have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp hx) hx0
        simp only [↓reduceIte, hx, Int.cast_ofNat]
        rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring]
        exact Complex.arg_eq_pi_iff.mpr
          ⟨show (x : ℝ) < 0 by exact_mod_cast hneg, by simp⟩
    · have hx0 : x = 0 := h.resolve_right hy0
      subst hx0
      simp only [hy0, ↓reduceIte, Int.cast_one, one_mul]
      exact Complex.arg_eq_pi_div_two_iff.mpr
        ⟨by simp, show (0 : ℝ) < (y : ℝ) by exact_mod_cast lt_of_le_of_ne hy (Ne.symm hy0)⟩
  unfold powAngle axisTurns
  rw [harg]
  cases negative <;> simp

/-! ## Enclosures of the general case -/

/-- The real part of the logarithm of a nonzero complex rational. -/
theorem log_re_mk (x y : Rat) :
    (Complex.log ⟨(x : ℝ), (y : ℝ)⟩).re =
      ((1 / 2 : Rat) : ℝ) * Real.log ((x * x + y * y : Rat) : ℝ) := by
  have hq : 0 ≤ x * x + y * y := add_nonneg (mul_self_nonneg x) (mul_self_nonneg y)
  rw [Complex.log_re, Complex.norm_eq_sqrt_sq_add_sq,
    show (x : ℝ) ^ 2 + (y : ℝ) ^ 2 = ((x * x + y * y : Rat) : ℝ) by push_cast; ring,
    Real.log_sqrt (by exact_mod_cast hq)]
  push_cast
  ring

/-- A sum of squares of rationals that are not both zero is positive. -/
theorem sumSq_pos {x y : Rat} (hne : ¬(x = 0 ∧ y = 0)) : 0 < x * x + y * y := by
  rcases lt_or_eq_of_le (add_nonneg (mul_self_nonneg x) (mul_self_nonneg y)) with h | h
  · exact h
  · exact absurd ⟨by nlinarith [mul_self_nonneg x, mul_self_nonneg y],
      by nlinarith [mul_self_nonneg x, mul_self_nonneg y]⟩ hne

/-- Every enclosure that `powEnclosure?` returns contains the part of the power. -/
theorem contains_powEnclosure? {trig : Trig} {x y c d : Rat} {negative : Bool}
    {precision : Nat} {interval : RationalInterval} (hne : ¬(x = 0 ∧ y = 0))
    (h : powEnclosure? fmt trig x y c d negative precision = some interval) :
    interval.Contains (powPartValue trig x y c d negative) := by
  have hlog (precision : Nat) : (logArgEnclosures x y negative precision).1.Contains
      (Complex.log ⟨(x : ℝ), (y : ℝ)⟩).re := by
    rw [log_re_mk]
    exact RationalInterval.contains_scale (contains_ratLogEnclosure (sumSq_pos hne) _) (1 / 2)
  have htheta (precision : Nat) : (logArgEnclosures x y negative precision).2.Contains
      (powAngle x y negative) := by
    unfold powAngle logArgEnclosures
    cases negative
    · exact TrigonometricComparison.contains_atan2Interval x y _
    · exact RationalInterval.contains_neg
        (TrigonometricComparison.contains_atan2Interval x y _)
  unfold powEnclosure? at h
  dsimp only at h
  split at h
  · simp at h
  · obtain ⟨angleBounds, hangle, rfl⟩ := Option.map_eq_some_iff.mp h
    have hexponent := RationalInterval.contains_sub
      (RationalInterval.contains_scale (hlog (precision + ⌈|c| + |d|⌉₊.log2 + 8)) c)
      (RationalInterval.contains_scale (htheta (precision + ⌈|c| + |d|⌉₊.log2 + 8)) d)
    exact RationalInterval.contains_mul (contains_expBounds hexponent _ _)
      (ProductComparison.contains_trigBounds? (RationalInterval.contains_add
        (RationalInterval.contains_scale (hlog (precision + ⌈|c| + |d|⌉₊.log2 + 8)) d)
        (RationalInterval.contains_scale (htheta (precision + ⌈|c| + |d|⌉₊.log2 + 8)) c)) hangle)

/-- A certified part of the general case is the rounding of the part of the power. -/
theorem powPart_eq (hfmt : fmt.isIEEE = true) (mode : Model.IEEERoundingMode) {trig : Trig}
    {x y c d : Rat} {negative : Bool} {levels : Nat} (hne : ¬(x = 0 ∧ y = 0))
    (h : (powPart fmt mode trig x y c d negative levels).2 = true) (zeroSign : Bool) :
    (powPart fmt mode trig x y c d negative levels).1 =
      Model.roundReal fmt mode (powPartValue trig x y c d negative) zeroSign := by
  unfold powPart at h ⊢
  cases hziv : zivRound? fmt mode (powEnclosure? fmt trig x y c d negative) levels
      (fmt.fracWidth + 32) with
  | some result =>
      exact (roundReal_eq_of_zivRound? hfmt mode
        (fun _ _ hinterval => contains_powEnclosure? hne hinterval) hziv zeroSign).symm
  | none => simp [hziv] at h

/-! ## The certified power -/

/-- A certified power of a nonzero complex rational is correctly rounded. -/
theorem powRat_eq (hfmt : fmt.isIEEE = true) (mode : Model.IEEERoundingMode) {x y c d : Rat}
    {negative : Bool} {levels : Nat} (hne : ¬(x = 0 ∧ y = 0)) (hy : 0 ≤ y)
    (h : (powRat fmt mode x y c d negative levels).2 = true) :
    (powRat fmt mode x y c d negative levels).1 =
      ⟨Model.roundReal fmt mode (powPartValue .cos x y c d negative) false,
        Model.roundReal fmt mode (powPartValue .sin x y c d negative) negative⟩ := by
  have hζ : (⟨(x : ℝ), (y : ℝ)⟩ : ℂ) ≠ 0 := fun hzero =>
    hne ⟨by simpa using congrArg Complex.re hzero, by simpa using congrArg Complex.im hzero⟩
  unfold powRat at h ⊢
  by_cases hone : x = 1 ∧ y = 0
  · rw [ite_eq_left hone]
    obtain ⟨rfl, rfl⟩ := hone
    have hlog : (Complex.log ⟨((1 : Rat) : ℝ), ((0 : Rat) : ℝ)⟩).re = 0 := by
      rw [show (⟨((1 : Rat) : ℝ), ((0 : Rat) : ℝ)⟩ : ℂ) = 1 by apply Complex.ext <;> simp]
      simp
    have hangle : powAngle ((1 : Rat) : ℝ) ((0 : Rat) : ℝ) negative = 0 := by
      unfold powAngle
      rw [show (⟨((1 : Rat) : ℝ), ((0 : Rat) : ℝ)⟩ : ℂ) = 1 by apply Complex.ext <;> simp]
      simp
    simp only [powPartValue, hlog, hangle, Trig.eval, mul_zero, sub_zero, add_zero, Real.exp_zero,
      Real.cos_zero, Real.sin_zero, mul_one, Model.roundReal_zero]
    rw [roundRat_eq_roundReal]
    simp
  · rw [ite_eq_right hone] at h ⊢
    cases hexact : (if d = 0 then gaussRatPow? x y c else none) with
    | some power =>
      dsimp only
      have hd : d = 0 := by
        by_contra hd
        simp [hd] at hexact
      have hpower := (cpow_mk hζ (c : ℝ) 0).symm.trans
        (gaussRatPow?_spec (by simpa [hd] using hexact : gaussRatPow? x y c = some power))
      have hre := congrArg Complex.re hpower
      have him := congrArg Complex.im hpower
      simp only at hre him
      have hcos : powPartValue .cos x y c d negative = (power.1 : ℝ) := by
        rw [← hre, powPartValue, hd]
        unfold powAngle
        cases negative <;> simp [Trig.eval]
      have hsin : powPartValue .sin x y c d negative =
          ((if negative then -power.2 else power.2 : Rat) : ℝ) := by
        rw [powPartValue, hd]
        unfold powAngle
        cases negative
        · simpa [Trig.eval] using him
        · simp only [Trig.eval, ↓reduceIte, Rat.cast_neg, ← him]
          simp
      rw [hcos, hsin, roundRat_eq_roundReal]
      congr 1
      exact roundSigned_eq_roundReal fmt mode
        (fun boundary => by simp only [cmp, cmpUsing, Rat.cast_lt]) negative
    | none =>
      simp only [hexact] at h ⊢
      by_cases haxis : d = 0 ∧ (x = 0 ∨ y = 0) ∧ (c * axisTurns x y negative).den = 1
      · rw [ite_eq_left haxis]
        obtain ⟨hd, hax, hden⟩ := haxis
        have hr : (0 : Rat) ≤ |x| + |y| := by positivity
        have hrpos : (0 : ℝ) < ((|x| + |y| : Rat) : ℝ) := by
          have : (0 : Rat) < |x| + |y| := by
            rcases lt_or_eq_of_le hr with hlt | heq
            · exact hlt
            · exact absurd ⟨abs_eq_zero.mp (by linarith [abs_nonneg x, abs_nonneg y]),
                abs_eq_zero.mp (by linarith [abs_nonneg x, abs_nonneg y])⟩ hne
          exact_mod_cast this
        have hturns : ((c * axisTurns x y negative : Rat) : ℝ) =
            (((c * axisTurns x y negative).num : ℤ) : ℝ) := by
          exact_mod_cast congrArg (fun q : Rat => (q : ℝ))
            (Rat.intCast_num_of_den_eq_one hden).symm
        have hlog : (Complex.log ⟨(x : ℝ), (y : ℝ)⟩).re = Real.log ((|x| + |y| : Rat) : ℝ) := by
          rw [Complex.log_re, norm_mk_of_axis (by exact_mod_cast hax)]
          push_cast
          rfl
        have hvalue (trig : Trig) : powPartValue trig x y c d negative =
            ((|x| + |y| : Rat) : ℝ) ^ (c : ℝ) *
              trig.eval (((c * axisTurns x y negative).num : ℤ) * (Real.pi / 2)) := by
          rw [powPartValue, hd, powAngle_of_axis hne hy hax, hlog, Real.rpow_def_of_pos hrpos,
            ← hturns]
          push_cast
          congr 2 <;> ring
        have hspec := axisComparators_spec hr c (c * axisTurns x y negative).num
        rw [hvalue .cos, hvalue .sin]
        dsimp only
        congr 1
        · exact roundSigned_eq_roundReal fmt mode (fun boundary => (hspec boundary).1) false
        · exact roundSigned_eq_roundReal fmt mode (fun boundary => (hspec boundary).2) negative
      · rw [ite_eq_right haxis] at h ⊢
        by_cases hunit : |x| + |y| = 1 ∧ (x = 0 ∨ y = 0) ∧ (c * axisTurns x y negative).den = 1
        · rw [ite_eq_left hunit] at h ⊢
          obtain ⟨hmodulus, hax, hden⟩ := hunit
          have hturns : ((c * axisTurns x y negative : Rat) : ℝ) =
              (((c * axisTurns x y negative).num : ℤ) : ℝ) := by
            exact_mod_cast congrArg (fun q : Rat => (q : ℝ))
              (Rat.intCast_num_of_den_eq_one hden).symm
          have hlog : (Complex.log ⟨(x : ℝ), (y : ℝ)⟩).re = 0 := by
            rw [Complex.log_re, norm_mk_of_axis (by exact_mod_cast hax)]
            have hreal : |(x : ℝ)| + |(y : ℝ)| = 1 := by exact_mod_cast hmodulus
            rw [hreal, Real.log_one]
          have hvalue (trig : Trig) : powPartValue trig x y c d negative =
              Real.exp (-(d * powAngle x y negative)) *
                trig.eval (((c * axisTurns x y negative).num : ℤ) * (Real.pi / 2)) := by
            rw [powPartValue, hlog, ← hturns, powAngle_of_axis hne hy hax]
            push_cast
            congr 2 <;> ring
          have hlower := Int.emod_nonneg (c * axisTurns x y negative).num
            (by norm_num : (4 : ℤ) ≠ 0)
          have hupper := Int.emod_lt_of_pos (c * axisTurns x y negative).num
            (by norm_num : (0 : ℤ) < 4)
          by_cases heven : (c * axisTurns x y negative).num % 2 = 0
          · rw [ite_eq_left heven] at h ⊢
            dsimp only at h ⊢
            have hsin : powPartValue .sin x y c d negative = 0 := by
              rw [hvalue, Trig.eval, sin_int_mul_pi_div_two,
                ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
            rw [powPart_eq hfmt mode hne h false, hsin, Model.roundReal_zero]
          · rw [ite_eq_right heven] at h ⊢
            dsimp only at h ⊢
            have hcos : powPartValue .cos x y c d negative = 0 := by
              rw [hvalue, Trig.eval, cos_int_mul_pi_div_two,
                ite_eq_right (by omega), ite_eq_right (by omega), mul_zero]
            rw [powPart_eq hfmt mode hne h negative, hcos, Model.roundReal_zero]
        · rw [ite_eq_right hunit] at h ⊢
          dsimp only at h ⊢
          rw [Bool.and_eq_true] at h
          rw [powPart_eq hfmt mode hne h.1 false, powPart_eq hfmt mode hne h.2 negative]

/--
For an IEEE descriptor, a certified `powChecked` at a finite base other than zero and a finite
exponent is the exact power with each part rounded once in the direction `mode`.
-/
theorem powChecked_eq (hfmt : fmt.isIEEE = true) {z w : ExecComplex fmt}
    (hz : isFinite z = true) (hw : isFinite w = true) (hne : toComplex z ≠ 0)
    (mode : Model.IEEERoundingMode := .nearest) (levels : Nat := 4)
    (h : (powChecked z w mode levels).2 = true) :
    (powChecked z w mode levels).1 = (powExact z w).round fmt mode := by
  obtain ⟨c, d, hc, hd, hexponent, -⟩ := exists_toRat?_of_isFinite hw
  have hbaseFinite : isFinite (⟨z.re, if Model.signBit z.im then Model.neg z.im else z.im⟩ :
      ExecComplex fmt) = true := by
    obtain ⟨hre, him⟩ := (isFinite_eq_true_iff z).1 hz
    cases Model.signBit z.im <;> simp [isFinite, hre, him]
  obtain ⟨x, y, hx, hy, hbase, -⟩ := exists_toRat?_of_isFinite hbaseFinite
  simp only at hx hy
  have hbaseValue : (if Model.signBit z.im then starRingEnd ℂ (toComplex z) else toComplex z) =
      ⟨(x : ℝ), (y : ℝ)⟩ := by
    rw [← hbase]
    cases hsign : Model.signBit z.im
    · simp
    · simp only [↓reduceIte]
      exact (toComplex_conj z hz).symm
  have hζ : (⟨(x : ℝ), (y : ℝ)⟩ : ℂ) ≠ 0 := by
    rw [← hbaseValue]
    cases Model.signBit z.im
    · simpa using hne
    · simpa using hne
  have hrat : ¬(x = 0 ∧ y = 0) := fun hzero => hζ (by rw [hzero.1, hzero.2]; simp; rfl)
  have hynonneg : 0 ≤ y := by
    refine toRat?_nonneg_of_signBit hy ?_
    cases hsign : Model.signBit z.im
    · simpa using hsign
    · simp [signBit_neg hfmt, hsign]
  unfold powChecked at h ⊢
  simp only [hc, hd, hx, hy] at h ⊢
  by_cases hzero : c = 0 ∧ d = 0
  · rw [ite_eq_left hzero, powExact_eq hz hw hbaseValue hζ hexponent]
    obtain ⟨rfl, rfl⟩ := hzero
    simp only [Exact.round, powPartValue, Trig.eval, Rat.cast_zero, zero_mul, sub_zero, add_zero,
      Real.exp_zero, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, Model.roundReal_zero]
    rw [roundRat_eq_roundReal]
    simp
  · rw [ite_eq_right hzero, ite_eq_right hrat] at h ⊢
    by_cases hhalf : c = 1 / 2 ∧ d = 0
    · rw [ite_eq_left hhalf]
      obtain ⟨rfl, rfl⟩ := hhalf
      have hexp : toComplex w = (2⁻¹ : ℂ) := by
        rw [hexponent]
        apply Complex.ext <;> simp
      have hpow : powExact z w = sqrtExact z := by
        unfold powExact sqrtExact Exact.ofUpperHalf
        have hconj : starRingEnd ℂ (2⁻¹ : ℂ) = 2⁻¹ := by
          rw [map_inv₀, map_ofNat]
        rw [toComplex_conj w hw, hexp, hconj]
      rw [hpow]
      exact sqrt_eq hfmt hz mode
    · rw [ite_eq_right hhalf] at h ⊢
      rw [powExact_eq hz hw hbaseValue hζ hexponent, powRat_eq hfmt mode hrat hynonneg h]
      rfl

/--
For an IEEE descriptor, a certified `pow` of a finite base other than zero and a finite exponent
is the exact power with each part rounded once in the direction `mode`.
-/
theorem pow_eq (hfmt : fmt.isIEEE = true) {z w : ExecComplex fmt} (hz : isFinite z = true)
    (hw : isFinite w = true) (hne : toComplex z ≠ 0)
    (mode : Model.IEEERoundingMode := .nearest) (levels : Nat := 4)
    (h : powCertified z w mode levels = true) :
    pow z w mode levels = (powExact z w).round fmt mode :=
  powChecked_eq hfmt hz hw hne mode levels h

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
