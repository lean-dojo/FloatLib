/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: Nicolas Rouquette, FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Analysis.SterbenzFLT
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Subtraction
public import Mathlib.Algebra.Order.Algebra

/-!
# Sterbenz exact subtraction

Sterbenz's lemma applies to the rounded-real grid of every `fmt`: two same-sign representable
values within a factor of two have an exactly representable difference. For an IEEE descriptor,
subtraction of the corresponding finite model values remains finite and decodes to that exact
real difference. The same-sign forms cover negative operands and zero as well.

## References

* R. P. Brent and P. Zimmermann, *Modern Computer Arithmetic*, Theorem 3.4.
  https://members.loria.fr/PZimmermann/mca/mca-cup-0.5.9.pdf
* Flocq, `Flocq.Prop.Sterbenz`.
  https://flocq.gitlabpages.inria.fr/flocq/html/Flocq.Prop.Sterbenz.html
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

/--
Sterbenz exactness for the rounded-real grid selected by `fmt`: two positive representable reals
within a factor of two have a representable difference, so nearest-even rounding changes nothing.

The nonnegative and same-sign variants below also cover zero and negative operands.
-/
theorem roundAt_sub_eq_of_sterbenz (fmt : FloatFormat) {u v : ℝ}
    (hu : genericFormat Numerics.binaryRadix (fexpOf fmt) u)
    (hv : genericFormat Numerics.binaryRadix (fexpOf fmt) v)
    (hupos : 0 < u) (hvpos : 0 < v)
    (huv : u ≤ 2 * v) (hvu : v ≤ 2 * u) :
    roundAt fmt (u - v) = u - v := by
  have hprec : (0 : Int) < Int.ofNat (fmt.fracWidth + 1) :=
    Int.natCast_pos.mpr (Nat.succ_pos fmt.fracWidth)
  have hfmt : genericFormat Numerics.binaryRadix (fexpOf fmt) (u - v) := by
    simpa [fexpOf] using
      (generic_format_FLT_sterbenz
        (β := Numerics.binaryRadix)
        (FloatFormat.minSubnormalExponent fmt)
        (Int.ofNat (fmt.fracWidth + 1))
        hprec hupos hvpos huv hvu hu hv)
  exact round_preserves_generic nearestEven (u - v) hfmt

/--
Subtraction of positive finite executable values within a factor of two has no rounding error.

The Sterbenz hypotheses also bound the exact difference by one of the finite operands, so
finiteness of the executable result follows rather than appearing as a separate premise.
-/
theorem toReal_sub_eq_of_sterbenz {fmt : FloatFormat} {x y : Model fmt}
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hxpos : 0 < toReal x) (hypos : 0 < toReal y)
    (hxy : toReal x ≤ 2 * toReal y) (hyx : toReal y ≤ 2 * toReal x) :
    toReal (sub x y) = toReal x - toReal y := by
  have hoperandBound :
      max (toReal x) (toReal y) ≤ toReal (posMaxFinite fmt) := by
    apply max_le
    · have hxBound :=
        abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite x hfmt hx
      simpa [abs_of_pos hxpos] using hxBound
    · have hyBound :=
        abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite y hfmt hy
      simpa [abs_of_pos hypos] using hyBound
  have hdifferenceBound :
      |toReal x - toReal y| ≤ toReal (posMaxFinite fmt) := by
    apply le_trans (b := max (toReal x) (toReal y))
    · by_cases horder : toReal x ≤ toReal y
      · rw [abs_of_nonpos (sub_nonpos.mpr horder)]
        simpa only [neg_sub] using
          (sub_le_self (toReal y) hxpos.le).trans
            (le_max_right (toReal x) (toReal y))
      · have hreverse : toReal y ≤ toReal x :=
          (lt_of_not_ge horder).le
        rw [abs_of_nonneg (sub_nonneg.mpr hreverse)]
        exact (sub_le_self _ hypos.le).trans (le_max_left _ _)
    · exact hoperandBound
  have hout : isFinite (sub x y) = true :=
    isFinite_sub_of_abs_toReal_sub_le_posMaxFinite
      x y hfmt hx hy hdifferenceBound
  rw [toReal_sub_eq_roundAt x y hfmt hx hy hout]
  exact roundAt_sub_eq_of_sterbenz fmt
    (toReal_genericFormat_of_isFinite x hx)
    (toReal_genericFormat_of_isFinite y hy)
    hxpos hypos hxy hyx

/-- Sterbenz exactness for nonnegative representable reals, including the zero case. -/
theorem roundAt_sub_eq_of_sterbenz_of_nonneg (fmt : FloatFormat) {u v : ℝ}
    (hu : genericFormat Numerics.binaryRadix (fexpOf fmt) u)
    (hv : genericFormat Numerics.binaryRadix (fexpOf fmt) v)
    (hupos : 0 ≤ u) (hvpos : 0 ≤ v)
    (huv : u ≤ 2 * v) (hvu : v ≤ 2 * u) :
    roundAt fmt (u - v) = u - v := by
  by_cases hu0 : u = 0
  · have hv0 : v = 0 := by linarith
    simp [hu0, hv0]
  · by_cases hv0 : v = 0
    · have hu0 : u = 0 := by linarith
      simp [hu0, hv0]
    · exact roundAt_sub_eq_of_sterbenz fmt hu hv
        (lt_of_le_of_ne hupos (Ne.symm hu0))
        (lt_of_le_of_ne hvpos (Ne.symm hv0)) huv hvu

/-- Sterbenz exactness for representable reals of the same sign within a factor of two. -/
theorem roundAt_sub_eq_of_sterbenz_of_same_sign (fmt : FloatFormat) {u v : ℝ}
    (hu : genericFormat Numerics.binaryRadix (fexpOf fmt) u)
    (hv : genericFormat Numerics.binaryRadix (fexpOf fmt) v)
    (hsign : 0 ≤ u * v)
    (huv : |u| ≤ 2 * |v|) (hvu : |v| ≤ 2 * |u|) :
    roundAt fmt (u - v) = u - v := by
  rcases mul_nonneg_iff.mp hsign with ⟨hu0, hv0⟩ | ⟨hu0, hv0⟩
  · rw [abs_of_nonneg hu0, abs_of_nonneg hv0] at huv hvu
    exact roundAt_sub_eq_of_sterbenz_of_nonneg fmt hu hv hu0 hv0 huv hvu
  · rw [abs_of_nonpos hu0, abs_of_nonpos hv0] at huv hvu
    -- Negation preserves representability and transports the negative case to nonnegative values.
    have h := roundAt_sub_eq_of_sterbenz_of_nonneg fmt
      (generic_format_neg u hu) (generic_format_neg v hv)
      (neg_nonneg.mpr hu0) (neg_nonneg.mpr hv0) huv hvu
    rw [show -u - -v = -(u - v) by ring, roundAt_neg] at h
    linarith

/-- Same-sign finite subtraction cannot overflow, independently of the factor-of-two condition. -/
theorem isFinite_sub_of_same_sign {fmt : FloatFormat} {x y : Model fmt}
    (hfmt : fmt.isIEEE = true) (hx : isFinite x = true) (hy : isFinite y = true)
    (hsign : 0 ≤ toReal x * toReal y) :
    isFinite (sub x y) = true := by
  have hbx := abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite x hfmt hx
  have hby := abs_toReal_le_posMaxFinite_of_isIEEE_of_isFinite y hfmt hy
  apply isFinite_sub_of_abs_toReal_sub_le_posMaxFinite x y hfmt hx hy
  rw [abs_le]
  rcases mul_nonneg_iff.mp hsign with ⟨hx0, hy0⟩ | ⟨hx0, hy0⟩
  · rw [abs_of_nonneg hx0] at hbx
    rw [abs_of_nonneg hy0] at hby
    constructor <;> linarith
  · rw [abs_of_nonpos hx0] at hbx
    rw [abs_of_nonpos hy0] at hby
    constructor <;> linarith

/--
Subtraction of finite values of the same sign within a factor of two has the exact real
difference. The real-valued statement includes both signs of zero.
-/
theorem toReal_sub_eq_of_sterbenz_of_same_sign {fmt : FloatFormat} {x y : Model fmt}
    (hfmt : fmt.isIEEE = true) (hx : isFinite x = true) (hy : isFinite y = true)
    (hsign : 0 ≤ toReal x * toReal y)
    (hxy : |toReal x| ≤ 2 * |toReal y|) (hyx : |toReal y| ≤ 2 * |toReal x|) :
    toReal (sub x y) = toReal x - toReal y := by
  rw [toReal_sub_eq_roundAt x y hfmt hx hy
    (isFinite_sub_of_same_sign hfmt hx hy hsign)]
  exact roundAt_sub_eq_of_sterbenz_of_same_sign fmt
    (toReal_genericFormat_of_isFinite x hx) (toReal_genericFormat_of_isFinite y hy)
    hsign hxy hyx

end Model
end FloatLib.Floats.Formats.BinaryInterchange
