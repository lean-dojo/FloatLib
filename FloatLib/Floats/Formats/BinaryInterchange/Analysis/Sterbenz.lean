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

Sterbenz's lemma holds on the rounded-real grid of every `fmt`: two same-sign representable values
within a factor of two have a representable difference, so subtracting them loses nothing. For an
IEEE descriptor, subtraction of the corresponding finite model values is finite and decodes to
that exact real difference. The factor-of-two bounds force nonnegative operands and include zero,
and the same-sign forms cover negative operands as well.

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
Sterbenz exactness for the rounded-real grid selected by `fmt`: two representable reals within a
factor of two of each other have a representable difference, so nearest-even rounding changes
nothing. The bounds force both reals to be nonnegative and include the zero case.

The same-sign variant below also covers negative operands.
-/
theorem roundAt_sub_eq_of_sterbenz (fmt : FloatFormat) {u v : ℝ}
    (hu : genericFormat Numerics.binaryRadix (fexpOf fmt) u)
    (hv : genericFormat Numerics.binaryRadix (fexpOf fmt) v)
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
        hprec huv hvu hu hv)
  exact round_preserves_generic nearestEven (u - v) hfmt

/-- Same-sign finite subtraction cannot overflow, independently of the factor-of-two condition. -/
theorem isFinite_sub_of_same_sign {fmt : FloatFormat} {x y : Model fmt}
    (hfmt : fmt.isIEEE = true) (hx : isFinite x = true) (hy : isFinite y = true)
    (hsign : 0 ≤ toReal x * toReal y) :
    isFinite (sub x y) = true := by
  have hbx := abs_toReal_le_posMaxFinite_of_isFinite x hx
  have hby := abs_toReal_le_posMaxFinite_of_isFinite y hy
  apply isFinite_sub_of_abs_toReal_sub_le_posMaxFinite x y hfmt hx hy
  rw [abs_le]
  rcases mul_nonneg_iff.mp hsign with ⟨hx0, hy0⟩ | ⟨hx0, hy0⟩
  · rw [abs_of_nonneg hx0] at hbx
    rw [abs_of_nonneg hy0] at hby
    constructor <;> linarith
  · rw [abs_of_nonpos hx0] at hbx
    rw [abs_of_nonpos hy0] at hby
    constructor <;> linarith

/-- Sterbenz exactness for representable reals of the same sign within a factor of two. -/
theorem roundAt_sub_eq_of_sterbenz_of_same_sign (fmt : FloatFormat) {u v : ℝ}
    (hu : genericFormat Numerics.binaryRadix (fexpOf fmt) u)
    (hv : genericFormat Numerics.binaryRadix (fexpOf fmt) v)
    (hsign : 0 ≤ u * v)
    (huv : |u| ≤ 2 * |v|) (hvu : |v| ≤ 2 * |u|) :
    roundAt fmt (u - v) = u - v := by
  rcases mul_nonneg_iff.mp hsign with ⟨hu0, hv0⟩ | ⟨hu0, hv0⟩
  · rw [abs_of_nonneg hu0, abs_of_nonneg hv0] at huv hvu
    exact roundAt_sub_eq_of_sterbenz fmt hu hv huv hvu
  · rw [abs_of_nonpos hu0, abs_of_nonpos hv0] at huv hvu
    -- Negation preserves representability and transports the negative case to nonnegative values.
    have h := roundAt_sub_eq_of_sterbenz fmt
      (generic_format_neg u hu) (generic_format_neg v hv) huv hvu
    rw [show -u - -v = -(u - v) by ring, roundAt_neg, IEEERoundingMode.negate] at h
    linarith

/--
Subtraction of finite values of the same sign within a factor of two has the exact real
difference. The real-valued statement includes both signs of zero.
-/
theorem toReal_sub_eq_of_sterbenz_of_same_sign {fmt : FloatFormat} {x y : Model fmt}
    (hfmt : fmt.isIEEE = true) (hx : isFinite x = true) (hy : isFinite y = true)
    (hsign : 0 ≤ toReal x * toReal y)
    (hxy : |toReal x| ≤ 2 * |toReal y|) (hyx : |toReal y| ≤ 2 * |toReal x|) :
    toReal (sub x y) = toReal x - toReal y := by
  rw [toReal_sub_eq_roundAt x y hfmt
    (isFinite_sub_of_same_sign hfmt hx hy hsign)]
  exact roundAt_sub_eq_of_sterbenz_of_same_sign fmt
    (toReal_genericFormat_of_isFinite x hx) (toReal_genericFormat_of_isFinite y hy)
    hsign hxy hyx

/--
Subtraction of positive executable values within a factor of two has no rounding error.

Positive real values are finite, since non-finite values decode to zero, so this is the
same-sign theorem for positive operands. Finiteness of the executable result is derived instead of
assumed: operands of the same sign cannot overflow when subtracted.
-/
theorem toReal_sub_eq_of_sterbenz {fmt : FloatFormat} {x y : Model fmt}
    (hfmt : fmt.isIEEE = true)
    (hxpos : 0 < toReal x) (hypos : 0 < toReal y)
    (hxy : toReal x ≤ 2 * toReal y) (hyx : toReal y ≤ 2 * toReal x) :
    toReal (sub x y) = toReal x - toReal y := by
  have hfinite {z : Model fmt} (hz : 0 < toReal z) : isFinite z = true := by
    rw [← toDyadic?_isSome_eq_isFinite]
    cases hd : toDyadic? z
    · simp [toReal_eq, hd] at hz
    · rfl
  exact toReal_sub_eq_of_sterbenz_of_same_sign hfmt (hfinite hxpos) (hfinite hypos)
    (mul_nonneg hxpos.le hypos.le) (by rwa [abs_of_pos hxpos, abs_of_pos hypos])
    (by rwa [abs_of_pos hxpos, abs_of_pos hypos])

end Model
end FloatLib.Floats.Formats.BinaryInterchange
