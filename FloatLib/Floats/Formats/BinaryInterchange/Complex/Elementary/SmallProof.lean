/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.Small
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.PartsProof
public import FloatLib.Numerics.Enclosure.Elementary.Proof
public import FloatLib.Numerics.Enclosure.Trigonometric.AtanProof
public import FloatLib.Numerics.Enclosure.Trigonometric.SinCosProof
public import FloatLib.Numerics.Exact.Product.FactorsProof
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The small-argument enclosures contain the parts

Every enclosure that `Small` returns contains the real that it stands for, so a part keeps the
real that it denotes when one of them answers its comparisons (`Part.Denotes.within`):

* `contains_smallProduct?`: `growth a * trig b`;
* `contains_smallLog?`: `log q`;
* `contains_smallArg?`: the principal argument of `x + i y`, which is `arctan (y / x)` for a
  positive `x` (`arg_eq_arctan`);
* `contains_orElse`: the first of two optional enclosures that exists contains the real when
  both do;
* `dyadicAround_bounds`: the interval of `dyadicAround` contains its rational.

The remainder bounds are those of the Taylor enclosures: `Enclosure.contains_expSmall`,
`contains_sin`, `contains_cos`, `contains_logOneSub` and `contains_atanSmall`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace ExecComplex

open FloatLib.Numerics
open ProductComparison (Growth Trig)

variable {fmt : FloatFormat}

/-- The first of two optional enclosures that exists contains a real that both contain. -/
theorem contains_orElse {x : ℝ} {small general : Option RationalInterval}
    (hsmall : ∀ interval, small = some interval → interval.Contains x)
    (hgeneral : ∀ interval, general = some interval → interval.Contains x)
    (interval : RationalInterval) (h : (small <|> general) = some interval) :
    interval.Contains x := by
  cases small with
  | some first => exact hsmall _ (by simpa using h)
  | none => exact hgeneral _ (by simpa using h)

/-- An enclosure that `tightOnly` returns is the one it was given. -/
theorem eq_of_tightOnly {given interval : RationalInterval}
    (h : tightOnly fmt given = some interval) : given = interval := by
  unfold tightOnly at h
  split at h
  · exact Option.some.inj h
  · simp at h

/-- The interval of `dyadicAround` contains the rational. -/
theorem dyadicAround_bounds (q : Rat) (bits : Nat) :
    (dyadicAround q bits).lo ≤ q ∧ q ≤ (dyadicAround q bits).hi := by
  unfold dyadicAround
  generalize ((bits : Int) + (q.den.log2 : Int) - (q.num.natAbs.log2 : Int)) = shift
  have hpos : (0 : Rat) < (2 : Rat) ^ shift := zpow_pos (by norm_num) shift
  constructor
  · rw [div_le_iff₀ hpos]
    exact Int.floor_le _
  · rw [le_div_iff₀ hpos]
    push_cast
    exact (Int.lt_floor_add_one _).le

/-- `smallGrowth` contains the unbounded factor at an argument of magnitude at most one. -/
theorem contains_smallGrowth (growth : Growth) {a : Rat} (ha : |a| ≤ 1) (degree : Nat) :
    (smallGrowth growth a degree).Contains (growth.eval (a : ℝ)) := by
  have hpositive := Enclosure.contains_expSmall a degree ha
  have hnegative := Enclosure.contains_expSmall (-a) degree (by rwa [abs_neg])
  cases growth
  · exact hpositive
  · have hvalue : Growth.sinh.eval (a : ℝ) =
        ((1 / 2 : Rat) : ℝ) * (Real.exp (a : ℝ) - Real.exp ((-a : Rat) : ℝ)) := by
      change Real.sinh (a : ℝ) = _
      rw [Real.sinh_eq]
      push_cast
      ring
    rw [hvalue]
    exact RationalInterval.contains_scale
      (RationalInterval.contains_sub hpositive hnegative) (1 / 2)
  · have hvalue : Growth.cosh.eval (a : ℝ) =
        ((1 / 2 : Rat) : ℝ) * (Real.exp (a : ℝ) + Real.exp ((-a : Rat) : ℝ)) := by
      change Real.cosh (a : ℝ) = _
      rw [Real.cosh_eq]
      push_cast
      ring
    rw [hvalue]
    exact RationalInterval.contains_scale
      (RationalInterval.contains_add hpositive hnegative) (1 / 2)

/-- `smallTrig` contains the bounded factor. -/
theorem contains_smallTrig (trig : Trig) (b : Rat) (degree : Nat) :
    (smallTrig trig b degree).Contains (trig.eval (b : ℝ)) := by
  cases trig
  · exact Enclosure.contains_cos b degree
  · exact Enclosure.contains_sin b degree

/-- Every enclosure that `smallProduct?` returns contains the product. -/
theorem contains_smallProduct? {growth : Growth} {trig : Trig} {a b : Rat}
    {interval : RationalInterval} (h : smallProduct? fmt growth trig a b = some interval) :
    interval.Contains (growth.eval (a : ℝ) * trig.eval (b : ℝ)) := by
  unfold smallProduct? at h
  split at h
  · rename_i hsmall
    rw [← eq_of_tightOnly h]
    exact RationalInterval.contains_mul
      (contains_smallGrowth growth (hsmall.1.trans (by norm_num)) _)
      (contains_smallTrig trig b _)
  · simp at h

/-- Every enclosure that `smallLog?` returns contains the logarithm. -/
theorem contains_smallLog? {q : Rat} {interval : RationalInterval}
    (h : smallLog? fmt q = some interval) : interval.Contains (Real.log (q : ℝ)) := by
  unfold smallLog? at h
  split at h
  · rename_i hsmall
    rw [← eq_of_tightOnly h]
    have hcontains := Enclosure.contains_logOneSub (1 - q) (smallDegree fmt |1 - q|)
      (lt_of_le_of_lt hsmall (by norm_num))
    have hvalue : (1 : ℝ) - ((1 - q : Rat) : ℝ) = (q : ℝ) := by
      push_cast
      ring
    rwa [hvalue] at hcontains
  · simp at h

/-- The principal argument of a complex number with a positive real part is the arctangent of
the quotient of its parts. -/
theorem arg_eq_arctan {x y : ℝ} (hx : 0 < x) : Complex.arg ⟨x, y⟩ = Real.arctan (y / x) := by
  have habs : |Complex.arg ⟨x, y⟩| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have htan : Real.tan (Complex.arg ⟨x, y⟩) = y / x := Complex.tan_arg ⟨x, y⟩
  rw [← htan, Real.arctan_tan (abs_lt.mp habs).1 (abs_lt.mp habs).2]

/-- Every enclosure that `smallArg?` returns contains the principal argument. -/
theorem contains_smallArg? {x y : Rat} {interval : RationalInterval}
    (h : smallArg? fmt x y = some interval) :
    interval.Contains (Complex.arg ⟨(x : ℝ), (y : ℝ)⟩) := by
  unfold smallArg? at h
  split at h
  · rename_i hsmall
    obtain ⟨hx, hy⟩ := hsmall
    rw [← eq_of_tightOnly h, arg_eq_arctan (by exact_mod_cast hx)]
    have hquotient : |y / x| < 1 := by
      rw [abs_div, abs_of_pos hx, div_lt_one hx]
      exact lt_of_le_of_lt hy (by linarith)
    have hcontains := Enclosure.contains_atanSmall (y / x) (smallDegree fmt |y / x|) hquotient
    rwa [Rat.cast_div] at hcontains
  · simp at h

end ExecComplex
end FloatLib.Floats.Formats.BinaryInterchange
