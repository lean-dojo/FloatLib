/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Root.ScaleProof
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.FormatProof
import Mathlib.Tactic.Positivity.Finset

/-!
# Coefficient range for decimal square root

To find the square-root grid, halve the base-ten logarithm of the squared scaled value. The proofs
here use integer logarithm bounds and never approximate the square root.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- The square-root grid shift is large enough: a scaled radicand is below `10 ^ (2 * (p + shift))`,
so its root has at most `p` digits after the shift. -/
theorem sqrtScaleShift_upper (p : Nat) (x : ℚ) :
    x < (10 : ℚ) ^ (2 * (p + sqrtScaleShift p x)) :=
  rootScaleShift_upper p (by decide) x

/-- The square-root grid is never finer than the format's least quantum. -/
theorem sqrtQuantum_ge_min (f : Format) (x : ℚ) : f.minQuantum ≤ sqrtQuantum f x := by
  unfold sqrtQuantum
  omega

/-- A fitting square bounds the grid shift without computing its root. -/
theorem sqrtScaleShift_le_of_lt {p k : Nat} (hp : 0 < p) {x : ℚ} (hx : 0 ≤ x)
    (h : x < (10 : ℚ) ^ (2 * (p + k))) : sqrtScaleShift p x ≤ k :=
  rootScaleShift_le_of_lt hp (by decide) hx h

/-- Every valid representation of an exact root is on a grid no finer than the selected grid. -/
theorem sqrtQuantum_le_of_valid (f : Format) (s : Bool) (c : Nat) (q : Int)
    (hvalid : (Datum.finite s c q).Valid f) :
    sqrtQuantum f (((c : ℚ) * (10 : ℚ) ^ q) ^ 2) ≤ q := by
  have hcq := (Datum.valid_quantum_iff ..).mp hvalid
  have hc : (c : ℚ) * (10 : ℚ) ^ q < (f.coefficientBound : ℚ) * (10 : ℚ) ^ q :=
    mul_lt_mul_of_pos_right (by exact_mod_cast hcq.1) (zpow_pos (by norm_num) _)
  refine rootQuantum_le f (by decide : 0 < 2) (sq_nonneg _) hcq.2.1 ?_
  rw [Nat.cast_ofNat, mul_comm (2 : Int) q, zpow_mul, zpow_ofNat, ← mul_pow]
  exact pow_lt_pow_left₀ hc (mul_nonneg (Nat.cast_nonneg c) (zpow_pos (by norm_num) q).le)
    (by decide)

/-- The radicand scaled to the selected square-root grid is strictly below the squared coefficient
bound, so its root has at most `precision` digits. -/
theorem div_sqrtQuantum_lt (f : Format) (x : ℚ) :
    x / (10 : ℚ) ^ (2 * sqrtQuantum f x) < (f.coefficientBound : ℚ) ^ 2 :=
  div_rootQuantum_lt f (by decide) x

/-- A nonzero square-root grid shift retains a full leading digit before rounding. -/
theorem sqrtScaleShift_lower {p : Nat} (hp : 0 < p) {x : ℚ}
    (hk : 0 < sqrtScaleShift p x) :
    (10 : ℚ) ^ (2 * (p + sqrtScaleShift p x - 1)) ≤ x :=
  rootScaleShift_lower hp hk

/-- Above the subnormal grid, the scaled radicand is at least the square of a full leading digit. -/
theorem payloadBound_sq_le_div_sqrtQuantum (f : Format) {x : ℚ}
    (hq : f.minQuantum < sqrtQuantum f x) :
    (f.payloadBound : ℚ) ^ 2 ≤ x / (10 : ℚ) ^ (2 * sqrtQuantum f x) :=
  payloadBound_pow_le_div_rootQuantum f hq

end FloatLib.Floats.Formats.DecimalInterchange
