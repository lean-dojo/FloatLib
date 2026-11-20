/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.KernelPath.Encoding
public import FloatLib.Floats.Formats.P3109.Arithmetic.Runtime
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The kernel P3109 arithmetic computes the reference arithmetic

P3109 Interim Report v4.1 (14 September 2026), §4.10, an unapproved draft. The exact closed
operations of the report act on classes and ratios of natural numbers without normalization:

* `negate_closed`, `abs_closed`, `add_closed`, `multiply_closed`, `divide_closed`: the closed
  value of `Arithmetic.Negate`, `Abs`, `Add`, `Multiply` and `Divide` on closed values given by
  class, sign and ratio, with the report's results for infinities, NaN and a zero divisor;
* `add_eq`, `mul_eq`, `div_eq`, `fma_eq`, `convert_eq`: `KernelPath.add`, `mul`, `div`, `fma`
  and `convert` on encodings store the reference `Add`, `Subtract`, `Multiply`, `Divide`,
  `FMA`, `Negate`, `Abs` and the plain projection, for independent operand and destination
  descriptors, every rounding mode with every random word and every saturation mode;
* `recip_eq`, `faa_eq`, `copySign_eq`: the same for `Recip`, `FAA` and `CopySign`, the last
  through `copySign_closed`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.KernelPath

open FloatLib.Numerics FloatLib.Numerics.Kernel
open FloatLib.Floats.Formats.P3109

/-! ## Closed operations on classes and ratios -/

/-- The sign bit of a stored code is at most one. -/
theorem signOf_le (K sg a : Nat) : signOf K sg a ≤ 1 := by
  unfold signOf
  kernel_notation
  split_ifs <;> omega

/-- The denominator of a stored code is a power of two, so it is not zero. -/
theorem denominatorOf_ne_zero (K P sg a : Nat) : denominatorOf K P sg a ≠ 0 := by
  unfold denominatorOf
  kernel_notation
  exact Nat.ne_of_gt (Nat.two_pow_pos _)

/-- P3109 interim report v4.1, §4.10.1: negation exchanges the infinities and flips the sign of
    a ratio. -/
theorem negate_closed (c s n d : Nat) (hs : s ≤ 1) :
    Arithmetic.Negate (closed c s n d) = closed (negClass c) (1 - s) n d := by
  unfold negClass closed
  kernel_notation
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;>
    by_cases h0 : c = 0 <;> by_cases h1 : c = 1 <;> by_cases h2 : c = 2 <;>
    simp [h0, h1, h2, Arithmetic.Negate, Arithmetic.nan, neg_div]

/-- P3109 interim report v4.1, §4.10.1: the absolute value maps `-∞` to `+∞` and clears the sign
    of a ratio. -/
theorem abs_closed (c s n d : Nat) :
    Arithmetic.Abs (closed c s n d) = closed (if c = 2 then 1 else c) 0 n d := by
  unfold closed
  have hnonneg : (0 : Rat) ≤ (n : Rat) / (d : Rat) :=
    div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg d)
  by_cases h0 : c = 0
  · subst h0
    simp only [ite_true, Arithmetic.Abs, OfNat.zero_ne_ofNat, ite_false]
    congr 1
    by_cases hs : s = 0
    · simp [hs, not_lt.mpr hnonneg]
    · simp only [hs, ite_false, neg_div, neg_neg]
      split_ifs with hlt
      · rfl
      · have : (n : Rat) / (d : Rat) = 0 := by linarith
        rw [this, neg_zero]
  · by_cases h1 : c = 1 <;> by_cases h2 : c = 2 <;>
      simp [h0, h1, h2, Arithmetic.Abs, Arithmetic.nan]

/-- The sign bit of a sum is one of the sign bits of its terms. -/
theorem addSign_le (sa sb a b : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1) : addSign sa sb a b ≤ 1 := by
  unfold addSign
  kernel_notation
  split_ifs <;> assumption

/-- The sum of two signed ratios, on the cross products of their terms. -/
theorem add_ratio (sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1) (hda : da ≠ 0)
    (hdb : db ≠ 0) :
    (if sa = 0 then (na : Rat) else -(na : Rat)) / (da : Rat) +
        (if sb = 0 then (nb : Rat) else -(nb : Rat)) / (db : Rat) =
      (if addSign sa sb (na * db) (nb * da) = 0 then
          ((addMagnitude sa sb (na * db) (nb * da) : Nat) : Rat)
        else -((addMagnitude sa sb (na * db) (nb * da) : Nat) : Rat)) /
        ((da * db : Nat) : Rat) := by
  have hda' : (da : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hda
  have hdb' : (db : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hdb
  unfold addSign addMagnitude
  kernel_notation
  by_cases hle : nb * da ≤ na * db
  · have hsub : nb * da - na * db = 0 := Nat.sub_eq_zero_of_le hle
    rcases (by omega : sa = 0 ∨ sa = 1) with rfl | rfl <;>
      rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
      simp only [hle, hsub, ite_true, ite_false, Nat.add_zero, Nat.one_ne_zero, Nat.zero_ne_one] <;>
      push_cast [Nat.cast_sub hle] <;> field_simp <;> ring
  · have hlt : na * db ≤ nb * da := Nat.le_of_not_le hle
    have hsub : na * db - nb * da = 0 := Nat.sub_eq_zero_of_le hlt
    rcases (by omega : sa = 0 ∨ sa = 1) with rfl | rfl <;>
      rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
      simp only [hle, hsub, ite_true, ite_false, Nat.zero_add, Nat.one_ne_zero, Nat.zero_ne_one] <;>
      push_cast [Nat.cast_sub hlt] <;> field_simp <;> ring

/--
P3109 interim report v4.1, §4.10.3: the exact sum of two closed values given by class, sign and
    ratio, with
NaN for a NaN operand and for opposite infinities.
-/
theorem add_closed (ca cb sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1) (hda : da ≠ 0)
    (hdb : db ≠ 0) :
    Arithmetic.Add (closed ca sa na da) (closed cb sb nb db) =
      closed (addClass ca cb) (addSign sa sb (na * db) (nb * da))
        (addMagnitude sa sb (na * db) (nb * da)) (da * db) := by
  have hratio := add_ratio sa sb na nb da db hsa hsb hda hdb
  unfold addClass closed
  kernel_notation
  simp only [Bool.or_eq_true, Nat.ble_eq]
  rcases (by omega : ca = 0 ∨ ca = 1 ∨ ca = 2 ∨ 3 ≤ ca) with rfl | rfl | rfl | ha <;>
    rcases (by omega : cb = 0 ∨ cb = 1 ∨ cb = 2 ∨ 3 ≤ cb) with rfl | rfl | rfl | hb
  all_goals first
    | (simp [Arithmetic.Add, Arithmetic.nan, hratio]; done)
    | (have h1 : ¬ca = 0 := by omega
       have h2 : ¬ca = 1 := by omega
       have h3 : ¬ca = 2 := by omega
       simp [Arithmetic.Add, Arithmetic.nan, h1, h2, h3, ha])
    | (have h1 : ¬cb = 0 := by omega
       have h2 : ¬cb = 1 := by omega
       have h3 : ¬cb = 2 := by omega
       simp [Arithmetic.Add, Arithmetic.nan, h1, h2, h3, hb])

/-- A signed ratio with a nonzero denominator is zero exactly when its numerator is. -/
theorem ratio_eq_zero_iff (s n d : Nat) (hd : d ≠ 0) :
    (if s = 0 then (n : Rat) else -(n : Rat)) / (d : Rat) = 0 ↔ n = 0 := by
  have hd' : (d : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hd
  rw [div_eq_zero_iff]
  split_ifs <;> simp [hd']

/-- A signed ratio with a nonzero denominator is negative exactly when its sign bit is set and
its numerator is not zero. -/
theorem ratio_neg_iff (s n d : Nat) (hs : s ≤ 1) (hd : d ≠ 0) :
    (if s = 0 then (n : Rat) else -(n : Rat)) / (d : Rat) < 0 ↔ s = 1 ∧ n ≠ 0 := by
  have hd' : (0 : Rat) < (d : Rat) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd)
  rw [div_lt_iff₀ hd', zero_mul]
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
  · simp
  · simp [Nat.pos_iff_ne_zero]

/-- The product of two signed ratios. -/
theorem mul_ratio (sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1) :
    (if sa = 0 then (na : Rat) else -(na : Rat)) / (da : Rat) *
        ((if sb = 0 then (nb : Rat) else -(nb : Rat)) / (db : Rat)) =
      (if Nat.xor sa sb = 0 then ((na * nb : Nat) : Rat) else -((na * nb : Nat) : Rat)) /
        ((da * db : Nat) : Rat) := by
  rcases (by omega : sa = 0 ∨ sa = 1) with rfl | rfl <;>
    rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
    simp [div_mul_div_comm]

/-- A closed value of a nonzero class does not depend on its sign and ratio. -/
theorem closed_of_ne_zero {c : Nat} (hc : c ≠ 0) (s n d : Nat) :
    closed c s n d = closed c 0 0 1 := by
  unfold closed
  simp [hc]

/-- The product or quotient of an infinity and a finite ratio: NaN for a zero ratio, and the
infinity with the product sign otherwise (§4.10.4, §4.10.5). The sign and the ratio of the
closed value on the right are arbitrary, since its class is not zero. -/
theorem infinity_ratio (negative : Bool) (s n d : Nat) (hs : s ≤ 1) (hd : d ≠ 0)
    (s' n' d' : Nat) :
    (if ((if s = 0 then (n : Rat) else -(n : Rat)) / (d : Rat) == 0) = true then Arithmetic.nan
      else NumericalValue.infinity
        (negative != decide ((if s = 0 then (n : Rat) else -(n : Rat)) / (d : Rat) < 0))) =
      closed (if n = 0 then 3 else ((if negative then 1 else 0) ^^^ s) + 1) s' n' d' := by
  have hzero := ratio_eq_zero_iff s n d hd
  have hneg := ratio_neg_iff s n d hs hd
  rw [closed_of_ne_zero (by split_ifs <;> omega) s' n' d']
  by_cases hn : n = 0
  · rw [ite_eq_left (by simpa using hzero.2 hn), ite_eq_left hn]
    rfl
  · rw [ite_eq_right (by simpa using fun h => hn (hzero.1 h)), ite_eq_right hn]
    have hdec : decide ((if s = 0 then (n : Rat) else -(n : Rat)) / (d : Rat) < 0) =
        decide (s = 1) := by
      rw [decide_eq_decide, hneg]
      exact ⟨fun h => h.1, fun h => ⟨h, hn⟩⟩
    rw [hdec]
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> cases negative <;> rfl

/--
P3109 interim report v4.1, §4.10.4: the exact product of two closed values given by class, sign
    and ratio,
with NaN for a NaN operand and for zero times infinity.
-/
theorem multiply_closed (ca cb sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1)
    (hda : da ≠ 0) (hdb : db ≠ 0) :
    Arithmetic.Multiply (closed ca sa na da) (closed cb sb nb db) =
      closed (mulClass ca cb sa sb na nb) (Nat.xor sa sb) (na * nb) (da * db) := by
  have hratio := mul_ratio sa sb na nb da db hsa hsb
  have hia (negative : Bool) :=
    infinity_ratio negative sa na da hsa hda (Nat.xor sa sb) (na * nb) (da * db)
  have hib (negative : Bool) :=
    infinity_ratio negative sb nb db hsb hdb (Nat.xor sa sb) (na * nb) (da * db)
  unfold mulClass
  kernel_notation
  simp only [Bool.or_eq_true, Nat.ble_eq]
  rcases (by omega : ca = 0 ∨ ca = 1 ∨ ca = 2 ∨ 3 ≤ ca) with rfl | rfl | rfl | ha
  · rcases (by omega : cb = 0 ∨ cb = 1 ∨ cb = 2 ∨ 3 ≤ cb) with rfl | rfl | rfl | hb
    · simp [closed, Arithmetic.Multiply, hratio]
    · refine Eq.trans ?_ ((hia false).trans ?_)
      · simp [closed, Arithmetic.Multiply]
      · congr 1
    · refine Eq.trans ?_ ((hia true).trans ?_)
      · simp [closed, Arithmetic.Multiply]
      · congr 1
    · have h1 : ¬cb = 0 := by omega
      have h2 : ¬cb = 1 := by omega
      have h3 : ¬cb = 2 := by omega
      simp [closed, Arithmetic.Multiply, Arithmetic.nan, h1, h2, h3, hb]
  · rcases (by omega : cb = 0 ∨ cb = 1 ∨ cb = 2 ∨ 3 ≤ cb) with rfl | rfl | rfl | hb
    · refine Eq.trans ?_ ((hib false).trans ?_)
      · simp [closed, Arithmetic.Multiply]
      · congr 1
    · simp [closed, Arithmetic.Multiply]
    · simp [closed, Arithmetic.Multiply]
    · have h1 : ¬cb = 0 := by omega
      have h2 : ¬cb = 1 := by omega
      have h3 : ¬cb = 2 := by omega
      simp [closed, Arithmetic.Multiply, Arithmetic.nan, h1, h2, h3, hb]
  · rcases (by omega : cb = 0 ∨ cb = 1 ∨ cb = 2 ∨ 3 ≤ cb) with rfl | rfl | rfl | hb
    · refine Eq.trans ?_ ((hib true).trans ?_)
      · simp [closed, Arithmetic.Multiply]
      · congr 1
    · simp [closed, Arithmetic.Multiply]
    · simp [closed, Arithmetic.Multiply]
    · have h1 : ¬cb = 0 := by omega
      have h2 : ¬cb = 1 := by omega
      have h3 : ¬cb = 2 := by omega
      simp [closed, Arithmetic.Multiply, Arithmetic.nan, h1, h2, h3, hb]
  · have h1 : ¬ca = 0 := by omega
    have h2 : ¬ca = 1 := by omega
    have h3 : ¬ca = 2 := by omega
    simp [closed, Arithmetic.Multiply, Arithmetic.nan, h1, h2, h3, ha]

/-- The quotient of two signed ratios with a nonzero divisor. -/
theorem div_ratio (sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1) :
    (if sa = 0 then (na : Rat) else -(na : Rat)) / (da : Rat) /
        ((if sb = 0 then (nb : Rat) else -(nb : Rat)) / (db : Rat)) =
      (if Nat.xor sa sb = 0 then ((na * db : Nat) : Rat) else -((na * db : Nat) : Rat)) /
        ((da * nb : Nat) : Rat) := by
  rcases (by omega : sa = 0 ∨ sa = 1) with rfl | rfl <;>
    rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
    simp [div_div_div_eq, neg_div, div_neg]

/--
P3109 interim report v4.1, §4.10.5: the exact quotient of two closed values given by class, sign
    and ratio,
with NaN for a NaN operand, for a zero divisor and for two infinities, and zero for a finite
value over an infinity.
-/
theorem divide_closed (ca cb sa sb na nb da db : Nat) (hsa : sa ≤ 1) (hsb : sb ≤ 1)
    (hdb : db ≠ 0) :
    Arithmetic.Divide (closed ca sa na da) (closed cb sb nb db) =
      closed (divClass ca cb sb nb) (Nat.xor sa sb) (if cb = 0 then na * db else 0)
        (if cb = 0 then da * nb else 1) := by
  have hratio := div_ratio sa sb na nb da db hsa hsb
  have hzero := ratio_eq_zero_iff sb nb db hdb
  have hib (negative : Bool) :=
    infinity_ratio negative sb nb db hsb hdb (Nat.xor sa sb) (na * db) (da * nb)
  unfold divClass
  kernel_notation
  simp only [Bool.or_eq_true, Nat.ble_eq]
  rcases (by omega : ca = 0 ∨ ca = 1 ∨ ca = 2 ∨ 3 ≤ ca) with rfl | rfl | rfl | ha
  · rcases (by omega : cb = 0 ∨ cb = 1 ∨ cb = 2 ∨ 3 ≤ cb) with rfl | rfl | rfl | hb
    · by_cases hn : nb = 0
      · simp [closed, Arithmetic.Divide, Arithmetic.nan, hn]
      · have hz : ¬(if sb = 0 then (nb : Rat) else -(nb : Rat)) / (db : Rat) = 0 :=
          fun h => hn (hzero.1 h)
        simp only [closed, Arithmetic.Divide, ite_true, beq_iff_eq, hz, ite_false, hratio]
        simp [hn]
    · simp [closed, Arithmetic.Divide]
    · simp [closed, Arithmetic.Divide]
    · have h1 : ¬cb = 0 := by omega
      have h2 : ¬cb = 1 := by omega
      have h3 : ¬cb = 2 := by omega
      simp [closed, Arithmetic.Divide, Arithmetic.nan, h1, h2, h3, hb]
  · rcases (by omega : cb = 0 ∨ cb = 1 ∨ cb = 2 ∨ 3 ≤ cb) with rfl | rfl | rfl | hb
    · refine Eq.trans ?_ ((hib false).trans ?_)
      · simp [closed, Arithmetic.Divide]
      · congr 1
    · simp [closed, Arithmetic.Divide, Arithmetic.nan]
    · simp [closed, Arithmetic.Divide, Arithmetic.nan]
    · have h1 : ¬cb = 0 := by omega
      have h2 : ¬cb = 1 := by omega
      have h3 : ¬cb = 2 := by omega
      simp [closed, Arithmetic.Divide, Arithmetic.nan, h1, h2, h3, hb]
  · rcases (by omega : cb = 0 ∨ cb = 1 ∨ cb = 2 ∨ 3 ≤ cb) with rfl | rfl | rfl | hb
    · refine Eq.trans ?_ ((hib true).trans ?_)
      · simp [closed, Arithmetic.Divide]
      · congr 1
    · simp [closed, Arithmetic.Divide, Arithmetic.nan]
    · simp [closed, Arithmetic.Divide, Arithmetic.nan]
    · have h1 : ¬cb = 0 := by omega
      have h2 : ¬cb = 1 := by omega
      have h3 : ¬cb = 2 := by omega
      simp [closed, Arithmetic.Divide, Arithmetic.nan, h1, h2, h3, hb]
  · have h1 : ¬ca = 0 := by omega
    have h2 : ¬ca = 1 := by omega
    have h3 : ¬ca = 2 := by omega
    simp [closed, Arithmetic.Divide, Arithmetic.nan, h1, h2, h3, ha]

/-! ## The operations on encodings -/

/-- The exclusive or of two sign bits is a sign bit. -/
theorem xor_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : Nat.xor a b ≤ 1 := by
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;>
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> decide

variable {leftFormat rightFormat thirdFormat : Format}

/--
P3109 interim report v4.1, §4.10.3: `add` on two encodings stores the reference sum (`flip = 0`)
    of two values
of independent formats, projected once into the destination, for every descriptor, rounding
mode, random word, saturation mode and pair of operands.
-/
theorem add_eq (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.Add x y target mode saturation =
      ExecFloat.P3109.ofNatBits
        (add leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) 0 x.toNatBits y.toNatBits) := by
  unfold ExecFloat.P3109.Add ExecFloat.P3109.binary
  rw [toClosedRat_eq x, toClosedRat_eq y,
    add_closed _ _ _ _ _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _) (denominatorOf_ne_zero _ _ _ _)
      (denominatorOf_ne_zero _ _ _ _),
    projectRat_eq _ _ _ _ _ _ _ (addSign_le _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _))
      (fun _ _ => Nat.mul_ne_zero (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _))]
  rfl

/--
P3109 interim report v4.1, §4.10.3: `add` with `flip = 1` stores the reference difference, with
    no projection
of the negated operand.
-/
theorem sub_eq (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.Subtract x y target mode saturation =
      ExecFloat.P3109.ofNatBits
        (add leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) 1 x.toNatBits y.toNatBits) := by
  unfold ExecFloat.P3109.Subtract ExecFloat.P3109.binary Arithmetic.Subtract
  rw [toClosedRat_eq x, toClosedRat_eq y, negate_closed _ _ _ _ (signOf_le _ _ _),
    add_closed _ _ _ _ _ _ _ _ (signOf_le _ _ _) (Nat.sub_le _ _) (denominatorOf_ne_zero _ _ _ _)
      (denominatorOf_ne_zero _ _ _ _),
    projectRat_eq _ _ _ _ _ _ _ (addSign_le _ _ _ _ (signOf_le _ _ _) (Nat.sub_le _ _))
      (fun _ _ => Nat.mul_ne_zero (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _))]
  rfl

/--
P3109 interim report v4.1, §4.10.4: `mul` on two encodings stores the reference product of two
    values of
independent formats, projected once into the destination.
-/
theorem mul_eq (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.Multiply x y target mode saturation =
      ExecFloat.P3109.ofNatBits
        (mul leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits y.toNatBits) := by
  unfold ExecFloat.P3109.Multiply ExecFloat.P3109.binary
  rw [toClosedRat_eq x, toClosedRat_eq y,
    multiply_closed _ _ _ _ _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _)
      (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _),
    projectRat_eq _ _ _ _ _ _ _ (xor_le_one (signOf_le _ _ _) (signOf_le _ _ _))
      (fun _ _ => Nat.mul_ne_zero (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _))]
  rfl

set_option hygiene false in
/--
`ternary_eq name Op kernel Reference [rules] sign`, after a docstring, declares the theorem
`name`: the operation `Op` of the report on three encodings of independent formats stores the
kernel function `kernel` of the encodings. `rules` rewrite the reference operation `Reference`
on three closed values into one closed value, and `sign` bounds its sign bit.
-/
local macro doc:docComment "ternary_eq " name:ident op:ident kernel:ident reference:ident
    "[" rules:Lean.Parser.Tactic.rwRule,* "]" sign:term : command =>
  `($doc:docComment
    theorem $name (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat)
        (z : ExecFloat.P3109 thirdFormat) (target : Format) (mode : RoundingMode)
        (saturation : SaturationMode) :
        $op x y z target mode saturation =
          ExecFloat.P3109.ofNatBits
            ($kernel leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
              rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
              thirdFormat.bitWidth thirdFormat.precision (sgOf thirdFormat) (exOf thirdFormat)
              target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
              (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits y.toNatBits
              z.toNatBits) := by
      unfold $op ExecFloat.P3109.ternary $reference
      rw [toClosedRat_eq x, toClosedRat_eq y, toClosedRat_eq z, $rules,*,
        projectRat_eq _ _ _ _ _ _ _ $sign
          (fun _ _ => Nat.mul_ne_zero
            (Nat.mul_ne_zero (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _))
            (denominatorOf_ne_zero _ _ _ _))]
      rfl)

/--
P3109 interim report v4.1, §4.10.6: `fma` on three encodings stores the reference `x * y + z` of
values of independent formats, with no intermediate rounding, projected once into the
destination.
-/
ternary_eq fma_eq ExecFloat.P3109.FMA fma Arithmetic.FMA
  [multiply_closed _ _ _ _ _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _)
      (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _),
    add_closed _ _ _ _ _ _ _ _ (xor_le_one (signOf_le _ _ _) (signOf_le _ _ _)) (signOf_le _ _ _)
      (Nat.mul_ne_zero (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _))
      (denominatorOf_ne_zero _ _ _ _)]
  (addSign_le _ _ _ _ (xor_le_one (signOf_le _ _ _) (signOf_le _ _ _)) (signOf_le _ _ _))

/--
P3109 interim report v4.1, §4.10.1: `convert` with `flip = 1` stores the reference negation of a
    value,
projected once into the destination, which also covers a negative result in an unsigned format.
-/
theorem negate_eq (x : ExecFloat.P3109 leftFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.Negate x target mode saturation =
      ExecFloat.P3109.ofNatBits
        (convert leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) 1 x.toNatBits) := by
  unfold ExecFloat.P3109.Negate ExecFloat.P3109.unary
  rw [toClosedRat_eq x, negate_closed _ _ _ _ (signOf_le _ _ _),
    projectRat_eq _ _ _ _ _ _ _ (Nat.sub_le _ _) (fun _ _ => denominatorOf_ne_zero _ _ _ _)]
  rfl

/--
P3109 interim report v4.1, §4.7.3: `convert` with `flip = 0` stores the projection of the exact
    value of a
code of one format into another, the conversion between two descriptors.
-/
theorem convert_eq (x : ExecFloat.P3109 leftFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.projectRat (format := target) x.toClosedRat mode saturation =
      ExecFloat.P3109.ofNatBits
        (convert leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) 0 x.toNatBits) := by
  rw [toClosedRat_eq x,
    projectRat_eq _ _ _ _ _ _ _ (signOf_le _ _ _) (fun _ _ => denominatorOf_ne_zero _ _ _ _)]
  rfl

/-- A quotient of class zero by a finite divisor has a nonzero divisor numerator. -/
theorem divClass_eq_zero {ca sb nb : Nat} (h : divClass ca 0 sb nb = 0) : nb ≠ 0 := by
  unfold divClass at h
  intro hnb
  subst hnb
  simp [(FloatLib.Numerics.Kernel.Z.casesOn_eq_ite Iff.rfl)] at h

/--
P3109 interim report v4.1, §4.10.5: `div` on two encodings stores the reference quotient of two
    values of
independent formats, NaN for every zero divisor, projected once into the destination.
-/
theorem div_eq (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.Divide x y target mode saturation =
      ExecFloat.P3109.ofNatBits
        (div leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits y.toNatBits) := by
  unfold ExecFloat.P3109.Divide ExecFloat.P3109.binary
  rw [toClosedRat_eq x, toClosedRat_eq y,
    divide_closed _ _ _ _ _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _)
      (denominatorOf_ne_zero _ _ _ _),
    projectRat_eq _ _ _ _ _ _ _ (xor_le_one (signOf_le _ _ _) (signOf_le _ _ _)) (by
      intro hcls hn
      by_cases hcb : classOf rightFormat.bitWidth (sgOf rightFormat) (exOf rightFormat)
          y.toNatBits = 0
      · rw [hcb] at hcls
        rw [ite_eq_left hcb]
        exact Nat.mul_ne_zero (denominatorOf_ne_zero _ _ _ _) (divClass_eq_zero hcls)
      · rw [ite_eq_right hcb]
        exact Nat.one_ne_zero)]
  unfold div
  kernel_notation

/--
P3109 interim report v4.1, §4.10.1: `convert` with `flip = 2` stores the reference absolute
    value, projected
once into the destination.
-/
theorem abs_eq (x : ExecFloat.P3109 leftFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.Abs x target mode saturation =
      ExecFloat.P3109.ofNatBits
        (convert leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) 2 x.toNatBits) := by
  unfold ExecFloat.P3109.Abs ExecFloat.P3109.unary
  rw [toClosedRat_eq x, abs_closed,
    projectRat_eq _ _ _ _ _ _ _ (Nat.zero_le 1) (fun _ _ => denominatorOf_ne_zero _ _ _ _)]
  unfold convert
  kernel_notation
  simp

/-! ## Reciprocal, fused add-add and the copy of a sign -/

/-- The closed value one is the ratio of one and one. -/
theorem one_closed : NumericalValue.finite (1 : Rat) = closed 0 0 1 1 := by
  simp [closed]

/-- The exclusive or with a clear sign bit keeps the other sign bit. -/
theorem zero_xor (s : Nat) : Nat.xor 0 s = s := Nat.zero_xor s

/--
P3109 interim report v4.1, §4.10.8: `recip` on an encoding stores the reference reciprocal of
its value, NaN for zero, projected once into the destination, for every descriptor, rounding
mode, random word and saturation mode.
-/
theorem recip_eq (x : ExecFloat.P3109 leftFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.Recip x target mode saturation =
      ExecFloat.P3109.ofNatBits
        (recip leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits) := by
  unfold ExecFloat.P3109.Recip ExecFloat.P3109.unary Arithmetic.Recip
  rw [toClosedRat_eq x, one_closed,
    divide_closed _ _ _ _ _ _ _ _ (Nat.zero_le 1) (signOf_le _ _ _)
      (denominatorOf_ne_zero _ _ _ _),
    zero_xor,
    projectRat_eq _ _ _ _ _ _ _ (signOf_le _ _ _) (by
      intro hcls _
      by_cases hcb : classOf leftFormat.bitWidth (sgOf leftFormat) (exOf leftFormat)
          x.toNatBits = 0
      · rw [hcb] at hcls
        rw [ite_eq_left hcb]
        exact Nat.mul_ne_zero Nat.one_ne_zero (divClass_eq_zero hcls)
      · rw [ite_eq_right hcb]
        exact Nat.one_ne_zero)]
  unfold recip
  kernel_notation

/--
P3109 interim report v4.1, §4.10.7: `faa` on three encodings stores the reference `x + y + z` of
values of independent formats, with no intermediate rounding, projected once into the
destination.
-/
ternary_eq faa_eq ExecFloat.P3109.FAA faa Arithmetic.FAA
  [add_closed _ _ _ _ _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _) (denominatorOf_ne_zero _ _ _ _)
      (denominatorOf_ne_zero _ _ _ _),
    add_closed _ _ _ _ _ _ _ _ (addSign_le _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _))
      (signOf_le _ _ _)
      (Nat.mul_ne_zero (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _))
      (denominatorOf_ne_zero _ _ _ _)]
  (addSign_le _ _ _ _ (addSign_le _ _ _ _ (signOf_le _ _ _) (signOf_le _ _ _))
    (signOf_le _ _ _))

/-- `negativeOf` with the notation of the library. -/
theorem negativeOf_eq (c s n : Nat) :
    negativeOf c s n = if c = 0 then (if n = 0 then 0 else s) else if c = 2 then 1 else 0 := by
  unfold negativeOf
  kernel_notation

/-- The sign bit that `negativeOf` returns is at most one. -/
theorem negativeOf_le (c s n : Nat) (hs : s ≤ 1) : negativeOf c s n ≤ 1 := by
  rw [negativeOf_eq]
  split_ifs <;> omega

/-- The absolute value of a closed value, negated when the bit `neg` is set. -/
theorem signed_abs_closed (c s n d neg : Nat) (hneg : neg ≤ 1) :
    (if neg = 1 then Arithmetic.Negate (Arithmetic.Abs (closed c s n d))
      else Arithmetic.Abs (closed c s n d)) = closed (signedClass c neg) neg n d := by
  rw [abs_closed, negate_closed _ _ _ _ (Nat.zero_le 1)]
  unfold signedClass negClass
  kernel_notation
  simp only [Bool.or_eq_true, Nat.beq_eq]
  rcases (by omega : neg = 0 ∨ neg = 1) with rfl | rfl <;>
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ 3 ≤ c) with rfl | rfl | rfl | hc
  all_goals first
    | (simp; done)
    | (have h1 : ¬c = 1 := by omega
       have h2 : ¬c = 2 := by omega
       simp [h1, h2])

/--
P3109 interim report v4.1, §4.10.2: the closed value of `Arithmetic.CopySign` on closed values
given by class, sign and ratio: the magnitude of the first with the sign of the second, where a
zero counts as not negative, and NaN for a NaN second operand.
-/
theorem copySign_closed (ca cb sa sb na nb da db : Nat) (hsb : sb ≤ 1) (hdb : db ≠ 0) :
    Arithmetic.CopySign (closed ca sa na da) (closed cb sb nb db) =
      closed (if 3 ≤ cb then 3 else signedClass ca (negativeOf cb sb nb)) (negativeOf cb sb nb)
        na da := by
  have hneg := ratio_neg_iff sb nb db hsb hdb
  have hset := signed_abs_closed ca sa na da 1 (Nat.le_refl 1)
  have hclear := signed_abs_closed ca sa na da 0 (Nat.zero_le 1)
  rw [ite_eq_left rfl] at hset
  rw [ite_eq_right Nat.zero_ne_one] at hclear
  rw [negativeOf_eq]
  rcases (by omega : cb = 0 ∨ cb = 1 ∨ cb = 2 ∨ 3 ≤ cb) with rfl | rfl | rfl | hb
  · have hB : closed 0 sb nb db =
        NumericalValue.finite ((if sb = 0 then (nb : Rat) else -(nb : Rat)) / (db : Rat)) := by
      simp [closed]
    rw [hB]
    by_cases hr : (if sb = 0 then (nb : Rat) else -(nb : Rat)) / (db : Rat) < 0
    · obtain ⟨hs1, hn0⟩ := hneg.1 hr
      simp only [Arithmetic.CopySign, hr, ite_true]
      simpa [hn0, hs1] using hset
    · have hk : (if nb = 0 then 0 else sb) = 0 := by
        by_cases hn0 : nb = 0
        · rw [ite_eq_left hn0]
        · rw [ite_eq_right hn0]
          by_contra hs0
          exact hr (hneg.2 ⟨by omega, hn0⟩)
      simp only [Arithmetic.CopySign, hr, ite_false]
      simpa [hk] using hclear
  · have hB : closed 1 sb nb db = NumericalValue.infinity false := by simp [closed]
    rw [hB]
    simpa [Arithmetic.CopySign] using hclear
  · have hB : closed 2 sb nb db = NumericalValue.infinity true := by simp [closed]
    rw [hB]
    simpa [Arithmetic.CopySign] using hset
  · have h0 : ¬cb = 0 := by omega
    have h1 : ¬cb = 1 := by omega
    have h2 : ¬cb = 2 := by omega
    simp [closed, Arithmetic.CopySign, Arithmetic.nan, h0, h1, h2, hb]

/--
P3109 interim report v4.1, §4.10.2: `copySign` on two encodings stores the reference value of
the first with the sign of the second, projected once into the destination.
-/
theorem copySign_eq (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.CopySign x y target mode saturation =
      ExecFloat.P3109.ofNatBits
        (copySign leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits y.toNatBits) := by
  unfold ExecFloat.P3109.CopySign ExecFloat.P3109.binary
  rw [toClosedRat_eq x, toClosedRat_eq y,
    copySign_closed _ _ _ _ _ _ _ _ (signOf_le _ _ _) (denominatorOf_ne_zero _ _ _ _),
    projectRat_eq _ _ _ _ _ _ _ (negativeOf_le _ _ _ (signOf_le _ _ _))
      (fun _ _ => denominatorOf_ne_zero _ _ _ _)]
  unfold copySign
  kernel_notation

end FloatLib.Floats.Formats.P3109.KernelPath
