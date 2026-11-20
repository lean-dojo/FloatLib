/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.KernelPath.Arithmetic
public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Runtime
public import FloatLib.Numerics.Kernel.RootProof
import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Literal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The kernel P3109 square roots compute the reference square roots

P3109 Interim Report v4.1 (14 September 2026), §§4.10.8 and 4.10.14, an unapproved draft. The
reference rounds the square root of a normalized rational on exact comparisons of squares. The
kernel does the same on a ratio of natural numbers as it is given:

* `sqrtQuantumOf_eq`: `sqrtQuantumOf` is the quantum exponent of the root, with its bias;
* `sqrtAway_eq`: `sqrtAway` is the reference decision `Arithmetic.sqrtRoundAway` in each of the
  nine modes, for every random word, and does not see a common factor of the two terms;
* `roundSqrtRatToPrecision_eq`: the reference rounding of the root of `n / d` is the dyadic
  with the significand `sqrtRoundedOf` at the quantum `sqrtQuantumOf`, for every descriptor,
  mode and ratio with `n ≠ 0` and `d ≠ 0`, whatever common factor `n` and `d` have;
* `projectSqrt_eq`: `projectSqrt` is the stored reference `ExecFloat.P3109.projectSqrt` of the
  closed value of a class and a ratio, for every saturation mode;
* `sqrt_eq`, `rsqrt_eq`, `hypot_eq`: `KernelPath.sqrt`, `rsqrt` and `hypot` on encodings store
  the reference `Sqrt`, `RSqrt` and `Hypot`, for independent operand and destination
  descriptors, every rounding mode with every random word and every saturation mode.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.KernelPath

open FloatLib.Numerics FloatLib.Numerics.Kernel
open FloatLib.Floats.Formats.P3109
open FloatLib.Floats.Formats.BinaryInterchange

/-! ## The quantum -/

/--
P3109 interim report v4.1, §4.10.8: `sqrtQuantumOf` is the quantum exponent
`max (⌊⌊log₂ (n / d)⌋ / 2⌋) (1 - B) - P + 1` of the square root of the ratio plus the bias
`log₂ d + 1 + B + P`, for every exponent bias `B` and precision `P`.
-/
theorem sqrtQuantumOf_eq (B P n d : Nat) (hn : n ≠ 0) (hd : d ≠ 0) :
    ((sqrtQuantumOf B n d : Nat) : Int) - ((d.log2 + 1 + (B + P) : Nat) : Int) =
      max (RationalBinary.floorLog2 n d / 2) (1 - (B : Int)) - (P : Int) + 1 := by
  rw [floorLog2_eq n d hn hd]
  unfold sqrtQuantumOf
  rw [size_sub_one hn, size_sub_one hd]
  kernel_notation
  simp only [Nat.add_one_le_iff]
  split_ifs <;> omega

/-! ## The rounding decision -/

/-- A comparison of natural numbers is not `lt` when the second is at most the first. -/
theorem compare_bne_lt (a b : Nat) : (compare a b != Ordering.lt) = decide (b ≤ a) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, Nat.compare_ne_lt, decide_eq_true_eq]

/-- A comparison of natural numbers is `gt` when the second is below the first. -/
theorem compare_beq_gt (a b : Nat) : (compare a b == Ordering.gt) = decide (b < a) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.compare_eq_gt, decide_eq_true_eq]

/-- A comparison of natural numbers is `eq` when they are equal. -/
theorem compare_beq_eq (a b : Nat) : (compare a b == Ordering.eq) = decide (a = b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.compare_eq_eq, decide_eq_true_eq]

/--
P3109 interim report v4.1, §4.7.4, for a square root: `sqrtAway` is the reference rounding
decision in each of the nine modes, for every supplied random word and parity, and for every
positive common factor `c` of the two terms of the scaled radicand.
-/
theorem sqrtAway_eq (format : Format) (mode : RoundingMode) (quantum : Int)
    (num den lower c : Nat) (hc : 0 < c) :
    sqrtAway (modeIndex mode) (modeWidth mode) (modeRandom mode)
        (if format.lowerCodeIsEven quantum lower then 1 else 0) (num * c) (den * c) lower =
      if Arithmetic.sqrtRoundAway format mode quantum num den lower then 1 else 0 := by
  have hexact : (num * c = den * c * lower ^ 2) ↔ (num = den * lower ^ 2) := by
    rw [Nat.mul_right_comm den c, Nat.mul_left_inj (Nat.ne_of_gt hc)]
  have hle (s t : Nat) : (den * c * t ≤ num * c * s) ↔ (den * t ≤ num * s) := by
    rw [Nat.mul_right_comm den c, Nat.mul_right_comm num c]
    exact Nat.mul_le_mul_right_iff hc
  have hlt (s t : Nat) : (den * c * t + 1 ≤ num * c * s) ↔ (den * t < num * s) := by
    rw [Nat.mul_right_comm den c, Nat.mul_right_comm num c]
    exact Nat.mul_lt_mul_right hc
  have heq (s t : Nat) : (num * c * s = den * c * t) ↔ (num * s = den * t) := by
    rw [Nat.mul_right_comm den c, Nat.mul_right_comm num c]
    exact Nat.mul_left_inj (Nat.ne_of_gt hc)
  unfold sqrtAway Arithmetic.sqrtRoundAway Format.roundMagnitudeUp Arithmetic.compareSqrt
  kernel_notation
  simp only [Nat.pow_eq, hexact, hle, hlt, heq, compare_bne_lt, compare_beq_gt, compare_beq_eq,
    beq_iff_eq]
  generalize format.lowerCodeIsEven quantum lower = even
  by_cases hex : num = den * lower ^ 2
  · simp [hex]
  simp only [hex, ↓reduceIte]
  cases mode <;> cases even <;>
    first
    | (simp [modeIndex, modeWidth, modeRandom]; done)
    | (simp only [modeIndex, modeWidth, modeRandom, Bool.and_eq_true, Bool.and_true,
        Bool.false_eq_true, Bool.not_false, Bool.or_eq_true, Nat.and_one_is_mod, Nat.reducePow,
        beq_iff_eq, decide_eq_true_eq, ite_self, tsub_self, tsub_zero, ↓reduceIte]
       first | rfl | (split_ifs <;> simp_all; omega))

/-! ## Rounding a root as its radicand is given -/

/--
P3109 interim report v4.1, §4.10.8: the reference precision rounding of the square root of the
ratio `n / d` is the dyadic with the significand `sqrtRoundedOf` at the quantum
`sqrtQuantumOf`, and zero when that significand is zero. This holds for every descriptor, every
rounding mode with every random word, and every ratio with `n ≠ 0` and `d ≠ 0`: the ratio need
not be in lowest terms.
-/
theorem roundSqrtRatToPrecision_eq (format : Format) (mode : RoundingMode) (n d : Nat)
    (hn : n ≠ 0) (hd : d ≠ 0) :
    Arithmetic.roundSqrtRatToPrecision format mode ((n : Rat) / (d : Rat)) =
      if sqrtRoundedOf format.precision format.exponentBias (modeIndex mode) (modeWidth mode)
          (modeRandom mode) n d (sqrtQuantumOf format.exponentBias n d) = 0 then
        Numerics.Dyadic.zero
      else
        { negative := false
          significand := sqrtRoundedOf format.precision format.exponentBias (modeIndex mode)
            (modeWidth mode) (modeRandom mode) n d (sqrtQuantumOf format.exponentBias n d)
          exponent := ((sqrtQuantumOf format.exponentBias n d : Nat) : Int) -
            ((d.log2 + 1 + (format.exponentBias + format.precision) : Nat) : Int) } := by
  obtain ⟨c, hc, hnc, hdc, -⟩ := exists_common_factor false n d hn hd
  simp only [Bool.false_eq_true, ite_false] at hnc hdc
  generalize (n : Rat) / (d : Rat) = q at hnc hdc ⊢
  have ha : q.num.natAbs ≠ 0 := by
    intro h
    rw [h, Nat.zero_mul] at hnc
    exact hn hnc
  have hfl : RationalBinary.floorLog2 q.num.natAbs q.den = RationalBinary.floorLog2 n d := by
    rw [hnc, hdc, KernelPath.floorLog2_mul_right _ _ c ha q.den_nz (by omega)]
  have hQ := sqrtQuantumOf_eq format.exponentBias format.precision n d hn hd
  have hmin : format.minimumNormalExponent = 1 - (format.exponentBias : Int) := rfl
  unfold Arithmetic.roundSqrtRatToPrecision Arithmetic.sqrtQuantum Arithmetic.sqrtFloor
  simp only [beq_iff_eq, ha, ite_false, hfl, hmin, Int.ofNat_eq_natCast, ← hQ,
    KernelPath.scaleByPowerOfTwo_eq_shifts]
  generalize sqrtQuantumOf format.exponentBias n d = Qb
  generalize hbeta : d.log2 + 1 + (format.exponentBias + format.precision) = beta
  have hs1 : (-2 * ((Qb : Int) - (beta : Int))).toNat = 2 * (beta - Qb) := by omega
  have hs2 : (-(-2 * ((Qb : Int) - (beta : Int)))).toNat = 2 * (Qb - beta) := by omega
  rw [hs1, hs2]
  unfold sqrtRoundedOf
  rw [size_sub_one hd]
  kernel_notation
  rw [isqrt_eq, hbeta, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have hnum : n * 2 ^ (2 * (beta - Qb)) = q.num.natAbs * 2 ^ (2 * (beta - Qb)) * c := by
    rw [hnc, Nat.mul_right_comm]
  have hden : d * 2 ^ (2 * (Qb - beta)) = q.den * 2 ^ (2 * (Qb - beta)) * c := by
    rw [hdc, Nat.mul_right_comm]
  rw [hnum, hden, Nat.mul_div_mul_right _ _ hc]
  have heven := even_eq format Qb beta
    (Nat.sqrt (q.num.natAbs * 2 ^ (2 * (beta - Qb)) / (q.den * 2 ^ (2 * (Qb - beta)))))
  rw [heven, sqrtAway_eq format mode _ _ _ _ c hc]
  generalize Nat.sqrt (q.num.natAbs * 2 ^ (2 * (beta - Qb)) / (q.den * 2 ^ (2 * (Qb - beta)))) =
    lower
  generalize Arithmetic.sqrtRoundAway format mode ((Qb : Int) - (beta : Int))
    (q.num.natAbs * 2 ^ (2 * (beta - Qb))) (q.den * 2 ^ (2 * (Qb - beta))) lower = away
  cases away <;> simp

/-! ## The square root of a closed value -/

/--
P3109 interim report v4.1, §4.10.8: `projectSqrt` is the reference code of the square root of
the closed value of a class and a ratio, rounded once, saturated and encoded, for every
descriptor, rounding mode, random word, saturation mode and input with a sign bit `s ≤ 1` and,
for a nonzero finite ratio, a denominator `d ≠ 0`.
-/
theorem sqrtCode_eq (format : Format) (mode : RoundingMode) (saturation : SaturationMode)
    (cls s n d : Nat) (hs : s ≤ 1) (hd : cls = 0 → n ≠ 0 → d ≠ 0) :
    Format.Internal.encodeDatumNat format
        (Arithmetic.sqrtValue format { rounding := mode, saturation } (closed cls s n d)) =
      projectSqrt format.bitWidth format.precision (sgOf format) (exOf format) (modeIndex mode)
        (modeWidth mode) (modeRandom mode) (satIndex saturation) cls s n d := by
  unfold projectSqrt
  kernel_notation
  by_cases h0 : cls = 0
  · subst h0
    rw [ite_eq_left rfl]
    by_cases hn : n = 0
    · subst hn
      rw [ite_eq_left rfl]
      have hval : Arithmetic.sqrtValue format { rounding := mode, saturation } (closed 0 s 0 d) =
          format.saturate saturation mode (.finite Numerics.Dyadic.zero) := by
        simp [Arithmetic.sqrtValue, Arithmetic.sqrtRounded, closed,
          Arithmetic.roundSqrtRatToPrecision]
      rw [hval]
      exact encode_saturate_zero format mode saturation
    · rw [ite_eq_right hn]
      have hdz := hd rfl hn
      rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
      · rw [ite_eq_left rfl]
        have hpos : ¬((n : Rat) / (d : Rat) < 0) :=
          not_lt.mpr (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg d))
        have hval : Arithmetic.sqrtValue format { rounding := mode, saturation }
            (closed 0 0 n d) =
            format.saturate saturation mode
              (.finite (Arithmetic.roundSqrtRatToPrecision format mode
                ((n : Rat) / (d : Rat)))) := by
          simp [Arithmetic.sqrtValue, Arithmetic.sqrtRounded, closed, hpos]
        rw [hval, roundSqrtRatToPrecision_eq format mode n d hn hdz,
          encodeRounded_eq format mode saturation false _ _ _ (by omega)]
        unfold projectSqrtFinite
        rw [exponentBias_eq, size_sub_one hdz]
        rfl
      · rw [ite_eq_right Nat.one_ne_zero, nanBits_eq]
        have hneg : -(n : Rat) / (d : Rat) < 0 := by
          have h := (ratio_neg_iff 1 n d (Nat.le_refl 1) hdz).2 ⟨rfl, hn⟩
          simpa using h
        have hval : Arithmetic.sqrtValue format { rounding := mode, saturation }
            (closed 0 1 n d) =
            format.saturate saturation mode (.exceptional .nan) := by
          simp [Arithmetic.sqrtValue, Arithmetic.sqrtRounded, closed, hneg]
        rw [hval]
        rfl
  · rw [ite_eq_right h0]
    by_cases h1 : cls = 1
    · subst h1
      rw [ite_eq_left rfl, ← project_eq format mode saturation 1 0 0 1 (Nat.zero_le 1)
        (fun h => absurd h Nat.one_ne_zero)]
      rfl
    · rw [ite_eq_right h1, ← project_eq format mode saturation 3 0 0 1 (Nat.zero_le 1)
        (fun h => absurd h (by decide))]
      have hval : Arithmetic.sqrtValue format { rounding := mode, saturation }
          (closed cls s n d) =
          format.projectRatValue { rounding := mode, saturation } (closed 3 0 0 1) := by
        by_cases h2 : cls = 2
        · subst h2
          rfl
        · simp [Arithmetic.sqrtValue, Arithmetic.sqrtRounded, closed, h0, h1, h2, Arithmetic.nan,
            Format.projectRatValue, Format.roundRatToPrecision]
      rw [hval]

/--
P3109 interim report v4.1, §4.10.8: the stored reference square root of the closed value of a
class and a ratio of natural numbers is the value that stores `projectSqrt`, for every
descriptor, rounding mode, random word, saturation mode and input.
-/
theorem projectSqrt_eq (format : Format) (mode : RoundingMode) (saturation : SaturationMode)
    (cls s n d : Nat) (hs : s ≤ 1) (hd : cls = 0 → n ≠ 0 → d ≠ 0) :
    ExecFloat.P3109.projectSqrt (format := format) (closed cls s n d) mode saturation =
      ExecFloat.P3109.ofNatBits
        (projectSqrt format.bitWidth format.precision (sgOf format) (exOf format)
          (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation) cls s n d) := by
  rw [← sqrtCode_eq format mode saturation cls s n d hs hd]
  rfl

/-! ## The radicands -/

/--
P3109 interim report v4.1, §4.10.8: the radicand of the reciprocal square root of a closed
value given by class, sign and ratio: the reciprocal ratio for a positive value, zero for `+∞`,
and NaN for zero, a negative value, `-∞` and NaN.
-/
theorem rsqrtRadicand_closed (c s n d : Nat) (hs : s ≤ 1) (hd : d ≠ 0) :
    Arithmetic.rsqrtRadicand (closed c s n d) =
      closed (if c = 0 then (if n = 0 ∨ s = 1 then 3 else 0) else if c = 1 then 0 else 3) 0
        (if c = 0 then d else 0) (if c = 0 then n else 1) := by
  have hzero := ratio_eq_zero_iff s n d hd
  have hneg := ratio_neg_iff s n d hs hd
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ 3 ≤ c) with rfl | rfl | rfl | hc
  · have hB : closed 0 s n d =
        NumericalValue.finite ((if s = 0 then (n : Rat) else -(n : Rat)) / (d : Rat)) := by
      simp [closed]
    rw [hB]
    by_cases hbad : n = 0 ∨ s = 1
    · have hle : (if s = 0 then (n : Rat) else -(n : Rat)) / (d : Rat) ≤ 0 := by
        by_cases hn : n = 0
        · exact le_of_eq (hzero.2 hn)
        · exact le_of_lt (hneg.2 ⟨by omega, hn⟩)
      simp [Arithmetic.rsqrtRadicand, hle, hbad, closed, Arithmetic.nan]
    · have hn : n ≠ 0 := fun h => hbad (Or.inl h)
      have hs0 : s = 0 := by omega
      have hgt : ¬(if s = 0 then (n : Rat) else -(n : Rat)) / (d : Rat) ≤ 0 := by
        intro hle
        rcases lt_or_eq_of_le hle with h | h
        · exact hbad (Or.inr (hneg.1 h).1)
        · exact hn (hzero.1 h)
      subst hs0
      rw [ite_eq_left rfl] at hgt
      simp [Arithmetic.rsqrtRadicand, hgt, hn, closed]
  · simp [closed, Arithmetic.rsqrtRadicand]
  · simp [closed, Arithmetic.rsqrtRadicand, Arithmetic.nan]
  · have h0 : ¬c = 0 := by omega
    have h1 : ¬c = 1 := by omega
    have h2 : ¬c = 2 := by omega
    simp [closed, Arithmetic.rsqrtRadicand, Arithmetic.nan, h0, h1, h2]

/-- The sum of the squares of two signed ratios, on the cross products of their terms. -/
theorem hypot_ratio (sa sb na nb da db : Nat) (hda : da ≠ 0) (hdb : db ≠ 0) :
    (if sa = 0 then (na : Rat) else -(na : Rat)) / (da : Rat) *
          ((if sa = 0 then (na : Rat) else -(na : Rat)) / (da : Rat)) +
        (if sb = 0 then (nb : Rat) else -(nb : Rat)) / (db : Rat) *
          ((if sb = 0 then (nb : Rat) else -(nb : Rat)) / (db : Rat)) =
      ((na * db * (na * db) + nb * da * (nb * da) : Nat) : Rat) /
        ((da * db * (da * db) : Nat) : Rat) := by
  have hda' : (da : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hda
  have hdb' : (db : Rat) ≠ 0 := Nat.cast_ne_zero.mpr hdb
  by_cases ha : sa = 0 <;> by_cases hb : sb = 0 <;>
    simp only [ha, hb, ite_true, ite_false] <;> push_cast <;> field_simp

/--
P3109 interim report v4.1, §4.10.14: the radicand of the hypotenuse of two closed values given
by class, sign and ratio: the exact sum of the squares, `+∞` for an infinite operand, and NaN
for a NaN operand.
-/
theorem hypotRadicand_closed (ca cb sa sb na nb da db : Nat) (hda : da ≠ 0) (hdb : db ≠ 0) :
    Arithmetic.hypotRadicand (closed ca sa na da) (closed cb sb nb db) =
      closed (if 3 ≤ ca ∨ 3 ≤ cb then 3 else if ca = 0 ∧ cb = 0 then 0 else 1) 0
        (na * db * (na * db) + nb * da * (nb * da)) (da * db * (da * db)) := by
  have hratio := hypot_ratio sa sb na nb da db hda hdb
  unfold closed
  rcases (by omega : ca = 0 ∨ ca = 1 ∨ ca = 2 ∨ 3 ≤ ca) with rfl | rfl | rfl | ha <;>
    rcases (by omega : cb = 0 ∨ cb = 1 ∨ cb = 2 ∨ 3 ≤ cb) with rfl | rfl | rfl | hb
  all_goals first
    | (simp [Arithmetic.hypotRadicand, Arithmetic.nan, hratio]; done)
    | (have h1 : ¬ca = 0 := by omega
       have h2 : ¬ca = 1 := by omega
       have h3 : ¬ca = 2 := by omega
       simp [Arithmetic.hypotRadicand, Arithmetic.nan, h1, h2, h3, ha])
    | (have h1 : ¬cb = 0 := by omega
       have h2 : ¬cb = 1 := by omega
       have h3 : ¬cb = 2 := by omega
       simp [Arithmetic.hypotRadicand, Arithmetic.nan, h1, h2, h3, hb])

/-! ## The operations on encodings -/

variable {leftFormat rightFormat : Format}

/--
P3109 interim report v4.1, §4.10.8: `sqrt` on an encoding stores the reference square root of
its value, rounded once into the destination, NaN for a negative value, for every descriptor,
rounding mode, random word and saturation mode.
-/
theorem sqrt_eq (x : ExecFloat.P3109 leftFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.Sqrt x target mode saturation =
      ExecFloat.P3109.ofNatBits
        (sqrt leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits) := by
  unfold ExecFloat.P3109.Sqrt
  rw [toClosedRat_eq x,
    projectSqrt_eq _ _ _ _ _ _ _ (signOf_le _ _ _) (fun _ _ => denominatorOf_ne_zero _ _ _ _)]
  rfl

/--
P3109 interim report v4.1, §4.10.8: `rsqrt` on an encoding stores the reference reciprocal
square root of its value, rounded once into the destination, NaN for zero and for a negative
value.
-/
theorem rsqrt_eq (x : ExecFloat.P3109 leftFormat) (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    ExecFloat.P3109.RSqrt x target mode saturation =
      ExecFloat.P3109.ofNatBits
        (rsqrt leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits) := by
  unfold ExecFloat.P3109.RSqrt
  rw [toClosedRat_eq x,
    rsqrtRadicand_closed _ _ _ _ (signOf_le _ _ _) (denominatorOf_ne_zero _ _ _ _),
    projectSqrt_eq _ _ _ _ _ _ _ (Nat.zero_le 1) (by
      intro hcls _
      by_cases hc : classOf leftFormat.bitWidth (sgOf leftFormat) (exOf leftFormat)
          x.toNatBits = 0
      · rw [ite_eq_left hc] at hcls ⊢
        intro hn0
        rw [ite_eq_left (Or.inl hn0)] at hcls
        exact absurd hcls (by decide)
      · rw [ite_eq_right hc]
        exact Nat.one_ne_zero)]
  unfold rsqrt
  kernel_notation
  simp only [Bool.or_eq_true, Nat.beq_eq]

/--
P3109 interim report v4.1, §4.10.14: `hypot` on two encodings stores the reference hypotenuse
of two values of independent formats: the root of the exact sum of the squares, rounded once
into the destination.
-/
theorem hypot_eq (x : ExecFloat.P3109 leftFormat) (y : ExecFloat.P3109 rightFormat)
    (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    ExecFloat.P3109.Hypot x y target mode saturation =
      ExecFloat.P3109.ofNatBits
        (hypot leftFormat.bitWidth leftFormat.precision (sgOf leftFormat) (exOf leftFormat)
          rightFormat.bitWidth rightFormat.precision (sgOf rightFormat) (exOf rightFormat)
          target.bitWidth target.precision (sgOf target) (exOf target) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) x.toNatBits y.toNatBits) := by
  unfold ExecFloat.P3109.Hypot
  rw [toClosedRat_eq x, toClosedRat_eq y,
    hypotRadicand_closed _ _ _ _ _ _ _ _ (denominatorOf_ne_zero _ _ _ _)
      (denominatorOf_ne_zero _ _ _ _),
    projectSqrt_eq _ _ _ _ _ _ _ (Nat.zero_le 1) (fun _ _ => Nat.mul_ne_zero
      (Nat.mul_ne_zero (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _))
      (Nat.mul_ne_zero (denominatorOf_ne_zero _ _ _ _) (denominatorOf_ne_zero _ _ _ _)))]
  unfold hypot
  kernel_notation
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq]

end FloatLib.Floats.Formats.P3109.KernelPath
