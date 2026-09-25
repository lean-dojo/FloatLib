/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Formatting
public import FloatLib.Numerics.Exact.DecimalText.NotationProof
public import FloatLib.Floats.Formats.Posit.Rounding.RoundTrip

/-!
# Value-preserving Posit decimal conversion

The decimal string denotes exactly the decoded dyadic rational. Rounding that rational recovers
the original posit word. This proves the decimal preservation guarantee of
Posit Standard (2022), §6.3 for every descriptor width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

open FloatLib.Numerics

variable {format : Format}

/-! ## Exponent clamping -/

private theorem minPositiveRat_pos' (format : Format) : 0 < minPositiveRat format :=
  nonnegativeRatAt_pos format (by decide) format.one_lt_signMaskNat

private theorem minPositiveRat_le_maxPositive (format : Format) :
    minPositiveRat format ≤ nonnegativeRatAt format (format.signMaskNat - 1) := by
  have h := format.one_lt_signMaskNat
  exact (nonnegativeRatAt_le_iff format h (by omega)).mpr (by omega)

/-- Every positive rational below minPos rounds to the code of minPos. -/
theorem roundPositiveCode_of_lt_minPositive (target : Rat) (hpos : 0 < target)
    (hlt : target < minPositiveRat format) :
    roundPositiveCode format target = 1 := by
  unfold roundPositiveCode
  rw [ite_eq_right (not_le_of_gt hpos), ite_eq_left hlt]

/-- Every rational at or above maxPos rounds to the code of maxPos. -/
theorem roundPositiveCode_of_maxPositive_le (target : Rat)
    (hle : nonnegativeRatAt format (format.signMaskNat - 1) ≤ target) :
    roundPositiveCode format target = format.signMaskNat - 1 := by
  have hmin := (minPositiveRat_le_maxPositive format).trans hle
  have hmask := format.one_lt_signMaskNat
  exact roundPositiveCode_eq_maxPositive_of_lowerCode format target
    ((minPositiveRat_pos' format).trans_le hmin) hmin
    (lowerCodeForPositive_eq_of_bracket format target _ (by omega) hle (fun h => by omega))

private theorem le_num_of_pos (q : Rat) (hq : 0 < q) : q ≤ (q.num.natAbs : Rat) := by
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have hcast : ((q.num.natAbs : Int) : Rat) = (q.num : Rat) := by
    rw [Int.natAbs_of_nonneg hnum.le]
  have hden : (1 : Rat) ≤ q.den := by exact_mod_cast q.den_pos
  calc q = (q.num : Rat) / q.den := (Rat.num_div_den q).symm
    _ ≤ (q.num : Rat) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [(show (0 : Rat) ≤ q.num by exact_mod_cast hnum.le)]
    _ = (q.num.natAbs : Rat) := by rw [← hcast]; rfl

private theorem inv_den_le_of_pos (q : Rat) (hq : 0 < q) : (1 : Rat) / q.den ≤ q := by
  have hnum : (1 : Rat) ≤ q.num := by exact_mod_cast Rat.num_pos.mpr hq
  have hden : (0 : Rat) < q.den := by exact_mod_cast q.den_pos
  calc (1 : Rat) / q.den ≤ (q.num : Rat) / q.den := div_le_div_of_nonneg_right hnum hden.le
    _ = q := Rat.num_div_den q

private theorem two_pow_le_ten_pow (k : Nat) : (2 : Rat) ^ k ≤ (10 : Rat) ^ k :=
  pow_le_pow_left₀ (by norm_num) (by norm_num) k

/-- A nonzero significand scaled at or past the saturation exponent reaches maxPos. -/
theorem maxPositive_le_of_saturationExponent_le (s : Nat) (e : Int) (hs : s ≠ 0)
    (he : decimalSaturationExponent format ≤ e) :
    nonnegativeRatAt format (format.signMaskNat - 1) ≤ (s : Rat) * (10 : Rat) ^ e := by
  set M := nonnegativeRatAt format (format.signMaskNat - 1)
  have hM : 0 < M := (minPositiveRat_pos' format).trans_le (minPositiveRat_le_maxPositive format)
  set k := M.num.natAbs.log2 + 1
  have hk : decimalSaturationExponent format = (k : Int) := by
    simp [decimalSaturationExponent, M, k]
  have hnum : (M.num.natAbs : Rat) < (2 : Rat) ^ k := by exact_mod_cast Nat.lt_log2_self
  have hs1 : (1 : Rat) ≤ s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hs
  have hpow : (10 : Rat) ^ (k : Int) ≤ (10 : Rat) ^ e :=
    zpow_le_zpow_right₀ (by norm_num) (hk ▸ he)
  calc M ≤ (M.num.natAbs : Rat) := le_num_of_pos M hM
    _ ≤ (2 : Rat) ^ k := hnum.le
    _ ≤ (10 : Rat) ^ k := two_pow_le_ten_pow k
    _ = (10 : Rat) ^ (k : Int) := (zpow_natCast _ _).symm
    _ ≤ (10 : Rat) ^ e := hpow
    _ = 1 * (10 : Rat) ^ e := (one_mul _).symm
    _ ≤ (s : Rat) * (10 : Rat) ^ e :=
      mul_le_mul_of_nonneg_right hs1 (zpow_pos (by norm_num) _).le

/-- A significand scaled at or below its vanishing exponent lies strictly below minPos. -/
theorem lt_minPositive_of_le_vanishingExponent (s : Nat) (e : Int)
    (he : e ≤ decimalVanishingExponent format s) :
    (s : Rat) * (10 : Rat) ^ e < minPositiveRat format := by
  set m := minPositiveRat format
  have hm : 0 < m := minPositiveRat_pos' format
  set a := s.log2 + 1
  set b := m.den.log2 + 1
  have hv : decimalVanishingExponent format s = -((a + b : Nat) : Int) := by
    simp [decimalVanishingExponent, m, a, b]
  have hsa : (s : Rat) < (2 : Rat) ^ a := by exact_mod_cast Nat.lt_log2_self
  have hdb : (m.den : Rat) < (2 : Rat) ^ b := by exact_mod_cast Nat.lt_log2_self
  have hden : (0 : Rat) < m.den := by exact_mod_cast m.den_pos
  have h10 : (10 : Rat) ^ e ≤ ((10 : Rat) ^ (a + b))⁻¹ := by
    calc (10 : Rat) ^ e ≤ (10 : Rat) ^ (-((a + b : Nat) : Int)) :=
          zpow_le_zpow_right₀ (by norm_num) (hv ▸ he)
      _ = ((10 : Rat) ^ (a + b))⁻¹ := by rw [zpow_neg, zpow_natCast]
  have h2 : ((10 : Rat) ^ (a + b))⁻¹ ≤ ((2 : Rat) ^ (a + b))⁻¹ :=
    inv_anti₀ (by positivity) (two_pow_le_ten_pow _)
  have h2a : (0 : Rat) < (2 : Rat) ^ a := by positivity
  calc (s : Rat) * (10 : Rat) ^ e ≤ (s : Rat) * ((2 : Rat) ^ (a + b))⁻¹ :=
        mul_le_mul_of_nonneg_left (h10.trans h2) (Nat.cast_nonneg s)
    _ < (2 : Rat) ^ a * ((2 : Rat) ^ (a + b))⁻¹ :=
        mul_lt_mul_of_pos_right hsa (inv_pos.mpr (pow_pos (by norm_num) _))
    _ = ((2 : Rat) ^ b)⁻¹ := by
        rw [pow_add (2 : Rat) a b, mul_inv, ← mul_assoc, mul_inv_cancel₀ h2a.ne', one_mul]
    _ < (1 : Rat) / m.den := by
        rw [one_div]
        exact inv_strictAnti₀ hden hdb
    _ ≤ m := inv_den_le_of_pos m hm

/-- Rounding a decimal depends on its magnitude only through the positive rounder. -/
private theorem roundRat_decimal (negative : Bool) (s : Nat) (e : Int) (hs : s ≠ 0) :
    roundRat format (DecimalText.Decimal.mk negative s e).toRat =
      if negative then neg (roundPositiveRat format ((s : Rat) * (10 : Rat) ^ e))
      else roundPositiveRat format ((s : Rat) * (10 : Rat) ^ e) := by
  have hpos : 0 < (s : Rat) * (10 : Rat) ^ e :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hs) (zpow_pos (by norm_num) _)
  unfold roundRat DecimalText.Decimal.toRat
  cases negative
  · simp [hpos.ne', not_lt_of_gt hpos]
  · simp [hpos.ne', hpos]

/-- Clamping the decimal exponent never changes the rounded posit. -/
theorem roundRat_clampDecimal (d : DecimalText.Decimal) :
    roundRat format (clampDecimal format d).toRat = roundRat format d.toRat := by
  by_cases hs : d.significand = 0
  · simp [clampDecimal, hs, DecimalText.Decimal.toRat]
  have hc : clampDecimal format d =
      { d with exponent := (max (decimalVanishingExponent format d.significand)
        (min (decimalSaturationExponent format) d.exponent)) } := by
    simp [clampDecimal, hs]
  rw [hc, roundRat_decimal d.negative d.significand _ hs]
  conv_rhs => rw [show d = ⟨d.negative, d.significand, d.exponent⟩ from rfl,
    roundRat_decimal d.negative d.significand d.exponent hs]
  suffices hcode : roundPositiveCode format ((d.significand : Rat) * (10 : Rat) ^
      max (decimalVanishingExponent format d.significand)
        (min (decimalSaturationExponent format) d.exponent)) =
      roundPositiveCode format ((d.significand : Rat) * (10 : Rat) ^ d.exponent) by
    simp only [roundPositiveRat, hcode]
  have hpos : ∀ e : Int, 0 < (d.significand : Rat) * (10 : Rat) ^ e := fun e =>
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hs) (zpow_pos (by norm_num) _)
  have horder : decimalVanishingExponent format d.significand <
      decimalSaturationExponent format := by
    simp only [decimalVanishingExponent, decimalSaturationExponent]
    omega
  by_cases hhi : decimalSaturationExponent format < d.exponent
  · rw [min_eq_left hhi.le, max_eq_right horder.le,
      roundPositiveCode_of_maxPositive_le _
        (maxPositive_le_of_saturationExponent_le _ _ hs le_rfl),
      roundPositiveCode_of_maxPositive_le _
        (maxPositive_le_of_saturationExponent_le _ _ hs hhi.le)]
  rw [min_eq_right (not_lt.mp hhi)]
  by_cases hlo : d.exponent < decimalVanishingExponent format d.significand
  · rw [max_eq_left hlo.le,
      roundPositiveCode_of_lt_minPositive _ (hpos _)
        (lt_minPositive_of_le_vanishingExponent _ _ le_rfl),
      roundPositiveCode_of_lt_minPositive _ (hpos _)
        (lt_minPositive_of_le_vanishingExponent _ _ hlo.le)]
  rw [max_eq_right (not_lt.mp hlo)]

/-- Decimal parsing uses the standard exact-rational rounder once. -/
theorem parse_eq_roundRat (input : String) (value : Rat)
    (hinput : DecimalText.parse input = some value) :
    parse format input = .ok (roundRat format value) := by
  have hnar : input ≠ "NaR" := by
    intro h
    subst input
    simp [DecimalText.parse, DecimalText.parseCharacters, DecimalText.splitSign,
      RadixText.parseMagnitude, RadixText.scanDigits, DecimalText.digitValue?] at hinput
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hinput
  simp [parse, hnar, hd, roundRat_clampDecimal]

/-- An ordinary finite word's decimal display has exactly its decoded rational value. -/
theorem decimalParse_display (value : Model format) (exact : FloatLib.Numerics.Dyadic)
    (hexact : value.toDyadic? = some exact) :
    DecimalText.parse value.display = some exact.toRat := by
  simp [display, hexact]

/-- Decimal display and parsing preserve every posit word, including zero and NaR. -/
@[simp] theorem parse_display (value : Model format) :
    parse format value.display = .ok value := by
  cases hexact : value.toDyadic? with
  | none =>
      have hrat : value.toRat? = none := by
        rw [toRat?_eq_toDyadic?_map, hexact]
        rfl
      have hnar := (toRat?_eq_none_iff value).mp hrat
      have hvalue := (isNaR_eq_true_iff value).mp hnar
      subst value
      simp [display, parse]
  | some exact =>
      rw [parse_eq_roundRat value.display exact.toRat (decimalParse_display value exact hexact)]
      congr 1
      apply roundRat_toRat? value exact.toRat
      simp [toRat?_eq_toDyadic?_map, hexact]

/-- Exact decimal parsing inverts `ToString`. -/
@[simp] theorem parse_toString (value : Model format) :
    parse format (toString value) = .ok value :=
  parse_display value

end FloatLib.Floats.Formats.Posit.Model
