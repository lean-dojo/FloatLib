/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.Posit.Functions.Basic
public import FloatLib.Floats.Formats.Posit.Rounding.RoundTrip
import FloatLib.Floats.Formats.Posit.Cast.Widening
import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Semantics.Candidates
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact integer-valued posit functions

Integer rounding does not introduce a second numerical rounding error. An integral input is
already representable. For a nonintegral input, the tapered fraction budget suffices to encode
both neighboring integers, including a ceiling at the next power of two. The argument uses
field-layout semantics and applies to every descriptor width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

open FloatLib.Numerics
open GuardStickyRounding

variable {format : Format}

/-- Keeping the whole normalized tail constructs the exact dyadic value. -/
private theorem exists_code_scaled_nat (format : Format) (significand leading scale : Nat)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hbudget : scale / 4 + leading + 4 ≤ format.payloadBits) :
    ∃ code < format.signMaskNat,
      nonnegativeRatAt format code =
        (significand : ℚ) * (2 : ℚ) ^ ((scale : ℤ) - leading) := by
  let regime : ℤ := (scale / 4 : Nat)
  let exponent := scale % 4
  have hr : 0 ≤ regime := Int.natCast_nonneg _
  have he : exponent < 4 := Nat.mod_lt _ (by decide)
  have hrun : regime.toNat + 1 < format.payloadBits := by
    simp only [regime, Int.toNat_natCast]
    omega
  have htail : leading + 2 ≤ format.payloadBits - (regime.toNat + 1) - 1 := by
    simp only [regime, Int.toNat_natCast]
    omega
  refine ⟨DirectDyadicPacking.lowerCandidateFromFields format regime exponent
    significand leading,
    DirectDyadicPacking.lowerCandidateFromFields_lt_signMask
      format regime exponent significand leading he hlower hupper, ?_⟩
  rw [lowerCandidateValue_positive format regime exponent significand leading
    hr hrun he hlower hupper,
    tailPrefix_eq_streamPrefix exponent significand leading _ hlower hupper,
    trailingRat_streamPrefix_eq_of_width_le _ _ _ htail,
    trailingRat_exactTailRaw exponent significand leading he hlower hupper]
  have hscale : regime * 4 + (exponent : ℤ) = scale := by
    dsimp [regime, exponent]
    omega
  simp only [Int.ofNat_eq_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_assoc,
    ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  rw [show (exponent : ℤ) + regime * 4 = scale by omega]
  rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
  simp only [zpow_natCast]
  ring

/-- Every integer whose normalized bits fit has an exact positive encoding. -/
private theorem exists_code_nat (format : Format) (n : Nat)
    (hbudget : n.log2 / 4 + n.log2 + 4 ≤ format.payloadBits) :
    ∃ code < format.signMaskNat, nonnegativeRatAt format code = (n : ℚ) := by
  by_cases hn : n = 0
  · exact ⟨0, format.signMaskNat_pos, by simp [hn]⟩
  simpa using exists_code_scaled_nat format n n.log2 n.log2
    (Nat.log2_self_le hn) (Nat.lt_log2_self) hbudget

/-- A power of two needs no explicit fraction positions. -/
private theorem exists_code_two_pow (format : Format) (e : Nat)
    (hbudget : e / 4 + 4 ≤ format.payloadBits) :
    ∃ code < format.signMaskNat, nonnegativeRatAt format code = (2 : ℚ) ^ e := by
  simpa using exists_code_scaled_nat format 1 0 e (by norm_num) (by norm_num)
    (by simpa using hbudget)

/-- The unit encoding exists even when the exponent field is completely tapered away. -/
private theorem exists_code_one (format : Format) :
    ∃ code < format.signMaskNat, nonnegativeRatAt format code = 1 := by
  refine ⟨format.oneCodeNat, format.oneCodeNat_lt_signMaskNat, ?_⟩
  have hw := nonnegativeRatAt_widen (Format.ofBits 2 (by decide)) format
    format.bits_ge_two (code := 1) (by decide)
  simp only [Format.ofBits] at hw
  have he : format.oneCodeNat = 1 * 2 ^ (format.bits - 2) := by
    simp [Format.oneCodeNat, Format.payloadBits, Nat.sub_sub]
  rw [he, hw]
  simpa [Format.ofBits, Format.signMaskNat, Format.signIndex, Format.payloadBits] using
    nonnegativeRatAt_maxPositive (Format.ofBits 2 (by decide))

/--
A nonintegral positive binade has enough fraction positions for every integer up to its
upper endpoint. That endpoint uses the separate fraction-free power-of-two construction.
-/
private theorem exists_code_integer_neighbor (format : Format) {code : Nat}
    (hcode : code < format.signMaskNat) (n : ℤ)
    (hlower : (nonnegativeRatAt format code).floor ≤ n)
    (hupper : n ≤ (nonnegativeRatAt format code).ceil) :
    ∃ other < format.signMaskNat, nonnegativeRatAt format other = (n : ℚ) := by
  let q := nonnegativeRatAt format code
  change q.floor ≤ n at hlower
  change n ≤ q.ceil at hupper
  by_cases hi : ∃ z : ℤ, q = (z : ℚ)
  · obtain ⟨z, hz⟩ := hi
    have hn : n = z := by
      rw [hz, Rat.floor_intCast] at hlower
      rw [hz, Rat.ceil_intCast] at hupper
      omega
    exact ⟨code, hcode, by simpa [hn] using hz⟩
  have hc : 0 < code := by
    by_contra h
    have : code = 0 := by omega
    exact hi ⟨0, by simp [q, this]⟩
  have hqpos : 0 < q := nonnegativeRatAt_pos format hc hcode
  have hn : 0 ≤ n := le_trans (Rat.le_floor_iff.mpr hqpos.le) hlower
  by_cases hsmall : q < 1
  · have hnle : n ≤ 1 := hupper.trans (Rat.ceil_le_iff.mpr hsmall.le)
    have hncase : n = 0 ∨ n = 1 := by omega
    rcases hncase with rfl | rfl
    · exact ⟨0, format.signMaskNat_pos, by simp⟩
    · simpa using exists_code_one format
  let value : Model format := ofNatBits code
  let significand := 2 ^ value.fractionBits + value.fractionField
  let exponent : ℤ := value.regimeValue * 4 + value.exponentField
  have hsign : value.signBit = false := signBit_ofNatBits_eq_false format code hcode
  have hq : q = (significand : ℚ) *
      (2 : ℚ) ^ (exponent - value.fractionBits) := by
    rw [show q = value.decodeFields.toRat from
      nonnegativeRatAt_of_pos_lt_signMask format hc hcode]
    simp [DecodedFields.toRat, DecodedFields.toDyadic, decodeFields,
      FloatLib.Numerics.Dyadic.toRat, FloatLib.Numerics.Dyadic.signedSignificand,
      hsign, significand, exponent, scale, Format.regimeExponentStep]
  have hfrac : value.fractionField < 2 ^ value.fractionBits :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have hsighi : significand < 2 ^ (value.fractionBits + 1) := by
    dsimp [significand]
    rw [pow_succ]
    omega
  have hpow (f : Nat) :
      ((2 ^ f : Nat) : ℚ) * (2 : ℚ) ^ (exponent - value.fractionBits) =
        (2 : ℚ) ^ ((f : ℤ) + exponent - value.fractionBits) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 1
    omega
  have hqhi : q < (2 : ℚ) ^ (exponent + 1) := by
    rw [hq]
    calc
      _ < ((2 ^ (value.fractionBits + 1) : Nat) : ℚ) *
          (2 : ℚ) ^ (exponent - value.fractionBits) :=
        mul_lt_mul_of_pos_right (by exact_mod_cast hsighi) (zpow_pos (by norm_num) _)
      _ = _ := by rw [hpow]; congr 1; push_cast; omega
  have he : 0 ≤ exponent := by
    by_contra h
    have hp : (2 : ℚ) ^ (exponent + 1) ≤ 1 := by
      calc _ ≤ (2 : ℚ) ^ (0 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
           _ = 1 := by simp
    exact hsmall (hqhi.trans_le hp)
  have hs : exponent < value.fractionBits := by
    by_contra h
    have hs : 0 ≤ exponent - value.fractionBits := by omega
    apply hi
    refine ⟨(significand * 2 ^ (exponent - value.fractionBits).toNat : Nat), ?_⟩
    rw [hq, ← Int.toNat_of_nonneg hs]
    simp
  have ht : value.trailingBits = value.fractionBits + 2 := by
    simp only [fractionBits, usedExponentBits, Format.exponentBits] at hs ⊢
    omega
  have hr := value.regimeRunLength_pos
  have hrle := value.regimeRunLength_le_payload
  have hterm : value.regimeRunLength < format.payloadBits := by
    simp only [trailingBits, hasRegimeTerminator] at ht
    split_ifs at ht <;> omega
  have hpayload : format.payloadBits = value.regimeRunLength + value.fractionBits + 3 := by
    simp only [trailingBits, hasRegimeTerminator, hterm, decide_true, ite_true] at ht
    omega
  have hex := value.exponentField_lt_four
  have hregime : value.regimeBit = true := by
    cases hb : value.regimeBit
    · simp only [exponent, regimeValue, hb, Bool.false_eq_true, ite_false,
        Int.ofNat_eq_natCast] at he
      omega
    · rfl
  have heq : exponent = ((value.regimeRunLength : ℤ) - 1) * 4 + value.exponentField := by
    simp [exponent, regimeValue, hregime]
  have hbudget : exponent.toNat / 4 + exponent.toNat + 5 ≤ format.payloadBits := by
    have hcast := Int.toNat_of_nonneg he
    omega
  have hnle : n ≤ (2 ^ (exponent.toNat + 1) : Nat) := by
    apply hupper.trans
    apply Rat.ceil_le_iff.mpr
    have hcast := Int.toNat_of_nonneg he
    have hp : (2 : ℚ) ^ (exponent + 1) = ((2 ^ (exponent.toNat + 1) : Nat) : ℚ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast]
      congr 1
      push_cast
      omega
    simpa only [hp, Int.cast_natCast] using hqhi.le
  by_cases htop : n = (2 ^ (exponent.toNat + 1) : Nat)
  · subst n
    simpa using exists_code_two_pow format (exponent.toNat + 1) (by omega)
  have hnat : n.toNat < 2 ^ (exponent.toNat + 1) := by omega
  have hlog : n.toNat.log2 ≤ exponent.toNat := by
    by_cases hz : n.toNat = 0
    · simp [hz]
    · exact Nat.le_of_lt_succ ((Nat.log2_lt hz).mpr hnat)
  obtain ⟨other, ho, hvalue⟩ := exists_code_nat format n.toNat (by omega)
  exact ⟨other, ho, hvalue.trans (by exact_mod_cast Int.toNat_of_nonneg hn)⟩

/-- Restoring the sign of a finite magnitude preserves its exact rational meaning. -/
private theorem toRat?_signed_code (format : Format) (code : Nat)
    (hcode : code < format.signMaskNat) (negative : Bool) :
    (if negative then neg (ofNatBits (format := format) code) else ofNatBits code).toRat? =
      some (if negative then -nonnegativeRatAt format code
        else nonnegativeRatAt format code) := by
  have hne (word : Nat) (hw : word < format.modulus)
      (hn : word ≠ format.signMaskNat) :
      ofNatBits (format := format) word ≠ nar format := by
    intro h
    have he := congrArg toNatBits h
    rw [toNatBits_ofNatBits_of_lt _ hw, nar_toNatBits] at he
    exact hn he
  cases negative
  · simp only [Bool.false_eq_true, ite_false]
    rw [toRat?_eq_signed_magnitude _
      (hne code (hcode.trans format.signMaskNat_lt_modulus) (Nat.ne_of_lt hcode)),
      signBit_ofNatBits_eq_false format code hcode,
      magnitudeBits_ofNatBits_of_lt_signMask format code hcode]
    rfl
  · simp only [ite_true]
    by_cases hz : code = 0
    · subst code
      change (neg (zero format)).toRat? = some (-nonnegativeRatAt format 0)
      simp
    have hm := format.modulus_eq_two_mul_signMaskNat
    have hw : format.modulus - code < format.modulus := by omega
    have hs : (ofNatBits (format := format) (format.modulus - code)).signBit = true := by
      rw [signBit_ofNatBits_eq_decide format _ hw]
      exact decide_eq_true (by omega)
    have hmag : (ofNatBits (format := format) (format.modulus - code)).magnitudeBits =
        code := by
      rw [magnitudeBits, hs, ite_eq_left rfl, toNatBits_ofNatBits_of_lt _ hw]
      omega
    rw [neg, toNatBits_ofNatBits_of_lt _ (hcode.trans format.signMaskNat_lt_modulus),
      toRat?_eq_signed_magnitude _ (hne _ hw (by omega)), hs, ite_eq_left rfl, hmag]

/--
Every integer between the exact floor and ceiling of a finite posit is representable.
This includes both endpoints and has no precision or magnitude precondition.
-/
theorem exists_toRat?_integer_neighbor (value : Model format) {q : ℚ}
    (hvalue : value.toRat? = some q) (n : ℤ)
    (hlower : q.floor ≤ n) (hupper : n ≤ q.ceil) :
    ∃ result : Model format, result.toRat? = some (n : ℚ) := by
  have hnar : value ≠ nar format := by
    intro h
    simp [h] at hvalue
  have hm := magnitudeBits_lt_signMask_of_ne_nar value hnar
  have hq := toRat?_eq_signed_magnitude value hnar
  rw [hvalue, Option.some.injEq] at hq
  cases hs : value.signBit
  · simp only [hs, Bool.false_eq_true, ite_false] at hq
    obtain ⟨code, hc, hv⟩ := exists_code_integer_neighbor format hm n
      (by simpa [hq] using hlower) (by simpa [hq] using hupper)
    refine ⟨ofNatBits code, ?_⟩
    simpa only [Bool.false_eq_true, ite_false, hv] using
      toRat?_signed_code format code hc false
  · simp only [hs, ite_true] at hq
    let magnitude := nonnegativeRatAt format value.magnitudeBits
    have hf : (-magnitude).floor = -magnitude.ceil := by
      rw [Rat.ceil_eq_neg_floor_neg, neg_neg]
    have hc : (-magnitude).ceil = -magnitude.floor := by
      rw [Rat.ceil_eq_neg_floor_neg, neg_neg]
    have hlo : magnitude.floor ≤ -n := by
      rw [hq, hc] at hupper
      omega
    have hhi : -n ≤ magnitude.ceil := by
      rw [hq, hf] at hlower
      omega
    obtain ⟨code, hcode, hv⟩ := exists_code_integer_neighbor format hm (-n) hlo hhi
    refine ⟨neg (ofNatBits code), ?_⟩
    simpa only [ite_true, hv, Int.cast_neg, neg_neg] using
      toRat?_signed_code format code hcode true

/-- Posit floor returns the exact mathematical floor, without a further rounding error. -/
theorem toRat?_floor_of_finite (value : Model format) {q : ℚ}
    (hvalue : value.toRat? = some q) :
    (floor value).toRat? = some (q.floor : ℚ) := by
  have hle : q.floor ≤ q.ceil := by
    exact_mod_cast (Rat.floor_le q).trans (Rat.le_ceil (x := q))
  obtain ⟨result, hr⟩ := exists_toRat?_integer_neighbor value hvalue q.floor le_rfl hle
  simp only [floor, hvalue]
  rw [roundRat_toRat? result _ hr]
  exact hr

/-- Posit ceiling returns the exact mathematical ceiling, without a further rounding error. -/
theorem toRat?_ceil_of_finite (value : Model format) {q : ℚ}
    (hvalue : value.toRat? = some q) :
    (ceil value).toRat? = some (q.ceil : ℚ) := by
  have hle : q.floor ≤ q.ceil := by
    exact_mod_cast (Rat.floor_le q).trans (Rat.le_ceil (x := q))
  obtain ⟨result, hr⟩ := exists_toRat?_integer_neighbor value hvalue q.ceil hle le_rfl
  simp only [ceil, hvalue]
  rw [roundRat_toRat? result _ hr]
  exact hr

/-- Nearest-integer posit rounding returns the shared exact nearest-even integer. -/
theorem toRat?_nearestInt_of_finite (value : Model format) {q : ℚ}
    (hvalue : value.toRat? = some q) :
    (nearestInt value).toRat? = some (roundRatEven q : ℚ) := by
  have hn : roundRatEven q = q.floor ∨ roundRatEven q = q.ceil := by
    rw [roundRatEven_eq_floor_ceil]
    split_ifs <;> simp_all
  have hle : q.floor ≤ q.ceil := by
    exact_mod_cast (Rat.floor_le q).trans (Rat.le_ceil (x := q))
  have hlo : q.floor ≤ roundRatEven q := by rcases hn with h | h <;> omega
  have hhi : roundRatEven q ≤ q.ceil := by rcases hn with h | h <;> omega
  obtain ⟨result, hr⟩ := exists_toRat?_integer_neighbor value hvalue _ hlo hhi
  change (match value.toRat? with
    | none => nar format
    | some q => roundRat format (roundRatEven q : ℚ)).toRat? = _
  simp only [hvalue]
  rw [roundRat_toRat? result _ hr]
  exact hr

/-- Exact floor semantics also accounts for the NaR input. -/
@[simp] theorem toRat?_floor (value : Model format) :
    (floor value).toRat? = value.toRat?.map (fun q => (q.floor : ℚ)) := by
  cases hvalue : value.toRat? with
  | none => simp [floor, hvalue]
  | some q => simpa only [hvalue, Option.map_some] using toRat?_floor_of_finite value hvalue

/-- Exact ceiling semantics also accounts for the NaR input. -/
@[simp] theorem toRat?_ceil (value : Model format) :
    (ceil value).toRat? = value.toRat?.map (fun q => (q.ceil : ℚ)) := by
  cases hvalue : value.toRat? with
  | none => simp [ceil, hvalue]
  | some q => simpa only [hvalue, Option.map_some] using toRat?_ceil_of_finite value hvalue

/-- Exact nearest-even semantics also accounts for the NaR input. -/
@[simp] theorem toRat?_nearestInt (value : Model format) :
    (nearestInt value).toRat? = value.toRat?.map (fun q => (roundRatEven q : ℚ)) := by
  cases hvalue : value.toRat? with
  | none => simp [nearestInt, hvalue]
  | some q =>
    simpa only [hvalue, Option.map_some] using toRat?_nearestInt_of_finite value hvalue

/-- Floor fixes every posit that already denotes an integer. -/
theorem floor_of_int (value : Model format) {n : ℤ}
    (hvalue : value.toRat? = some (n : ℚ)) : floor value = value := by
  simp only [floor, hvalue, Rat.floor_intCast]
  exact roundRat_toRat? value _ hvalue

/-- Ceiling fixes every posit that already denotes an integer. -/
theorem ceil_of_int (value : Model format) {n : ℤ}
    (hvalue : value.toRat? = some (n : ℚ)) : ceil value = value := by
  simp only [ceil, hvalue, Rat.ceil_intCast]
  exact roundRat_toRat? value _ hvalue

/-- Nearest-integer rounding fixes every posit that already denotes an integer. -/
theorem nearestInt_of_int (value : Model format) {n : ℤ}
    (hvalue : value.toRat? = some (n : ℚ)) : nearestInt value = value := by
  simp only [nearestInt, hvalue, nearestEvenInteger, roundRatEven_intCast]
  exact roundRat_toRat? value _ hvalue

/--
The returned integer minimizes distance among all integers, lies within half a unit, and
is even whenever that bound is attained. These properties describe the delivered posit.
-/
theorem nearestInt_spec (value : Model format) {q : ℚ}
    (hvalue : value.toRat? = some q) :
    ∃ n : ℤ, (nearestInt value).toRat? = some (n : ℚ) ∧
      |(n : ℚ) - q| ≤ (1 : ℚ) / 2 ∧
      (∀ z : ℤ, |(n : ℚ) - q| ≤ |(z : ℚ) - q|) ∧
      (|(n : ℚ) - q| = (1 : ℚ) / 2 → n % 2 = 0) :=
  ⟨roundRatEven q, toRat?_nearestInt_of_finite value hvalue,
    roundRatEven_error_le_half q, roundRatEven_nearest q,
    roundRatEven_even_of_error_eq_half q⟩

end FloatLib.Floats.Formats.Posit.Model
