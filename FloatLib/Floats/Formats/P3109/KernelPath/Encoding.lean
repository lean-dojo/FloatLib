/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.KernelPath.Projection
public import FloatLib.Floats.Formats.P3109.Projection.Encoding

/-!
# The kernel P3109 projection computes the reference projection

P3109 Interim Report v4.1 (14 September 2026), §§4.7.3 to 4.7.6, an unapproved draft.

* `magnitudeCode_eq`: `magnitudeCode` is the reference encoding of a positive finite datum;
* `aboveCode_eq`, `belowCode_eq`: the codes of the saturated results of §4.7.5, for every
  saturation mode, rounding mode, signedness and domain;
* `encodeRounded_eq`: the saturation and the code of a magnitude that is already rounded,
  the last stage of every projection and of the square roots;
* `projectFinite_eq`: the code of a nonzero ratio, rounded, saturated and encoded;
* `projectRat_eq`: `project` is the stored reference projection `ExecFloat.P3109.projectRat` of
  the closed value of a class and a ratio of natural numbers, for every descriptor, every
  rounding mode with every random word, every saturation mode and every input. The ratio need
  not be in lowest terms.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.KernelPath

open FloatLib.Numerics FloatLib.Numerics.Kernel
open FloatLib.Floats.Formats.P3109

/-! ## Encoding a finite magnitude -/

/--
P3109 interim report v4.1, §4.7.6: `magnitudeCode` is the reference code of the positive dyadic
`r * 2 ^ (Qb - beta)`, for every descriptor, every `r ≠ 0` and every bias `beta` of at least the
exponent bias.
-/
theorem magnitudeCode_eq (format : Format) (r Qb beta : Nat) (hr : r ≠ 0)
    (hbeta : format.exponentBias ≤ beta) :
    Format.Internal.encodePositiveFinite format
        { negative := false, significand := r, exponent := (Qb : Int) - (beta : Int) } =
      magnitudeCode format.precision format.exponentBias r Qb beta := by
  unfold Format.Internal.encodePositiveFinite magnitudeCode
  rw [size_sub_one hr, trailingBits_eq]
  kernel_notation
  simp only [beq_iff_eq, hr, ite_false, Int.ofNat_eq_natCast, Format.minimumNormalExponent]
  generalize hE : max (r.log2 + Qb) (beta + 1 - format.exponentBias) = e
  have hexp : max ((r.log2 : Int) + ((Qb : Int) - (beta : Int))) (1 - (format.exponentBias : Int)) =
      (e : Int) - (beta : Int) := by omega
  have hbias : ((e : Int) - (beta : Int) + (format.exponentBias : Int)).toNat =
      e + format.exponentBias - beta := by omega
  simp only [hexp, hbias]
  generalize hscale : (Qb : Int) - (beta : Int) - ((e : Int) - (beta : Int)) +
    (format.trailingBits : Int) = scale
  cases scale with
  | ofNat k =>
      have h1 : Qb + format.trailingBits - e = k := by
        have : (Int.ofNat k) = (k : Int) := rfl
        omega
      have h2 : e - (Qb + format.trailingBits) = 0 := by
        have : (Int.ofNat k) = (k : Int) := rfl
        omega
      simp only [h1, h2, Nat.pow_zero, Nat.div_one]
      split_ifs <;> first | rfl | omega
  | negSucc k =>
      have h1 : Qb + format.trailingBits - e = 0 := by
        have : (Int.negSucc k) = -((k : Int) + 1) := rfl
        omega
      have h2 : e - (Qb + format.trailingBits) = k + 1 := by
        have : (Int.negSucc k) = -((k : Int) + 1) := rfl
        omega
      simp only [h1, h2, Nat.pow_zero, Nat.mul_one]
      split_ifs <;> first | rfl | omega

/-! ## Saturated results -/

/-- The largest finite value has a nonzero significand and a clear sign. -/
theorem maxFinite_fields (format : Format) :
    format.maxFinite.significand ≠ 0 ∧ format.maxFinite.negative = false := by
  unfold Format.maxFinite
  exact ⟨fun h => Nat.ne_of_gt format.maxFiniteBits_pos
    ((format.decodePositiveFinite_significand_eq_zero_iff _).1 h),
    format.decodePositiveFinite_negative _⟩

/-- The reference code of the largest finite value is the largest finite code. -/
theorem encode_maxFinite (format : Format) :
    Format.Internal.encodeDatumNat format (.finite format.maxFinite) = format.maxFiniteBits := by
  have h := format.encodeDatumNat_decode (BitVec.ofNat format.bitWidth format.maxFiniteBits)
  unfold Format.decode at h
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show format.maxFiniteBits < 2 ^ format.bitWidth from
      format.maxFiniteBits_lt_modulus),
    format.decodeNat_of_le_maxFiniteBits _ (Nat.le_refl _)] at h
  exact h

/-- The reference code of the smallest finite value: the mirrored largest code of a signed
format, zero for an unsigned one. -/
theorem encode_minFinite (format : Format) :
    Format.Internal.encodeDatumNat format (.finite format.minFinite) =
      minFiniteCode format.bitWidth (sgOf format) (exOf format) := by
  obtain ⟨hsig, hneg⟩ := maxFinite_fields format
  have hmax := encode_maxFinite format
  unfold minFiniteCode
  rw [signBoundary_eq, maxFiniteBits_eq]
  kernel_notation
  unfold Format.Internal.encodeDatumNat at hmax ⊢
  unfold Format.minFinite sgOf
  cases hs : format.signedness
  · simp only [beq_iff_eq, hsig, ite_false, hneg, Bool.false_eq_true] at hmax
    simp [hsig, hneg, hmax]
  · simp

/-- The reference code of an infinity is the descriptor's code of that infinity. -/
theorem encode_infinity (format : Format) (negative : Bool) :
    Format.Internal.encodeDatumNat format (.infinity negative) =
      if negative then format.negativeInfinityBits else format.positiveInfinityBits := by
  cases negative <;> rfl

/-- The reference code of an exceptional value is the descriptor's NaN code. -/
theorem encode_exceptional (format : Format) (value : ExceptionalValue) :
    Format.Internal.encodeDatumNat format (.exceptional value) = format.nanBits := rfl

/-- P3109 interim report v4.1, §4.7.5: the reference code of the result above the finite range. -/
theorem aboveCode_eq (format : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    Format.Internal.encodeDatumNat format (Format.Internal.saturateAbove format saturation mode) =
      aboveCode format.bitWidth (sgOf format) (exOf format) (modeIndex mode)
        (satIndex saturation) := by
  have hmax := encode_maxFinite format
  unfold aboveCode Format.Internal.saturateAbove
  rw [maxFiniteBits_eq, nanBits_eq, positiveInfinityBits_eq]
  kernel_notation
  unfold exOf
  cases saturation <;> cases mode <;> cases hd : format.domain <;>
    simp [satIndex, modeIndex, hmax, encode_infinity, encode_exceptional]

/-- P3109 interim report v4.1, §4.7.5: the reference code of the result below the finite range. -/
theorem belowCode_eq (format : Format) (mode : RoundingMode) (saturation : SaturationMode) :
    Format.Internal.encodeDatumNat format (Format.Internal.saturateBelow format saturation mode) =
      belowCode format.bitWidth (sgOf format) (exOf format) (modeIndex mode)
        (satIndex saturation) := by
  have hmin := encode_minFinite format
  unfold belowCode Format.Internal.saturateBelow
  rw [nanBits_eq, negativeInfinityBits_eq]
  kernel_notation
  generalize minFiniteCode format.bitWidth (sgOf format) (exOf format) = code at hmin ⊢
  unfold exOf sgOf
  cases saturation <;> cases mode <;> cases hs : format.signedness <;>
    cases hd : format.domain <;>
    simp [satIndex, modeIndex, hmin, encode_infinity, encode_exceptional]

/-! ## The projection of a finite ratio -/

/-- The smallest finite value is at most zero: minus the largest one when signed, zero when
unsigned. -/
theorem minFinite_toRat (format : Format) :
    format.minFinite.toRat = if sgOf format = 0 then 0 else -format.maxFinite.toRat := by
  unfold Format.minFinite sgOf
  cases hs : format.signedness
  · change format.maxFinite.neg.toRat = if (1 : Nat) = 0 then 0 else -format.maxFinite.toRat
    rw [Numerics.Dyadic.neg_toRat]
    simp
  · simp

/-- The reference code of the saturation of the zero value is zero. -/
theorem encode_saturate_zero (format : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    Format.Internal.encodeDatumNat format
        (format.saturate saturation mode (.finite Numerics.Dyadic.zero)) = 0 := by
  have hmaxpos := format.maxFinite_toRat_pos
  have hmin := minFinite_toRat format
  rw [format.saturate_finite_eq_range]
  have h1 : ¬(Numerics.Dyadic.zero.toRat < format.minFinite.toRat) := by
    rw [hmin]
    split_ifs <;> simp
    linarith
  have h2 : ¬(format.maxFinite.toRat < Numerics.Dyadic.zero.toRat) := by
    simp
    linarith
  rw [ite_eq_right h1, ite_eq_right h2]
  rfl

/--
P3109 interim report v4.1, §§4.7.5 and 4.7.6: `encodeRounded` is the reference code of the
saturation of a rounded dyadic `(-1) ^ s * r * 2 ^ (Qb - beta)`, and of zero for `r = 0`, for
every descriptor, rounding mode, saturation mode, significand and bias `beta` of at least the
exponent bias.
-/
theorem encodeRounded_eq (format : Format) (mode : RoundingMode) (saturation : SaturationMode)
    (negative : Bool) (r Qb beta : Nat) (hbeta : format.exponentBias ≤ beta) :
    Format.Internal.encodeDatumNat format
        (format.saturate saturation mode
          (.finite (if r = 0 then Numerics.Dyadic.zero
            else { negative := negative, significand := r,
                   exponent := (Qb : Int) - (beta : Int) }))) =
      encodeRounded format.bitWidth format.precision (sgOf format) (exOf format)
        (modeIndex mode) (satIndex saturation) format.exponentBias (if negative then 1 else 0) r
        Qb beta := by
  have hmaxpos := format.maxFinite_toRat_pos
  have hmin := minFinite_toRat format
  unfold encodeRounded
  kernel_notation
  simp only [Bool.or_eq_true, Nat.beq_eq]
  by_cases hr : r = 0
  · rw [ite_eq_left hr, ite_eq_left hr]
    exact encode_saturate_zero format mode saturation
  rw [ite_eq_right hr, ite_eq_right hr, format.saturate_finite_eq_range]
  have hexceeds := exceeds_eq format r Qb beta
  have hV : (0 : Rat) < (r : Rat) * (2 : Rat) ^ ((Qb : Int) - (beta : Int)) :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hr) (zpow_pos (by norm_num) _)
  have hmag := magnitudeCode_eq format r Qb beta hr hbeta
  have htF : (Numerics.Dyadic.mk false r ((Qb : Int) - (beta : Int))).toRat =
      (r : Rat) * (2 : Rat) ^ ((Qb : Int) - (beta : Int)) := Numerics.Dyadic.toRat_mk_false _ _
  have htT : (Numerics.Dyadic.mk true r ((Qb : Int) - (beta : Int))).toRat =
      -((r : Rat) * (2 : Rat) ^ ((Qb : Int) - (beta : Int))) := by
    have h := Numerics.Dyadic.neg_toRat (Numerics.Dyadic.mk false r ((Qb : Int) - (beta : Int)))
    rw [htF] at h
    exact h
  generalize exceeds format.bitWidth format.precision (sgOf format) (exOf format)
    format.exponentBias r Qb beta = over at hexceeds ⊢
  generalize (r : Rat) * (2 : Rat) ^ ((Qb : Int) - (beta : Int)) = V at hexceeds hV htF htT
  have hover : over = true ↔ format.maxFinite.toRat < V := by
    rw [hexceeds, decide_eq_true_eq]
  cases negative
  · have h1 : ¬(V < format.minFinite.toRat) := by
      rw [hmin]
      split_ifs <;> linarith
    simp only [Bool.false_eq_true, ite_false, htF, ite_eq_right h1]
    by_cases ho : over = true
    · rw [ite_eq_left (hover.1 ho), ite_eq_left ho]
      exact aboveCode_eq format mode saturation
    · rw [ite_eq_right (fun h => ho (hover.2 h)), ite_eq_right ho]
      unfold Format.Internal.encodeDatumNat
      simp only [beq_iff_eq, hr, ite_false, Bool.false_eq_true]
      exact hmag
  · simp only [ite_true, htT, Nat.one_ne_zero, ite_false]
    by_cases hcond : sgOf format = 0 ∨ over = true
    · have h1 : -V < format.minFinite.toRat := by
        rw [hmin]
        rcases hcond with hsg | ho
        · rw [ite_eq_left hsg]
          linarith
        · have := hover.1 ho
          split_ifs <;> linarith
      rw [ite_eq_left h1, ite_eq_left hcond]
      exact belowCode_eq format mode saturation
    · have hsg : ¬sgOf format = 0 := fun h => hcond (Or.inl h)
      have ho : ¬format.maxFinite.toRat < V := fun h => hcond (Or.inr (hover.2 h))
      have h1 : ¬(-V < format.minFinite.toRat) := by
        rw [hmin, ite_eq_right hsg]
        linarith
      have h2 : ¬(format.maxFinite.toRat < -V) := by linarith
      rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right hcond, signBoundary_eq]
      unfold Format.Internal.encodeDatumNat
      simp only [beq_iff_eq, hr, ite_false, ite_true]
      rw [hmag]

/--
P3109 interim report v4.1, §§4.7.3 to 4.7.6: `projectFinite` is the reference code of the
    nonzero ratio
`(-1) ^ s * n / d`, rounded to the precision grid, saturated and encoded, for every descriptor,
rounding mode, random word, saturation mode and ratio with `n ≠ 0` and `d ≠ 0`.
-/
theorem projectFinite_eq (format : Format) (mode : RoundingMode) (saturation : SaturationMode)
    (negative : Bool) (n d : Nat) (hn : n ≠ 0) (hd : d ≠ 0) :
    Format.Internal.encodeDatumNat format
        (format.saturate saturation mode
          (.finite (format.roundFiniteRatToPrecision mode
            ((if negative then -(n : Rat) else (n : Rat)) / (d : Rat))))) =
      projectFinite format.bitWidth format.precision (sgOf format) (exOf format)
        (modeIndex mode) (modeWidth mode) (modeRandom mode) (satIndex saturation)
        (if negative then 1 else 0) n d := by
  rw [roundFiniteRatToPrecision_eq format mode negative n d hn hd,
    encodeRounded_eq format mode saturation negative _ _ _ (by omega)]
  unfold projectFinite
  rw [exponentBias_eq, size_sub_one hd]
  rfl

/-! ## The projection of a closed value -/

/--
P3109 interim report v4.1, §§4.7.3 to 4.7.6: `project` is the reference code of the projection
    of the closed
value of a class and a ratio, for every descriptor, rounding mode, random word, saturation
mode and input with a sign bit `s ≤ 1` and, for a nonzero finite ratio, a denominator `d ≠ 0`.
-/
theorem project_eq (format : Format) (mode : RoundingMode) (saturation : SaturationMode)
    (cls s n d : Nat) (hs : s ≤ 1) (hd : cls = 0 → n ≠ 0 → d ≠ 0) :
    Format.Internal.encodeDatumNat format
        (format.projectRatValue { rounding := mode, saturation } (closed cls s n d)) =
      project format.bitWidth format.precision (sgOf format) (exOf format) (modeIndex mode)
        (modeWidth mode) (modeRandom mode) (satIndex saturation) cls s n d := by
  have hmax := encode_maxFinite format
  have hmin := encode_minFinite format
  unfold project closed Format.projectRatValue Format.roundRatToPrecision
  rw [nanBits_eq, positiveInfinityBits_eq, negativeInfinityBits_eq, maxFiniteBits_eq]
  kernel_notation
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq]
  by_cases h0 : cls = 0
  · simp only [h0, ite_true]
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true, Nat.cast_zero, neg_zero, ite_self, zero_div]
      have hzero : format.roundFiniteRatToPrecision mode 0 = Numerics.Dyadic.zero := by
        simp [Format.roundFiniteRatToPrecision]
      rw [hzero]
      exact encode_saturate_zero format mode saturation
    · rw [ite_eq_right hn]
      rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
      · exact projectFinite_eq format mode saturation false n d hn (hd h0 hn)
      · exact projectFinite_eq format mode saturation true n d hn (hd h0 hn)
  by_cases h1 : cls = 1
  · simp only [h1, Nat.one_ne_zero, ite_false, ite_true]
    unfold Format.saturate exOf
    cases saturation <;> cases hdom : format.domain <;>
      simp [satIndex, hmax, encode_infinity, encode_exceptional]
  by_cases h2 : cls = 2
  · simp only [h2, ite_false, ite_true, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
    generalize minFiniteCode format.bitWidth (sgOf format) (exOf format) = code at hmin ⊢
    unfold Format.saturate exOf sgOf
    cases saturation <;> cases hsg : format.signedness <;> cases hdom : format.domain <;>
      simp [satIndex, hmin, encode_infinity, encode_exceptional]
  · simp only [h0, h1, h2, ite_false]
    rfl

/--
P3109 interim report v4.1, §§4.7.3 to 4.7.6: the stored reference projection of the closed value
    of a class
and a ratio of natural numbers is the value that stores `project`, for every descriptor,
rounding mode, random word, saturation mode and input.
-/
theorem projectRat_eq (format : Format) (mode : RoundingMode) (saturation : SaturationMode)
    (cls s n d : Nat) (hs : s ≤ 1) (hd : cls = 0 → n ≠ 0 → d ≠ 0) :
    ExecFloat.P3109.projectRat (format := format) (closed cls s n d) mode saturation =
      ExecFloat.P3109.ofNatBits
        (project format.bitWidth format.precision (sgOf format) (exOf format) (modeIndex mode)
          (modeWidth mode) (modeRandom mode) (satIndex saturation) cls s n d) := by
  rw [← project_eq format mode saturation cls s n d hs hd]
  rfl

end FloatLib.Floats.Formats.P3109.KernelPath
