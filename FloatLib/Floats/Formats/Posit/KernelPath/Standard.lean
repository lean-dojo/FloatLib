/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.General.Code
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.RoundTrip
public import FloatLib.Floats.Formats.Posit.Functions.Basic
public import FloatLib.Floats.Formats.Posit.Cast.Precision
public import FloatLib.Numerics.Kernel.RootProof
public meta import FloatLib.Tactic.KernelNotation
public import FloatLib.Numerics.Kernel.ZProof
import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# The kernel posit operations compute the Posit Standard operations

At `es = 2`, the exponent size that the Posit Standard (2022) fixes, the operations of
`KernelPath.Core` on encodings equal the reference operations of `Model.Spec`, for every width
`n ≥ 2` and every operand, zero and NaR included:

* `decode_eq`: the fields read by bit length are those of the reference decoder
  `Model.decodeFiniteDyadicCode`, which scans the regime bit by bit;
* `encode_eq`: `encode` is the direct rounding `DirectDyadicPacking.roundPositiveCode` of a
  positive dyadic, which equals the Posit Standard's rounding (§4.1) of its value;
* `add_eq_spec`, `sub_eq_spec`, `mul_eq_spec`, `div_eq_spec`, `sqrt_eq_spec`, `fma_eq_spec`:
  each operation on the encodings of its operands is the encoding of the reference result
  (§5.4, §5.5, and the FloatLib FMA extension rounded by §4.1).

The proofs reduce each function to the direct exact-dyadic algorithm that
`Model.DirectDyadicArithmetic` already proves equal to the specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.KernelPath

open FloatLib.Numerics FloatLib.Numerics.Kernel
open FloatLib.Floats.Formats.Posit.Model

/-! ## Rounding a stream -/

/--
`roundTail` is the guard-and-sticky rounding of the stream specification: the first `t` bits of
the stream above `base`, plus one when the first discarded bit is set and a later bit or the low
bit of the kept code is set.
-/
theorem roundTail_eq (t base raw w : Nat) :
    roundTail t base raw w =
      if GuardStickyRounding.streamGuard raw w t &&
          (GuardStickyRounding.streamSticky raw w t ||
            (base + GuardStickyRounding.streamPrefix raw w t) % 2 != 0) then
        base + GuardStickyRounding.streamPrefix raw w t + 1
      else base + GuardStickyRounding.streamPrefix raw w t := by
  unfold roundTail GuardStickyRounding.streamGuard GuardStickyRounding.streamSticky
    GuardStickyRounding.streamPrefix
  kernel_notation
  rw [Nat.and_one_is_mod]
  by_cases htw : t < w
  · obtain ⟨s, hs⟩ : ∃ s, w - t = s + 1 := ⟨w - t - 1, by omega⟩
    have hd : t + 1 - w = 0 := by omega
    have hsh : w + 0 - t = s + 1 := by omega
    have hpos := Nat.two_pow_pos s
    have hmod : raw % 2 ^ (s + 1) = raw % 2 ^ s + 2 ^ s * (raw / 2 ^ s % 2) := by
      rw [Nat.pow_succ, Nat.mod_mul]
    have hlt := Nat.mod_lt raw hpos
    simp only [hd, hsh, hs, Nat.pow_zero, Nat.mul_one, ite_eq_left (show t ≤ w by omega),
      ite_eq_left htw, Nat.testBit_eq_decide_div_mod_eq, hmod, Nat.pow_one, Nat.add_sub_cancel]
    clear hmod
    generalize raw / 2 ^ (s + 1) = q
    generalize raw % 2 ^ s = r0 at hlt ⊢
    have hg2 : raw / 2 ^ s % 2 < 2 := Nat.mod_lt _ (by decide)
    generalize raw / 2 ^ s % 2 = g at hg2 ⊢
    rw [Nat.pow_succ]
    generalize 2 ^ s = P at hpos hlt ⊢
    have ho2 : (base + q) % 2 < 2 := Nat.mod_lt _ (by decide)
    generalize (base + q) % 2 = o at ho2 ⊢
    have hiff : (P * 2 + 1 ≤ (r0 + P * g) * 2 + o) ↔ (g = 1 ∧ (r0 ≠ 0 ∨ o ≠ 0)) := by
      rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl <;> simp <;> omega
    simp only [hiff, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne]
  · obtain ⟨d, hd⟩ : ∃ d, t + 1 - w = d + 1 := ⟨t - w, by omega⟩
    have hsh : w + (d + 1) - t = 1 := by omega
    have hprefix : (if t ≤ w then raw / 2 ^ (w - t) else raw * 2 ^ (t - w)) = raw * 2 ^ d := by
      split_ifs with h
      · have hw : w = t := by omega
        subst hw
        have : d = 0 := by omega
        subst this
        simp
      · rw [show t - w = d by omega]
    rw [hd, hsh, ite_eq_right htw, Nat.pow_one, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod_left,
      Nat.mul_div_cancel _ (by decide : 0 < 2), hprefix]
    simp
    omega

/-! ## Decoding -/

variable {format : Format}

/-- A format has one bit more than its payload. -/
theorem bits_eq (format : Format) : format.bits = format.payloadBits + 1 := by
  have := format.bits_ge_two
  unfold Format.payloadBits
  omega

/-- The modulus of a format is `2 ^ (payloadBits + 1)`. -/
theorem modulus_eq (format : Format) : format.modulus = 2 ^ (format.payloadBits + 1) := by
  rw [Format.modulus, bits_eq]

/-- The first regime bit of a `p`-bit magnitude is set exactly from `2 ^ (p - 1)` on. -/
theorem testBit_top {p m : Nat} (hp : 0 < p) (hm : m < 2 ^ p) :
    m.testBit (p - 1) = decide (2 ^ (p - 1) ≤ m) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hpow : 2 ^ p = 2 * 2 ^ (p - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hpos := Nat.two_pow_pos (p - 1)
  have hq : m / 2 ^ (p - 1) < 2 := (Nat.div_lt_iff_lt_mul hpos).2 (by omega)
  by_cases h : 2 ^ (p - 1) ≤ m
  · have : 1 ≤ m / 2 ^ (p - 1) := (Nat.le_div_iff_mul_le hpos).2 (by omega)
    rw [decide_eq_true h, decide_eq_true (by omega)]
  · have : m / 2 ^ (p - 1) = 0 := Nat.div_eq_of_lt (by omega)
    rw [decide_eq_false h, this]
    rfl

/--
The regime run that the reference decoder counts bit by bit is the payload width minus
`tailLength`, for every nonzero magnitude of `p` bits.
-/
theorem countLeadingRun_eq {p m : Nat} (hp : 0 < p) (hpos : 0 < m) (hm : m < 2 ^ p) :
    countLeadingRun m p (m.testBit (p - 1)) = p - tailLength p m := by
  rw [testBit_top hp hm, tailLength_eq hm, complement_eq]
  by_cases h : 2 ^ (p - 1) ≤ m
  · rw [decide_eq_true h, ite_eq_left h, countLeadingRun_true_eq_fixedComplement m p hm]
    by_cases hz : 2 ^ p - 1 - m = 0
    · rw [hz, ite_eq_left rfl, countLeadingRun_zero_false]
      omega
    · rw [ite_eq_right hz,
        countLeadingRun_false_eq_log2 _ p (Nat.pos_of_ne_zero hz) (by omega)]
  · rw [decide_eq_false h, ite_eq_right h, ite_eq_right (by omega),
      countLeadingRun_false_eq_log2 m p hpos hm]

/--
Posit Standard (2022), §3: the reference decoder of a nonzero finite word, which scans the
regime, returns the fields that `significand` and `exponent` read by bit length, for every
standard width. `m` is the magnitude of the word.
-/
theorem decode_eq (format : Format) (negative : Bool) (code m : Nat)
    (hm : (if negative then format.modulus - code else code) = m)
    (hpos : 0 < m) (hlt : m < 2 ^ format.payloadBits) :
    decodeFiniteDyadicCode format negative code =
      { negative
        significand := significand 2 m (tailLength format.payloadBits m)
        exponent := ((exponent format.payloadBits 2 m (tailLength format.payloadBits m) : Nat) :
          Int) - ((bias format.payloadBits 2 : Nat) : Int) } := by
  have hp := format.payloadBits_pos
  have hrun := countLeadingRun_eq hp hpos hlt
  have hz := tailLength_le hlt
  have htop := testBit_top hp hlt
  rw [htop] at hrun
  unfold decodeFiniteDyadicCode
  simp only [hm, hrun, htop, Format.exponentBits, Format.regimeExponentStep]
  generalize tailLength format.payloadBits m = z at hz ⊢
  generalize format.payloadBits = p at hp hz ⊢
  have htrail : p - (p - z) - (if decide (p - z < p) = true then 1 else 0) = z - 1 := by
    by_cases h0 : z = 0
    · subst h0
      simp
    · rw [ite_eq_left (by simpa using (by omega : p - z < p))]
      omega
  have hfb : z - 1 - min 2 (z - 1) = z - 1 - 2 := by omega
  simp only [htrail, hfb]
  congr 1
  · unfold significand fractionBits
    kernel_notation
  · unfold exponent bias regimeBias
    kernel_notation
    generalize m / 2 ^ (z - 1 - 2) % 2 ^ min 2 (z - 1) * 2 ^ (2 - min 2 (z - 1)) = ef
    simp only [Int.ofNat_eq_natCast, Nat.reducePow]
    by_cases h : 2 ^ (p - 1) ≤ m
    · simp only [decide_eq_true h, ite_eq_left h, ite_true]
      omega
    · simp only [decide_eq_false h, ite_eq_right h]
      simp
      omega

/-! ## Rounding -/

/-- The base of a nonnegative regime: `run` ones above `p - run` zeros. -/
theorem regimeBase_eq {p run : Nat} (hrun : run ≤ p) :
    (2 ^ run - 1) * 2 ^ (p - run) = 2 ^ p - 2 ^ (p - run) := by
  rw [Nat.sub_mul, ← Nat.pow_add, Nat.add_sub_cancel' hrun, Nat.one_mul]

/--
Posit Standard (2022), §4.1: `encode` is the direct rounding of a positive dyadic
`M * 2 ^ x`, for every standard width, every nonzero `M` and every exponent, given as
`E = x + 4 * bK`.
-/
theorem encode_eq (format : Format) (M : Nat) (x : Int) (E bK : Nat) (hM : M ≠ 0)
    (hE : (E : Int) = x + 4 * (bK : Int)) :
    DirectDyadicPacking.roundPositiveCode format ⟨false, M, x⟩ =
      encode format.payloadBits 2 bK M E := by
  have hp := format.payloadBits_pos
  have hL : size M - 1 = M.log2 := by
    rw [size_eq_log2, ite_eq_right hM]
    omega
  have hlower : 2 ^ M.log2 ≤ M := Nat.log2_self_le hM
  have hupper : M < 2 ^ (M.log2 + 1) := Nat.lt_log2_self
  unfold DirectDyadicPacking.roundPositiveCode encode
  kernel_notation
  simp only [hL, DirectDyadicPacking.leadingBit_eq_log2, Dyadic.isLessPowerOfTwoAtLeading,
    beq_iff_eq, hM, Bool.or_false, ite_false, Int.ofNat_eq_natCast]
  generalize M.log2 = L at hlower hupper ⊢
  have hregime : (x + (L : Int)).ediv 4 = (((E + L) / 2 ^ 2 : Nat) : Int) - (bK : Int) := by
    change (x + (L : Int)) / 4 = _
    omega
  have hfield : ((x + (L : Int)).emod 4).toNat = (E + L) % 2 ^ 2 := by
    change ((x + (L : Int)) % 4).toNat = _
    omega
  rw [hregime, hfield]
  have hS : E + L = 4 * ((E + L) / 2 ^ 2) + (E + L) % 2 ^ 2 := by
    have := Nat.div_add_mod (E + L) (2 ^ 2)
    omega
  have hef4 : (E + L) % 2 ^ 2 < 4 := Nat.mod_lt _ (by decide)
  generalize (E + L) / 2 ^ 2 = K at hS ⊢
  generalize (E + L) % 2 ^ 2 = ef at hS hef4 ⊢
  have hsm : format.signMaskNat = 2 ^ format.payloadBits := rfl
  have hinterior (regime : Int) (run base : Nat)
      (hbase : DirectDyadicPacking.lowerCandidateFromFields format regime ef M L =
        base + GuardStickyRounding.streamPrefix (ef * 2 ^ L + (M - 2 ^ L)) (L + 2)
          (format.payloadBits - run - 1)) :
      GuardStickyRounding.roundInteriorCodeFromFields format regime ef M L (run + 1) =
        roundTail (format.payloadBits - run - 1) base (ef * 2 ^ L + (M - 2 ^ L)) (L + 2) := by
    rw [GuardStickyRounding.roundInteriorCodeFromFields_eq_roundInteriorCode _ _ _ _ _ _ hlower
      hupper, roundTail_eq]
    unfold GuardStickyRounding.roundInteriorCode
    simp only [hbase, Nat.sub_add_eq, GuardStickyRounding.exactTailRaw,
      GuardStickyRounding.fractionRaw]
  by_cases hreg : bK ≤ K
  · have h1 : ¬(x + (L : Int) < -(4 * ((format.payloadBits - 1 : Nat) : Int))) := by omega
    have h2 : (0 : Int) ≤ (K : Int) - bK := by omega
    have h3 : ((K : Int) - bK).toNat = K - bK := by omega
    simp only [decide_eq_false h1, Bool.false_eq_true, ite_false, ite_eq_left h2,
      ite_eq_left hreg, h3, hsm]
    by_cases hsat : format.payloadBits ≤ K - bK + 1
    · rw [ite_eq_left hsat, ite_eq_left hsat]
    · rw [ite_eq_right hsat, ite_eq_right hsat]
      apply hinterior
      unfold DirectDyadicPacking.lowerCandidateFromFields
      simp only [ite_eq_left h2, h3, ite_eq_right hsat,
        GuardStickyRounding.tailPrefix_eq_streamPrefix _ _ _ _ hlower hupper,
        GuardStickyRounding.exactTailRaw, GuardStickyRounding.fractionRaw, Nat.shiftLeft_eq,
        Nat.one_mul, regimeBase_eq (Nat.le_of_not_le hsat)]
  · have h2 : ¬(0 : Int) ≤ (K : Int) - bK := by omega
    have h3 : (-((K : Int) - bK)).toNat = bK - K := by omega
    simp only [ite_eq_right h2, ite_eq_right hreg, h3]
    by_cases hsat : format.payloadBits ≤ bK - K
    · have h1 : x + (L : Int) < -(4 * ((format.payloadBits - 1 : Nat) : Int)) := by omega
      simp only [decide_eq_true h1, ite_true, ite_eq_left hsat]
    · have h1 : ¬(x + (L : Int) < -(4 * ((format.payloadBits - 1 : Nat) : Int))) := by omega
      simp only [decide_eq_false h1, Bool.false_eq_true, ite_false, ite_eq_right hsat]
      apply hinterior
      unfold DirectDyadicPacking.lowerCandidateFromFields
      simp only [ite_eq_right h2, h3, ite_eq_right hsat,
        GuardStickyRounding.tailPrefix_eq_streamPrefix _ _ _ _ hlower hupper,
        GuardStickyRounding.exactTailRaw, GuardStickyRounding.fractionRaw, Nat.shiftLeft_eq,
        Nat.one_mul]

/-- `roundTail` returns at least its base code. -/
theorem le_roundTail (t base raw w : Nat) : base ≤ roundTail t base raw w := by
  rw [roundTail_eq]
  split_ifs <;> omega

/-- `encode` never returns the zero code. -/
theorem encode_pos (p es bK M E : Nat) (hp : 0 < p) : 0 < encode p es bK M E := by
  have hone := Nat.one_lt_two_pow (Nat.ne_of_gt hp)
  unfold encode
  kernel_notation
  split_ifs with h1 h2 h3
  · omega
  · have hlt : 2 ^ (p - ((E + (size M - 1)) / 2 ^ es - bK + 1)) < 2 ^ p :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    exact lt_of_lt_of_le (by omega) (le_roundTail _ _ _ _)
  · omega
  · exact lt_of_lt_of_le (Nat.two_pow_pos _) (le_roundTail _ _ _ _)

/-- `withSign` with the sign bit of a Boolean: the two's complement for a negative sign. -/
theorem withSign_eq (p : Nat) (s : Bool) (c : Nat) :
    withSign p (if s then 1 else 0) c = if s then 2 ^ (p + 1) - c else c := by
  unfold withSign
  kernel_notation
  cases s <;> simp

/-- Sign restoration on a nonzero magnitude code is `withSign`. -/
theorem restoreSignCode_eq (format : Format) (s : Bool) {c : Nat} (hc : 0 < c) :
    DyadicRounding.restoreSignCode format s c =
      withSign format.payloadBits (if s then 1 else 0) c := by
  simp only [DyadicRounding.restoreSignCode, withSign_eq, modulus_eq, beq_iff_eq,
    ite_eq_right (Nat.ne_of_gt hc)]

/--
Posit Standard (2022), §4.1: the encoding of the direct rounding of a nonzero dyadic is the signed
`encode` of its fields, for every standard width, with the exponent given as
`E = exponent + 4 * bK`.
-/
theorem round_eq (format : Format) (d : FloatLib.Numerics.Dyadic) (E bK : Nat) (hM :
    d.significand ≠ 0)
    (hE : (E : Int) = d.exponent + 4 * (bK : Int)) :
    (DirectDyadicPacking.round format d).toNatBits =
      withSign format.payloadBits (if d.negative then 1 else 0)
        (encode format.payloadBits 2 bK d.significand E) := by
  rw [← DirectDyadicPacking.ofNatBits_roundCode,
    toNatBits_ofNatBits_of_lt _ (DirectDyadicPacking.roundCode_lt_modulus format d)]
  unfold DirectDyadicPacking.roundCode
  rw [ite_eq_right (by simpa using hM)]
  have hmag : DyadicRounding.magnitude d = ⟨false, d.significand, d.exponent⟩ := rfl
  have hpos := encode_pos format.payloadBits 2 bK d.significand E format.payloadBits_pos
  simp only [hmag, encode_eq format d.significand d.exponent E bK hM hE,
    restoreSignCode_eq format d.negative hpos]

/-- The direct rounding of a dyadic with zero significand is the zero word. -/
theorem round_zero (format : Format) (s : Bool) (x : Int) :
    (DirectDyadicPacking.round format ⟨s, 0, x⟩).toNatBits = 0 := by
  unfold DirectDyadicPacking.round
  simp

/--
The signed sum of two aligned nonzero magnitudes, rounded: the three cases of `sumFields` are
the direct rounding of the dyadic that exact addition returns.
-/
theorem round_sum (format : Format) (bK : Nat) (s₁ s₂ : Bool) (a b E : Nat) (x : Int)
    (hb : b ≠ 0) (hx : (E : Int) = x + 4 * (bK : Int)) :
    (if (if s₁ = true then 1 else 0) = (if s₂ = true then 1 else 0) then
        withSign format.payloadBits (if s₁ = true then 1 else 0)
          (encode format.payloadBits 2 bK (a + b) E)
      else if b ≤ a then
        if a = b then 0
        else withSign format.payloadBits (if s₁ = true then 1 else 0)
          (encode format.payloadBits 2 bK (a - b) E)
      else withSign format.payloadBits (if s₂ = true then 1 else 0)
        (encode format.payloadBits 2 bK (b - a) E)) =
      (DirectDyadicPacking.round format
        (if ((if s₁ = true then -Int.ofNat a else Int.ofNat a) +
            if s₂ = true then -Int.ofNat b else Int.ofNat b) = 0 then
          { negative := s₁ && s₂, significand := 0, exponent := 0 }
        else
          { negative := decide (((if s₁ = true then -Int.ofNat a else Int.ofNat a) +
              if s₂ = true then -Int.ofNat b else Int.ofNat b) < 0)
            significand := ((if s₁ = true then -Int.ofNat a else Int.ofNat a) +
              if s₂ = true then -Int.ofNat b else Int.ofNat b).natAbs
            exponent := x })).toNatBits := by
  simp only [Int.ofNat_eq_natCast]
  by_cases hsum : ((if s₁ = true then -(a : Int) else (a : Int)) +
      if s₂ = true then -(b : Int) else (b : Int)) = 0
  · rw [ite_eq_left hsum, round_zero]
    cases s₁ <;> cases s₂ <;>
      simp only [Bool.false_eq_true, ↓reduceIte, zero_ne_one, one_ne_zero] at hsum ⊢ <;>
      first
      | omega
      | (have hab : a = b := by omega
         subst hab
         simp)
  · rw [ite_eq_right hsum, round_eq format _ E bK (by simpa using hsum) hx]
    cases s₁ <;> cases s₂ <;> simp only [Bool.false_eq_true, ↓reduceIte, zero_ne_one, one_ne_zero,
      add_neg_lt_iff_lt_add, neg_add_lt_iff_lt_add, zero_add, add_zero,
      Nat.cast_lt, decide_eq_true_eq] at hsum ⊢
    · rw [ite_eq_right (by omega), show ((a : Int) + b).natAbs = a + b by omega]
    · rcases Nat.lt_trichotomy a b with h | h | h
      · rw [ite_eq_right (by omega), ite_eq_left h,
          show ((a : Int) + -b).natAbs = b - a by omega]
      · exact absurd (by omega) hsum
      · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          show ((a : Int) + -b).natAbs = a - b by omega]
    · rcases Nat.lt_trichotomy a b with h | h | h
      · rw [ite_eq_right (by omega), ite_eq_right (by omega),
          show (-(a : Int) + b).natAbs = b - a by omega]
      · exact absurd (by omega) hsum
      · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h,
          show (-(a : Int) + b).natAbs = a - b by omega]
    · rw [ite_eq_left (by omega), show (-(a : Int) + -b).natAbs = a + b by omega]

/--
`sumFields` is the encoding of the direct rounding of the exact sum of two nonzero dyadics, for
every standard width, with both exponents biased by `4 * bK`.
-/
theorem sumFields_eq (format : Format) (bK : Nat) (s₁ s₂ : Bool) (m₁ m₂ e₁ e₂ : Nat)
    (x₁ x₂ : Int) (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (hx₁ : (e₁ : Int) = x₁ + 4 * (bK : Int))
    (hx₂ : (e₂ : Int) = x₂ + 4 * (bK : Int)) :
    sumFields format.payloadBits 2 bK (if s₁ then 1 else 0) m₁ e₁ (if s₂ then 1 else 0) m₂ e₂ =
      (DirectDyadicPacking.round format
        (FloatLib.Numerics.Dyadic.addFields s₁ m₁ x₁ s₂ m₂ x₂)).toNatBits := by
  unfold sumFields FloatLib.Numerics.Dyadic.addFields
  kernel_notation
  simp only [beq_iff_eq, h₁, h₂, ite_false]
  by_cases hle : x₁ ≤ x₂
  · have hsh : (x₂ - x₁).toNat = e₂ - e₁ := by omega
    have h0 : e₁ - e₂ = 0 := by omega
    have hmin : min e₁ e₂ = e₁ := by omega
    simp only [ite_eq_left hle, hsh, h0, hmin, Nat.pow_zero, Nat.mul_one]
    exact round_sum format bK s₁ s₂ m₁ (m₂ * 2 ^ (e₂ - e₁)) e₁ x₁
      (Nat.mul_ne_zero h₂ (Nat.ne_of_gt (Nat.two_pow_pos _))) hx₁
  · have hsh : (x₁ - x₂).toNat = e₁ - e₂ := by omega
    have h0 : e₂ - e₁ = 0 := by omega
    have hmin : min e₁ e₂ = e₂ := by omega
    simp only [ite_eq_right hle, hsh, h0, hmin, Nat.pow_zero, Nat.mul_one]
    exact round_sum format bK s₁ s₂ (m₁ * 2 ^ (e₁ - e₂)) m₂ e₂ x₂ h₂ hx₂

/-! ## Words -/

/-- The NaR encoding of the kernel path is the sign mask of the format. -/
theorem nar_eq (format : Format) : nar format.payloadBits = format.signMaskNat := by
  unfold nar
  kernel_notation
  rfl

/-- The NaR test on an encoding decides whether the word is NaR. -/
theorem beq_nar (x : Model format) :
    Nat.beq x.toNatBits (nar format.payloadBits) = decide (x = Model.nar format) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_eq, nar_eq]
  exact toNatBits_eq_signMaskNat_iff x

/-- The zero test on an encoding decides whether the word is zero. -/
theorem beq_zero (x : Model format) :
    Nat.beq x.toNatBits 0 = decide (x = Model.zero format) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_eq]
  exact toNatBits_eq_zero_iff x

/-- `magnitude` computes the unsigned magnitude of a word. -/
theorem magnitude_eq (x : Model format) :
    magnitude format.payloadBits x.toNatBits = x.magnitudeBits := by
  rw [magnitudeBits_eq_ite, modulus_eq]
  unfold magnitude nar
  kernel_notation
  rfl

/-- The sign bit of an encoding, as zero or one. -/
theorem sign_eq (x : Model format) :
    Nat.shiftRight x.toNatBits format.payloadBits = if x.signBit then 1 else 0 := by
  have hlt := toNatBits_lt_modulus x
  rw [modulus_eq, Nat.pow_succ] at hlt
  have hsm : format.signMaskNat = 2 ^ format.payloadBits := rfl
  rw [signBit_eq_decide, hsm]
  kernel_notation
  by_cases h : 2 ^ format.payloadBits ≤ x.toNatBits
  · rw [decide_eq_true h, ite_eq_left rfl]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · rw [decide_eq_false h, ite_eq_right (by decide)]
    exact Nat.div_eq_of_lt (by omega)

/-- The exact dyadic that the kernel fields of a word denote. -/
def fields (x : Model format) : FloatLib.Numerics.Dyadic :=
  { negative := x.signBit
    significand := significand 2 x.magnitudeBits (tailLength format.payloadBits x.magnitudeBits)
    exponent :=
      ((exponent format.payloadBits 2 x.magnitudeBits
        (tailLength format.payloadBits x.magnitudeBits) : Nat) : Int) -
        ((bias format.payloadBits 2 : Nat) : Int) }

/--
Posit Standard (2022), §3: a word that is neither zero nor NaR decodes to the dyadic of its
kernel fields, for every standard width.
-/
theorem toDyadic?_eq (x : Model format) (hnar : x ≠ Model.nar format)
    (hzero : x ≠ Model.zero format) : x.toDyadic? = some (fields x) := by
  rw [toDyadic?_eq_code]
  have h1 : (x.toNatBits == format.signMaskNat) = false := by
    simpa using mt (toNatBits_eq_signMaskNat_iff x).1 hnar
  have h2 : (x.toNatBits == 0) = false := by
    simpa using mt (toNatBits_eq_zero_iff x).1 hzero
  simp only [h1, h2, Bool.false_eq_true, ite_false]
  congr 1
  exact decode_eq format x.signBit x.toNatBits x.magnitudeBits rfl
    (Nat.pos_of_ne_zero (magnitudeBits_ne_zero_of_ne_zero x hzero))
    (magnitudeBits_lt_signMask_of_ne_nar x hnar)

/-- The exponent bias at `es = 2` is four times the regime bias. -/
theorem bias_eq (p : Nat) : ((bias p 2 : Nat) : Int) = 4 * ((regimeBias p : Nat) : Int) := by
  unfold bias
  kernel_notation
  push_cast
  omega

/-- The biased exponent of a word is the exponent of its dyadic plus the bias. -/
theorem exponent_fields (x : Model format) :
    ((exponent format.payloadBits 2 x.magnitudeBits
      (tailLength format.payloadBits x.magnitudeBits) : Nat) : Int) =
      (fields x).exponent + 4 * ((regimeBias format.payloadBits : Nat) : Int) := by
  have := bias_eq format.payloadBits
  change _ = _ - _ + _
  omega

/-- A word other than NaR has a rational value. -/
theorem exists_toRat? (x : Model format) (hnar : x ≠ Model.nar format) :
    ∃ q, x.toRat? = some q := by
  cases h : x.toRat? with
  | none => exact absurd ((isNaR_eq_true_iff x).1 ((toRat?_eq_none_iff x).1 h)) hnar
  | some q => exact ⟨q, rfl⟩

/-! ## The operations -/

/--
Posit Standard (2022), §5.4: `add` on the encodings of two words is the encoding of their
specified sum, for every standard width and all operands.
-/
theorem add_eq_spec (x y : Model format) :
    add format.payloadBits 2 x.toNatBits y.toNatBits = (Spec.addition x y).toNatBits := by
  unfold add
  simp only [beq_nar, beq_zero, (FloatLib.Numerics.Kernel.Z.casesOn_eq_ite Iff.rfl),
    Bool.or_eq_true, decide_eq_true_eq]
  by_cases hx : x = Model.nar format
  · subst hx
    simp [nar_eq]
  by_cases hy : y = Model.nar format
  · subst hy
    simp [nar_eq]
  obtain ⟨qx, hqx⟩ := exists_toRat? x hx
  obtain ⟨qy, hqy⟩ := exists_toRat? y hy
  rw [ite_eq_right (by tauto)]
  by_cases hx0 : x = Model.zero format
  · subst hx0
    simp [Spec.addition, hqy, roundRat_toRat? y qy hqy]
  by_cases hy0 : y = Model.zero format
  · subst hy0
    simp [Spec.addition, hqx, roundRat_toRat? x qx hqx, hx0]
  rw [ite_eq_right hx0, ite_eq_right hy0, ← DirectDyadicArithmetic.add_eq_spec]
  unfold sumFinite DirectDyadicArithmetic.add
  rw [toDyadic?_eq x hx hx0, toDyadic?_eq y hy hy0]
  simp only [magnitude_eq, sign_eq]
  exact sumFields_eq format _ x.signBit y.signBit _ _ _ _ _ _ (significand_ne_zero _ _ _)
    (significand_ne_zero _ _ _) (exponent_fields x) (exponent_fields y)

/-- `neg` on an encoding is the encoding of the negated word. -/
theorem neg_eq (x : Model format) :
    neg format.payloadBits x.toNatBits = (Model.negate x).toNatBits := by
  unfold neg Model.negate
  kernel_notation
  rw [Nat.and_two_pow_sub_one_eq_mod, modulus_eq]
  change _ = (BitVec.ofNat format.bits _).toNat
  rw [BitVec.toNat_ofNat, bits_eq]

/--
Posit Standard (2022), §5.4: `sub` on the encodings of two words is the encoding of their
specified difference, for every standard width and all operands.
-/
theorem sub_eq_spec (x y : Model format) :
    sub format.payloadBits 2 x.toNatBits y.toNatBits = (Spec.subtraction x y).toNatBits := by
  unfold sub
  simp only [beq_nar, beq_zero, (FloatLib.Numerics.Kernel.Z.casesOn_eq_ite Iff.rfl),
    Bool.or_eq_true, decide_eq_true_eq]
  by_cases hx : x = Model.nar format
  · subst hx
    simp [nar_eq]
  by_cases hy : y = Model.nar format
  · subst hy
    simp [nar_eq]
  obtain ⟨qx, hqx⟩ := exists_toRat? x hx
  obtain ⟨qy, hqy⟩ := exists_toRat? y hy
  rw [ite_eq_right (by tauto)]
  by_cases hy0 : y = Model.zero format
  · subst hy0
    simp [Spec.subtraction, hqx, roundRat_toRat? x qx hqx]
  by_cases hx0 : x = Model.zero format
  · subst hx0
    simp [Spec.subtraction, hqy, hy0, neg_eq, roundRat_neg, roundRat_toRat? y qy hqy]
  rw [ite_eq_right hy0, ite_eq_right hx0, ← DirectDyadicArithmetic.sub_eq_spec]
  unfold sumFinite DirectDyadicArithmetic.sub
  rw [toDyadic?_eq x hx hx0, toDyadic?_eq y hy hy0]
  simp only [magnitude_eq, sign_eq]
  have hflip : Nat.sub 1 (if y.signBit = true then 1 else 0) = if (!y.signBit) = true then 1
    else 0 := by
    cases y.signBit <;> rfl
  rw [hflip]
  exact sumFields_eq format _ x.signBit (!y.signBit) _ _ _ _ _ _ (significand_ne_zero _ _ _)
    (significand_ne_zero _ _ _) (exponent_fields x) (exponent_fields y)

/--
Posit Standard (2022), §5.4: `mul` on the encodings of two words is the encoding of their
specified product, for every standard width and all operands.
-/
theorem mul_eq_spec (x y : Model format) :
    mul format.payloadBits 2 x.toNatBits y.toNatBits = (Spec.multiplication x y).toNatBits := by
  unfold mul
  simp only [beq_nar, beq_zero, (FloatLib.Numerics.Kernel.Z.casesOn_eq_ite Iff.rfl),
    Bool.or_eq_true, decide_eq_true_eq]
  by_cases hx : x = Model.nar format
  · subst hx
    simp [nar_eq]
  by_cases hy : y = Model.nar format
  · subst hy
    simp [nar_eq]
  obtain ⟨qx, hqx⟩ := exists_toRat? x hx
  obtain ⟨qy, hqy⟩ := exists_toRat? y hy
  rw [ite_eq_right (by tauto)]
  by_cases hx0 : x = Model.zero format
  · subst hx0
    simp [Spec.multiplication, hqy]
  by_cases hy0 : y = Model.zero format
  · subst hy0
    simp [Spec.multiplication, hqx]
  rw [ite_eq_right (by tauto), ← DirectDyadicArithmetic.mul_eq_spec]
  unfold DirectDyadicArithmetic.mul
  rw [toDyadic?_eq x hx hx0, toDyadic?_eq y hy hy0]
  simp only [magnitude_eq, sign_eq]
  have hxor : Nat.xor (if x.signBit = true then 1 else 0) (if y.signBit = true then 1 else 0) =
      if (Bool.xor x.signBit y.signBit) = true then 1 else 0 := by
    cases x.signBit <;> cases y.signBit <;> rfl
  rw [hxor]
  have hx' := exponent_fields x
  have hy' := exponent_fields y
  exact (round_eq format (FloatLib.Numerics.Dyadic.mul (fields x) (fields y)) _ _
    (Nat.mul_ne_zero (significand_ne_zero _ _ _) (significand_ne_zero _ _ _)) (by
      change ((Nat.add _ _ : Nat) : Int) = (fields x).exponent + (fields y).exponent +
        4 * ((Nat.mul 2 (regimeBias format.payloadBits) : Nat) : Int)
      kernel_notation
      push_cast
      omega)).symm

/--
FloatLib FMA extension with Posit Standard (2022), §4.1 rounding: `fma` on the encodings of
three words is the encoding of the specified `x * y + z` rounded once, for every standard width
and all operands.
-/
theorem fma_eq_spec (x y z : Model format) :
    fma format.payloadBits 2 x.toNatBits y.toNatBits z.toNatBits =
      (Spec.fma x y z).toNatBits := by
  unfold fma
  simp only [beq_nar, beq_zero, (FloatLib.Numerics.Kernel.Z.casesOn_eq_ite Iff.rfl),
    Bool.or_eq_true, decide_eq_true_eq]
  by_cases hx : x = Model.nar format
  · subst hx
    simp [nar_eq]
  by_cases hy : y = Model.nar format
  · subst hy
    simp [nar_eq]
  by_cases hz : z = Model.nar format
  · subst hz
    simp [nar_eq]
  obtain ⟨qx, hqx⟩ := exists_toRat? x hx
  obtain ⟨qy, hqy⟩ := exists_toRat? y hy
  obtain ⟨qz, hqz⟩ := exists_toRat? z hz
  rw [ite_eq_right (by tauto)]
  by_cases hx0 : x = Model.zero format
  · subst hx0
    simp [Spec.fma, hqy, hqz, roundRat_toRat? z qz hqz]
  by_cases hy0 : y = Model.zero format
  · subst hy0
    simp [Spec.fma, hqx, hqz, roundRat_toRat? z qz hqz]
  rw [ite_eq_right (by tauto)]
  by_cases hz0 : z = Model.zero format
  · subst hz0
    simp [Spec.fma, Spec.multiplication, hqx, hqy, mul_eq_spec]
  rw [ite_eq_right hz0, ← DirectDyadicArithmetic.fma_eq_spec]
  unfold DirectDyadicArithmetic.fma
  rw [toDyadic?_eq x hx hx0, toDyadic?_eq y hy hy0, toDyadic?_eq z hz hz0]
  simp only [magnitude_eq, sign_eq]
  have hxor : Nat.xor (if x.signBit = true then 1 else 0) (if y.signBit = true then 1 else 0) =
      if (Bool.xor x.signBit y.signBit) = true then 1 else 0 := by
    cases x.signBit <;> cases y.signBit <;> rfl
  rw [hxor]
  have hx' := exponent_fields x
  have hy' := exponent_fields y
  have hz' := exponent_fields z
  have hb := bias_eq format.payloadBits
  exact sumFields_eq format _ (Bool.xor x.signBit y.signBit) z.signBit _ _ _ _
    ((fields x).exponent + (fields y).exponent) (fields z).exponent
    (Nat.mul_ne_zero (significand_ne_zero _ _ _) (significand_ne_zero _ _ _))
    (significand_ne_zero _ _ _)
    (by
      show ((Nat.add _ _ : Nat) : Int) = _ + 4 * ((Nat.mul 2 _ : Nat) : Int)
      kernel_notation
      push_cast
      omega)
    (by
      show ((Nat.add _ _ : Nat) : Int) = _ + 4 * ((Nat.mul 2 _ : Nat) : Int)
      kernel_notation
      push_cast
      omega)

/-- The leading bit of a decoded significand is at its number of fraction bits. -/
theorem significand_log2 (es m z : Nat) : (significand es m z).log2 = fractionBits es z := by
  have hpos := Nat.two_pow_pos (fractionBits es z)
  have hlt := Nat.mod_lt m hpos
  have hne : significand es m z ≠ 0 := significand_ne_zero es m z
  rw [Nat.log2_eq_iff hne]
  unfold significand
  kernel_notation
  rw [Nat.pow_succ]
  omega

/-- `jam` is the sticky fold of the reference prefix kernels. -/
theorem jam_eq (q r : Nat) : jam q r = StickyPrefix.jamRemainder q r := by
  unfold jam StickyPrefix.jamRemainder
  kernel_notation
  by_cases h : r = 0 <;> simp [h]

/-- A jammed prefix is at least the prefix. -/
theorem le_jam (q r : Nat) : q ≤ jam q r := by
  unfold jam
  kernel_notation
  split_ifs
  · exact Nat.le_refl q
  · exact Nat.left_le_or

/-- The biased exponent of a decoded magnitude stays within `5 * p` of the bias. -/
theorem exponent_bounds {p m z : Nat} (hp : 0 < p) (hz : z ≤ p) :
    4 * regimeBias p ≤ exponent p 2 m z + 5 * p ∧
      exponent p 2 m z < 4 * regimeBias p + 4 * p + 4 := by
  have hfield : m / 2 ^ (z - 1 - 2) % 2 ^ min 2 (z - 1) * 2 ^ (2 - min 2 (z - 1)) < 4 := by
    have hlt := Nat.mod_lt (m / 2 ^ (z - 1 - 2)) (Nat.two_pow_pos (min 2 (z - 1)))
    rcases (by omega : min 2 (z - 1) = 0 ∨ min 2 (z - 1) = 1 ∨ min 2 (z - 1) = 2) with h | h | h <;>
      rw [h] at hlt ⊢ <;> omega
  unfold exponent regimeBias
  kernel_notation
  generalize m / 2 ^ (z - 1 - 2) % 2 ^ min 2 (z - 1) * 2 ^ (2 - min 2 (z - 1)) = ef at hfield
  simp only [Nat.reducePow]
  split_ifs <;> omega

/--
Posit Standard (2022), §4.1: `quotient` is the direct rounding of the quotient of two positive
dyadics from `p + 1` quotient bits and the remainder, for every standard width. The exponent is
given as `E₀ - steps = n.exponent - d.exponent + log₂ n - log₂ d - steps + 4 * bK` for every
number of steps up to `p + 1`.
-/
theorem quotient_eq (format : Format) (n d : FloatLib.Numerics.Dyadic)
    (hn : n.significand ≠ 0) (hd : d.significand ≠ 0) (hnn : n.negative = false)
    (hdn : d.negative = false) (E₀ bK : Nat)
    (hE : ∀ steps : Nat, steps ≤ format.payloadBits + 1 →
      ((E₀ - steps : Nat) : Int) = n.exponent - d.exponent + (n.significand.log2 : Int) -
        (d.significand.log2 : Int) - (steps : Int) + 4 * (bK : Int)) :
    DirectDyadicQuotient.roundPositiveCode format n d =
      quotient format.payloadBits 2 bK n.significand n.significand.log2 d.significand
        d.significand.log2 E₀ := by
  have hp := format.payloadBits_pos
  unfold DirectDyadicQuotient.roundPositiveCode DirectDyadicQuotient.quotientPrefix
    DirectDyadicQuotient.prefixAtLeading DirectDyadicQuotient.normalizeSignificands
    DirectDyadicQuotient.prefixLeading quotient
  simp only [hnn, hdn, Bool.or_false, Int.ofNat_eq_natCast, Nat.shiftLeft_eq]
  kernel_notation
  have hlowx := Nat.log2_self_le hn
  have hupy : d.significand < 2 ^ (d.significand.log2 + 1) := Nat.lt_log2_self
  generalize n.significand.log2 = fx at hlowx hE ⊢
  generalize d.significand.log2 = fy at hupy hE ⊢
  generalize n.significand = sx at hn hlowx ⊢
  generalize d.significand = sy at hd hupy ⊢
  have hNlow : 2 ^ max fx fy ≤ sx * 2 ^ (max fx fy - fx) :=
    calc 2 ^ max fx fy = 2 ^ fx * 2 ^ (max fx fy - fx) := by
          rw [← Nat.pow_add]
          congr 1
          omega
      _ ≤ sx * 2 ^ (max fx fy - fx) := Nat.mul_le_mul_right _ hlowx
  have hDup : sy * 2 ^ (max fx fy - fy) < 2 ^ (max fx fy + 1) :=
    calc sy * 2 ^ (max fx fy - fy) < 2 ^ (fy + 1) * 2 ^ (max fx fy - fy) :=
          Nat.mul_lt_mul_of_pos_right hupy (Nat.two_pow_pos _)
      _ = 2 ^ (max fx fy + 1) := by
          rw [← Nat.pow_add]
          congr 1
          omega
  have hDpos : 0 < sy * 2 ^ (max fx fy - fy) :=
    Nat.mul_pos (Nat.pos_of_ne_zero hd) (Nat.two_pow_pos _)
  generalize sx * 2 ^ (max fx fy - fx) = N at hNlow ⊢
  generalize sy * 2 ^ (max fx fy - fy) = D at hDup hDpos ⊢
  have hsteps : (if N < D then format.payloadBits + 1 else format.payloadBits) =
      (if D ≤ N then format.payloadBits else format.payloadBits + 1) := by
    split_ifs <;> omega
  rw [hsteps]
  have hstepsBound : format.payloadBits ≤
      (if D ≤ N then format.payloadBits else format.payloadBits + 1) ∧
      (if D ≤ N then format.payloadBits else format.payloadBits + 1) ≤
        format.payloadBits + 1 := by
    split_ifs <;> omega
  generalize (if D ≤ N then format.payloadBits else format.payloadBits + 1) = steps
    at hstepsBound ⊢
  have hquot : 0 < N * 2 ^ steps / D := by
    apply Nat.div_pos _ hDpos
    have h2 : 2 ^ 1 ≤ 2 ^ steps := Nat.pow_le_pow_right (by decide) (by omega)
    calc D ≤ 2 ^ max fx fy * 2 ^ 1 := by rw [← Nat.pow_add]; exact Nat.le_of_lt hDup
      _ ≤ N * 2 ^ steps := Nat.mul_le_mul hNlow h2
  have hM : jam (N * 2 ^ steps / D) (N * 2 ^ steps % D) ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le hquot (le_jam _ _))
  have hnonzero : ¬((sx == 0 || sy == 0) = true) := by simp [hn, hd]
  rw [ite_eq_right hnonzero, ← jam_eq]
  exact encode_eq format _ _ (E₀ - steps) bK hM (hE steps hstepsBound.2)

/--
Posit Standard (2022), §5.4: `div` on the encodings of two words is the encoding of their
specified quotient, for every standard width and all operands, NaR for a zero divisor.
-/
theorem div_eq_spec (x y : Model format) :
    div format.payloadBits 2 x.toNatBits y.toNatBits = (Spec.division x y).toNatBits := by
  unfold div
  simp only [beq_nar, beq_zero, (FloatLib.Numerics.Kernel.Z.casesOn_eq_ite Iff.rfl),
    Bool.or_eq_true, decide_eq_true_eq]
  by_cases hx : x = Model.nar format
  · subst hx
    simp [nar_eq]
  by_cases hy : y = Model.nar format
  · subst hy
    simp [nar_eq]
  by_cases hy0 : y = Model.zero format
  · subst hy0
    simp [nar_eq]
  obtain ⟨qx, hqx⟩ := exists_toRat? x hx
  obtain ⟨qy, hqy⟩ := exists_toRat? y hy
  have hqy0 : qy ≠ 0 := by
    rintro rfl
    exact hy0 ((roundRat_toRat? y 0 hqy).symm.trans (roundRat_zero format))
  rw [ite_eq_right (by tauto)]
  by_cases hx0 : x = Model.zero format
  · subst hx0
    simp [Spec.division, hqy, hqy0]
  rw [ite_eq_right hx0, ← DirectDyadicArithmetic.div_eq_spec]
  unfold DirectDyadicArithmetic.div DirectDyadicArithmetic.divDecoded
  rw [toDyadic?_eq x hx hx0, toDyadic?_eq y hy hy0]
  simp only [magnitude_eq, sign_eq]
  rw [← DirectDyadicQuotient.roundCode_eq_toNatBits]
  have hp := format.payloadBits_pos
  have hzx : tailLength format.payloadBits x.magnitudeBits ≤ format.payloadBits :=
    tailLength_le (magnitudeBits_lt_signMask_of_ne_nar x hx)
  have hzy : tailLength format.payloadBits y.magnitudeBits ≤ format.payloadBits :=
    tailLength_le (magnitudeBits_lt_signMask_of_ne_nar y hy)
  have hbx := exponent_bounds (m := x.magnitudeBits) hp hzx
  have hby := exponent_bounds (m := y.magnitudeBits) hp hzy
  have hb := bias_eq format.payloadBits
  have hrb : regimeBias format.payloadBits = 8 * (format.payloadBits + 1) := rfl
  have hlx := significand_log2 2 x.magnitudeBits (tailLength format.payloadBits x.magnitudeBits)
  have hly := significand_log2 2 y.magnitudeBits (tailLength format.payloadBits y.magnitudeBits)
  have hsx := significand_ne_zero 2 x.magnitudeBits (tailLength format.payloadBits x.magnitudeBits)
  have hsy := significand_ne_zero 2 y.magnitudeBits (tailLength format.payloadBits y.magnitudeBits)
  have hfy : fractionBits 2 (tailLength format.payloadBits y.magnitudeBits) ≤
      format.payloadBits := by
    unfold fractionBits
    kernel_notation
    omega
  have hxor : Nat.xor (if x.signBit = true then 1 else 0) (if y.signBit = true then 1 else 0) =
      if (Bool.xor x.signBit y.signBit) = true then 1 else 0 := by
    cases x.signBit <;> cases y.signBit <;> rfl
  have hquotient := quotient_eq format (DyadicRounding.magnitude (fields x))
    (DyadicRounding.magnitude (fields y)) hsx hsy rfl rfl
    (exponent format.payloadBits 2 x.magnitudeBits (tailLength format.payloadBits x.magnitudeBits) +
        bias format.payloadBits 2 +
        fractionBits 2 (tailLength format.payloadBits x.magnitudeBits) -
      (exponent format.payloadBits 2 y.magnitudeBits
          (tailLength format.payloadBits y.magnitudeBits) +
        fractionBits 2 (tailLength format.payloadBits y.magnitudeBits)))
    (regimeBias format.payloadBits) (by
      intro steps hsteps
      change _ = ((exponent _ _ _ _ : Nat) : Int) - ((bias _ _ : Nat) : Int) -
        (((exponent _ _ _ _ : Nat) : Int) - ((bias _ _ : Nat) : Int)) +
        ((significand _ _ _).log2 : Int) - ((significand _ _ _).log2 : Int) - _ + _
      rw [hlx, hly]
      omega)
  unfold DirectDyadicQuotient.roundCode
  simp only [fields, DyadicRounding.magnitude, beq_iff_eq, hsx, hsy, ite_false] at hquotient ⊢
  rw [hquotient, hlx, hly, hxor,
    restoreSignCode_eq format _ (by
      unfold quotient
      exact encode_pos _ _ _ _ _ hp)]
  rfl

/--
Posit Standard (2022), §4.1: `ofRatio` stores the rounding of the ratio of two natural numbers
with a sign, for every standard width, every numerator and every nonzero denominator.
-/
theorem ofRatio_eq (format : Format) (negative : Bool) (num den : Nat) (hden : den ≠ 0) :
    Model.ofNatBits (ofRatio format.payloadBits 2 (if negative then 1 else 0) num den) =
      roundRat format ((if negative then -(num : Rat) else (num : Rat)) / (den : Rat)) := by
  have hp := format.payloadBits_pos
  unfold ofRatio
  simp only [(FloatLib.Numerics.Kernel.Z.casesOn_eq_ite Iff.rfl), Nat.beq_eq]
  by_cases hnum : num = 0
  · subst hnum
    simp
    rfl
  rw [ite_eq_right hnum]
  have hla : Nat.sub (size num) 1 = num.log2 := by
    change size num - 1 = _
    rw [size_eq_log2, ite_eq_right hnum]
    omega
  have hlb : Nat.sub (size den) 1 = den.log2 := by
    change size den - 1 = _
    rw [size_eq_log2, ite_eq_right hden]
    omega
  have hvalue : (if negative then -(num : Rat) else (num : Rat)) / (den : Rat) =
      (FloatLib.Numerics.Dyadic.mk negative num 0).toRat /
        (FloatLib.Numerics.Dyadic.mk false den 0).toRat := by
    cases negative <;>
      simp [FloatLib.Numerics.Dyadic.toRat, FloatLib.Numerics.Dyadic.signedSignificand]
  have hdenRat : (FloatLib.Numerics.Dyadic.mk false den 0).toRat ≠ 0 := by
    simp [FloatLib.Numerics.Dyadic.toRat, FloatLib.Numerics.Dyadic.signedSignificand, hden]
  have hround := DirectDyadicQuotient.round_eq_reference format
    (FloatLib.Numerics.Dyadic.mk negative num 0) (FloatLib.Numerics.Dyadic.mk false den 0)
  rw [ite_eq_right hdenRat] at hround
  rw [hvalue, ← hround, ← DirectDyadicQuotient.ofNatBits_roundCode]
  congr 1
  unfold DirectDyadicQuotient.roundCode
  have hquotient := quotient_eq format
    (DyadicRounding.magnitude (FloatLib.Numerics.Dyadic.mk negative num 0))
    (DyadicRounding.magnitude (FloatLib.Numerics.Dyadic.mk false den 0)) hnum hden rfl rfl
    (Nat.succ (Nat.shiftRight (Nat.add den.log2 (Nat.succ format.payloadBits)) 2) * 2 ^ 2 +
      num.log2 - den.log2)
    (Nat.succ (Nat.shiftRight (Nat.add den.log2 (Nat.succ format.payloadBits)) 2)) (by
      intro steps hsteps
      change _ = (0 : Int) - 0 + (num.log2 : Int) - (den.log2 : Int) - _ + _
      kernel_notation
      simp only [Nat.reducePow]
      omega)
  simp only [DyadicRounding.magnitude, beq_iff_eq, hnum, hden, ite_false, Bool.xor_false]
    at hquotient ⊢
  rw [hla, hlb, hquotient, restoreSignCode_eq format _ (by
      unfold quotient
      exact encode_pos _ _ _ _ _ hp)]
  kernel_notation

/--
Posit Standard (2022), §5.5: `sqrt` on the encoding of a word is the encoding of its specified
square root, for every standard width and every operand, NaR for a negative value.
-/
theorem sqrt_eq_spec (x : Model format) :
    sqrt format.payloadBits 2 x.toNatBits = (Spec.sqrt x).toNatBits := by
  unfold sqrt
  simp only [beq_zero, (FloatLib.Numerics.Kernel.Z.casesOn_eq_ite Iff.rfl), decide_eq_true_eq]
  have hsign := signBit_eq_decide x
  have hble : (Nat.ble (nar format.payloadBits) x.toNatBits = true) =
      (format.signMaskNat ≤ x.toNatBits) := by
    rw [nar_eq, Nat.ble_eq]
  simp only [hble]
  by_cases hx : x = Model.nar format
  · subst hx
    simp [nar_eq]
  by_cases hneg : format.signMaskNat ≤ x.toNatBits
  · rw [ite_eq_left hneg]
    have hx0 : x ≠ Model.zero format := by
      rintro rfl
      rw [zero_toNatBits] at hneg
      exact absurd hneg (Nat.not_le.2 format.signMaskNat_pos)
    have hs : x.signBit = true := by
      rw [hsign]
      exact decide_eq_true hneg
    have hspec : Spec.sqrt x = Model.nar format := by
      unfold Spec.sqrt
      rw [toRat?_eq_toDyadic?_map, toDyadic?_eq x hx hx0]
      have hlt : (fields x).toRat < 0 :=
        FloatLib.Numerics.Dyadic.toRat_neg_of_significand_ne_zero _
          (significand_ne_zero _ _ _) hs
      simp [hlt]
    rw [hspec, nar_toNatBits, nar_eq]
  rw [ite_eq_right hneg]
  by_cases hx0 : x = Model.zero format
  · subst hx0
    simp
  rw [ite_eq_right hx0, ← DirectDyadicArithmetic.sqrt_eq_spec]
  have hs : x.signBit = false := by
    rw [hsign]
    exact decide_eq_false hneg
  have hmag : x.magnitudeBits = x.toNatBits := by
    rw [magnitudeBits_eq_ite, ite_eq_right hneg]
  have hpos : 0 < (fields x).toRat :=
    FloatLib.Numerics.Dyadic.toRat_pos_of_significand_ne_zero _ (significand_ne_zero _ _ _) hs
  have hless : (fields x).isLess FloatLib.Numerics.Dyadic.zero = false := by
    rw [FloatLib.Numerics.Dyadic.isLess_eq_decide]
    simpa using hpos.le
  unfold DirectDyadicArithmetic.sqrt
  rw [toDyadic?_eq x hx hx0]
  simp only [hless, Bool.false_eq_true, ite_false]
  unfold DirectDyadicSquareRoot.round
  rw [toNatBits_ofNatBits_of_lt _ (DirectDyadicSquareRoot.roundCode_lt_modulus format _)]
  unfold DirectDyadicSquareRoot.roundCode DirectDyadicSquareRoot.rootPrefix
    DirectDyadicSquareRoot.prefixAtPrecision DirectDyadicSquareRoot.prefixPrecision
    DirectDyadicSquareRoot.truncatedRoot DirectDyadicSquareRoot.squareRemainder
    DirectDyadicSquareRoot.scaledRadicand DirectDyadicSquareRoot.exponentParity
  simp only [fields, hs, hmag, beq_iff_eq, significand_ne_zero, Bool.or_false, ite_false,
    Int.ofNat_eq_natCast]
  kernel_notation
  have hbn : bias format.payloadBits 2 = 4 * regimeBias format.payloadBits := by
    unfold bias
    kernel_notation
    omega
  have hrb : regimeBias format.payloadBits = 8 * (format.payloadBits + 1) := rfl
  have hsig := significand_ne_zero 2 x.toNatBits (tailLength format.payloadBits x.toNatBits)
  generalize significand 2 x.toNatBits (tailLength format.payloadBits x.toNatBits) = sig
    at hsig ⊢
  generalize exponent format.payloadBits 2 x.toNatBits
    (tailLength format.payloadBits x.toNatBits) = e
  have hpar : (((e : Int) - ((bias format.payloadBits 2 : Nat) : Int)).emod 2).toNat =
      e &&& 1 := by
    rw [Nat.and_one_is_mod, hbn]
    change (((e : Int) - ((4 * regimeBias format.payloadBits : Nat) : Int)) % 2).toNat = e % 2
    push_cast
    omega
  rw [hpar, isqrt_eq, ← jam_eq]
  have hroot : 0 < Nat.sqrt (sig * 2 ^ ((e &&& 1) + 2 * format.payloadBits)) :=
    Nat.sqrt_pos.2 (Nat.mul_pos (Nat.pos_of_ne_zero hsig) (Nat.two_pow_pos _))
  exact (encode_eq format _ _ _ _ (Nat.ne_of_gt (lt_of_lt_of_le hroot (le_jam _ _))) (by
    change _ = ((e : Int) - ((bias format.payloadBits 2 : Nat) : Int)) / 2 - _ + _
    rw [hbn]
    simp only [Nat.pow_one]
    push_cast
    omega)).symm

/-! ## Order and neighbours -/

/-- The comparison key of a word is its signed code plus the sign bit. -/
theorem signedKey_toNatBits (x : Model format) :
    ((signedKey format.payloadBits x.toNatBits : Nat) : Int) =
      x.signedCode + ((2 ^ format.payloadBits : Nat) : Int) := by
  have hlt := toNatBits_lt_modulus x
  rw [modulus_eq] at hlt
  rw [signedKey_eq hlt]
  have hmod : (2 : Nat) ^ format.bits = 2 ^ (format.payloadBits + 1) := modulus_eq format
  change _ = x.bits.toInt + _
  rw [BitVec.toInt_eq_toNat_cond, hmod]
  change _ = (if 2 * x.toNatBits < _ then (x.toNatBits : Int) else _) + _
  rw [Nat.pow_succ] at hlt ⊢
  by_cases h : x.toNatBits < 2 ^ format.payloadBits
  · rw [ite_eq_left h, ite_eq_left (by omega)]
    push_cast
    rfl
  · rw [ite_eq_right h, ite_eq_right (by omega)]
    change ((x.toNatBits - 2 ^ format.payloadBits : Nat) : Int) =
      (x.toNatBits : Int) - ((2 ^ format.payloadBits * 2 : Nat) : Int) + _
    omega

/-- Posit Standard (2022), §5.3: `lt` on two encodings is the strict comparison of the words,
with NaR least, for every standard width. -/
theorem lt_eq (x y : Model format) :
    lt format.payloadBits x.toNatBits y.toNatBits = Model.compareLess x y := by
  have hx := signedKey_toNatBits x
  have hy := signedKey_toNatBits y
  rw [Bool.eq_iff_iff, compareLess_eq_true_iff]
  unfold lt
  rw [Nat.ble_eq]
  change _ ↔ x.signedCode < y.signedCode
  change signedKey _ _ + 1 ≤ signedKey _ _ ↔ _
  omega

/-- Posit Standard (2022), §5.3: `le` on two encodings is the comparison of the words, with NaR
least, for every standard width. -/
theorem le_eq (x y : Model format) :
    le format.payloadBits x.toNatBits y.toNatBits = Model.compareLessEqual x y := by
  have hx := signedKey_toNatBits x
  have hy := signedKey_toNatBits y
  rw [Bool.eq_iff_iff, compareLessEqual_eq_true_iff]
  unfold le
  rw [Nat.ble_eq]
  change _ ↔ x.signedCode ≤ y.signedCode
  omega

/-- Posit Standard (2022), §5.2: `abs` on an encoding is the encoding of the absolute value,
NaR for NaR, for every standard width. -/
theorem abs_eq (x : Model format) :
    abs format.payloadBits x.toNatBits = (Model.abs x).toNatBits := by
  have hxlt := toNatBits_lt_modulus x
  rw [modulus_eq] at hxlt
  have hpos := Nat.two_pow_pos format.payloadBits
  have hless : Model.compareLess x (Model.zero format) =
      decide (2 ^ format.payloadBits ≤ x.toNatBits) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, ← lt_eq, zero_toNatBits]
    unfold lt
    rw [Nat.ble_eq, signedKey_eq hxlt, signedKey_eq (Nat.two_pow_pos _), ite_eq_left hpos]
    rw [Nat.pow_succ] at hxlt
    split_ifs <;> omega
  have hsm : format.signMaskNat = 2 ^ format.payloadBits := rfl
  unfold abs Model.abs
  simp only [(FloatLib.Numerics.Kernel.Z.casesOn_eq_ite Iff.rfl), nar_eq, Nat.ble_eq, hless,
    decide_eq_true_eq, hsm]
  split_ifs with h
  · exact neg_eq x
  · rfl

/-- Posit Standard (2022), §5.2: `next` on an encoding is the encoding of the next word,
wrapping, for every standard width. -/
theorem next_eq (x : Model format) :
    next format.payloadBits x.toNatBits = (Model.next x).toNatBits := by
  have hmod : (2 : Nat) ^ format.bits = 2 ^ (format.payloadBits + 1) := modulus_eq format
  unfold next Model.next
  kernel_notation
  change _ = (x.bits + 1).toNat
  rw [BitVec.toNat_add]
  change _ = (x.toNatBits + (BitVec.ofNat format.bits 1).toNat) % _
  rw [BitVec.toNat_ofNat, hmod,
    Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega) : 1 < 2 ^ (format.payloadBits + 1))]

/-- Posit Standard (2022), §5.2: `prior` on an encoding is the encoding of the previous word,
wrapping, for every standard width. -/
theorem prior_eq (x : Model format) :
    prior format.payloadBits x.toNatBits = (Model.prior x).toNatBits := by
  have hlt := toNatBits_lt_modulus x
  rw [modulus_eq] at hlt
  have hmod : (2 : Nat) ^ format.bits = 2 ^ (format.payloadBits + 1) := modulus_eq format
  unfold prior Model.prior
  kernel_notation
  change _ = (x.bits - 1).toNat
  rw [BitVec.toNat_sub]
  change _ = (2 ^ format.bits - (BitVec.ofNat format.bits 1).toNat + x.toNatBits) % _
  rw [BitVec.toNat_ofNat, hmod,
    Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega) : 1 < 2 ^ (format.payloadBits + 1))]
  congr 1
  have := Nat.two_pow_pos (format.payloadBits + 1)
  omega

/-! ## Change of width -/

/--
Posit Standard (2022), §6.1: `cast` on the encoding of a word of one standard width is the
encoding of its conversion to another, rounded once by the destination, for every pair of
widths and every operand.
-/
theorem cast_eq_spec {source : Format} (target : Format) (x : Model source) :
    cast source.payloadBits 2 target.payloadBits 2 x.toNatBits =
      (pₘToₙ target x).toNatBits := by
  unfold cast pₘToₙ
  simp only [beq_nar, beq_zero, (FloatLib.Numerics.Kernel.Z.casesOn_eq_ite Iff.rfl),
    decide_eq_true_eq]
  by_cases hx : x = Model.nar source
  · subst hx
    simp [nar_eq]
  rw [ite_eq_right hx]
  by_cases hx0 : x = Model.zero source
  · subst hx0
    simp
  rw [ite_eq_right hx0, toRat?_eq_toDyadic?_map, toDyadic?_eq x hx hx0]
  change _ = (roundRat target (fields x).toRat).toNatBits
  rw [← DirectDyadicPacking.round_eq_roundRat]
  simp only [magnitude_eq, sign_eq]
  have hb := bias_eq source.payloadBits
  exact (round_eq target (fields x) _ _ (significand_ne_zero _ _ _) (by
    change ((Nat.sub (Nat.add _ (Nat.shiftLeft _ 2)) _ : Nat) : Int) =
      ((exponent _ _ _ _ : Nat) : Int) - ((bias _ _ : Nat) : Int) + _
    kernel_notation
    simp only [Nat.reducePow]
    omega)).symm

end FloatLib.Floats.Formats.Posit.KernelPath
