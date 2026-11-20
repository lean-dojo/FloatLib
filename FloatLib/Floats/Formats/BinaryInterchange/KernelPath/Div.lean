/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Reference

import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.NearestAwayAgreement
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.ScaledDyadic

/-!
# Kernel division on encodings

`div fmt mode a b` is the natural-number encoding of the quotient of the values encoded by `a`
and `b` in `fmt`, rounded in the direction `mode`. Both significands are first normalized to
`fracWidth + 1` bits
(their bit lengths come from `significandLength`), so that one comparison gives the binary exponent
of the quotient. The quotient is then one exact integer division at the scale of the result,
rounded with its remainder, and packed by `pack`. The division works on numbers of about twice
the significand width whatever the exponents of the operands are (`divCore_def`). Operands that
are not both finite, and a zero
divisor, go to `divSpecial`, which applies the rules of the reference with flags computed on the
encodings.

`div_eq_spec` proves that it is the encoding of `Model.div x y (mode := mode)`, for every format
descriptor, every rounding direction and every operand.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
The quotient of two words when an operand is not finite or the divisor is zero, by the rules of
`Model.Spec.div`: a NaN operand gives `nanChoice`; an infinity over an infinity and a zero over a
zero give the invalid result; an infinity over a finite value and a nonzero value over a zero
give the infinity with the quotient sign; a finite value over an infinity gives the zero with
the quotient sign.
-/
def divSpecial (fmt : FloatFormat) (a b : Nat) : Nat :=
  (fun sa sb ua ub =>
    (fun infA infB nanA nanB =>
      Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.add nanA nanB) 0)
        (nanChoice fmt a b (Nat.mul nanA (signalingFlag fmt a))
          (Nat.mul nanB (signalingFlag fmt b)) nanA)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq infA 0)
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq infB 0)
            (invalidWord fmt)
            (Bool.casesOn (motive := fun _ => Nat) (Nat.beq sa sb)
              (overflowWord fmt true) (overflowWord fmt false)))
          (Bool.casesOn (motive := fun _ => Nat) (Nat.beq infB 0)
            (Bool.casesOn (motive := fun _ => Nat) (Nat.beq sa sb)
              (zeroWord fmt true) (zeroWord fmt false))
            (Bool.casesOn (motive := fun _ => Nat) (Nat.beq ua 0)
              (Bool.casesOn (motive := fun _ => Nat) (Nat.beq sa sb)
                (overflowWord fmt true) (overflowWord fmt false))
              (invalidWord fmt)))))
      (infFlag fmt ua) (infFlag fmt ub) (nanFlag fmt sa ua) (nanFlag fmt sb ub))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

kernel_constant divSpecial

/--
Round and pack the quotient `na / nb * 2 ^ (D - U)` of two significands normalized to one width
(`na` may be zero), in the direction `mode`. `below` is one when `na < nb`, and `t` is the
exponent field of the result minus one.

A quotient below the subnormal range is rounded as `na / (nb * 2 ^ s)`, where `s` is how far its
exponent lies under the least one. From `s = 2` on the floor is zero and the rounding increment
no longer depends on `s` (`roundQuotient_clamp`), so the denominator is shifted by at most two
places and no power of two of the size of the exponent range is built (`divCore_def`).
-/
def divCore (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign na nb D U guard special : Nat) : Nat :=
  (fun below =>
    (fun t =>
      (fun s =>
        roundQuotient fmt mode sign sign guard special t
          (Nat.shiftLeft na
            (Nat.sub (Nat.add (Nat.add D fmt.exponentBias) fmt.fracWidth)
              (Nat.succ (Nat.add U t))))
          (Nat.shiftLeft nb (Nat.sub s (Nat.sub s 2))))
        (Nat.sub (Nat.succ (Nat.add U t)) (Nat.add (Nat.add D fmt.exponentBias) fmt.fracWidth)))
      (Nat.sub (Nat.add D fmt.exponentBias) (Nat.add (Nat.add U below) 1)))
    (Nat.sub 1 (Nat.sub 1 (Nat.sub nb na)))

/--
A numerator below twice the divisor, over the divisor shifted by two places or more: the floor
is zero, and the rounding of the quotient is the same for every such shift, in every direction.
-/
theorem roundQuotient_clamp (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign zeroSign guard special t na nb s : Nat) (hna : na < 2 * nb) (hs : 2 ≤ s) :
    roundQuotient fmt mode sign zeroSign guard special t na (Nat.shiftLeft nb s) =
      roundQuotient fmt mode sign zeroSign guard special t na (Nat.shiftLeft nb 2) := by
  have hfour : ∀ k, 2 ≤ k → 4 * nb ≤ Nat.shiftLeft nb k := fun k hk => by
    change 4 * nb ≤ nb <<< k
    rw [Nat.shiftLeft_eq]
    calc 4 * nb = nb * 2 ^ 2 := by ac_rfl
      _ ≤ nb * 2 ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk)
  have hfloor : ∀ den, 4 * nb ≤ den → Nat.div na den = 0 ∧ Nat.mod na den = na :=
    fun den hden => ⟨Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)⟩
  have hup : ∀ den, 4 * nb ≤ den →
      roundUp mode sign 0 na den = roundUp mode sign 0 na (4 * nb) := fun den hden => by
    unfold roundUp
    cases mode <;>
      first
        | rfl
        | (simp only [Nat.add_eq, Nat.sub_eq, div_def, Nat.land_eq, Nat.zero_and, Nat.add_zero]
           rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)])
  unfold roundQuotient
  simp only []
  rw [(hfloor _ (hfour s hs)).1, (hfloor _ (hfour s hs)).2, (hfloor _ (hfour 2 le_rfl)).1,
    (hfloor _ (hfour 2 le_rfl)).2, hup _ (hfour s hs), hup _ (hfour 2 le_rfl)]

/--
`divCore` is the rounding of the quotient at its own scale, with the denominator shifted by the
whole distance under the subnormal range, when the numerator is below twice the divisor: the
case of two significands normalized to one width.
-/
theorem divCore_def (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (sign na nb D U guard special : Nat) (hna : na < 2 * nb) :
    divCore fmt mode sign na nb D U guard special =
      (fun below =>
        (fun t =>
          roundQuotient fmt mode sign sign guard special t
            (Nat.shiftLeft na
              (Nat.sub (Nat.add (Nat.add D fmt.exponentBias) fmt.fracWidth)
                (Nat.succ (Nat.add U t))))
            (Nat.shiftLeft nb
              (Nat.sub (Nat.succ (Nat.add U t))
                (Nat.add (Nat.add D fmt.exponentBias) fmt.fracWidth))))
          (Nat.sub (Nat.add D fmt.exponentBias) (Nat.add (Nat.add U below) 1)))
        (Nat.sub 1 (Nat.sub 1 (Nat.sub nb na))) := by
  unfold divCore
  dsimp only
  generalize Nat.sub (Nat.add D fmt.exponentBias)
    (Nat.add (Nat.add U (Nat.sub 1 (Nat.sub 1 (Nat.sub nb na)))) 1) = t
  generalize Nat.add (Nat.add D fmt.exponentBias) fmt.fracWidth = X
  generalize Nat.succ (Nat.add U t) = Y
  by_cases hs : Nat.sub Y X ≤ 2
  · rw [show Nat.sub (Nat.sub Y X) (Nat.sub (Nat.sub Y X) 2) = Nat.sub Y X from by
      simp only [Nat.sub_eq] at hs ⊢; omega]
  · have hnum : Nat.sub X Y = 0 := by simp only [Nat.sub_eq] at hs ⊢; omega
    rw [show Nat.sub (Nat.sub Y X) (Nat.sub (Nat.sub Y X) 2) = 2 from by
      simp only [Nat.sub_eq] at hs ⊢; omega, hnum]
    exact (roundQuotient_clamp fmt mode sign sign guard special t _ nb _ (by simpa using hna)
      (by simp only [Nat.sub_eq] at hs ⊢; omega)).symm

/--
Encoding of the quotient of the values encoded by `a` and `b`, rounded in the direction `mode`
(`div_eq_spec`).
-/
def div (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  (fun sa sb ua ub =>
    (fun ha hb =>
      (fun ma mb =>
        (fun la lb =>
          divCore fmt mode (Nat.xor sa sb) (Nat.shiftLeft ma la) (Nat.shiftLeft mb lb)
            (Nat.add ha lb) (Nat.add hb la)
            (Nat.add
              (Nat.add
                (Nat.add (Nat.sub ua (maxFinite fmt)) (Nat.mul (negZeroNaN fmt) (Nat.sub sa ua)))
                (Nat.add (Nat.sub ub (maxFinite fmt)) (Nat.mul (negZeroNaN fmt) (Nat.sub sb ub))))
              (Nat.sub 1 mb))
            (divSpecial fmt a b))
          (Nat.sub (Nat.succ fmt.fracWidth) (significandLength fmt.fracWidth ma))
          (Nat.sub (Nat.succ fmt.fracWidth) (significandLength fmt.fracWidth mb)))
        (Nat.sub ua (Nat.shiftLeft ha fmt.fracWidth)) (Nat.sub ub (Nat.shiftLeft hb fmt.fracWidth)))
      (Nat.sub (Nat.shiftRight ua fmt.fracWidth) 1) (Nat.sub (Nat.shiftRight ub fmt.fracWidth) 1))
    (Nat.shiftRight a (signPos fmt)) (Nat.shiftRight b (signPos fmt))
    (Nat.land a (magnitudeMask fmt)) (Nat.land b (magnitudeMask fmt))

/-! ## Quotient rounding -/

/-- Scaling a ratio by a power of two shifts the numerator or the denominator. -/
theorem scaleByPowerOfTwo_eq_shifts (n d : Nat) (s : Int) :
    RationalBinary.scaleByPowerOfTwo n d s = (n <<< s.toNat, d <<< (-s).toNat) := by
  cases s with
  | ofNat k =>
      have h1 : (Int.ofNat k).toNat = k := rfl
      have h2 : (-Int.ofNat k).toNat = 0 := by
        cases k <;> rfl
      rw [h1, h2]
      rfl
  | negSucc k =>
      have h1 : (Int.negSucc k).toNat = 0 := rfl
      have h2 : (-Int.negSucc k).toNat = k + 1 := rfl
      rw [h1, h2]
      rfl

/-! ## Normalized operands -/

/-- A nonzero significand shifted until its leading bit is bit `width`. -/
theorem normalized_bounds {m width : Nat} (hm : m ≠ 0) (hlt : m < 2 ^ (width + 1)) :
    2 ^ width ≤ m <<< (width - m.log2) ∧ m <<< (width - m.log2) < 2 ^ (width + 1) := by
  have hlog : m.log2 ≤ width := by
    have := (Nat.log2_lt hm).2 hlt
    omega
  have h1 : 2 ^ m.log2 ≤ m := Nat.log2_self_le hm
  have h2 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  rw [Nat.shiftLeft_eq]
  constructor
  · calc 2 ^ width = 2 ^ m.log2 * 2 ^ (width - m.log2) := by
          rw [← Nat.pow_add]; congr 1; omega
      _ ≤ m * 2 ^ (width - m.log2) := Nat.mul_le_mul_right _ h1
  · calc m * 2 ^ (width - m.log2) < 2 ^ (m.log2 + 1) * 2 ^ (width - m.log2) :=
          Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
      _ = 2 ^ (width + 1) := by rw [← Nat.pow_add]; congr 1; omega

/-- The binary exponent of a ratio of shifted operands. -/
theorem floorLog2_shiftLeft (n d a b : Nat) (hn : n ≠ 0) (hd : d ≠ 0) :
    RationalBinary.floorLog2 (n <<< a) (d <<< b) =
      RationalBinary.floorLog2 n d + (a : Int) - b := by
  have hna : n <<< a ≠ 0 := by simp [Nat.shiftLeft_eq, hn]
  have h1 := Model.floorLog2_scaleByPowerOfTwo n d (a : Int) hn hd
  have h2 := Model.floorLog2_scaleByPowerOfTwo (n <<< a) d (-(b : Int)) hna hd
  simp only [scaleByPowerOfTwo_eq_shifts] at h1 h2
  have ha1 : ((a : Int)).toNat = a := Int.toNat_natCast a
  have ha2 : (-(a : Int)).toNat = 0 := by omega
  have hb1 : (-(b : Int)).toNat = 0 := by omega
  have hb2 : (-(-(b : Int))).toNat = b := by omega
  rw [ha1, ha2, Nat.shiftLeft_zero] at h1
  rw [hb1, hb2, Nat.shiftLeft_zero] at h2
  rw [h2, h1]
  omega

/-- Directed rounding of a quotient is the policy rounding away from zero or toward zero. -/
theorem roundQuotDirected_eq (up : Bool) (n d : Nat) (hd : d ≠ 0) :
    Model.roundQuotDirected up n d =
      Model.Policy.roundQuot
        (if up then Model.IEEERoundingMode.away
          else Model.IEEERoundingMode.towardZero).toRoundingMode
        false 0 n d := by
  cases up
  · exact (Model.Policy.roundQuot_towardZero_eq_roundQuotDirected false 0 n d).symm
  · exact (Model.Policy.roundQuot_away_eq_roundQuotDirected false 0 n d hd).symm

/--
Scaling a ratio of shifted operands gives a pair proportional to the scaled ratio of the
operands, with positive denominators.
-/
theorem scale_shiftLeft_cross (n d a b : Nat) (s : Int) (hd : d ≠ 0) :
    0 < (RationalBinary.scaleByPowerOfTwo (n <<< a) (d <<< b) (s - a + b)).2 ∧
      0 < (RationalBinary.scaleByPowerOfTwo n d s).2 ∧
      (RationalBinary.scaleByPowerOfTwo (n <<< a) (d <<< b) (s - a + b)).1 *
          (RationalBinary.scaleByPowerOfTwo n d s).2 =
        (RationalBinary.scaleByPowerOfTwo n d s).1 *
          (RationalBinary.scaleByPowerOfTwo (n <<< a) (d <<< b) (s - a + b)).2 := by
  simp only [scaleByPowerOfTwo_eq_shifts, Nat.shiftLeft_eq]
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  refine ⟨Nat.mul_pos (Nat.mul_pos hdpos (Nat.two_pow_pos _)) (Nat.two_pow_pos _),
    Nat.mul_pos hdpos (Nat.two_pow_pos _), ?_⟩
  have hexp : a + (s - a + b).toNat + (-s).toNat = s.toNat + (b + (-(s - a + b)).toNat) := by
    omega
  calc n * 2 ^ a * 2 ^ (s - a + b).toNat * (d * 2 ^ (-s).toNat)
      = n * d * 2 ^ (a + (s - a + b).toNat + (-s).toNat) := by rw [Nat.pow_add, Nat.pow_add]; ac_rfl
    _ = n * d * 2 ^ (s.toNat + (b + (-(s - a + b)).toNat)) := by rw [hexp]
    _ = n * 2 ^ s.toNat * (d * 2 ^ b * 2 ^ (-(s - a + b)).toNat) := by
        rw [Nat.pow_add, Nat.pow_add]; ac_rfl

/-- Rounding a scaled ratio in any direction does not see a common shift of its operands. -/
theorem roundQuot_scale_shiftLeft (mode : Model.IEEERoundingMode) (negative : Bool)
    (entropy n d a b : Nat) (s : Int) (hd : d ≠ 0) :
    Model.Policy.roundQuot mode.toRoundingMode negative entropy
        (RationalBinary.scaleByPowerOfTwo (n <<< a) (d <<< b) (s - a + b)).1
        (RationalBinary.scaleByPowerOfTwo (n <<< a) (d <<< b) (s - a + b)).2 =
      Model.Policy.roundQuot mode.toRoundingMode negative entropy
        (RationalBinary.scaleByPowerOfTwo n d s).1 (RationalBinary.scaleByPowerOfTwo n d s).2 := by
  obtain ⟨h1, h2, hcross⟩ := scale_shiftLeft_cross n d a b s hd
  exact roundQuot_eq_of_cross mode negative entropy h1 h2 hcross

/-- Rounding a scaled ratio to nearest even does not see a common shift of its operands. -/
theorem roundQuotientEven_scale_shiftLeft (n d a b : Nat) (s : Int) (hd : d ≠ 0) :
    roundQuotientEven
        (RationalBinary.scaleByPowerOfTwo (n <<< a) (d <<< b) (s - a + b)).1
        (RationalBinary.scaleByPowerOfTwo (n <<< a) (d <<< b) (s - a + b)).2 =
      roundQuotientEven (RationalBinary.scaleByPowerOfTwo n d s).1
        (RationalBinary.scaleByPowerOfTwo n d s).2 := by
  obtain ⟨h1, h2, _⟩ := scale_shiftLeft_cross n d a b s hd
  rw [← Model.Policy.roundQuot_nearest_eq_roundQuotientEven false 0 _ _ h1.ne',
    ← Model.Policy.roundQuot_nearest_eq_roundQuotientEven false 0 _ _ h2.ne']
  exact roundQuot_scale_shiftLeft .nearest false 0 n d a b s hd

/-- Directed rounding of a scaled ratio does not see a common shift of its operands. -/
theorem roundQuotDirected_scale_shiftLeft (up : Bool) (n d a b : Nat) (s : Int) (hd : d ≠ 0) :
    Model.roundQuotDirected up
        (RationalBinary.scaleByPowerOfTwo (n <<< a) (d <<< b) (s - a + b)).1
        (RationalBinary.scaleByPowerOfTwo (n <<< a) (d <<< b) (s - a + b)).2 =
      Model.roundQuotDirected up (RationalBinary.scaleByPowerOfTwo n d s).1
        (RationalBinary.scaleByPowerOfTwo n d s).2 := by
  obtain ⟨h1, h2, _⟩ := scale_shiftLeft_cross n d a b s hd
  rw [roundQuotDirected_eq up _ _ h1.ne', roundQuotDirected_eq up _ _ h2.ne']
  exact roundQuot_scale_shiftLeft _ false 0 n d a b s hd

/-- Whether twice the remainder of a quotient is its divisor depends on the quotient only. -/
theorem tie_eq_of_cross {n₁ d₁ n₂ d₂ : Nat} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (hcross : n₁ * d₂ = n₂ * d₁) :
    (2 * (n₁ % d₁) == d₁) = (2 * (n₂ % d₂) == d₂) := by
  have hscale : ∀ n d c : Nat, 0 < c → (2 * (n * c % (d * c)) = d * c ↔ 2 * (n % d) = d) := by
    intro n d c hc
    rw [Nat.mul_mod_mul_right, ← Nat.mul_assoc]
    exact Nat.mul_left_inj hc.ne'
  have hiff : 2 * (n₁ % d₁) = d₁ ↔ 2 * (n₂ % d₂) = d₂ := by
    rw [← hscale n₁ d₁ d₂ h₂, ← hscale n₂ d₂ d₁ h₁, hcross, Nat.mul_comm d₁ d₂]
  by_cases h : 2 * (n₁ % d₁) = d₁
  · simp [h, hiff.1 h]
  · have h' : ¬ 2 * (n₂ % d₂) = d₂ := fun h2 => h (hiff.2 h2)
    simp [h, h']

/-- A nonzero natural stays nonzero when shifted left. -/
theorem shiftLeft_ne_zero {n : Nat} (a : Nat) (hn : n ≠ 0) : n <<< a ≠ 0 := by
  simp [Nat.shiftLeft_eq, hn]

/--
The exponents that the rational rounders compute do not see a common normalization: with the
numerator shifted by `a` and the denominator by `b`, the exponent of the leading bit, the
subnormal scale and the normal scale are those of the original operands, moved by `a - b`.
-/
theorem shiftLeft_exponents (fmt : FloatFormat) (n d a b : Nat) (e : Int) :
    RationalBinary.floorLog2 n d + (a : Int) - b + (e - a + b) =
        RationalBinary.floorLog2 n d + e ∧
      e - (a : Int) + b + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1) =
        (e + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1)) - a + b ∧
      Int.ofNat fmt.fracWidth - (RationalBinary.floorLog2 n d + (a : Int) - b) =
        (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 n d) - a + b := by
  refine ⟨?_, ?_, ?_⟩ <;> omega

/--
The reference rational rounder does not see a common normalization of its operands: shifting the
numerator by `a` and the denominator by `b` and correcting the exponent leaves the result unchanged.
-/
theorem roundRatScaledGeneral_shiftLeft (fmt : FloatFormat) (negative : Bool) (n d a b : Nat)
    (e : Int) (hn : n ≠ 0) (hd : d ≠ 0) :
    Model.roundRatScaledGeneral fmt negative (n <<< a) (d <<< b) (e - a + b) =
      Model.roundRatScaledGeneral fmt negative n d e := by
  obtain ⟨htot, hsub, hnorm⟩ := shiftLeft_exponents fmt n d a b e
  unfold Model.roundRatScaledGeneral
  simp only [beq_iff_eq, shiftLeft_ne_zero a hn, shiftLeft_ne_zero b hd, hn, hd, ite_false,
    floorLog2_shiftLeft n d a b hn hd]
  rw [htot, hsub, hnorm, roundQuotientEven_scale_shiftLeft n d a b _ hd,
    roundQuotientEven_scale_shiftLeft n d a b _ hd]

/-- A quotient below one half rounds to zero. -/
theorem roundQuotientEven_eq_zero {n d : Nat} (h : 2 * n < d) : roundQuotientEven n d = 0 := by
  have hlt : n < d := by omega
  simp [roundQuotientEven, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, h]

/-- A quotient below `k` rounds to at most `k`. -/
theorem roundQuotientEven_le {n d k : Nat} (hd : 0 < d) (h : n < k * d) :
    roundQuotientEven n d ≤ k := by
  have hfloor : n / d < k := (Nat.div_lt_iff_lt_mul hd).2 h
  rw [roundQuotientEven_eq_quotient_add]
  split <;> omega

/-- A quotient of at least `k` rounds to at least `k`. -/
theorem le_roundQuotientEven {n d k : Nat} (hd : 0 < d) (h : k * d ≤ n) :
    k ≤ roundQuotientEven n d := by
  have hfloor : k ≤ n / d := (Nat.le_div_iff_mul_le hd).2 h
  rw [roundQuotientEven_eq_quotient_add]
  omega

/--
The quotient of two significands normalized to `width + 1` bits, scaled to `scale + 1` bits and
rounded, lies between `2 ^ scale` and `2 ^ (scale + 1)`.
-/
theorem normalized_quotient_bounds {na nb width : Nat} (scale : Nat)
    (hna : 2 ^ width ≤ na ∧ na < 2 ^ (width + 1)) (hnb : 2 ^ width ≤ nb ∧ nb < 2 ^ (width + 1)) :
    2 ^ scale ≤ roundQuotientEven (na <<< (scale + if na < nb then 1 else 0)) nb ∧
      roundQuotientEven (na <<< (scale + if na < nb then 1 else 0)) nb ≤ 2 ^ (scale + 1) := by
  have hsplit : 2 ^ (scale + 1) = 2 ^ scale * 2 := by rw [Nat.pow_succ]
  have hnbpos : 0 < nb := lt_of_lt_of_le (Nat.two_pow_pos _) hnb.1
  rw [Nat.shiftLeft_eq]
  by_cases hlt : na < nb
  · simp only [hlt, ite_true]
    constructor
    · apply le_roundQuotientEven hnbpos
      calc 2 ^ scale * nb ≤ 2 ^ scale * (2 * na) := Nat.mul_le_mul_left _ (by omega)
        _ = na * 2 ^ (scale + 1) := by rw [hsplit]; ac_rfl
    · apply roundQuotientEven_le hnbpos
      calc na * 2 ^ (scale + 1) < nb * 2 ^ (scale + 1) :=
            Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
        _ = 2 ^ (scale + 1) * nb := Nat.mul_comm _ _
  · simp only [hlt, ite_false, Nat.add_zero]
    constructor
    · apply le_roundQuotientEven hnbpos
      calc 2 ^ scale * nb ≤ 2 ^ scale * na := Nat.mul_le_mul_left _ (by omega)
        _ = na * 2 ^ scale := Nat.mul_comm _ _
    · apply roundQuotientEven_le hnbpos
      calc na * 2 ^ scale < (2 * nb) * 2 ^ scale :=
            Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
        _ = 2 ^ (scale + 1) * nb := by rw [hsplit]; ac_rfl

/-! ## The reference rounder on normalized operands -/

/--
For operands normalized to a common width of `W + 1` bits, let `below` be one when the numerator
is the smaller operand and zero otherwise. Then the binary logarithm of the quotient, rounded
down, is `-below`, and the quotient is below `2 ^ (1 - below)`.
-/
private theorem normalized_below {W na nb : Nat} (hna : 2 ^ W ≤ na ∧ na < 2 ^ (W + 1))
    (hnb : 2 ^ W ≤ nb ∧ nb < 2 ^ (W + 1)) :
    ∃ below : Nat, (below = if na < nb then 1 else 0) ∧ below ≤ 1 ∧
      RationalBinary.floorLog2 na nb = -(below : Int) ∧ na < nb * 2 ^ (1 - below) := by
  have hlog := Model.FiniteQuotientRound.floorLog2_eq_of_normal W na nb hna hnb
  have hratioBase : na < nb * 2 := by
    have : 2 ^ (W + 1) = 2 ^ W * 2 := by rw [Nat.pow_succ]
    omega
  obtain ⟨below, hbelow⟩ : ∃ below : Nat, below = if na < nb then 1 else 0 := ⟨_, rfl⟩
  refine ⟨below, hbelow, ?_, ?_, ?_⟩
  · rw [hbelow]; split <;> omega
  · simp only [hlog, hbelow, ← not_lt]
    split_ifs <;> rfl
  · rw [hbelow]
    by_cases h : na < nb
    · simp [h]
    · simp only [h, ite_false]
      exact hratioBase

/--
The encoding of the reference rational rounding of `na / nb * 2 ^ (D - U)` for operands
normalized to a common width of `W + 1` bits, in the quantities `divCore` computes: `t` is the
exponent field minus one (zero below the normal range) and `mantissa` the quotient at that
scale, rounded.
-/
theorem roundRatScaledGeneral_bits (fmt : FloatFormat) (negative : Bool) (W na nb D U : Nat)
    (hna : 2 ^ W ≤ na ∧ na < 2 ^ (W + 1))
    (hnb : 2 ^ W ≤ nb ∧ nb < 2 ^ (W + 1))
    (t mantissa : Nat)
    (ht : t = D + fmt.exponentBias - (U + (if na < nb then 1 else 0) + 1))
    (hmantissa : mantissa =
      roundQuotientEven (na <<< (D + fmt.exponentBias + fmt.fracWidth - (U + t + 1)))
        (nb <<< (U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth)))) :
    (Model.roundRatScaledGeneral fmt negative na nb ((D : Int) - U)).toNatBits =
      if mantissa = 0 then zeroWord fmt negative
      else if t * 2 ^ fmt.fracWidth + mantissa ≤ maxFinite fmt then
        (if negative then 2 ^ signPos fmt else 0) + (t * 2 ^ fmt.fracWidth + mantissa)
      else overflowWord fmt negative := by
  have hpos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  have hWpos : 0 < 2 ^ W := Nat.two_pow_pos _
  have hna0 : na ≠ 0 := by omega
  have hnb0 : nb ≠ 0 := by omega
  have hnbpos : 0 < nb := Nat.pos_of_ne_zero hnb0
  have hexpPos := fmt.maxFiniteExpField_pos
  have hfracMax := fmt.maxFiniteFracField_lt_two_pow
  have hbiasPos := fmt.exponentBias_pos
  have hfracPos := fmt.fracWidth_pos
  have hmaxge : 2 ^ fmt.fracWidth ≤ maxFinite fmt := by
    unfold maxFinite
    have : 1 * 2 ^ fmt.fracWidth ≤ fmt.maxFiniteExpField * 2 ^ fmt.fracWidth :=
      Nat.mul_le_mul_right _ hexpPos
    omega
  have hbounds := normalized_quotient_bounds fmt.fracWidth hna hnb
  obtain ⟨below, hbelow, hbelowLe, hlog', hratio⟩ := normalized_below hna hnb
  rw [← hbelow] at ht hbounds
  unfold Model.roundRatScaledGeneral
  simp only [beq_iff_eq, hna0, hnb0, ite_false, hlog', FloatFormat.maxNormalExponent,
    FloatFormat.minNormalExponent, FloatFormat.minSubnormalExponent, Int.ofNat_eq_natCast,
    scaleByPowerOfTwo_eq_shifts, gt_iff_lt]
  by_cases hover : (fmt.maxFiniteExpField : Int) - fmt.exponentBias <
      -(below : Int) + ((D : Int) - U)
  · -- The quotient is above the largest finite exponent.
    have ht' : fmt.maxFiniteExpField ≤ t := by omega
    have hsl : D + fmt.exponentBias + fmt.fracWidth - (U + t + 1) = fmt.fracWidth + below := by
      omega
    have hsr : U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth) = 0 := by omega
    rw [hsl, hsr, Nat.shiftLeft_zero] at hmantissa
    rw [← hmantissa] at hbounds
    have hM0 : mantissa ≠ 0 := by omega
    have hnle : ¬ (t * 2 ^ fmt.fracWidth + mantissa ≤ maxFinite fmt) := by
      intro hle
      unfold maxFinite at hle
      have := Nat.mul_le_mul_right (2 ^ fmt.fracWidth) ht'
      omega
    rw [ite_eq_left hover, ite_eq_right hM0, ite_eq_right hnle]
    exact (overflowWord_eq fmt negative).symm
  · rw [ite_eq_right hover]
    by_cases htiny : -(below : Int) + ((D : Int) - U) + 1 <
        1 - (fmt.exponentBias : Int) - fmt.fracWidth
    · -- Below half the least subnormal the quotient rounds to zero.
      have ht0 : t = 0 := by omega
      subst ht0
      have hsl : D + fmt.exponentBias + fmt.fracWidth - (U + 0 + 1) = 0 := by omega
      have hsr : 2 - below ≤ U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth) := by omega
      have hzero : mantissa = 0 := by
        rw [hmantissa, hsl, Nat.shiftLeft_zero]
        apply roundQuotientEven_eq_zero
        rw [Nat.shiftLeft_eq]
        have hpow : 2 ^ (2 - below) ≤
            2 ^ (U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth)) :=
          Nat.pow_le_pow_right (by decide) hsr
        have hstep : 2 * na < nb * 2 ^ (2 - below) := by
          have h2 : 2 ^ (2 - below) = 2 * 2 ^ (1 - below) := by
            rw [show 2 - below = (1 - below) + 1 by omega, Nat.pow_succ]; ac_rfl
          rw [h2]
          have := Nat.mul_lt_mul_of_pos_left hratio (by decide : 0 < 2)
          calc 2 * na < 2 * (nb * 2 ^ (1 - below)) := this
            _ = nb * (2 * 2 ^ (1 - below)) := by ac_rfl
        exact lt_of_lt_of_le hstep (Nat.mul_le_mul_left _ hpow)
      rw [ite_eq_left htiny, ite_eq_left hzero]
      exact (zeroWord_eq fmt negative).symm
    · rw [ite_eq_right htiny]
      by_cases hsub : -(below : Int) + ((D : Int) - U) < 1 - (fmt.exponentBias : Int)
      · -- Below the normal range the quantum is the least subnormal.
        have ht0 : t = 0 := by omega
        subst ht0
        have hscaleL :
            ((D : Int) - U + ((fmt.exponentBias + fmt.fracWidth - 1 : Nat) : Int)).toNat =
            D + fmt.exponentBias + fmt.fracWidth - (U + 0 + 1) := by omega
        have hscaleR : (-((D : Int) - U +
            ((fmt.exponentBias + fmt.fracWidth - 1 : Nat) : Int))).toNat =
            U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth) := by omega
        rw [ite_eq_left hsub, hscaleL, hscaleR, ← hmantissa]
        have hbound : mantissa ≤ 2 ^ fmt.fracWidth := by
          rw [hmantissa]
          apply roundQuotientEven_le
            (by rw [Nat.shiftLeft_eq]; exact Nat.mul_pos hnbpos (Nat.two_pow_pos _))
          rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
          generalize hsl : D + fmt.exponentBias + fmt.fracWidth - (U + 0 + 1) = sl
          generalize hsr : U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth) = sr
          have hexp : 1 - below + sl ≤ sr + fmt.fracWidth := by omega
          calc na * 2 ^ sl < nb * 2 ^ (1 - below) * 2 ^ sl :=
                Nat.mul_lt_mul_of_pos_right hratio (Nat.two_pow_pos _)
            _ = nb * 2 ^ (1 - below + sl) := by rw [Nat.pow_add]; ac_rfl
            _ ≤ nb * 2 ^ (sr + fmt.fracWidth) :=
                Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hexp)
            _ = 2 ^ fmt.fracWidth * (nb * 2 ^ sr) := by rw [Nat.pow_add]; ac_rfl
        rw [packRoundedSubnormal_bits fmt negative _ hbound]
        by_cases hM0 : mantissa = 0
        · simp [hM0]
        · have hle : mantissa ≤ maxFinite fmt := by omega
          simp [hM0, hle]
      · -- In the normal range the quotient is scaled to `fracWidth + 1` bits.
        have hsl : D + fmt.exponentBias + fmt.fracWidth - (U + t + 1) =
            fmt.fracWidth + below := by omega
        have hsr : U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth) = 0 := by omega
        rw [hsl, hsr, Nat.shiftLeft_zero] at hmantissa
        rw [← hmantissa] at hbounds
        have hshiftL : ((fmt.fracWidth : Int) - -(below : Int)).toNat = fmt.fracWidth + below := by
          omega
        have hshiftR : (-((fmt.fracWidth : Int) - -(below : Int))).toNat = 0 := by omega
        have hM0 : mantissa ≠ 0 := by omega
        rw [ite_eq_right hsub, hshiftL, hshiftR, Nat.shiftLeft_zero, ← hmantissa,
          packRoundedNormal_bits fmt negative _ t mantissa _ (by omega) hbounds.1 hbounds.2,
          ite_eq_right hM0, overflowWord_eq]

/-! ## The IEEE rounder is the general one -/

/--
For a conventional IEEE descriptor the reference rounder `ieeeRoundRatScaled` computes
`roundRatScaledGeneral`, given a nonzero denominator and a normal-range significand of at most
`2 ^ (fracWidth + 1)`, which holds for every positive quotient.
-/
theorem ieeeRoundRatScaled_eq_general (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (negative : Bool) (num den : Nat) (e : Int) (hden : den ≠ 0)
    (hbound :
      roundQuotientEven
          (RationalBinary.scaleByPowerOfTwo num den
            (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den)).1
          (RationalBinary.scaleByPowerOfTwo num den
            (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den)).2 ≤
        2 ^ (fmt.fracWidth + 1)) :
    Model.ieeeRoundRatScaled fmt negative num den e hfmt =
      Model.roundRatScaledGeneral fmt negative num den e := by
  obtain ⟨hencoding, hbias⟩ := (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt
  have hzero := Model.zero_eq_signedZero_of_isIEEE fmt hfmt negative
  have hoverflow := Model.nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt negative
  unfold Model.ieeeRoundRatScaled Model.roundRatScaledGeneral
  simp only [beq_iff_eq, hden, ite_false, hzero, hoverflow]
  by_cases hnum : num = 0
  · simp [hnum]
  simp only [hnum, ite_false]
  have hfracMask : fmt.maxFiniteFracField = 2 ^ fmt.fracWidth - 1 := by
    simp [FloatFormat.maxFiniteFracField, FloatFormat.fracMaskNat, hencoding]
  have hexpMax : fmt.maxFiniteExpField = 2 * fmt.bias := by
    have h := fmt.two_pow_expWidth_eq_two_mul_bias_add_two
    simp only [FloatFormat.maxFiniteExpField, FloatFormat.Encoding.maxFiniteExponent, hencoding]
    omega
  have hpos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  rw [show fmt.exponentBias + fmt.fracWidth - 1 = fmt.subnormalAlignExp from rfl]
  generalize roundQuotientEven
      (RationalBinary.scaleByPowerOfTwo num den (e + Int.ofNat fmt.subnormalAlignExp)).1
      (RationalBinary.scaleByPowerOfTwo num den (e + Int.ofNat fmt.subnormalAlignExp)).2 =
        fraction
  generalize roundQuotientEven
      (RationalBinary.scaleByPowerOfTwo num den
        (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den)).1
      (RationalBinary.scaleByPowerOfTwo num den
        (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 num den)).2 = mantissa at hbound ⊢
  generalize RationalBinary.floorLog2 num den + e = total
  have hmaxNormal : fmt.maxNormalExponent = (fmt.bias : Int) := by
    simp only [FloatFormat.maxNormalExponent, hexpMax, hbias, Int.ofNat_eq_natCast]
    omega
  have hieeeMax : Int.ofNat fmt.ieeeMaxNormalExponent = (fmt.bias : Int) := rfl
  have hunder : -Int.ofNat fmt.normalMantissaExpOffset =
      -(((fmt.bias + fmt.fracWidth : Nat) : Int)) := by
    simp [FloatFormat.normalMantissaExpOffset, hbias]
  have hminSub : fmt.minSubnormalExponent = 1 - (fmt.bias : Int) - fmt.fracWidth := by
    simp [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent, hbias]
  have hminNormal : fmt.minNormalExponent = 1 - (fmt.bias : Int) := by
    simp [FloatFormat.minNormalExponent, hbias]
  have hieeeMin : fmt.ieeeMinNormalExponent = 1 - (fmt.bias : Int) := by
    simp [FloatFormat.ieeeMinNormalExponent]
  rw [hieeeMax, hunder, hieeeMin, hmaxNormal, hminSub, hminNormal]
  simp only [gt_iff_lt]
  by_cases hover : (fmt.bias : Int) < total
  · rw [ite_eq_left hover, ite_eq_left hover]
  · rw [ite_eq_right hover, ite_eq_right hover]
    by_cases htiny : total < -(((fmt.bias + fmt.fracWidth : Nat) : Int))
    · have htiny' : total + 1 < 1 - (fmt.bias : Int) - fmt.fracWidth := by omega
      rw [ite_eq_left htiny, ite_eq_left htiny']
    · have htiny' : ¬ total + 1 < 1 - (fmt.bias : Int) - fmt.fracWidth := by omega
      rw [ite_eq_right htiny, ite_eq_right htiny']
      by_cases hsub : total < 1 - (fmt.bias : Int)
      · rw [ite_eq_left hsub, ite_eq_left hsub]
        unfold Model.packRoundedSubnormal
        simp only [beq_iff_eq, ge_iff_le]
        by_cases hzeroFraction : fraction = 0
        · rw [ite_eq_left hzeroFraction, ite_eq_left hzeroFraction]
        · rw [ite_eq_right hzeroFraction, ite_eq_right hzeroFraction]
          split
          · rw [ite_eq_left (by assumption)]
          · rw [ite_eq_right (by assumption)]
      · rw [ite_eq_right hsub, ite_eq_right hsub]
        unfold Model.packRoundedNormal
        simp only [beq_iff_eq, Model.pow2_eq_two_pow, hmaxNormal, hexpMax,
          hbias, hfracMask, Int.ofNat_eq_natCast, gt_iff_lt, Bool.or_eq_true, decide_eq_true_eq,
          Bool.and_eq_true]
        by_cases hcarry : mantissa = 2 ^ (fmt.fracWidth + 1)
        · simp only [hcarry, ite_true]
          by_cases hover2 : (fmt.bias : Int) < total + 1
          · rw [ite_eq_left hover2, ite_eq_left hover2]
          · have hinner : ¬ (2 * fmt.bias < (total + 1 + (fmt.bias : Int)).toNat ∨
                (total + 1 + (fmt.bias : Int)).toNat = 2 * fmt.bias ∧
                  2 ^ fmt.fracWidth - 1 < 2 ^ fmt.fracWidth - 2 ^ fmt.fracWidth) := by omega
            rw [ite_eq_right hover2, ite_eq_right hover2, ite_eq_right hinner]
        · simp only [hcarry, ite_false]
          have hinner : ¬ (2 * fmt.bias < (total + (fmt.bias : Int)).toNat ∨
              (total + (fmt.bias : Int)).toNat = 2 * fmt.bias ∧
                2 ^ fmt.fracWidth - 1 < mantissa - 2 ^ fmt.fracWidth) := by omega
          rw [ite_eq_right hover, ite_eq_right hover, ite_eq_right hinner]

/-! ## The directed rounders on normalized operands -/

/-- A positive quotient below one rounds to one upward and to zero downward. -/
theorem roundQuotDirected_tiny (up : Bool) {n d : Nat} (hn : n ≠ 0) (h : n < d) :
    Model.roundQuotDirected up n d = if up then 1 else 0 := by
  have hq : n / d = 0 := Nat.div_eq_of_lt h
  have hr : n % d = n := Nat.mod_eq_of_lt h
  have hd : d ≠ 0 := by omega
  unfold Model.roundQuotDirected
  cases up
  · simp [hq]
  · simp [Numerics.roundQuotient_up_eq, hd, hr, hn, hq]

/--
The quotient of two significands normalized to `width + 1` bits, scaled to `scale + 1` bits and
rounded in any direction, lies between `2 ^ scale` and `2 ^ (scale + 1)`.
-/
theorem normalized_roundQuot_bounds (mode : Model.IEEERoundingMode) (negative : Bool)
    (entropy : Nat) {na nb width : Nat} (scale : Nat)
    (hna : 2 ^ width ≤ na ∧ na < 2 ^ (width + 1)) (hnb : 2 ^ width ≤ nb ∧ nb < 2 ^ (width + 1)) :
    2 ^ scale ≤ Model.Policy.roundQuot mode.toRoundingMode negative entropy
        (na <<< (scale + if na < nb then 1 else 0)) nb ∧
      Model.Policy.roundQuot mode.toRoundingMode negative entropy
        (na <<< (scale + if na < nb then 1 else 0)) nb ≤ 2 ^ (scale + 1) := by
  have hsplit : 2 ^ (scale + 1) = 2 ^ scale * 2 := by rw [Nat.pow_succ]
  have hnbpos : 0 < nb := lt_of_lt_of_le (Nat.two_pow_pos _) hnb.1
  rw [Nat.shiftLeft_eq]
  by_cases hlt : na < nb
  · simp only [hlt, ite_true]
    constructor
    · apply le_roundQuot mode negative entropy hnbpos
      calc 2 ^ scale * nb ≤ 2 ^ scale * (2 * na) := Nat.mul_le_mul_left _ (by omega)
        _ = na * 2 ^ (scale + 1) := by rw [hsplit]; ac_rfl
    · apply roundQuot_le mode negative entropy hnbpos
      calc na * 2 ^ (scale + 1) ≤ nb * 2 ^ (scale + 1) :=
            Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
        _ = 2 ^ (scale + 1) * nb := Nat.mul_comm _ _
  · simp only [hlt, ite_false, Nat.add_zero]
    constructor
    · apply le_roundQuot mode negative entropy hnbpos
      calc 2 ^ scale * nb ≤ 2 ^ scale * na := Nat.mul_le_mul_left _ (by omega)
        _ = na * 2 ^ scale := Nat.mul_comm _ _
    · apply roundQuot_le mode negative entropy hnbpos
      calc na * 2 ^ scale ≤ (2 * nb) * 2 ^ scale :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ (scale + 1) * nb := by rw [hsplit]; ac_rfl

/--
The encoding of the reference directed rounding of `na / nb * 2 ^ (D - U)` toward or away from
zero, for operands normalized to a common width of `W + 1` bits, in the quantities `divCore`
computes: `t` is the exponent field minus one (zero below the normal range) and `mantissa` the
quotient at that scale, rounded down or up.
-/
theorem roundRatMagnitudeDirected_bits (fmt : FloatFormat) (up negative : Bool)
    (W na nb D U : Nat)
    (hna : 2 ^ W ≤ na ∧ na < 2 ^ (W + 1))
    (hnb : 2 ^ W ≤ nb ∧ nb < 2 ^ (W + 1))
    (t mantissa : Nat)
    (ht : t = D + fmt.exponentBias - (U + (if na < nb then 1 else 0) + 1))
    (hmantissa : mantissa =
      Model.roundQuotDirected up (na <<< (D + fmt.exponentBias + fmt.fracWidth - (U + t + 1)))
        (nb <<< (U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth)))) :
    (Model.roundRatMagnitudeDirectedScaled fmt up negative na nb ((D : Int) - U)).toNatBits =
      if mantissa = 0 then zeroWord fmt negative
      else if t * 2 ^ fmt.fracWidth + mantissa ≤ maxFinite fmt then
        (if negative then 2 ^ signPos fmt else 0) + (t * 2 ^ fmt.fracWidth + mantissa)
      else (Model.directedOverflow fmt negative up).toNatBits := by
  have hpos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  have hWpos : 0 < 2 ^ W := Nat.two_pow_pos _
  have hna0 : na ≠ 0 := by omega
  have hnb0 : nb ≠ 0 := by omega
  have hnbpos : 0 < nb := Nat.pos_of_ne_zero hnb0
  have hdenpos : ∀ k, 0 < nb <<< k := fun k => by
    rw [Nat.shiftLeft_eq]
    exact Nat.mul_pos hnbpos (Nat.two_pow_pos _)
  have hexpPos := fmt.maxFiniteExpField_pos
  have hfracMax := fmt.maxFiniteFracField_lt_two_pow
  have hbiasPos := fmt.exponentBias_pos
  have hfracPos := fmt.fracWidth_pos
  have hmaxge : 2 ^ fmt.fracWidth ≤ maxFinite fmt := by
    unfold maxFinite
    have : 1 * 2 ^ fmt.fracWidth ≤ fmt.maxFiniteExpField * 2 ^ fmt.fracWidth :=
      Nat.mul_le_mul_right _ hexpPos
    omega
  have hbounds := normalized_roundQuot_bounds
    (if up then Model.IEEERoundingMode.away else Model.IEEERoundingMode.towardZero) false 0
    fmt.fracWidth hna hnb
  rw [← roundQuotDirected_eq up _ _ hnb0] at hbounds
  obtain ⟨below, hbelow, hbelowLe, hlog', hratio⟩ := normalized_below hna hnb
  rw [← hbelow] at ht hbounds
  unfold Model.roundRatMagnitudeDirectedScaled
  simp only [beq_iff_eq, hna0, hnb0, ite_false, hlog', FloatFormat.maxNormalExponent,
    FloatFormat.minNormalExponent, FloatFormat.minSubnormalExponent, Int.ofNat_eq_natCast,
    scaleByPowerOfTwo_eq_shifts, gt_iff_lt]
  by_cases hover : (fmt.maxFiniteExpField : Int) - fmt.exponentBias <
      -(below : Int) + ((D : Int) - U)
  · -- The quotient is above the largest finite exponent.
    have ht' : fmt.maxFiniteExpField ≤ t := by omega
    have hsl : D + fmt.exponentBias + fmt.fracWidth - (U + t + 1) = fmt.fracWidth + below := by
      omega
    have hsr : U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth) = 0 := by omega
    rw [hsl, hsr, Nat.shiftLeft_zero] at hmantissa
    rw [← hmantissa] at hbounds
    have hM0 : mantissa ≠ 0 := by omega
    have hnle : ¬ (t * 2 ^ fmt.fracWidth + mantissa ≤ maxFinite fmt) := by
      intro hle
      unfold maxFinite at hle
      have := Nat.mul_le_mul_right (2 ^ fmt.fracWidth) ht'
      omega
    rw [ite_eq_left hover, ite_eq_right hM0, ite_eq_right hnle]
  · rw [ite_eq_right hover]
    by_cases htiny : -(below : Int) + ((D : Int) - U) <
        1 - (fmt.exponentBias : Int) - fmt.fracWidth
    · -- Below the least subnormal the direction alone decides.
      have ht0 : t = 0 := by omega
      subst ht0
      have hsl : D + fmt.exponentBias + fmt.fracWidth - (U + 0 + 1) = 0 := by omega
      have hsr : 1 - below ≤ U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth) := by omega
      have hlt : na < nb <<< (U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth)) := by
        rw [Nat.shiftLeft_eq]
        exact lt_of_lt_of_le hratio
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hsr))
      have hvalue : mantissa = if up then 1 else 0 := by
        rw [hmantissa, hsl, Nat.shiftLeft_zero]
        exact roundQuotDirected_tiny up hna0 hlt
      have hone : 0 * 2 ^ fmt.fracWidth + 1 ≤ maxFinite fmt := by omega
      have hfraction : 1 < 2 ^ fmt.fracWidth := Nat.one_lt_two_pow (by omega)
      rw [ite_eq_left htiny, hvalue]
      cases up
      · simp [zeroWord_eq]
      · simp only [ite_true, one_ne_zero, ite_false, hone]
        cases negative
        · simp only [Bool.false_eq_true, ite_false]
          rw [Model.posMinSubnormal_eq_ofFields,
            toNatBits_ofFields fmt _ _ _ (Nat.two_pow_pos _) hfraction]
          simp
        · simp only [ite_true]
          rw [Model.negMinSubnormal_eq_ofFields,
            toNatBits_ofFields fmt _ _ _ (Nat.two_pow_pos _) hfraction]
          simp
    · rw [ite_eq_right htiny]
      by_cases hsub : -(below : Int) + ((D : Int) - U) < 1 - (fmt.exponentBias : Int)
      · -- Below the normal range the quantum is the least subnormal.
        have ht0 : t = 0 := by omega
        subst ht0
        have hscaleL :
            ((D : Int) - U + ((fmt.exponentBias + fmt.fracWidth - 1 : Nat) : Int)).toNat =
            D + fmt.exponentBias + fmt.fracWidth - (U + 0 + 1) := by omega
        have hscaleR : (-((D : Int) - U +
            ((fmt.exponentBias + fmt.fracWidth - 1 : Nat) : Int))).toNat =
            U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth) := by omega
        rw [ite_eq_left hsub, hscaleL, hscaleR, ← hmantissa]
        have hbound : mantissa ≤ 2 ^ fmt.fracWidth := by
          rw [hmantissa, roundQuotDirected_eq up _ _ (hdenpos _).ne']
          apply roundQuot_le _ _ _ (hdenpos _)
          rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
          generalize hsl : D + fmt.exponentBias + fmt.fracWidth - (U + 0 + 1) = sl
          generalize hsr : U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth) = sr
          have hexp : 1 - below + sl ≤ sr + fmt.fracWidth := by omega
          calc na * 2 ^ sl ≤ nb * 2 ^ (1 - below) * 2 ^ sl :=
                Nat.mul_le_mul_right _ (Nat.le_of_lt hratio)
            _ = nb * 2 ^ (1 - below + sl) := by rw [Nat.pow_add]; ac_rfl
            _ ≤ nb * 2 ^ (sr + fmt.fracWidth) :=
                Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hexp)
            _ = 2 ^ fmt.fracWidth * (nb * 2 ^ sr) := by rw [Nat.pow_add]; ac_rfl
        rw [packRoundedSubnormal_bits fmt negative _ hbound]
        by_cases hM0 : mantissa = 0
        · simp [hM0]
        · have hle : mantissa ≤ maxFinite fmt := by omega
          simp [hM0, hle]
      · -- In the normal range the quotient is scaled to `fracWidth + 1` bits.
        have hsl : D + fmt.exponentBias + fmt.fracWidth - (U + t + 1) =
            fmt.fracWidth + below := by omega
        have hsr : U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth) = 0 := by omega
        rw [hsl, hsr, Nat.shiftLeft_zero] at hmantissa
        rw [← hmantissa] at hbounds
        have hshiftL : ((fmt.fracWidth : Int) - -(below : Int)).toNat = fmt.fracWidth + below := by
          omega
        have hshiftR : (-((fmt.fracWidth : Int) - -(below : Int))).toNat = 0 := by omega
        have hM0 : mantissa ≠ 0 := by omega
        rw [ite_eq_right hsub, hshiftL, hshiftR, Nat.shiftLeft_zero, ← hmantissa,
          packRoundedNormal_bits fmt negative _ t mantissa _ (by omega) hbounds.1 hbounds.2,
          ite_eq_right hM0]

/-- The directed rounder does not see a common normalization of its operands. -/
theorem roundRatMagnitudeDirected_shiftLeft (fmt : FloatFormat) (up negative : Bool)
    (n d a b : Nat) (e : Int) (hn : n ≠ 0) (hd : d ≠ 0) :
    Model.roundRatMagnitudeDirectedScaled fmt up negative (n <<< a) (d <<< b) (e - a + b) =
      Model.roundRatMagnitudeDirectedScaled fmt up negative n d e := by
  obtain ⟨htot, hsub, hnorm⟩ := shiftLeft_exponents fmt n d a b e
  unfold Model.roundRatMagnitudeDirectedScaled
  simp only [beq_iff_eq, shiftLeft_ne_zero a hn, shiftLeft_ne_zero b hd, hn, hd, ite_false,
    floorLog2_shiftLeft n d a b hn hd]
  rw [htot, hsub, hnorm, roundQuotDirected_scale_shiftLeft up n d a b _ hd,
    roundQuotDirected_scale_shiftLeft up n d a b _ hd]

/-- The grid-tie test does not see a common normalization of its operands. -/
theorem rationalIsGridTie_shiftLeft (fmt : FloatFormat) (n d a b : Nat) (e : Int)
    (hn : n ≠ 0) (hd : d ≠ 0) :
    Model.rationalIsGridTieScaled fmt (n <<< a) (d <<< b) (e - a + b) =
      Model.rationalIsGridTieScaled fmt n d e := by
  have hna := shiftLeft_ne_zero a hn
  have hdb := shiftLeft_ne_zero b hd
  obtain ⟨htot, hsub, hnorm⟩ := shiftLeft_exponents fmt n d a b e
  have hzero : (d == 0 || n == 0) = false := by simp [hn, hd]
  have hzero' : (d <<< b == 0 || n <<< a == 0) = false := by simp [hna, hdb]
  unfold Model.rationalIsGridTieScaled
  simp only [hzero, hzero', Bool.false_eq_true, ite_false, floorLog2_shiftLeft n d a b hn hd,
    htot]
  by_cases hfar : RationalBinary.floorLog2 n d + e + 1 < fmt.minSubnormalExponent
  · simp only [hfar, ite_true]
  · simp only [hfar, ite_false]
    by_cases hsubnormal : RationalBinary.floorLog2 n d + e < fmt.minNormalExponent
    · simp only [hsubnormal, ite_true]
      rw [hsub]
      obtain ⟨h1, h2, hcross⟩ := scale_shiftLeft_cross n d a b
        (e + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1)) hd
      exact tie_eq_of_cross h1 h2 hcross
    · simp only [hsubnormal, ite_false]
      rw [hnorm]
      obtain ⟨h1, h2, hcross⟩ := scale_shiftLeft_cross n d a b
        (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 n d) hd
      exact tie_eq_of_cross h1 h2 hcross

/--
The grid-tie test of operands normalized to a common width of `W + 1` bits, in the quantities
`divCore` computes: twice the remainder of the scaled quotient is its divisor.
-/
theorem rationalIsGridTie_normalized (fmt : FloatFormat) (W na nb D U : Nat)
    (hna : 2 ^ W ≤ na ∧ na < 2 ^ (W + 1))
    (hnb : 2 ^ W ≤ nb ∧ nb < 2 ^ (W + 1))
    (t : Nat) (ht : t = D + fmt.exponentBias - (U + (if na < nb then 1 else 0) + 1)) :
    Model.rationalIsGridTieScaled fmt na nb ((D : Int) - U) =
      (2 * (na <<< (D + fmt.exponentBias + fmt.fracWidth - (U + t + 1)) %
          nb <<< (U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth))) ==
        nb <<< (U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth))) := by
  have hWpos : 0 < 2 ^ W := Nat.two_pow_pos _
  have hna0 : na ≠ 0 := by omega
  have hnb0 : nb ≠ 0 := by omega
  have hbiasPos := fmt.exponentBias_pos
  have hfracPos := fmt.fracWidth_pos
  obtain ⟨below, hbelow, hbelowLe, hlog', hratio⟩ := normalized_below hna hnb
  rw [← hbelow] at ht
  have hzero : (nb == 0 || na == 0) = false := by simp [hna0, hnb0]
  unfold Model.rationalIsGridTieScaled
  simp only [hzero, Bool.false_eq_true, ite_false, hlog',
    FloatFormat.minNormalExponent, FloatFormat.minSubnormalExponent, Int.ofNat_eq_natCast,
    scaleByPowerOfTwo_eq_shifts]
  by_cases hfar : -(below : Int) + ((D : Int) - U) + 1 <
      1 - (fmt.exponentBias : Int) - fmt.fracWidth
  · -- Below half the least subnormal there is no tie.
    have ht0 : t = 0 := by omega
    subst ht0
    have hsl : D + fmt.exponentBias + fmt.fracWidth - (U + 0 + 1) = 0 := by omega
    have hsr : 2 - below ≤ U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth) := by omega
    have hlt : 2 * na < nb <<< (U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth)) := by
      rw [Nat.shiftLeft_eq]
      have hpow : 2 ^ (2 - below) ≤
          2 ^ (U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth)) :=
        Nat.pow_le_pow_right (by decide) hsr
      have h2 : 2 ^ (2 - below) = 2 * 2 ^ (1 - below) := by
        rw [show 2 - below = (1 - below) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
      calc 2 * na < 2 * (nb * 2 ^ (1 - below)) := Nat.mul_lt_mul_of_pos_left hratio (by decide)
        _ = nb * 2 ^ (2 - below) := by rw [h2]; ac_rfl
        _ ≤ nb * 2 ^ (U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth)) :=
            Nat.mul_le_mul_left _ hpow
    rw [ite_eq_left hfar, hsl, Nat.shiftLeft_zero, Nat.mod_eq_of_lt (by omega)]
    have hne : ¬ 2 * na = nb <<< (U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth)) := by
      omega
    simp [hne]
  · rw [ite_eq_right hfar]
    by_cases hsub : -(below : Int) + ((D : Int) - U) < 1 - (fmt.exponentBias : Int)
    · have ht0 : t = 0 := by omega
      subst ht0
      have hscaleL :
          ((D : Int) - U + ((fmt.exponentBias + fmt.fracWidth - 1 : Nat) : Int)).toNat =
          D + fmt.exponentBias + fmt.fracWidth - (U + 0 + 1) := by omega
      have hscaleR : (-((D : Int) - U +
          ((fmt.exponentBias + fmt.fracWidth - 1 : Nat) : Int))).toNat =
          U + 0 + 1 - (D + fmt.exponentBias + fmt.fracWidth) := by omega
      rw [ite_eq_left hsub, hscaleL, hscaleR]
    · have hsl : D + fmt.exponentBias + fmt.fracWidth - (U + t + 1) =
          fmt.fracWidth + below := by omega
      have hsr : U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth) = 0 := by omega
      have hshiftL : ((fmt.fracWidth : Int) - -(below : Int)).toNat = fmt.fracWidth + below := by
        omega
      have hshiftR : (-((fmt.fracWidth : Int) - -(below : Int))).toNat = 0 := by omega
      rw [ite_eq_right hsub, hshiftL, hshiftR, hsl, hsr]

/-! ## The kernel division computes the reference division -/

/-- The flag `1 - (1 - (b - a))` is one exactly when `a < b`. -/
private theorem below_eq (a b : Nat) : 1 - (1 - (b - a)) = if a < b then 1 else 0 := by
  split <;> omega

/--
The encoding of the reference rounding of `na / nb * 2 ^ (D - U)` in the direction `mode`, for
operands normalized to a common width of `W + 1` bits, in the quantities `divCore` computes: `t`
is the exponent field minus one (zero below the normal range) and `mantissa` the quotient at that
scale, rounded in that direction.
-/
theorem directedRat_bits (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (negative : Bool)
    (W na nb D U : Nat)
    (hna : 2 ^ W ≤ na ∧ na < 2 ^ (W + 1))
    (hnb : 2 ^ W ≤ nb ∧ nb < 2 ^ (W + 1))
    (hgeneral : Model.roundRatScaled fmt negative na nb ((D : Int) - U) =
      Model.roundRatScaledGeneral fmt negative na nb ((D : Int) - U))
    (t mantissa : Nat)
    (ht : t = D + fmt.exponentBias - (U + (if na < nb then 1 else 0) + 1))
    (hmantissa : mantissa = Model.Policy.roundQuot mode.toRoundingMode negative 0
      (na <<< (D + fmt.exponentBias + fmt.fracWidth - (U + t + 1)))
      (nb <<< (U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth)))) :
    (Model.Internal.Directed.roundRatScaled fmt mode negative na nb ((D : Int) - U)).toNatBits =
      if mantissa = 0 then zeroWord fmt negative
      else if t * 2 ^ fmt.fracWidth + mantissa ≤ maxFinite fmt then
        (if negative then 2 ^ signPos fmt else 0) + (t * 2 ^ fmt.fracWidth + mantissa)
      else roundOverflowWord fmt mode negative := by
  have hnbpos : 0 < nb := lt_of_lt_of_le (Nat.two_pow_pos _) hnb.1
  have hden : nb <<< (U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth)) ≠ 0 := by
    rw [Nat.shiftLeft_eq]
    exact (Nat.mul_pos hnbpos (Nat.two_pow_pos _)).ne'
  cases mode <;> simp only [Model.IEEERoundingMode.toRoundingMode] at hmantissa
  · -- nearest, ties to even
    change (Model.roundRatScaled fmt negative na nb _).toNatBits = _
    rw [hgeneral]
    rw [Model.Policy.roundQuot_nearest_eq_roundQuotientEven _ _ _ _ hden] at hmantissa
    exact roundRatScaledGeneral_bits fmt negative W na nb D U hna hnb t mantissa ht hmantissa
  · -- nearest, ties away from zero
    change (Model.roundRatNearestAwayScaled fmt negative na nb _).toNatBits = _
    unfold Model.roundRatNearestAwayScaled
    rw [rationalIsGridTie_normalized fmt W na nb D U hna hnb t ht]
    by_cases htie : 2 * (na <<< (D + fmt.exponentBias + fmt.fracWidth - (U + t + 1)) %
        nb <<< (U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth))) =
      nb <<< (U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth))
    · rw [Model.Policy.roundQuot_nearestAway_eq_roundQuotDirected_of_tie _ _ _ _ hden htie]
        at hmantissa
      rw [show (2 * (na <<< (D + fmt.exponentBias + fmt.fracWidth - (U + t + 1)) %
          nb <<< (U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth))) ==
        nb <<< (U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth))) = true by simpa using htie,
        ite_eq_left rfl, roundOverflowWord_eq]
      exact roundRatMagnitudeDirected_bits fmt true negative W na nb D U hna hnb t mantissa ht
        hmantissa
    · rw [Model.Policy.roundQuot_nearestAway_eq_nearest_of_ne _ _ 0 _ _ htie,
        Model.Policy.roundQuot_nearest_eq_roundQuotientEven _ _ _ _ hden] at hmantissa
      rw [show (2 * (na <<< (D + fmt.exponentBias + fmt.fracWidth - (U + t + 1)) %
          nb <<< (U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth))) ==
        nb <<< (U + t + 1 - (D + fmt.exponentBias + fmt.fracWidth))) = false by simpa using htie,
        ite_eq_right (by decide), hgeneral]
      exact roundRatScaledGeneral_bits fmt negative W na nb D U hna hnb t mantissa ht hmantissa
  · -- toward zero
    rw [Model.Policy.roundQuot_towardZero_eq_roundQuotDirected] at hmantissa
    rw [roundOverflowWord_eq]
    exact roundRatMagnitudeDirected_bits fmt false negative W na nb D U hna hnb t mantissa ht
      hmantissa
  · -- toward positive infinity
    rw [Model.Policy.roundQuot_up_eq_roundQuotDirected _ _ _ _ hden] at hmantissa
    rw [roundOverflowWord_eq]
    exact roundRatMagnitudeDirected_bits fmt (!negative) negative W na nb D U hna hnb t mantissa
      ht hmantissa
  · -- toward negative infinity
    rw [Model.Policy.roundQuot_down_eq_roundQuotDirected _ _ _ _ hden] at hmantissa
    rw [roundOverflowWord_eq]
    exact roundRatMagnitudeDirected_bits fmt negative negative W na nb D U hna hnb t mantissa ht
      hmantissa
  · -- away from zero
    rw [Model.Policy.roundQuot_away_eq_roundQuotDirected _ _ _ _ hden] at hmantissa
    rw [roundOverflowWord_eq]
    exact roundRatMagnitudeDirected_bits fmt true negative W na nb D U hna hnb t mantissa ht
      hmantissa

/--
The normal-range significand of a quotient of nonzero operands, as the reference rounder computes
it, is at most `2 ^ (fracWidth + 1)`.
-/
theorem scaled_quotient_le (fmt : FloatFormat) (W mx my la lb : Nat) (hmx : mx ≠ 0)
    (hmy : my ≠ 0)
    (hna : 2 ^ W ≤ mx <<< la ∧ mx <<< la < 2 ^ (W + 1))
    (hnb : 2 ^ W ≤ my <<< lb ∧ my <<< lb < 2 ^ (W + 1)) :
    roundQuotientEven
        (RationalBinary.scaleByPowerOfTwo mx my
          (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 mx my)).1
        (RationalBinary.scaleByPowerOfTwo mx my
          (Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 mx my)).2 ≤
      2 ^ (fmt.fracWidth + 1) := by
  have hshift := floorLog2_shiftLeft mx my la lb hmx hmy
  have hnormal := Model.FiniteQuotientRound.floorLog2_eq_of_normal W _ _ hna hnb
  have hbounds := normalized_quotient_bounds fmt.fracWidth hna hnb
  rw [← roundQuotientEven_scale_shiftLeft mx my la lb _ hmy]
  have hexp : Int.ofNat fmt.fracWidth - RationalBinary.floorLog2 mx my - (la : Int) + lb =
      ((fmt.fracWidth + if mx <<< la < my <<< lb then 1 else 0 : Nat) : Int) := by
    rw [hnormal] at hshift
    by_cases h : mx <<< la < my <<< lb
    · have hle : ¬ my <<< lb ≤ mx <<< la := by omega
      simp only [hle, ite_false] at hshift
      simp only [h, ite_true, Int.ofNat_eq_natCast]
      push_cast
      omega
    · have hle : my <<< lb ≤ mx <<< la := by omega
      simp only [hle, ite_true] at hshift
      simp only [h, ite_false, Int.ofNat_eq_natCast]
      push_cast
      omega
  rw [hexp, scaleByPowerOfTwo_eq_shifts]
  have h1 : (((fmt.fracWidth + if mx <<< la < my <<< lb then 1 else 0 : Nat) : Int)).toNat =
      fmt.fracWidth + if mx <<< la < my <<< lb then 1 else 0 := Int.toNat_natCast _
  have h2 : (-((fmt.fracWidth + if mx <<< la < my <<< lb then 1 else 0 : Nat) : Int)).toNat =
      0 := by omega
  rw [h1, h2, Nat.shiftLeft_zero]
  exact hbounds.2

/-- The reference rational rounder is the general one, for normalizable nonzero operands. -/
theorem roundRatScaled_eq_general (fmt : FloatFormat) (negative : Bool) (W mx my la lb : Nat)
    (e : Int) (hmx : mx ≠ 0) (hmy : my ≠ 0)
    (hna : 2 ^ W ≤ mx <<< la ∧ mx <<< la < 2 ^ (W + 1))
    (hnb : 2 ^ W ≤ my <<< lb ∧ my <<< lb < 2 ^ (W + 1)) :
    Model.roundRatScaled fmt negative mx my e =
      Model.roundRatScaledGeneral fmt negative mx my e := by
  unfold Model.roundRatScaled
  by_cases hfmt : fmt.isIEEE = true
  · simp only [hfmt, ↓reduceDIte]
    exact ieeeRoundRatScaled_eq_general fmt hfmt negative mx my e hmy
      (scaled_quotient_le fmt W mx my la lb hmx hmy hna hnb)
  · simp [hfmt]

/--
The reference rounder of a quotient in any direction does not see a common normalization of its
operands: shifting the numerator by `la` and the denominator by `lb` and correcting the exponent
leaves the result unchanged.
-/
theorem directedRat_shiftLeft (fmt : FloatFormat) (mode : Model.IEEERoundingMode)
    (negative : Bool) (W mx my la lb : Nat) (e : Int) (hmx : mx ≠ 0) (hmy : my ≠ 0)
    (hna : 2 ^ W ≤ mx <<< la ∧ mx <<< la < 2 ^ (W + 1))
    (hnb : 2 ^ W ≤ my <<< lb ∧ my <<< lb < 2 ^ (W + 1)) :
    Model.Internal.Directed.roundRatScaled fmt mode negative (mx <<< la) (my <<< lb)
        (e - la + lb) =
      Model.Internal.Directed.roundRatScaled fmt mode negative mx my e := by
  have hna0 : mx <<< la ≠ 0 := by have := Nat.two_pow_pos W; omega
  have hnb0 : my <<< lb ≠ 0 := by have := Nat.two_pow_pos W; omega
  have hnearest : Model.roundRatScaled fmt negative (mx <<< la) (my <<< lb) (e - la + lb) =
      Model.roundRatScaled fmt negative mx my e := by
    rw [roundRatScaled_eq_general fmt negative W mx my la lb e hmx hmy hna hnb,
      roundRatScaled_eq_general fmt negative W (mx <<< la) (my <<< lb) 0 0 _ hna0 hnb0
        (by simpa using hna) (by simpa using hnb),
      roundRatScaledGeneral_shiftLeft fmt negative mx my la lb e hmx hmy]
  cases mode
  · exact hnearest
  · change Model.roundRatNearestAwayScaled fmt negative _ _ _ =
      Model.roundRatNearestAwayScaled fmt negative mx my e
    unfold Model.roundRatNearestAwayScaled
    rw [rationalIsGridTie_shiftLeft fmt mx my la lb e hmx hmy,
      roundRatMagnitudeDirected_shiftLeft fmt true negative mx my la lb e hmx hmy, hnearest]
  · exact roundRatMagnitudeDirected_shiftLeft fmt false negative mx my la lb e hmx hmy
  · exact roundRatMagnitudeDirected_shiftLeft fmt (!negative) negative mx my la lb e hmx hmy
  · exact roundRatMagnitudeDirected_shiftLeft fmt negative negative mx my la lb e hmx hmy
  · exact roundRatMagnitudeDirected_shiftLeft fmt true negative mx my la lb e hmx hmy

/--
`divCore` computes the encoding of the reference rational rounding in the direction `mode` of
operands normalized to a common width of `W + 1` bits, and the signed zero for a zero numerator.
-/
theorem divCore_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (negative : Bool)
    (W sign na nb D U special : Nat)
    (hsign : sign = if negative then 1 else 0)
    (hna : na = 0 ∨ (2 ^ W ≤ na ∧ na < 2 ^ (W + 1)))
    (hnb : 2 ^ W ≤ nb ∧ nb < 2 ^ (W + 1)) :
    divCore fmt mode sign na nb D U 0 special =
      if na = 0 then zeroWord fmt negative
      else (Model.Internal.Directed.roundRatScaled fmt mode negative na nb
        ((D : Int) - U)).toNatBits := by
  have hnbpos : 0 < nb := lt_of_lt_of_le (Nat.two_pow_pos _) hnb.1
  have hnb0 : nb ≠ 0 := hnbpos.ne'
  have hdenpos : ∀ k, 0 < nb <<< k := fun k => by
    rw [Nat.shiftLeft_eq]
    exact Nat.mul_pos hnbpos (Nat.two_pow_pos _)
  have hsign : sign = signNat negative := hsign
  have hzs : decide (sign ≠ 0) = negative := by
    subst hsign
    cases negative <;> simp [signNat]
  have hsw : sign * 2 ^ signPos fmt = if negative then 2 ^ signPos fmt else 0 := by
    subst hsign
    cases negative <;> simp [signNat]
  rw [divCore_def fmt mode sign na nb D U 0 special (by rcases hna with h | h <;> omega)]
  unfold roundQuotient
  simp only [Nat.add_eq, Nat.sub_eq, Nat.shiftLeft_eq', div_def, mod_def,
    Nat.succ_eq_add_one]
  simp only [below_eq]
  rw [pack_eq, hsign, roundUp_eq mode negative 0 _ _ (hdenpos _), ← hsign]
  simp only [ne_eq, not_true_eq_false, ite_false, hzs, hsw]
  rcases hna with hna0 | hna
  · subst hna0
    simp [Model.Policy.roundQuot]
  · have hna0 : na ≠ 0 := by
      have := Nat.two_pow_pos W
      omega
    rw [ite_eq_right hna0,
      directedRat_bits fmt mode negative W na nb D U hna hnb
        (roundRatScaled_eq_general fmt negative W na nb 0 0 _ hna0 hnb0 (by simpa using hna)
          (by simpa using hnb)) _ _ rfl rfl]

/--
`divSpecial` computes the encoding of the reference quotient when an operand is not finite, in
every encoding.
-/
theorem divSpecial_eq_of_nonFinite {fmt : FloatFormat} (x y : Model fmt)
    (h : Model.isFinite x = false ∨ Model.isFinite y = false) :
    divSpecial fmt x.toNatBits y.toNatBits = (Model.Spec.div x y).toNatBits := by
  have hspec : Model.Spec.div x y =
      (Model.chooseNaN2 x y).getD
        (if Model.isInfinite x then
          if Model.isInfinite y then Model.invalidResult fmt
          else Model.nativeOverflow fmt (Model.signBit x != Model.signBit y)
        else if Model.isInfinite y then Model.zero fmt (Model.signBit x != Model.signBit y)
        else Model.invalidResult fmt) := by
    unfold Model.Spec.div Model.Spec.divSpecial
    rcases h with h | h
    · rw [toDyadic?_eq_none_of_isFinite_eq_false x h]
      cases Model.toDyadic? y <;> cases Model.chooseNaN2 x y <;> rfl
    · rw [toDyadic?_eq_none_of_isFinite_eq_false y h]
      cases Model.toDyadic? x <;> cases Model.chooseNaN2 x y <;> rfl
  unfold divSpecial
  simp only [Nat.shiftRight_eq', Nat.land_eq, sign_toNatBits, magnitude_toNatBits, infFlag_eq,
    nanFlag_eq, beq_sign]
  rw [hspec]
  refine (chooseNaN2_getD_bits x y _ _ ?_).symm
  intro hnx hny
  have hinf : Model.isInfinite x = true ∨ Model.isInfinite y = true := by
    have hx := isNaN_eq_not_isFinite_and_not_isInfinite x
    have hy := isNaN_eq_not_isFinite_and_not_isInfinite y
    rw [hnx] at hx
    rw [hny] at hy
    rcases h with h | h
    · rw [h] at hx
      cases hi : Model.isInfinite x
      · rw [hi] at hx
        exact absurd hx (by decide)
      · exact Or.inl rfl
    · rw [h] at hy
      cases hi : Model.isInfinite y
      · rw [hi] at hy
        exact absurd hy (by decide)
      · exact Or.inr rfl
  simp only [bne, zeroWord_eq, invalidWord_eq, overflowWord_eq]
  rcases hinf with hi | hi
  · rw [hi]
    cases Model.isInfinite y <;> cases (Model.signBit x == Model.signBit y) <;> rfl
  · rw [hi]
    cases Model.isInfinite x <;> cases (Model.signBit x == Model.signBit y) <;> rfl

/--
`divSpecial` computes the encoding of the reference quotient of two finite values when the
divisor is a zero.
-/
theorem divSpecial_eq_of_zero_divisor {fmt : FloatFormat} (x y : Model fmt)
    (hfinx : Model.isFinite x = true) (hfiny : Model.isFinite y = true)
    (hzero : (if Model.expField y = 0 then Model.fracField y
      else 2 ^ fmt.fracWidth + Model.fracField y) = 0) :
    divSpecial fmt x.toNatBits y.toNatBits = (Model.Spec.div x y).toNatBits := by
  obtain ⟨dx, hdx, hnx, hsx, -⟩ := toDyadic?_of_isFinite x hfinx
  obtain ⟨dy, hdy, hny, hsy, -⟩ := toDyadic?_of_isFinite y hfiny
  have hpos : 0 < 2 ^ fmt.fracWidth := Nat.two_pow_pos _
  have hux : (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x = 0) ↔
      dx.significand = 0 := by
    rw [hsx]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := Nat.eq_zero_of_add_eq_zero h
      rw [ite_eq_left ((Nat.mul_eq_zero.mp h1).resolve_right hpos.ne'), h2]
    · intro h
      by_cases he : Model.expField x = 0
      · rw [ite_eq_left he] at h
        rw [he, h, Nat.zero_mul]
      · rw [ite_eq_right he] at h
        omega
  have hspec : Model.Spec.div x y =
      if dx.significand = 0 then Model.invalidResult fmt
      else Model.nativeOverflow fmt (Bool.xor (Model.signBit x) (Model.signBit y)) := by
    have hy0 : dy.significand = 0 := by rw [hsy]; exact hzero
    simp [Model.Spec.div, hdx, hdy, hy0, hnx, hny]
  unfold divSpecial
  simp only [Nat.shiftRight_eq', Nat.land_eq, sign_toNatBits, magnitude_toNatBits, infFlag_eq,
    nanFlag_eq, beq_sign, Model.isInfinite_eq_false_of_toDyadic?_some hdx,
    Model.isInfinite_eq_false_of_toDyadic?_some hdy, Model.isNaN_eq_false_of_toDyadic?_some hdx,
    Model.isNaN_eq_false_of_toDyadic?_some hdy]
  rw [hspec]
  simp only [invalidWord_eq, overflowWord_eq]
  by_cases hx0 : dx.significand = 0
  · rw [ite_eq_left hx0, hux.mpr hx0]
    rfl
  · have hne : Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x ≠ 0 :=
      fun h => hx0 (hux.mp h)
    have hbeq : Nat.beq (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) 0 = false := by
      cases hb : Nat.beq (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hne
    rw [ite_eq_right hx0, hbeq]
    cases Model.signBit x <;> cases Model.signBit y <;> rfl

/--
`div` computes the encoding of the reference division `Model.div x y (mode := mode)`, for every
format descriptor, every rounding direction and all operands.
-/
theorem div_eq_spec {fmt : FloatFormat} (mode : Model.IEEERoundingMode) (x y : Model fmt) :
    div fmt mode x.toNatBits y.toNatBits = (Model.div x y (mode := mode)).toNatBits := by
  have hfx := Model.fracField_lt_pow2 x
  have hfy := Model.fracField_lt_pow2 y
  unfold div
  simp only [Nat.shiftRight_eq', Nat.land_eq, Nat.shiftLeft_eq', Nat.sub_eq, Nat.add_eq,
    Nat.mul_eq, Nat.xor_eq, Nat.succ_eq_add_one, sign_toNatBits, magnitude_toNatBits,
    fields_shiftRight _ _ _ hfx, fields_shiftRight _ _ _ hfy, fields_sub_shiftLeft, xor_sign]
  by_cases hguard :
      Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x - maxFinite fmt +
            negZeroNaN fmt * ((if Model.signBit x then 1 else 0) -
              (Model.expField x * 2 ^ fmt.fracWidth + Model.fracField x)) +
          (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y - maxFinite fmt +
            negZeroNaN fmt * ((if Model.signBit y then 1 else 0) -
              (Model.expField y * 2 ^ fmt.fracWidth + Model.fracField y))) +
        (1 - if Model.expField y = 0 then Model.fracField y
          else 2 ^ fmt.fracWidth + Model.fracField y) = 0
  · obtain ⟨hgxy, hgdivisor⟩ := Nat.eq_zero_of_add_eq_zero hguard
    obtain ⟨hgx, hgy⟩ := Nat.eq_zero_of_add_eq_zero hgxy
    obtain ⟨dx, hdx, hnx, hsx, hex⟩ :=
      toDyadic?_of_isFinite x (isFinite_of_nonFinite_eq_zero x hgx)
    obtain ⟨dy, hdy, hny, hsy, hey⟩ :=
      toDyadic?_of_isFinite y (isFinite_of_nonFinite_eq_zero y hgy)
    have hmx := decoded_significand_lt x
    have hmy := decoded_significand_lt y
    rw [hguard]
    rw [← hsx] at hmx
    rw [← hsy] at hmy hgdivisor
    rw [← hsx, ← hsy, ← hnx, ← hny]
    have hy0 : dy.significand ≠ 0 := by omega
    have hlenx := significandLength_eq hmx
    have hleny := significandLength_eq hmy
    rw [hlenx, hleny, ite_eq_right hy0]
    have hnb := normalized_bounds hy0 hmy
    have hlb : fmt.fracWidth + 1 - (dy.significand.log2 + 1) =
        fmt.fracWidth - dy.significand.log2 := by omega
    rw [hlb, div_of_finite mode x y dx dy hdx hdy, ite_eq_right hy0]
    by_cases hx0 : dx.significand = 0
    · rw [ite_eq_left hx0, hx0]
      simp only [ite_true, Nat.zero_shiftLeft]
      rw [divCore_eq fmt mode (Bool.xor dx.negative dy.negative) fmt.fracWidth _ 0 _ _ _ _ rfl
        (Or.inl rfl) hnb]
      simp [zeroWord_eq]
    · have hna := normalized_bounds hx0 hmx
      have hla : fmt.fracWidth + 1 - (dx.significand.log2 + 1) =
          fmt.fracWidth - dx.significand.log2 := by omega
      rw [ite_eq_right hx0, ite_eq_right hx0, hla,
        divCore_eq fmt mode (Bool.xor dx.negative dy.negative) fmt.fracWidth _ _ _ _ _ _ rfl
          (Or.inr hna) hnb,
        ite_eq_right (by omega : dx.significand <<< (fmt.fracWidth - dx.significand.log2) ≠ 0),
        ← directedRat_shiftLeft fmt mode _ fmt.fracWidth dx.significand dy.significand
          (fmt.fracWidth - dx.significand.log2) (fmt.fracWidth - dy.significand.log2)
          (dx.exponent - dy.exponent) hx0 hy0 hna hnb]
      congr 2
      rw [hex hx0, hey hy0]
      push_cast
      omega
  · rw [show divCore fmt mode _ _ _ _ _ _ _ = divSpecial fmt x.toNatBits y.toNatBits from by
      unfold divCore roundQuotient
      simp only [pack_eq, ne_eq, hguard, not_false_eq_true, ite_true]]
    by_cases hfinx : Model.isFinite x = true
    · by_cases hfiny : Model.isFinite y = true
      · have hzero : (if Model.expField y = 0 then Model.fracField y
            else 2 ^ fmt.fracWidth + Model.fracField y) = 0 := by
          have hgx := nonFinite_eq_zero_of_isFinite x hfinx
          have hgy := nonFinite_eq_zero_of_isFinite y hfiny
          unfold nonFinite at hgx hgy
          simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq] at hgx hgy
          rw [hgx, hgy] at hguard
          omega
        obtain ⟨dx, hdx, -⟩ := toDyadic?_of_isFinite x hfinx
        obtain ⟨dy, hdy, -, hsy, -⟩ := toDyadic?_of_isFinite y hfiny
        have hy0 : dy.significand = 0 := by rw [hsy]; exact hzero
        have hspec : Model.div x y (mode := mode) = Model.Spec.div x y := by
          rw [div_of_finite mode x y dx dy hdx hdy, ite_eq_left hy0]
          simp [Model.Spec.div, hdx, hdy, hy0]
        rw [hspec]
        exact divSpecial_eq_of_zero_divisor x y hfinx hfiny hzero
      · rw [div_of_nonFinite mode x y (Or.inr (Bool.eq_false_of_not_eq_true hfiny))]
        exact divSpecial_eq_of_nonFinite x y (Or.inr (Bool.eq_false_of_not_eq_true hfiny))
    · rw [div_of_nonFinite mode x y (Or.inl (Bool.eq_false_of_not_eq_true hfinx))]
      exact divSpecial_eq_of_nonFinite x y (Or.inl (Bool.eq_false_of_not_eq_true hfinx))

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
