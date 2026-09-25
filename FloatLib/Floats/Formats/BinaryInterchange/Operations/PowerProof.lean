/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Power
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.PowerProof
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Finite

/-!
# Correct rounding of integral powers

`Model.pow` sends a finite nonzero base with a finite integral exponent to
`Power.integerPower?`. This file proves that the result is the nearest-even rounding of the
exact real power.

The executable kernel has three routes. Small exact problems call `powInt`, which rounds the
exact rational power once. A base of magnitude one gives a signed one. Every other case brackets
the exact power between two dyadic endpoints (`powBounds`, `squareScreen`) and accepts the
rounding only when both endpoints round to the same finite value (`roundEnclosure?`); if no
working precision decides, `powInt` is the fallback. The endpoint lemmas show that the
brackets are sound, `toReal_of_attempt` turns an accepted bracket into correct rounding, and
`toReal_integerPowerWith` combines the three routes.

The main result is `toReal_pow_of_eq_intCast`: for an IEEE format, a finite nonzero base and a
finite exponent with integer value `n`, every finite result of `pow` equals
`roundAt fmt (toReal base ^ n)`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Power

namespace Endpoint

/-- Every endpoint is nonnegative. -/
theorem toRat_nonneg (x : Endpoint) : 0 ≤ x.toRat := by
  unfold toRat; positivity

/-- The exact product of endpoints denotes the product of their values. -/
@[simp] theorem toRat_mul (x y : Endpoint) : (x.mul y).toRat = x.toRat * y.toRat := by
  simp only [toRat, mul, Nat.cast_mul, zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
  ring

/-- The unit endpoint denotes one. -/
@[simp] theorem toRat_one : one.toRat = 1 := by simp [toRat, one]

private theorem shift_value (m : Nat) (e : Int) (s : Nat) :
    ((m >>> s : Nat) : Rat) * 2 ^ (e + s) = ((m / 2 ^ s : Nat) * 2 ^ s : Nat) * 2 ^ e := by
  rw [Nat.shiftRight_eq_div_pow, zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
  push_cast
  rw [zpow_natCast]
  ring

/-- Truncation toward zero never increases an endpoint. -/
theorem toRat_truncDown_le (precision : Nat) (x : Endpoint) :
    (truncDown precision x).toRat ≤ x.toRat := by
  simp only [truncDown, toRat]
  rw [shift_value]
  gcongr
  exact Nat.div_mul_le_self _ _

/-- Truncation away from zero never decreases an endpoint. -/
theorem le_toRat_truncUp (precision : Nat) (x : Endpoint) :
    x.toRat ≤ (truncUp precision x).toRat := by
  simp only [truncUp, toRat]
  set s := excess precision x
  have hpow : (0 : Rat) < 2 ^ x.exponent := by positivity
  split
  · rename_i h
    have h' : x.mantissa >>> s <<< s = x.mantissa := by simpa using h
    rw [shift_value, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftLeft_eq, h']
  · rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
    have hlt : x.mantissa < (x.mantissa / 2 ^ s + 1) * 2 ^ s := by
      rw [add_mul, one_mul]
      have := Nat.lt_div_mul_add (a := x.mantissa) (Nat.two_pow_pos s)
      linarith
    have hlt' : (x.mantissa : Rat) ≤ ((x.mantissa / 2 ^ s + 1 : Nat) : Rat) * 2 ^ s := by
      exact_mod_cast hlt.le
    rw [Nat.shiftRight_eq_div_pow]
    calc (x.mantissa : Rat) * 2 ^ x.exponent
        ≤ ((x.mantissa / 2 ^ s + 1 : Nat) : Rat) * 2 ^ s * 2 ^ x.exponent := by gcongr
      _ = _ := by push_cast; rw [zpow_natCast]; ring

/-- The leading-bit test is a sound lower bound. -/
theorem two_zpow_le_of_geTwoPow {x : Endpoint} {bound : Int} (h : x.geTwoPow bound = true) :
    (2 : Rat) ^ bound ≤ x.toRat := by
  simp only [geTwoPow, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨hm, hb⟩ := h
  have hlog : ((2 ^ Nat.log2 x.mantissa : Nat) : Rat) ≤ x.mantissa := by
    exact_mod_cast Nat.log2_self_le hm
  unfold toRat
  calc (2 : Rat) ^ bound ≤ 2 ^ ((Nat.log2 x.mantissa : Int) + x.exponent) :=
        zpow_le_zpow_right₀ (by norm_num) hb
    _ = ((2 ^ Nat.log2 x.mantissa : Nat) : Rat) * 2 ^ x.exponent := by
        rw [zpow_add₀ (by norm_num)]; push_cast; rw [zpow_natCast]
    _ ≤ _ := by gcongr

/-- The leading-bit test is a sound upper bound. -/
theorem le_two_zpow_of_leTwoPow {x : Endpoint} {bound : Int} (h : x.leTwoPow bound = true) :
    x.toRat ≤ (2 : Rat) ^ bound := by
  simp only [leTwoPow, decide_eq_true_eq] at h
  have hlog : (x.mantissa : Rat) ≤ ((2 ^ (Nat.log2 x.mantissa + 1) : Nat) : Rat) := by
    exact_mod_cast (Nat.lt_log2_self (n := x.mantissa)).le
  unfold toRat
  calc (x.mantissa : Rat) * 2 ^ x.exponent
      ≤ ((2 ^ (Nat.log2 x.mantissa + 1) : Nat) : Rat) * 2 ^ x.exponent := by gcongr
    _ = 2 ^ ((Nat.log2 x.mantissa : Int) + 1 + x.exponent) := by
        rw [zpow_add₀ (by norm_num)]; push_cast; rw [← zpow_natCast]; push_cast; rfl
    _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) h

end Endpoint

/-- Binary exponentiation with directed truncation encloses the exact power. -/
theorem powBounds_spec (precision : Nat) (base : Endpoint) (exponent : Nat) :
    (powBounds precision base exponent).1.toRat ≤ base.toRat ^ exponent ∧
      base.toRat ^ exponent ≤ (powBounds precision base exponent).2.toRat := by
  induction exponent using Nat.strong_induction_on with
  | _ n ih =>
    rw [powBounds]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      obtain ⟨hlo, hhi⟩ := ih (n / 2) (by omega)
      set half := powBounds precision base (n / 2)
      have hlo0 := half.1.toRat_nonneg
      have ha0 := base.toRat_nonneg
      have hsq : base.toRat ^ n = (base.toRat ^ (n / 2)) ^ 2 * base.toRat ^ (n % 2) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      have hlower : (Endpoint.truncDown precision (half.1.mul half.1)).toRat ≤
          (base.toRat ^ (n / 2)) ^ 2 := by
        refine (Endpoint.toRat_truncDown_le _ _).trans ?_
        rw [Endpoint.toRat_mul, sq]
        exact mul_le_mul hlo hlo hlo0 (hlo0.trans hlo)
      have hupper : (base.toRat ^ (n / 2)) ^ 2 ≤
          (Endpoint.truncUp precision (half.2.mul half.2)).toRat := by
        refine le_trans ?_ (Endpoint.le_toRat_truncUp _ _)
        rw [Endpoint.toRat_mul, sq]
        exact mul_le_mul hhi hhi (by positivity) (hlo0.trans (hlo.trans hhi))
      split
      · rename_i hodd
        rw [hsq, hodd, pow_one]
        constructor
        · refine (Endpoint.toRat_truncDown_le _ _).trans ?_
          rw [Endpoint.toRat_mul]
          exact mul_le_mul_of_nonneg_right hlower ha0
        · refine le_trans ?_ (Endpoint.le_toRat_truncUp _ _)
          rw [Endpoint.toRat_mul]
          exact mul_le_mul_of_nonneg_right hupper ha0
      · rename_i heven
        rw [hsq, show n % 2 = 0 by omega, pow_zero, mul_one]
        exact ⟨hlower, hupper⟩

/-- What a screening outcome certifies about `v ^ (2 ^ t)` for every `t ≥ remaining`. -/
def Screen.Holds (above below : Int) (remaining : Nat) (v : Rat) : Screen → Prop
  | .above => ∀ t, remaining ≤ t → (2 : Rat) ^ above ≤ v ^ (2 ^ t)
  | .below => ∀ t, remaining ≤ t → v ^ (2 ^ t) ≤ (2 : Rat) ^ below
  | .bounds lower upper => lower.toRat ≤ v ^ (2 ^ remaining) ∧ v ^ (2 ^ remaining) ≤ upper.toRat

/-- Repeated squaring with early screening is sound for every value in the enclosure. -/
theorem squareScreen_holds (precision : Nat) (above below : Int) (remaining : Nat)
    (lower upper : Endpoint) (v : Rat) (hv : 0 ≤ v)
    (hlower : lower.toRat ≤ v) (hupper : v ≤ upper.toRat) :
    (squareScreen precision above below remaining lower upper).Holds above below remaining v := by
  induction remaining generalizing lower upper v with
  | zero =>
    rw [squareScreen]
    split
    · rename_i h
      intro t _
      have h1 := Endpoint.two_zpow_le_of_geTwoPow h
      have hone : (1 : Rat) ≤ v :=
        le_trans (one_le_zpow₀ (by norm_num) (le_max_right _ _)) (h1.trans hlower)
      calc (2 : Rat) ^ above ≤ 2 ^ max above 0 := zpow_le_zpow_right₀ (by norm_num) (le_max_left _ _)
        _ ≤ v := h1.trans hlower
        _ ≤ v ^ (2 ^ t) := le_self_pow₀ hone (by positivity)
    · split
      · rename_i _ h
        intro t _
        have h1 := Endpoint.le_two_zpow_of_leTwoPow h
        have hone : v ≤ 1 :=
          le_trans (hupper.trans h1) (zpow_le_one_of_nonpos₀ (by norm_num) (min_le_right _ _))
        calc v ^ (2 ^ t) ≤ v := pow_le_of_le_one hv hone (by positivity)
          _ ≤ 2 ^ min below 0 := hupper.trans h1
          _ ≤ 2 ^ below := zpow_le_zpow_right₀ (by norm_num) (min_le_left _ _)
      · simpa [Screen.Holds] using ⟨hlower, hupper⟩
  | succ r ih =>
    rw [squareScreen]
    split
    · rename_i h
      intro t _
      have h1 := Endpoint.two_zpow_le_of_geTwoPow h
      have hone : (1 : Rat) ≤ v :=
        le_trans (one_le_zpow₀ (by norm_num) (le_max_right _ _)) (h1.trans hlower)
      calc (2 : Rat) ^ above ≤ 2 ^ max above 0 := zpow_le_zpow_right₀ (by norm_num) (le_max_left _ _)
        _ ≤ v := h1.trans hlower
        _ ≤ v ^ (2 ^ t) := le_self_pow₀ hone (by positivity)
    · split
      · rename_i _ h
        intro t _
        have h1 := Endpoint.le_two_zpow_of_leTwoPow h
        have hone : v ≤ 1 :=
          le_trans (hupper.trans h1) (zpow_le_one_of_nonpos₀ (by norm_num) (min_le_right _ _))
        calc v ^ (2 ^ t) ≤ v := pow_le_of_le_one hv hone (by positivity)
          _ ≤ 2 ^ min below 0 := hupper.trans h1
          _ ≤ 2 ^ below := zpow_le_zpow_right₀ (by norm_num) (min_le_left _ _)
      · have hlo0 := lower.toRat_nonneg
        have hsqlo : (Endpoint.truncDown precision (lower.mul lower)).toRat ≤ v ^ 2 := by
          refine (Endpoint.toRat_truncDown_le _ _).trans ?_
          rw [Endpoint.toRat_mul, sq]
          exact mul_le_mul hlower hlower hlo0 hv
        have hsqhi : v ^ 2 ≤ (Endpoint.truncUp precision (upper.mul upper)).toRat := by
          refine le_trans ?_ (Endpoint.le_toRat_truncUp _ _)
          rw [Endpoint.toRat_mul, sq]
          exact mul_le_mul hupper hupper hv (hv.trans hupper)
        have hrec := ih _ _ (v ^ 2) (by positivity) hsqlo hsqhi
        have hpow : ∀ t : Nat, (v ^ 2) ^ (2 ^ t) = v ^ (2 ^ (t + 1)) := by
          intro t
          rw [← pow_mul, pow_succ, mul_comm]
        revert hrec
        cases squareScreen precision above below r
            (Endpoint.truncDown precision (lower.mul lower))
            (Endpoint.truncUp precision (upper.mul upper)) with
        | above =>
          intro hrec t ht
          obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
          simpa [hpow] using hrec t' (by omega)
        | below =>
          intro hrec t ht
          obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
          simpa [hpow] using hrec t' (by omega)
        | bounds lo hi =>
          intro hrec
          simpa [Screen.Holds, hpow] using hrec

/-- An accepted signed enclosure is the nearest-even rounding of every real target inside it. -/
theorem toReal_of_roundEnclosure? {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {lower upper : Rat} {result : Model fmt} (h : roundEnclosure? fmt lower upper = some result)
    {target : ℝ} (hlower : (lower : ℝ) ≤ target) (hupper : target ≤ upper) :
    toReal result = roundAt fmt target := by
  unfold roundEnclosure? at h
  dsimp only at h
  split at h
  · rename_i hsame
    obtain ⟨hfinite, hequal⟩ := hsame
    cases h
    have hlo := toReal_roundAlgebraicRat fmt hfmt lower hfinite
    have hhi := toReal_roundAlgebraicRat fmt hfmt upper (hequal ▸ hfinite)
    rw [← hequal] at hhi
    exact le_antisymm (hlo.trans_le (roundAt_mono fmt hlower))
      ((roundAt_mono fmt hupper).trans_eq hhi.symm)
  · simp at h

private theorem bpow_binary (e : Int) :
    Flocq.bpow Numerics.binaryRadix e = (2 : ℝ) ^ e := by
  simp [Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

private theorem roundAt_signed_eq_zero (fmt : FloatFormat) (negative : Bool) {v : ℝ}
    (hv : 0 ≤ v) (hsmall : v ≤ (2 : ℝ) ^ AlgebraicRounding.lowerExponent fmt) :
    roundAt fmt ((if negative then -1 else 1) * v) = 0 := by
  have hz := AlgebraicRounding.roundAt_eq_zero_of_le_halfMinSubnormal fmt v hv
    (by rwa [bpow_binary])
  cases negative <;> simp [hz]

private theorem isFinite_nativeOverflow {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (sign : Bool) : isFinite (nativeOverflow fmt sign) = false := by
  have hs := FloatFormat.supportsInfinity_eq_true_of_isIEEE fmt hfmt
  cases sign <;> simp [nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt,
    isFinite_posInf fmt hs, isFinite_negInf fmt hs]

/--
The exact target of `attempt`: `(-1)^negative * ((base ^ magnitude) ^ (2 ^ shift)) ^ (±1)`,
with the reciprocal selected by `reciprocal`.
-/
noncomputable def attemptTarget (negative reciprocal : Bool) (base : Endpoint)
    (magnitude shift : Nat) : ℝ :=
  let value : ℝ := (((base.toRat ^ magnitude) ^ (2 ^ shift) : Rat) : ℝ)
  (if negative then -1 else 1) * (if reciprocal then value⁻¹ else value)

/-- Every finite result of one enclosure attempt is the correctly rounded exact power. -/
theorem toReal_of_attempt {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {precision : Nat} {negative reciprocal : Bool} {base : Endpoint} {magnitude shift : Nat}
    {result : Model fmt}
    (h : attempt fmt precision negative reciprocal base magnitude shift = some result)
    (hfinite : isFinite result = true) :
    toReal result = roundAt fmt (attemptTarget negative reciprocal base magnitude shift) := by
  unfold attempt at h
  dsimp only at h
  set upperBound := AlgebraicRounding.upperExponent fmt
  set lowerBound := AlgebraicRounding.lowerExponent fmt
  set above := if reciprocal then -lowerBound else upperBound
  set below := if reciprocal then -upperBound else lowerBound
  set cap := precision + 2 * (Nat.log2 (AlgebraicRounding.exponentSpan fmt) + 1) + 16
  set start := powBounds precision base magnitude
  have hstart := powBounds_spec precision base magnitude
  have hholds := squareScreen_holds precision above below (min shift cap) start.1 start.2
    (base.toRat ^ magnitude) (by have := base.toRat_nonneg; positivity) hstart.1 hstart.2
  set V : Rat := (base.toRat ^ magnitude) ^ (2 ^ shift) with hV
  have hV0 : 0 ≤ V := by have := base.toRat_nonneg; positivity
  unfold attemptTarget
  simp only [← hV]
  have hcastV : ∀ e : Int, ((2 : Rat) ^ e ≤ V ↔ (2 : ℝ) ^ e ≤ (V : ℝ)) := by
    intro e
    rw [← Rat.cast_le (K := ℝ)]
    push_cast
    rfl
  have hcastV' : ∀ e : Int, (V ≤ (2 : Rat) ^ e ↔ (V : ℝ) ≤ (2 : ℝ) ^ e) := by
    intro e
    rw [← Rat.cast_le (K := ℝ)]
    push_cast
    rfl
  rcases hs : squareScreen precision above below (min shift cap) start.1 start.2 with
    _ | _ | ⟨lo, hi⟩ <;> simp only [hs] at h hholds
  · have hbig : (2 : ℝ) ^ above ≤ (V : ℝ) := (hcastV _).1 (hholds shift (min_le_left _ _))
    cases reciprocal
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp [isFinite_nativeOverflow hfmt] at hfinite
    · simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      rw [toReal_zero, eq_comm]
      simp only [↓reduceIte]
      apply roundAt_signed_eq_zero fmt negative (by positivity)
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (-lowerBound) := by positivity
      have hbig' : (2 : ℝ) ^ (-lowerBound) ≤ (V : ℝ) := by simpa [above] using hbig
      calc (V : ℝ)⁻¹ ≤ ((2 : ℝ) ^ (-lowerBound))⁻¹ := inv_anti₀ hpos hbig'
        _ = (2 : ℝ) ^ lowerBound := by rw [zpow_neg, inv_inv]
  · have hsmall : (V : ℝ) ≤ (2 : ℝ) ^ below := (hcastV' _).1 (hholds shift (min_le_left _ _))
    cases reciprocal
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      rw [toReal_zero, eq_comm]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply roundAt_signed_eq_zero fmt negative (by exact_mod_cast hV0)
      simpa [below] using hsmall
    · simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      simp [isFinite_nativeOverflow hfmt] at hfinite
  · split at h
    · simp at h
    · rename_i hguard
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true',
        Bool.not_eq_false] at hguard
      have hcap : min shift cap = shift := by omega
      rw [hcap] at hholds
      obtain ⟨hlo, hhi⟩ := hholds
      rw [← hV] at hlo hhi
      have hlo' : (lo.toRat : ℝ) ≤ V := by exact_mod_cast hlo
      have hhi' : (V : ℝ) ≤ hi.toRat := by exact_mod_cast hhi
      have hlopos : (0 : ℝ) < lo.toRat := by
        have : (0 : Rat) < lo.toRat := by
          unfold Endpoint.toRat
          have : lo.mantissa ≠ 0 := hguard.1.1.2
          positivity
        exact_mod_cast this
      have hVpos : (0 : ℝ) < V := hlopos.trans_le hlo'
      have hrange : ((if reciprocal then hi.toRat⁻¹ else lo.toRat : Rat) : ℝ) ≤
            (if reciprocal then (V : ℝ)⁻¹ else V) ∧
          (if reciprocal then (V : ℝ)⁻¹ else V) ≤
            ((if reciprocal then lo.toRat⁻¹ else hi.toRat : Rat) : ℝ) := by
        cases reciprocal
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨hlo', hhi'⟩
        · simp only [↓reduceIte, Rat.cast_inv]
          exact ⟨inv_anti₀ hVpos hhi', inv_anti₀ hlopos hlo'⟩
      cases negative
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h ⊢
        exact toReal_of_roundEnclosure? hfmt h hrange.1 hrange.2
      · simp only [↓reduceIte, neg_mul, one_mul] at h ⊢
        refine toReal_of_roundEnclosure? hfmt h ?_ ?_
        · push_cast; exact neg_le_neg hrange.2
        · push_cast; exact neg_le_neg hrange.1

private theorem odd_shiftLeft_iff (magnitude shift : Nat) :
    Odd (magnitude <<< shift) ↔ (shift == 0 && magnitude % 2 == 1) = true := by
  rw [Nat.shiftLeft_eq]
  cases shift with
  | zero => simp [Nat.odd_iff]
  | succ s =>
    have heven : Even (magnitude * 2 ^ (s + 1)) :=
      (Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_left _
    constructor
    · intro hodd
      exact absurd hodd (Nat.not_odd_iff_even.mpr heven)
    · intro h
      simp at h

/--
The exact target of `attempt` for the decoded base is the real power
`toReal base ^ integralValue negativeExponent magnitude shift`.
-/
theorem zpow_integralValue_eq_attemptTarget (b : Numerics.Dyadic) (negativeExponent : Bool)
    (magnitude shift : Nat) :
    b.toReal ^ integralValue negativeExponent magnitude shift =
      attemptTarget (b.negative && (shift == 0 && magnitude % 2 == 1)) negativeExponent
        ⟨b.significand, b.exponent⟩ magnitude shift := by
  set N := magnitude <<< shift with hN
  set a : ℝ := (b.significand : ℝ) * (2 : ℝ) ^ b.exponent
  have hreal : b.toReal = (if b.negative then -1 else 1) * a := by
    cases hneg : b.negative <;>
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hneg, a]
  have hpow : a ^ N = ((a ^ magnitude) ^ (2 ^ shift)) := by
    rw [hN, Nat.shiftLeft_eq, pow_mul]
  have hsign : ((if b.negative then -1 else 1 : ℝ)) ^ N =
      if (b.negative && (shift == 0 && magnitude % 2 == 1)) then -1 else 1 := by
    cases hneg : b.negative
    · simp
    · rw [ite_eq_left rfl, neg_one_pow_eq_ite]
      have hodd := odd_shiftLeft_iff magnitude shift
      rw [← hN] at hodd
      by_cases h : (shift == 0 && magnitude % 2 == 1) = true
      · have : ¬ Even N := Nat.not_even_iff_odd.mpr (hodd.mpr h)
        simp [this, h]
      · have : Even N := Nat.not_odd_iff_even.mp (fun ho => h (hodd.mp ho))
        simp only [Bool.true_and]
        simp [this, h]
  have hval : integralValue negativeExponent magnitude shift =
      if negativeExponent then -(N : ℤ) else (N : ℤ) := rfl
  have hV : (((((⟨b.significand, b.exponent⟩ : Endpoint).toRat ^
      magnitude) ^ (2 ^ shift) : ℚ) : ℝ)) = a ^ N := by
    rw [hpow]; simp only [Endpoint.toRat, a]; push_cast; rfl
  unfold attemptTarget
  rw [hV, hval, hreal, ← hsign]
  cases negativeExponent
  · simp only [Bool.false_eq_true, ite_false, zpow_natCast, mul_pow]
  · simp only [ite_true, zpow_neg, zpow_natCast, mul_pow, mul_inv]
    congr 1
    rcases (show ((if b.negative then -1 else 1 : ℝ)) = 1 ∨
        ((if b.negative then -1 else 1 : ℝ)) = -1 by split <;> simp) with h | h
    · rw [h]; simp
    · rw [h]
      rcases neg_one_pow_eq_or ℝ N with h' | h' <;> rw [h'] <;> norm_num

/--
`integerPowerWith` is correctly rounded for every exact budget: a finite result is the
nearest-even rounding of the real power of a finite nonzero base.
-/
theorem toReal_integerPowerWith {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (exactBudget : Nat) {base : Model fmt} {b : Numerics.Dyadic} (hb : toDyadic? base = some b)
    (hzero : isZero base = false) (negativeExponent : Bool) (magnitude shift : Nat)
    (hfinite :
      isFinite (integerPowerWith exactBudget base b negativeExponent magnitude shift) = true) :
    toReal (integerPowerWith exactBudget base b negativeExponent magnitude shift) =
      roundAt fmt (toReal base ^ integralValue negativeExponent magnitude shift) := by
  have hbase : isFinite base = true := isFinite_eq_true_of_toDyadic?_some hb
  have hreal : toReal base = b.toReal := by rw [toReal_eq, hb]
  have hexact :
      isFinite (powInt base (integralValue negativeExponent magnitude shift)) = true →
      toReal (powInt base (integralValue negativeExponent magnitude shift)) =
        roundAt fmt (toReal base ^ integralValue negativeExponent magnitude shift) :=
    toReal_powInt_eq_roundAt base _ hfmt hbase hzero
  unfold integerPowerWith at hfinite ⊢
  dsimp only at hfinite ⊢
  split
  · rw [ite_eq_left ‹_›] at hfinite
    exact hexact hfinite
  · rw [ite_eq_right ‹_›] at hfinite
    split
    · rename_i hunit
      rw [ite_eq_left hunit] at hfinite
      rw [toReal_roundAlgebraicRat fmt hfmt _ hfinite, hreal,
        zpow_integralValue_eq_attemptTarget]
      simp only [Bool.and_eq_true, beq_iff_eq] at hunit
      obtain ⟨hsig, hexp⟩ := hunit
      have hone : (((b.significand : Rat) * 2 ^ b.exponent : Rat)) = 1 := by
        have hsig' : (b.significand : Rat) = 2 ^ (Nat.log2 b.significand) := by
          rw [hsig]; simp [Nat.shiftLeft_eq]
        rw [hsig', ← zpow_natCast, ← zpow_add₀ (by norm_num), hexp, zpow_zero]
      unfold attemptTarget
      simp only [Endpoint.toRat, hone, one_pow, Rat.cast_one, inv_one, ite_self, mul_one]
      split <;> simp
    · rw [ite_eq_right ‹_›] at hfinite
      split
      · rename_i result hsome
        rw [hsome] at hfinite
        obtain ⟨precision, _, hattempt⟩ := List.exists_of_findSome?_eq_some hsome
        rw [toReal_of_attempt hfmt hattempt hfinite, hreal,
          zpow_integralValue_eq_attemptTarget]
      · rename_i hnone
        rw [hnone] at hfinite
        exact hexact hfinite

/--
`integralParts?` finds the decomposition of every dyadic whose unsigned value is a natural
number `value`, and the parts recombine to that number.
-/
theorem integralParts?_of_eq_natCast (y : Numerics.Dyadic) (value : Nat)
    (h : (y.significand : ℝ) * (2 : ℝ) ^ y.exponent = value) :
    ∃ magnitude shift, integralParts? y = some (magnitude, shift) ∧
      magnitude <<< shift = value := by
  unfold integralParts?
  rcases hexp : y.exponent with shift | shift
  · refine ⟨y.significand, shift, rfl, ?_⟩
    rw [hexp, Int.ofNat_eq_natCast, zpow_natCast] at h
    rw [Nat.shiftLeft_eq]
    exact_mod_cast h
  · rw [hexp, zpow_negSucc] at h
    have hsig : y.significand = value * 2 ^ (shift + 1) := by
      have h2 : (y.significand : ℝ) = value * 2 ^ (shift + 1) := by
        rw [← h]; field_simp
      exact_mod_cast h2
    have hmag : y.significand >>> (shift + 1) = value := by
      rw [Nat.shiftRight_eq_div_pow, hsig, Nat.mul_div_cancel _ (by positivity)]
    refine ⟨value, 0, ?_, by simp⟩
    dsimp only
    rw [hmag, Nat.shiftLeft_eq, ← hsig]
    simp

/--
Main correctness theorem for integral exponents: when the base is finite and nonzero and the
exponent is a finite float with integer value `n`, every finite result of `pow` is the
nearest-even rounding of the real power `toReal base ^ n`.
-/
theorem toReal_pow_of_eq_intCast {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    {base exponent : Model fmt} {n : ℤ} (hbase : isFinite base = true)
    (hbzero : isZero base = false) (hexp : isFinite exponent = true)
    (hn : toReal exponent = n) (hfinite : isFinite (pow base exponent) = true) :
    toReal (pow base exponent) = roundAt fmt (toReal base ^ n) := by
  obtain ⟨b, hb⟩ := exists_toDyadic?_of_isFinite hbase
  obtain ⟨y, hy⟩ := exists_toDyadic?_of_isFinite hexp
  have hone_finite : isFinite (posOne fmt) = true := isFinite_eq_true_of_toDyadic?_some
    (Classical.choose_spec (exists_toDyadic?_of_isFinite (isFinite_posOne fmt)))
  have hroundOne : roundAt fmt 1 = 1 := by
    simpa using roundAt_toReal_eq (posOne fmt) hone_finite
  have hbne : toReal base ≠ 0 := by
    rw [toReal_eq, hb]
    have hsig : b.significand ≠ 0 := by
      have := isZero_eq_beq_zero_of_toDyadic?_some hb
      rw [hbzero] at this
      simpa using this.symm
    simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand]
    have : (b.significand : ℝ) ≠ 0 := by exact_mod_cast hsig
    split <;> simp [this, zpow_ne_zero]
  unfold pow at hfinite ⊢
  by_cases hz : isZero exponent = true
  · rw [ite_eq_left hz]
    have : (n : ℝ) = 0 := by rw [← hn]; exact toReal_eq_zero_of_isZero exponent hz
    have hn0 : n = 0 := by exact_mod_cast this
    simp [hn0, hroundOne]
  rw [ite_eq_right hz] at hfinite ⊢
  by_cases hunit : (compare base (posOne fmt) = some .eq && !isSNaN exponent) = true
  · rw [ite_eq_left hunit]
    simp only [Bool.and_eq_true] at hunit
    have h1 : toReal base = 1 := by
      simpa using (compare_eq_some_eq_iff_toReal_eq_of_isFinite base (posOne fmt) hbase
        hone_finite).mp (of_decide_eq_true hunit.1)
    simp [h1, hroundOne]
  rw [ite_eq_right hunit] at hfinite ⊢
  rw [chooseNaN2_none_of_isFinite base exponent hbase hexp] at hfinite ⊢
  dsimp only at hfinite ⊢
  by_cases hexp1 : compare exponent (posOne fmt) = some .eq
  · rw [ite_eq_left hexp1]
    have : (n : ℝ) = 1 := by
      rw [← hn]
      simpa using (compare_eq_some_eq_iff_toReal_eq_of_isFinite exponent (posOne fmt) hexp
        hone_finite).mp hexp1
    have hn1 : n = 1 := by exact_mod_cast this
    rw [hn1, zpow_one, roundAt_toReal_eq base hbase]
  rw [ite_eq_right hexp1] at hfinite ⊢
  have hinf : isInf exponent = false := isInf_eq_false_of_isFinite_eq_true exponent hexp
  rw [ite_eq_right (by simp [hinf])] at hfinite ⊢
  have hbaseZero : compare base (zero fmt false) ≠ some .eq := by
    intro h
    exact hbne (by simpa using (compare_eq_some_eq_iff_toReal_eq_of_isFinite base
      (zero fmt false) hbase
      (isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt false))).mp h)
  have hbinf : isInf base = false := isInf_eq_false_of_isFinite_eq_true base hbase
  -- The exponent's unsigned value is the natural number `n.natAbs`.
  have hyreal : y.toReal = n := by rw [← hn, toReal_eq, hy]
  have habs : (y.significand : ℝ) * (2 : ℝ) ^ y.exponent = (n.natAbs : ℝ) := by
    have h := congrArg (fun r : ℝ => |r|) hyreal
    simp only [Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand, abs_mul] at h
    rw [Nat.cast_natAbs, Int.cast_abs, ← h]
    have : |(if y.negative = true then (-1 : ℝ) else 1)| = 1 := by split <;> simp
    rw [this, one_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  obtain ⟨magnitude, shift, hparts, hvalue⟩ := integralParts?_of_eq_natCast y _ habs
  have hint : integralValue y.negative magnitude shift = n := by
    have hsign : (n : ℝ) = (if y.negative then -1 else 1) * (n.natAbs : ℝ) := by
      rw [← hyreal, ← habs]
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand]
    unfold integralValue
    rw [hvalue]
    have : (n : ℝ) = ((if y.negative then -(n.natAbs : ℤ) else (n.natAbs : ℤ) : ℤ) : ℝ) := by
      rw [hsign]; split <;> simp
    exact_mod_cast this.symm
  have hpower : integerPower? base exponent =
      some (integerPowerWith exactBitBudget base b y.negative magnitude shift) := by
    simp [integerPower?, hb, hy, hparts]
  rcases hc : compare base (zero fmt false) with _ | ⟨_ | _ | _⟩ <;>
    simp only [hc] at hfinite ⊢
  all_goals first
    | exact absurd hc hbaseZero
    | rw [hbinf, ite_eq_right Bool.false_ne_true] at hfinite ⊢
      rw [hpower] at hfinite ⊢
      dsimp only at hfinite ⊢
      rw [toReal_integerPowerWith hfmt exactBitBudget hb hbzero y.negative magnitude shift
        hfinite, hint]

end FloatLib.Floats.Formats.BinaryInterchange.Model.Power
