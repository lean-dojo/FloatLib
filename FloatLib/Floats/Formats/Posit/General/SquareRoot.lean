/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.General.Quotient
public import FloatLib.Numerics.Kernel.RootProof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Posits with any number of exponent bits: the square root

A FloatLib extension beyond the Posit Standard (2022), which fixes `es = 2`. A square root is in
general not rational, so its rounding is stated on squares, with rational numbers only:

* `IsRoundedSqrt p es x c`: `c` is the magnitude code that the rounding rule of the Posit
  Standard (2022), §4.1, assigns to the square root of the positive rational `x`. It is
  `IsRounded` with every comparison `v ≤ √x` written `v ^ 2 ≤ x`.
  `IsRoundedSqrt.unique`: at most one code satisfies it, and `isRoundedSqrt_sq`: for a rational
  root it is the rounding of the root.
* `sameSideSqrt_jam`: the integer square root of `S` with a nonzero remainder recorded in its
  low bit is on the same side of every rounding boundary as the exact root of `S`.
* `sqrt_isRoundedSqrt`: `KernelPath.sqrt` on a positive encoding returns the rounding of the
  square root of its value, for every number `p ≥ 1` of payload bits and every number `es` of
  exponent bits (Posit Standard (2022), §5.5 and §4.1 with `2 ^ es` in place of `4`).
  `sqrt_nar`, `sqrt_zero`: NaR and every negative encoding give NaR, and zero gives zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.General

open FloatLib.Numerics.Kernel FloatLib.Floats.Formats.Posit.KernelPath

/-! ## The rounding of a square root, on squares -/

/--
The rounding rule of the Posit Standard (2022), §4.1, with `es` exponent bits, applied to the
square root of the positive rational `x` and stated on squares: `c` is a positive magnitude
code; a root at or below the least positive value has the least code and one at or above the
greatest value the greatest code; any other root lies between the values, in the format with
one more payload bit, of the codes `2 * c - 1` and `2 * c + 1`, and `c` is even when the root is
one of these two.
-/
structure IsRoundedSqrt (p es : ℕ) (x : ℚ) (c : ℕ) : Prop where
  /-- The code is not zero. -/
  pos : 0 < c
  /-- The code is below the sign bit. -/
  lt : c < 2 ^ p
  /-- A root at or below the least positive value has the least code. -/
  low : x ≤ value p es 1 ^ 2 → c = 1
  /-- A root at or above the greatest value has the greatest code. -/
  high : value p es (2 ^ p - 1) ^ 2 ≤ x → c = 2 ^ p - 1
  /-- Any other root lies between the two midpoints next to its code, with ties to the even
  code. -/
  between : value p es 1 ^ 2 < x → x < value p es (2 ^ p - 1) ^ 2 →
    value (p + 1) es (2 * c - 1) ^ 2 ≤ x ∧ x ≤ value (p + 1) es (2 * c + 1) ^ 2 ∧
      (x = value (p + 1) es (2 * c - 1) ^ 2 ∨ x = value (p + 1) es (2 * c + 1) ^ 2 → Even c)

/-- Two codes of one root under the rule cannot be in increasing order. -/
private theorem IsRoundedSqrt.not_lt {p es : ℕ} {x : ℚ} {c c' : ℕ}
    (h : IsRoundedSqrt p es x c) (h' : IsRoundedSqrt p es x c') (hlo : value p es 1 ^ 2 < x)
    (hhi : x < value p es (2 ^ p - 1) ^ 2) : ¬c < c' := by
  intro hlt
  obtain ⟨-, h2, h3⟩ := h.between hlo hhi
  obtain ⟨h1', -, h3'⟩ := h'.between hlo hhi
  have := h.pos
  have := h'.lt
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  have hv1 := (value_pos (p + 1) es (2 * c + 1)).le
  have hv2 := (value_pos (p + 1) es (2 * c' - 1)).le
  have hle : value (p + 1) es (2 * c + 1) ^ 2 ≤ value (p + 1) es (2 * c' - 1) ^ 2 :=
    pow_le_pow_left₀ hv1
      ((value_le_value_iff (Nat.succ_pos p) (by omega) (by omega) (by omega) (by omega)).mpr
        (by omega)) 2
  have hx1 : x = value (p + 1) es (2 * c + 1) ^ 2 := le_antisymm h2 (hle.trans h1')
  have hx2 : x = value (p + 1) es (2 * c' - 1) ^ 2 := le_antisymm (h2.trans hle) h1'
  have : 2 * c + 1 = 2 * c' - 1 :=
    value_injective (Nat.succ_pos p) (by omega) (by omega) (by omega) (by omega)
      ((sq_eq_sq₀ hv1 hv2).mp (hx1.symm.trans hx2))
  have he : Even c := h3 (Or.inr hx1)
  have he' : Even c' := h3' (Or.inl hx2)
  have hcc : c' = c + 1 := by omega
  rw [hcc, Nat.even_add_one] at he'
  exact he' he

/-- The rounding rule assigns at most one code to a square root. -/
theorem IsRoundedSqrt.unique {p es : ℕ} {x : ℚ} {c c' : ℕ} (h : IsRoundedSqrt p es x c)
    (h' : IsRoundedSqrt p es x c') : c = c' := by
  by_cases hlo : x ≤ value p es 1 ^ 2
  · rw [h.low hlo, h'.low hlo]
  by_cases hhi : value p es (2 ^ p - 1) ^ 2 ≤ x
  · rw [h.high hhi, h'.high hhi]
  rcases Nat.lt_trichotomy c c' with hlt | heq | hgt
  · exact absurd hlt (h.not_lt h' (not_le.mp hlo) (not_le.mp hhi))
  · exact heq
  · exact absurd hgt (h'.not_lt h (not_le.mp hlo) (not_le.mp hhi))

/-- `X` compares with the square of every value of the format with one more payload bit as `x'`
compares with the value: `x'` is on the same side of every boundary as the square root of
`X`. -/
def SameSideSqrt (p es : ℕ) (X x' : ℚ) : Prop :=
  ∀ n, 0 < n → n < 2 ^ (p + 1) →
    (X < value (p + 1) es n ^ 2 ↔ x' < value (p + 1) es n) ∧
      (X = value (p + 1) es n ^ 2 ↔ x' = value (p + 1) es n)

/-- A number on the same side of every boundary as a square root has the rounding of that
root. -/
theorem IsRounded.sqrt_of_sameSide {p es : ℕ} {X x' : ℚ} {c : ℕ} (hp : 0 < p)
    (hs : SameSideSqrt p es X x') (h : IsRounded p es x' c) : IsRoundedSqrt p es X c := by
  have : 2 ≤ 2 ^ p := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hp
    simpa using this
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  have hmin : value p es 1 = value (p + 1) es 2 :=
    (value_succ (es := es) hp Nat.one_pos (by omega)).symm
  have hmax : value p es (2 ^ p - 1) = value (p + 1) es (2 * (2 ^ p - 1)) :=
    (value_succ (es := es) hp (by omega) (by omega)).symm
  have := h.pos
  have := h.lt
  have hle : ∀ n, 0 < n → n < 2 ^ (p + 1) →
      (X ≤ value (p + 1) es n ^ 2 ↔ x' ≤ value (p + 1) es n) := fun n hn0 hn => by
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq, (hs n hn0 hn).1, (hs n hn0 hn).2]
  refine ⟨h.pos, h.lt, fun hlo => h.low ?_, fun hhi => h.high ?_, fun hlo hhi => ?_⟩
  · rw [hmin] at hlo ⊢
    exact (hle _ (by omega) (by omega)).mp hlo
  · rw [hmax] at hhi ⊢
    exact not_lt.mp (mt (hs _ (by omega) (by omega)).1.mpr (not_lt.mpr hhi))
  · have hlo' : value p es 1 < x' := by
      rw [hmin] at hlo ⊢
      exact not_le.mp (mt (hle _ (by omega) (by omega)).mpr (not_le.mpr hlo))
    have hhi' : x' < value p es (2 ^ p - 1) := by
      rw [hmax] at hhi ⊢
      exact (hs _ (by omega) (by omega)).1.mp hhi
    obtain ⟨h1, h2, h3⟩ := h.between hlo' hhi'
    refine ⟨?_, (hle _ (by omega) (by omega)).mpr h2, fun hx => h3 ?_⟩
    · exact not_lt.mp (mt (hs _ (by omega) (by omega)).1.mp (not_lt.mpr h1))
    · rcases hx with hx | hx
      · exact Or.inl ((hs _ (by omega) (by omega)).2.mp hx)
      · exact Or.inr ((hs _ (by omega) (by omega)).2.mp hx)

/-- For a rational root, the rounding of the square root is the rounding of the root. -/
theorem isRoundedSqrt_sq {p es : ℕ} {r : ℚ} {c : ℕ} (hp : 0 < p) (hr : 0 < r)
    (h : IsRounded p es r c) : IsRoundedSqrt p es (r ^ 2) c :=
  h.sqrt_of_sameSide hp fun n _ _ =>
    ⟨sq_lt_sq₀ hr.le (value_pos (p + 1) es n).le, sq_eq_sq₀ hr.le (value_pos (p + 1) es n).le⟩

/-! ## The integer square root with its remainder -/

/--
The integer square root of `S` with a nonzero remainder recorded in its low bit, at the unit
`2 ^ e`, is on the same side of every rounding boundary as the square root of
`S * (2 ^ e) ^ 2`, when the root has at least `p + 1` bits.
-/
theorem sameSideSqrt_jam {p es S : ℕ} (hp : 0 < p) (hroot : 2 ^ p ≤ Nat.sqrt S) (e : ℤ) :
    SameSideSqrt p es ((S : ℚ) * (2 ^ e) ^ 2)
      (((jam (Nat.sqrt S) (S - Nat.sqrt S * Nat.sqrt S) : ℕ) : ℚ) * 2 ^ e) := by
  intro n hn0 hn
  have hu : (0 : ℚ) < 2 ^ e := zpow_pos two_pos e
  have hr1 : Nat.sqrt S * Nat.sqrt S ≤ S := Nat.sqrt_le S
  have hr2 : S < (Nat.sqrt S + 1) * (Nat.sqrt S + 1) := Nat.lt_succ_sqrt S
  have hr0 : Nat.sqrt S ≠ 0 := by
    have := Nat.two_pow_pos p
    omega
  have hL1 : 2 ^ (Nat.sqrt S).log2 ≤ Nat.sqrt S := Nat.log2_self_le hr0
  have hL2 : Nat.sqrt S < 2 ^ ((Nat.sqrt S).log2 + 1) := Nat.lt_log2_self
  have hLp : p ≤ (Nat.sqrt S).log2 :=
    Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by decide)).mp (lt_of_le_of_lt hroot hL2))
  have hsqrt : ∀ w : ℕ, S < w * w ↔ Nat.sqrt S < w := fun w => Nat.sqrt_lt.symm
  have hsqrteq : ∀ w : ℕ, S = w * w → Nat.sqrt S = w := fun w h => by
    rw [h]
    exact Nat.sqrt_eq w
  generalize (Nat.sqrt S).log2 = L at hL1 hL2 hLp
  have hJ := jam_eq_ite (Nat.sqrt S) (S - Nat.sqrt S * Nat.sqrt S)
  rw [FloatLib.Numerics.or_one_eq] at hJ
  generalize jam (Nat.sqrt S) (S - Nat.sqrt S * Nat.sqrt S) = J at hJ
  generalize Nat.sqrt S = r at hr1 hr2 hL1 hL2 hsqrt hsqrteq hJ
  have hJle : r ≤ J := by
    rw [hJ]
    split_ifs <;> omega
  have : J ≤ r + 1 := by
    rw [hJ]
    split_ifs <;> omega
  have hJodd : S - r * r ≠ 0 → J % 2 = 1 := fun h => by
    rw [hJ, ite_eq_right h]
    split_ifs <;> omega
  have hJexact : S - r * r = 0 → J = r := fun h => by rw [hJ, ite_eq_left h]
  have hv0 := value_pos (p + 1) es n
  have heven : ∀ t : ℤ, (2 : ℚ) ^ t ≤ value (p + 1) es n → value (p + 1) es n < 2 ^ (t + 1) →
      ∃ k : ℕ, value (p + 1) es n = ((2 * k : ℕ) : ℚ) * 2 ^ (t - (p : ℤ)) :=
    fun t h1 h2 => value_succ_even hp hn0 hn h1 h2
  generalize value (p + 1) es n = v at hv0 heven ⊢
  have hLq : ((2 : ℚ) ^ L) ≤ (r : ℚ) := by exact_mod_cast hL1
  have hLq2 : (r : ℚ) + 1 ≤ 2 ^ (L + 1) := by exact_mod_cast hL2
  have hSq1 : (r : ℚ) ^ 2 ≤ (S : ℚ) := by
    have : ((r * r : ℕ) : ℚ) ≤ (S : ℚ) := by exact_mod_cast hr1
    rw [sq]
    exact_mod_cast this
  have hSq2 : (S : ℚ) < ((r : ℚ) + 1) ^ 2 := by
    have : (S : ℚ) < (((r + 1) * (r + 1) : ℕ) : ℚ) := by exact_mod_cast hr2
    rw [sq]
    exact_mod_cast this
  have hsqu : ∀ a : ℚ, a ^ 2 * (2 ^ e) ^ 2 = (a * 2 ^ e) ^ 2 := fun a => by ring
  rcases lt_or_ge v ((2 : ℚ) ^ ((L : ℤ) + e)) with hlow | hge
  · -- the value is below the root and below its truncation
    have hB : (2 : ℚ) ^ ((L : ℤ) + e) = 2 ^ L * 2 ^ e := by
      rw [zpow_add₀ two_ne_zero, zpow_natCast]
    rw [hB] at hlow
    have hru : v < (r : ℚ) * 2 ^ e := hlow.trans_le (mul_le_mul_of_nonneg_right hLq hu.le)
    have hX : v ^ 2 < (S : ℚ) * (2 ^ e) ^ 2 :=
      calc v ^ 2 < ((r : ℚ) * 2 ^ e) ^ 2 := pow_lt_pow_left₀ hru hv0.le two_ne_zero
        _ = (r : ℚ) ^ 2 * (2 ^ e) ^ 2 := (hsqu _).symm
        _ ≤ (S : ℚ) * (2 ^ e) ^ 2 := mul_le_mul_of_nonneg_right hSq1 (sq_nonneg _)
    have hx' : v < (J : ℚ) * 2 ^ e :=
      hru.trans_le (mul_le_mul_of_nonneg_right (by exact_mod_cast hJle) hu.le)
    exact ⟨iff_of_false (not_lt.mpr hX.le) (not_lt.mpr hx'.le), iff_of_false hX.ne' hx'.ne'⟩
  rcases le_or_gt ((2 : ℚ) ^ ((L : ℤ) + e + 1)) v with hhigh | hlt
  · -- the value is above the root and above its truncation
    have hB : (2 : ℚ) ^ ((L : ℤ) + e + 1) = 2 ^ (L + 1) * 2 ^ e := by
      rw [show (L : ℤ) + e + 1 = ((L + 1 : ℕ) : ℤ) + e by push_cast; ring,
        zpow_add₀ two_ne_zero, zpow_natCast]
    rw [hB] at hhigh
    have hru : ((r : ℚ) + 1) * 2 ^ e ≤ v :=
      (mul_le_mul_of_nonneg_right hLq2 hu.le).trans hhigh
    have hX : (S : ℚ) * (2 ^ e) ^ 2 < v ^ 2 :=
      calc (S : ℚ) * (2 ^ e) ^ 2 < ((r : ℚ) + 1) ^ 2 * (2 ^ e) ^ 2 :=
            mul_lt_mul_of_pos_right hSq2 (by positivity)
        _ = (((r : ℚ) + 1) * 2 ^ e) ^ 2 := hsqu _
        _ ≤ v ^ 2 := pow_le_pow_left₀ (by positivity) hru 2
    have hJlt : J < 2 ^ (L + 1) := by
      have h2 : 2 ^ (L + 1) % 2 = 0 := by
        rw [pow_succ]
        omega
      by_cases hrem : S - r * r = 0
      · rw [hJexact hrem]
        exact hL2
      · have := hJodd hrem
        omega
    have hx' : (J : ℚ) * 2 ^ e < v :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_right (by exact_mod_cast hJlt) hu) hhigh
    exact ⟨iff_of_true hX hx', iff_of_false hX.ne hx'.ne⟩
  · -- inside the binade the value is an even multiple of the unit
    obtain ⟨k, hk⟩ := heven _ hge hlt
    have hexp : (2 : ℚ) ^ ((L : ℤ) + e - (p : ℤ)) = 2 ^ (L - p) * 2 ^ e := by
      rw [show (L : ℤ) + e - (p : ℤ) = ((L - p : ℕ) : ℤ) + e by omega, zpow_add₀ two_ne_zero,
        zpow_natCast]
    have hvw : v = ((2 * k * 2 ^ (L - p) : ℕ) : ℚ) * 2 ^ e := by
      rw [hk, hexp]
      push_cast
      ring
    have hweven : (2 * k * 2 ^ (L - p)) % 2 = 0 := by
      rw [Nat.mul_assoc]
      exact Nat.mul_mod_right 2 _
    generalize 2 * k * 2 ^ (L - p) = w at hvw hweven
    have hu2 : (0 : ℚ) < (2 ^ e) ^ 2 := by positivity
    have hXlt : (S : ℚ) * (2 ^ e) ^ 2 < v ^ 2 ↔ S < w * w := by
      rw [hvw, ← hsqu]
      constructor
      · intro h
        have h' := lt_of_mul_lt_mul_right h hu2.le
        have : (S : ℚ) < ((w * w : ℕ) : ℚ) := by
          push_cast
          rwa [sq] at h'
        exact_mod_cast this
      · intro h
        have : (S : ℚ) < (w : ℚ) ^ 2 := by
          rw [sq]
          exact_mod_cast h
        exact mul_lt_mul_of_pos_right this hu2
    have hXeq : (S : ℚ) * (2 ^ e) ^ 2 = v ^ 2 ↔ S = w * w := by
      rw [hvw, ← hsqu]
      constructor
      · intro h
        have h' := mul_right_cancel₀ hu2.ne' h
        have : (S : ℚ) = ((w * w : ℕ) : ℚ) := by
          push_cast
          rwa [sq] at h'
        exact_mod_cast this
      · intro h
        rw [h]
        push_cast
        ring
    have hxlt : (J : ℚ) * 2 ^ e < v ↔ J < w := by
      rw [hvw]
      exact ⟨fun h => by exact_mod_cast lt_of_mul_lt_mul_right h hu.le,
        fun h => mul_lt_mul_of_pos_right (by exact_mod_cast h) hu⟩
    have hxeq : (J : ℚ) * 2 ^ e = v ↔ J = w := by
      rw [hvw]
      exact ⟨fun h => by exact_mod_cast mul_right_cancel₀ hu.ne' h, fun h => by rw [h]⟩
    rw [hXlt, hXeq, hxlt, hxeq, hsqrt]
    by_cases hrem : S - r * r = 0
    · have hJr := hJexact hrem
      have hS : S = r * r := by omega
      refine ⟨by rw [hJr], ?_⟩
      rw [hJr, hS]
      exact ⟨fun h => Nat.mul_self_inj.mp h, fun h => by rw [h]⟩
    · have hodd := hJodd hrem
      refine ⟨by omega, iff_of_false (fun h => ?_) (by omega)⟩
      have := hsqrteq w h
      rw [h, ← this] at hrem
      exact hrem (Nat.sub_self _)

/-! ## The square root of an encoding -/

/-- The square root of NaR and of every negative encoding is NaR. -/
theorem sqrt_nar {p a : ℕ} (es : ℕ) (h : 2 ^ p ≤ a) : sqrt p es a = 2 ^ p := by
  unfold sqrt nar
  kernel_notation
  rw [ite_eq_left h]

/-- The square root of zero is zero. -/
theorem sqrt_zero (p es : ℕ) : sqrt p es 0 = 0 := by
  unfold sqrt nar
  kernel_notation
  rw [ite_eq_right (Nat.not_le.mpr (Nat.two_pow_pos p)), ite_eq_left trivial]

/--
Posit Standard (2022), §5.5 and §4.1, for every number of exponent bits: `sqrt` on a positive
encoding returns the rounding of the square root of its value, stated on squares.
-/
theorem sqrt_isRoundedSqrt {p es a : ℕ} (hp : 0 < p) (ha0 : 0 < a) (ha : a < 2 ^ p) :
    IsRoundedSqrt p es (value p es a) (sqrt p es a) := by
  have hv := value_eq_fields (es := es) hp ha0 ha
  have hsig := significand_ne_zero es a (tailLength p a)
  have hb : bias p es = 2 * (4 * (p + 1) * 2 ^ es) := by
    rw [bias_eq_mul]
    ring
  have hh : p ≤ 4 * (p + 1) * 2 ^ es := by
    have := Nat.le_mul_of_pos_right (4 * (p + 1)) (Nat.two_pow_pos es)
    omega
  have hbc := bias_cast p es
  generalize 4 * (p + 1) * 2 ^ es = H at hb hh
  unfold sqrt nar
  kernel_notation
  rw [ite_eq_right (Nat.not_le.mpr ha), ite_eq_right ha0.ne', isqrt_eq, Nat.and_one_is_mod,
    pow_one]
  generalize significand es a (tailLength p a) = sig at hv hsig ⊢
  generalize exponent p es a (tailLength p a) = e at hv ⊢
  have hroot : 2 ^ p ≤ Nat.sqrt (sig * 2 ^ (e % 2 + 2 * p)) := by
    rw [Nat.le_sqrt, ← pow_add]
    calc 2 ^ (p + p) ≤ 1 * 2 ^ (e % 2 + 2 * p) := by
          rw [Nat.one_mul]
          exact Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ sig * 2 ^ (e % 2 + 2 * p) := Nat.mul_le_mul_right _ (Nat.pos_of_ne_zero hsig)
  have hJ0 : jam (Nat.sqrt (sig * 2 ^ (e % 2 + 2 * p)))
      (sig * 2 ^ (e % 2 + 2 * p) - Nat.sqrt (sig * 2 ^ (e % 2 + 2 * p)) *
        Nat.sqrt (sig * 2 ^ (e % 2 + 2 * p))) ≠ 0 := by
    have := Nat.two_pow_pos p
    rw [jam_eq_ite, FloatLib.Numerics.or_one_eq]
    split_ifs <;> omega
  have henc := encode_isRounded (es := es) (bK := regimeBias p)
    (E := e / 2 + bias p es / 2 - p) hp hJ0
  have hs := sameSideSqrt_jam (es := es) hp hroot
    (((e / 2 + bias p es / 2 - p : ℕ) : ℤ) - ((regimeBias p : ℕ) : ℤ) * 2 ^ es)
  have hX : value p es a = ((sig * 2 ^ (e % 2 + 2 * p) : ℕ) : ℚ) *
      (2 ^ (((e / 2 + bias p es / 2 - p : ℕ) : ℤ) - ((regimeBias p : ℕ) : ℤ) * 2 ^ es)) ^ 2 := by
    generalize hg : ((e / 2 + bias p es / 2 - p : ℕ) : ℤ) -
      ((regimeBias p : ℕ) : ℤ) * 2 ^ es = g
    have hsq : ((2 : ℚ) ^ g) ^ 2 = 2 ^ (g * ((2 : ℕ) : ℤ)) := by
      rw [← zpow_natCast ((2 : ℚ) ^ g) 2, ← zpow_mul]
    rw [hv, hsq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      ← zpow_natCast (2 : ℚ) (e % 2 + 2 * p), mul_assoc, ← zpow_add₀ two_ne_zero]
    congr 2
    rw [← hg, ← hbc, hb, Nat.mul_div_cancel_left H (by decide : 0 < 2)]
    push_cast
    omega
  rw [hX]
  exact henc.sqrt_of_sameSide hp hs

end FloatLib.Floats.Formats.Posit.General
