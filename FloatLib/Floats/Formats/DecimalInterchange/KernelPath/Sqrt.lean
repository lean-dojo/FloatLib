/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Quantum
public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Runtime
public import FloatLib.Numerics.Kernel.RootShape
public import FloatLib.Numerics.Kernel.RootProof

/-!
# Kernel path of the decimal square root, reciprocal square root and hypotenuse

`Arithmetic.sqrt` (IEEE 754-2019 §5.4.1) is specified on rational numbers: the radicand is put
on a grid by a rational quotient, an integer square root brackets the root, and comparisons of
rational squares decide the rounding, the `inexact` flag and the tininess.

`sqrtRatio` computes the same outcome for a radicand `(num / den) × 10 ^ (2 × minQuantum)`, a
ratio of natural numbers on the square of the least quantum: the number of digits of the
integer part of the ratio gives the rounding quantum, `Numerics.Kernel.isqrt` the integer
square root of the ratio at the square of that quantum, and comparisons of natural numbers the
increment (`sqrtIncrement`), the `inexact` flag and the tininess. `sqrtRatio_eq` proves it equal
to `sqrtMagnitude` for every format, rounding direction, numerator, nonzero denominator and
preferred exponent.

`sqrtScaled` is `sqrtRatio` of a numerator times a power of ten, given by its exponent
(`sqrtScaled_eq`). The square of the least quantum puts a radicand eight hundred digits up in
decimal64 and twelve thousand in decimal128, and all but the last few of those digits only move
the rounding quantum of the root: `sqrtScaled` keeps the powers of ten that give the radicand
twice the precision less one digits and adds half of the rest to the quantum (`sqrtCancelled`),
so the integer square root is taken of a number of about twice the precision.

Three operations are built on it, each tagged `@[kernel_optimize]` and proved equal to its
specification for every format, rounding direction and datum:

* `sqrt` (`sqrt_eq`), the kernel form of `Arithmetic.sqrt`: the coefficient of a positive
  finite datum at its exponent is such a ratio.
* `rSqrt` (`rSqrt_eq`), the kernel form of `Arithmetic.rSqrt` (§9.2): the reciprocal of a
  positive finite datum is such a ratio.
* `hypot` (`hypot_eq`), the kernel form of `Arithmetic.hypot` (§9.2): the exact sum of the
  squares of two finite data is such a ratio.

A zero and a negative operand of `sqrt` and `rSqrt`, an infinity and a NaN are left to the
specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

open FloatLib.Numerics
open FloatLib.Numerics.Kernel (isqrt isqrt_eq)

/--
The amount, zero or one, by which the integer square root `lower` of `n / scale` is incremented
when the root is rounded in `mode` (`sqrtIncrement_eq`): to nearest by comparing the square of
the midpoint with the radicand, with the parity of `lower` at a tie, and toward positive
infinity when the root is not exact.
-/
def sqrtIncrement (mode : RoundingMode) (lower n scale : Nat) : Nat :=
  (fun midpoint =>
    RoundingMode.casesOn (motive := fun _ => Nat) mode
      (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ midpoint) (Nat.mul 4 n))
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq midpoint (Nat.mul 4 n)) 0
          (Nat.mod lower 2))
        1)
      (flag (Nat.ble midpoint (Nat.mul 4 n)))
      0
      (flag (Nat.ble (Nat.succ (Nat.mul (Nat.pow lower 2) scale)) n))
      0)
    (Nat.mul (Nat.pow (Nat.succ (Nat.mul 2 lower)) 2) scale)

/-- `sqrtIncrement` decides the increment of the specification on natural numbers. -/
theorem sqrtIncrement_eq (mode : RoundingMode) (lower n : Nat) {scale : Nat}
    (hscale : 0 < scale) :
    (if mode.sqrtIncrement lower ((n : ℚ) / (scale : ℚ)) then lower + 1 else lower) =
      lower + sqrtIncrement mode lower n scale := by
  have hS : (0 : ℚ) < (scale : ℚ) := Nat.cast_pos.2 hscale
  have hlt : (2 * (lower : ℚ) + 1) ^ 2 < 4 * ((n : ℚ) / (scale : ℚ)) ↔
      (2 * lower + 1) ^ 2 * scale < 4 * n := by
    rw [← mul_div_assoc, lt_div_iff₀ hS]
    norm_cast
  have heq : (2 * (lower : ℚ) + 1) ^ 2 = 4 * ((n : ℚ) / (scale : ℚ)) ↔
      (2 * lower + 1) ^ 2 * scale = 4 * n := by
    rw [← mul_div_assoc, eq_div_iff hS.ne']
    norm_cast
  have hle : (2 * (lower : ℚ) + 1) ^ 2 ≤ 4 * ((n : ℚ) / (scale : ℚ)) ↔
      (2 * lower + 1) ^ 2 * scale ≤ 4 * n := by
    rw [← mul_div_assoc, le_div_iff₀ hS]
    norm_cast
  have hup : (lower : ℚ) ^ 2 < (n : ℚ) / (scale : ℚ) ↔ lower ^ 2 * scale < n := by
    rw [lt_div_iff₀ hS]
    norm_cast
  have hmodf : ∀ m k : Nat, Nat.mod m k = m % k := fun _ _ => rfl
  cases mode <;>
    simp only [RoundingMode.sqrtIncrement, sqrtIncrement, flag_eq, hlt, heq, hle, hup, natBle_eq,
      natBeq_eq, hmodf, casesOn_decide, decide_eq_true_eq, Nat.mul_eq, Nat.pow_eq,
      Nat.succ_eq_add_one, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] <;>
    split_ifs <;> omega

/--
The outcome of the square root of the radicand `(num / den) × 10 ^ (2 × minQuantum)` rounded
into `f`, with `preferred` as the preferred exponent of an exact result (`sqrtRatio_eq`).
-/
def sqrtRatio (f : Format) (mode : RoundingMode) (num den : Nat) (preferred : Int) : Outcome :=
  (fun shift =>
    (fun scale =>
      (fun lower =>
        (fun rounded =>
          deliverRounded f mode false rounded shift
            (Bool.not (Nat.beq (Nat.mul (Nat.pow rounded 2) scale) num))
            (Nat.ble (Nat.succ num) (Nat.mul den (Nat.pow 100 (Nat.mul 3 f.declets))))
            preferred)
          (Nat.add lower (sqrtIncrement mode lower num scale)))
        (isqrt (Nat.div num scale)))
      (Nat.mul den (Nat.pow 100 shift)))
    (Nat.sub (Nat.succ (Nat.div (Nat.pred (decimalLength (Nat.div num den))) 2))
      (Nat.succ (Nat.mul 3 f.declets)))

/--
`sqrtRatio` is the specified square root of the radicand `(num / den) × 10 ^ (2 × minQuantum)`:
the same datum and the same flags, for every format, rounding direction, numerator, nonzero
denominator and preferred exponent.
-/
theorem sqrtRatio_eq (f : Format) (mode : RoundingMode) (num : Nat) {den : Nat}
    (hden : den ≠ 0) (preferred : Int) :
    sqrtRatio f mode num den preferred =
      sqrtMagnitude f mode ((num : ℚ) / (den : ℚ) * (10 : ℚ) ^ (2 * f.minQuantum))
        preferred := by
  have hten : (10 : ℚ) ≠ 0 := by norm_num
  have hdenq : (0 : ℚ) < (den : ℚ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hden)
  have hmin : (0 : ℚ) < (10 : ℚ) ^ (2 * f.minQuantum) := zpow_pos (by norm_num) _
  have hdivf : ∀ m k : Nat, Nat.div m k = m / k := fun _ _ => rfl
  have hprecision : 3 * f.declets + 1 = f.precision := rfl
  unfold sqrtRatio
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.pow_eq, Nat.succ_eq_add_one,
    Nat.pred_eq_sub_one, hdivf, decimalLength_eq_log, Nat.add_sub_cancel, hprecision, isqrt_eq]
  obtain ⟨r, hr⟩ : ∃ r : ℚ, r = (num : ℚ) / (den : ℚ) * (10 : ℚ) ^ (2 * f.minQuantum) :=
    ⟨_, rfl⟩
  rw [← hr]
  have hscaled : r / (10 : ℚ) ^ (2 * f.minQuantum) = (num : ℚ) / (den : ℚ) := by
    rw [hr, mul_div_assoc, div_self hmin.ne', mul_one]
  generalize hshift : Nat.log 10 (num / den) / 2 + 1 - f.precision = shift
  have hquantum : sqrtQuantum f r = (shift : Int) - f.bias := by
    rw [sqrtQuantum, hscaled, sqrtScaleShift, Rat.natFloor_natCast_div_natCast, hshift,
      Format.minQuantum]
    ring
  have hscale : 0 < den * 100 ^ shift := Nat.mul_pos (Nat.pos_of_ne_zero hden) (by positivity)
  have hpow : (10 : ℚ) ^ (2 * ((shift : Int) - f.bias)) =
      ((100 ^ shift : Nat) : ℚ) * (10 : ℚ) ^ (2 * f.minQuantum) := by
    have h100 : (10 : ℚ) ^ (2 * (shift : Int)) = ((100 ^ shift : Nat) : ℚ) := by
      rw [zpow_mul, show (10 : ℚ) ^ (2 : Int) = 100 by norm_num, zpow_natCast]
      norm_cast
    rw [Format.minQuantum, mul_sub, sub_eq_add_neg, zpow_add₀ hten, h100, mul_neg]
  have hvalue : r / (10 : ℚ) ^ (2 * ((shift : Int) - f.bias)) =
      (num : ℚ) / ((den * 100 ^ shift : Nat) : ℚ) := by
    rw [hpow, hr, mul_div_mul_right _ _ hmin.ne', div_div, Nat.cast_mul]
  have hround : mode.sqrtRound (r / (10 : ℚ) ^ (2 * ((shift : Int) - f.bias))) =
      Nat.sqrt (num / (den * 100 ^ shift)) +
        sqrtIncrement mode (Nat.sqrt (num / (den * 100 ^ shift))) num (den * 100 ^ shift) := by
    rw [RoundingMode.sqrtRound, hvalue, sqrtFloor, Rat.natFloor_natCast_div_natCast]
    exact sqrtIncrement_eq mode _ num hscale
  generalize 100 ^ shift = S at hscale hpow hvalue hround ⊢
  generalize hD : den * S = D at hscale hvalue hround ⊢
  generalize Nat.sqrt (num / D) + sqrtIncrement mode (Nat.sqrt (num / D)) num D = R
    at hround ⊢
  have hsquare : ((10 : ℚ) ^ ((shift : Int) - f.bias)) ^ 2 =
      (S : ℚ) * (10 : ℚ) ^ (2 * f.minQuantum) := by
    rw [pow_two, ← zpow_add₀ hten, ← two_mul, hpow]
  have hval : ((sqrtPair f mode r).1 : ℚ) * (10 : ℚ) ^ (sqrtPair f mode r).2 =
      (R : ℚ) * (10 : ℚ) ^ ((shift : Int) - f.bias) := by
    rw [← hround, ← hquantum]
    exact Numerics.RadixText.carry_value 10 (by decide) _ _ _
  have hinexact : decide ((((sqrtPair f mode r).1 : ℚ) * (10 : ℚ) ^ (sqrtPair f mode r).2) ^ 2 ≠
      r) = !Nat.beq (R ^ 2 * D) num := by
    have hcast : ((R : ℚ) ^ 2 * (S : ℚ) * (den : ℚ) = (num : ℚ)) ↔ R ^ 2 * D = num := by
      rw [← hD, Nat.mul_comm den S, ← Nat.mul_assoc]
      norm_cast
    rw [hval, mul_pow, hsquare, hr, ← mul_assoc, Bool.eq_iff_iff, decide_eq_true_eq, ne_eq,
      mul_left_inj' hmin.ne', eq_div_iff hdenq.ne', hcast, natBeq_eq]
    simp
  have htiny : decide (r < f.minNormal ^ 2) =
      Nat.ble (num + 1) (den * 100 ^ (3 * f.declets)) := by
    have hp : f.precision - 1 = 3 * f.declets := rfl
    have hnormal : f.minNormal ^ 2 =
        ((100 ^ (3 * f.declets) : Nat) : ℚ) * (10 : ℚ) ^ (2 * f.minQuantum) := by
      rw [Format.minNormal, mul_pow, hp, pow_two ((10 : ℚ) ^ f.minQuantum), ← zpow_add₀ hten,
        ← two_mul, ← pow_mul, mul_comm (3 * f.declets) 2, pow_mul]
      norm_num
    rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.ble_eq, hnormal, ← div_lt_iff₀ hmin, hscaled,
      div_lt_iff₀ hdenq, Nat.add_one_le_iff, Nat.mul_comm den]
    norm_cast
  have hpair : sqrtPair f mode r =
      if R = f.coefficientBound then (f.payloadBound, (shift : Int) - f.bias + 1)
      else (R, (shift : Int) - f.bias) := by
    rw [sqrtPair, hquantum, hround, f.carry_eq]
  rw [sqrtMagnitude]
  dsimp only
  rw [hinexact, htiny]
  exact deliverRounded_eq f mode false R shift _ _ preferred _ hpair

/-- A power of ten as the ratio of two powers of ten on the grid `10 ^ (2 × minQuantum)`. -/
theorem zpow_eq_ratio (f : Format) (e : Int) {a b : Nat}
    (hab : (a : Int) - (b : Int) = e + f.bias + f.bias) :
    (10 : ℚ) ^ e = (10 : ℚ) ^ a / (10 : ℚ) ^ b * (10 : ℚ) ^ (2 * f.minQuantum) := by
  have hten : (10 : ℚ) ≠ 0 := by norm_num
  rw [← zpow_natCast (10 : ℚ) a, ← zpow_natCast (10 : ℚ) b, ← zpow_sub₀ hten, ← zpow_add₀ hten]
  congr 1
  unfold Format.minQuantum
  omega

/--
`sqrtRatio f mode (scaled × 100 ^ cancelled) den preferred` for a radicand `scaled / den` of at
least twice the precision less one digits (`sqrtCancelled_eq`): the rounding quantum of the
root is then at least `10 ^ cancelled`, so that power is never formed.
-/
def sqrtCancelled (f : Format) (mode : RoundingMode) (scaled den cancelled : Nat)
    (preferred : Int) : Outcome :=
  (fun shift =>
    (fun scale =>
      (fun lower =>
        (fun rounded =>
          deliverRounded f mode false rounded (Nat.add shift cancelled)
            (Bool.not (Nat.beq (Nat.mul (Nat.pow rounded 2) scale) scaled)) false preferred)
          (Nat.add lower (sqrtIncrement mode lower scaled scale)))
        (isqrt (Nat.div scaled scale)))
      (Nat.mul den (Nat.pow 100 shift)))
    (Nat.sub (Nat.succ (Nat.div (Nat.pred (decimalLength (Nat.div scaled den))) 2))
      (Nat.succ (Nat.mul 3 f.declets)))

/--
`sqrtRatio f mode (num × 10 ^ scale) den preferred` (`sqrtScaled_eq`) without the power
`10 ^ scale` when it is large: `least` powers of ten (twice the precision less two, plus a bound
on the digits of the denominator), or one more for the parity of `scale`, give the radicand
twice the precision less one digits, and the other powers, an even number, only move the
rounding quantum of the root.
-/
def sqrtScaled (f : Format) (mode : RoundingMode) (num den scale : Nat) (preferred : Int) :
    Outcome :=
  (fun least =>
    Bool.casesOn (motive := fun _ => Outcome)
      (Bool.and (Nat.ble 1 num) (Nat.ble least scale))
      (sqrtRatio f mode (Nat.mul num (Nat.pow 10 scale)) den preferred)
      ((fun kept =>
          sqrtCancelled f mode (Nat.mul num (Nat.pow 10 kept)) den
            (Nat.div (Nat.sub scale kept) 2) preferred)
        (Nat.add least (Nat.mod (Nat.sub scale least) 2))))
    (Nat.add (Nat.mul 6 f.declets) (digitBound den))

/-- The increment of a root does not change when the radicand and its scale are multiplied by
one positive number. -/
theorem sqrtIncrement_mul (mode : RoundingMode) (lower n : Nat) {scale k : Nat}
    (hscale : 0 < scale) (hk : 0 < k) :
    sqrtIncrement mode lower (n * k) (scale * k) = sqrtIncrement mode lower n scale := by
  have h1 := sqrtIncrement_eq mode lower (n * k) (Nat.mul_pos hscale hk)
  have h2 := sqrtIncrement_eq mode lower n hscale
  have hq : ((n * k : Nat) : ℚ) / ((scale * k : Nat) : ℚ) = (n : ℚ) / (scale : ℚ) := by
    push_cast
    exact mul_div_mul_right _ _ (by exact_mod_cast hk.ne')
  rw [hq, h2] at h1
  exact (Nat.add_left_cancel h1).symm

/--
`sqrtCancelled` is `sqrtRatio` of the radicand with the cancelled power of one hundred, when
the radicand `scaled / den` has at least twice the precision less one digits.
-/
theorem sqrtCancelled_eq (f : Format) (mode : RoundingMode) {scaled den : Nat} (hden : 0 < den)
    (hq : 100 ^ (3 * f.declets) ≤ scaled / den) (cancelled : Nat) (preferred : Int) :
    sqrtCancelled f mode scaled den cancelled preferred =
      sqrtRatio f mode (scaled * 100 ^ cancelled) den preferred := by
  have hdivf : ∀ m n : Nat, Nat.div m n = m / n := fun _ _ => rfl
  have hpow : 0 < 100 ^ cancelled := Nat.pow_pos (by decide)
  have hpos : 0 < scaled / den := Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) hq
  have hhundred : (100 : Nat) ^ cancelled = 10 ^ (2 * cancelled) := by
    rw [Nat.pow_mul]
  have hlength : decimalLength (scaled * 100 ^ cancelled / den) =
      decimalLength (scaled / den) + 2 * cancelled := by
    rw [hhundred]
    exact decimalLength_mul_pow_div hden hpos _
  have hdigits : 6 * f.declets + 1 ≤ decimalLength (scaled / den) := by
    rw [decimalLength_eq_log]
    refine Nat.succ_le_succ (Nat.le_log_of_pow_le (by decide) ?_)
    rw [show 6 * f.declets = 2 * (3 * f.declets) by omega, Nat.pow_mul]
    exact hq
  unfold sqrtCancelled sqrtRatio
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.pow_eq, Nat.succ_eq_add_one,
    Nat.pred_eq_sub_one, hdivf]
  rw [hlength]
  generalize hshift : (decimalLength (scaled / den) - 1) / 2 + 1 - (3 * f.declets + 1) = shift
  have hsum : (decimalLength (scaled / den) + 2 * cancelled - 1) / 2 + 1 - (3 * f.declets + 1) =
      shift + cancelled := by omega
  have hscale : den * 100 ^ (shift + cancelled) = den * 100 ^ shift * 100 ^ cancelled := by
    rw [Nat.pow_add, Nat.mul_assoc]
  have hS : 0 < den * 100 ^ shift := Nat.mul_pos hden (Nat.pow_pos (by decide))
  have htiny : Nat.ble (scaled * 100 ^ cancelled + 1) (den * 100 ^ (3 * f.declets)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hle := Nat.le_of_ble_eq_true h
    have h1 : den * 100 ^ (3 * f.declets) ≤ scaled :=
      (Nat.mul_comm _ _).le.trans ((Nat.le_div_iff_mul_le hden).1 hq)
    have h2 : scaled ≤ scaled * 100 ^ cancelled := Nat.le_mul_of_pos_right _ hpow
    omega
  have hexact : ∀ a : Nat,
      Nat.beq (a * (den * 100 ^ shift * 100 ^ cancelled)) (scaled * 100 ^ cancelled) =
        Nat.beq (a * (den * 100 ^ shift)) scaled := by
    intro a
    rw [← Nat.mul_assoc]
    cases h : Nat.beq (a * (den * 100 ^ shift)) scaled
    · exact Bool.eq_false_iff.mpr fun hb =>
        Nat.ne_of_beq_eq_false h (Nat.eq_of_mul_eq_mul_right hpow (Nat.eq_of_beq_eq_true hb))
    · rw [Nat.eq_of_beq_eq_true h]
      exact Nat.beq_refl _
  rw [hsum, hscale, Nat.mul_div_mul_right _ _ hpow, sqrtIncrement_mul mode _ scaled hS hpow,
    hexact, htiny]

/--
`sqrtScaled` is `sqrtRatio` of the numerator with its power of ten, for every format, rounding
direction, numerator, nonzero denominator, scale and preferred exponent.
-/
theorem sqrtScaled_eq (f : Format) (mode : RoundingMode) (num : Nat) {den : Nat}
    (hden : den ≠ 0) (scale : Nat) (preferred : Int) :
    sqrtScaled f mode num den scale preferred =
      sqrtRatio f mode (num * 10 ^ scale) den preferred := by
  unfold sqrtScaled
  generalize hleast : Nat.add (Nat.mul 6 f.declets) (digitBound den) = least
  beta_reduce
  cases hnum : Nat.ble 1 num
  · rfl
  cases hle : Nat.ble least scale
  · rfl
  have hn : 0 < num := Nat.le_of_ble_eq_true hnum
  have hls : least ≤ scale := Nat.le_of_ble_eq_true hle
  have hd : 0 < den := Nat.pos_of_ne_zero hden
  generalize hkept : least + (scale - least) % 2 = kept
  have hks : kept + 2 * ((scale - kept) / 2) = scale := by omega
  -- The kept power gives the radicand twice the precision less one digits.
  have hq : 100 ^ (3 * f.declets) ≤ num * 10 ^ kept / den := by
    have hk : least ≤ kept := by omega
    rw [Nat.le_div_iff_mul_le hd, show (100 : Nat) = 10 ^ 2 from rfl, ← Nat.pow_mul]
    calc 10 ^ (2 * (3 * f.declets)) * den
        ≤ 10 ^ (2 * (3 * f.declets)) * 10 ^ digitBound den :=
          Nat.mul_le_mul_left _ (lt_ten_pow_digitBound den).le
      _ = 10 ^ least := by
          rw [← Nat.pow_add, ← hleast, show 2 * (3 * f.declets) = 6 * f.declets by omega]
          rfl
      _ ≤ 10 ^ kept := Nat.pow_le_pow_right (by decide) hk
      _ ≤ num * 10 ^ kept := Nat.le_mul_of_pos_left _ hn
  change sqrtCancelled f mode (num * 10 ^ (least + (scale - least) % 2)) den
    ((scale - (least + (scale - least) % 2)) / 2) preferred = _
  rw [hkept, sqrtCancelled_eq f mode hd hq, Nat.mul_assoc, show (100 : Nat) = 10 ^ 2 from rfl,
    ← Nat.pow_mul, ← Nat.pow_add, hks]

/--
Kernel form of `Arithmetic.sqrt` (`sqrt_eq`): the coefficient of a positive finite datum is put
on the grid `10 ^ (2 × minQuantum)` as a ratio of natural numbers, and `sqrtRatio` rounds its
root with half the quantum exponent, rounded down, as the preferred exponent. A zero, a
negative datum, an infinity and a NaN are left to the specification.
-/
def sqrt (f : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun s c q =>
      Bool.casesOn (motive := fun _ => Outcome) (Bool.or s (Nat.beq c 0))
        (offsets3 q f.bias f.bias fun above below =>
          sqrtScaled f mode c (Nat.pow 10 below) above (q / 2))
        (Arithmetic.sqrt f mode x))
    (fun _ => Arithmetic.sqrt f mode x) (fun _ _ _ => Arithmetic.sqrt f mode x)

/--
IEEE 754-2019 §5.4.1 `squareRoot` on decimal data is its kernel form, for every format, rounding
direction and datum: the same datum and the same flags.
-/
@[kernel_optimize] theorem sqrt_eq (f : Format) (mode : RoundingMode) (x : Datum) :
    Arithmetic.sqrt f mode x = sqrt f mode x := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  cases s
  · rcases c with _ | c
    · rfl
    · change _ = offsets3 q f.bias f.bias fun above below =>
        sqrtScaled f mode (c + 1) (Nat.pow 10 below) above (q / 2)
      rw [offsets3_eq]
      simp only [Nat.pow_eq]
      generalize ha : (q + f.bias + f.bias).toNat = a
      generalize hb : (-(q + f.bias + f.bias)).toNat = b
      have hab : (a : Int) - (b : Int) = q + f.bias + f.bias := by omega
      have hspec : Arithmetic.sqrt f mode (.finite false (c + 1) q) =
          sqrtMagnitude f mode (((c + 1 : Nat) : ℚ) * (10 : ℚ) ^ q) (q / 2) := by
        simp [Arithmetic.sqrt]
      rw [hspec, sqrtScaled_eq f mode _ (by positivity), sqrtRatio_eq f mode _ (by positivity),
        zpow_eq_ratio f q hab]
      congr 1
      push_cast
      ring
  · rfl

/--
Kernel form of `Arithmetic.rSqrt` (`rSqrt_eq`): the reciprocal of a positive finite datum is
put on the grid `10 ^ (2 × minQuantum)` as a ratio of natural numbers, and `sqrtRatio` rounds
its root with half the negated quantum exponent, rounded down, as the preferred exponent. A
zero, a negative datum, an infinity and a NaN are left to the specification.
-/
def rSqrt (f : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun s c q =>
      Bool.casesOn (motive := fun _ => Outcome) (Bool.or s (Nat.beq c 0))
        (offsets3 (-q) f.bias f.bias fun above below =>
          sqrtScaled f mode 1 (Nat.mul c (Nat.pow 10 below)) above ((-q) / 2))
        (Arithmetic.rSqrt f mode x))
    (fun _ => Arithmetic.rSqrt f mode x) (fun _ _ _ => Arithmetic.rSqrt f mode x)

/--
IEEE 754-2019 §9.2 `rSqrt` on decimal data is its kernel form, for every format, rounding
direction and datum: the same datum and the same flags.
-/
@[kernel_optimize] theorem rSqrt_eq (f : Format) (mode : RoundingMode) (x : Datum) :
    Arithmetic.rSqrt f mode x = rSqrt f mode x := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  cases s
  · rcases c with _ | c
    · rfl
    · change _ = offsets3 (-q) f.bias f.bias fun above below =>
        sqrtScaled f mode 1 (Nat.mul (c + 1) (Nat.pow 10 below)) above ((-q) / 2)
      rw [offsets3_eq]
      simp only [Nat.mul_eq, Nat.pow_eq]
      generalize ha : (-q + f.bias + f.bias).toNat = a
      generalize hb : (-(-q + f.bias + f.bias)).toNat = b
      have hab : (a : Int) - (b : Int) = -q + f.bias + f.bias := by omega
      have hspec : Arithmetic.rSqrt f mode (.finite false (c + 1) q) =
          sqrtMagnitude f mode ((((c + 1 : Nat) : ℚ) * (10 : ℚ) ^ q)⁻¹) ((-q) / 2) := by
        simp [Arithmetic.rSqrt]
      rw [hspec, sqrtScaled_eq f mode _ (Nat.mul_ne_zero (Nat.succ_ne_zero c) (by positivity)),
        Nat.one_mul,
        sqrtRatio_eq f mode _ (Nat.mul_ne_zero (Nat.succ_ne_zero c) (by positivity)),
        mul_inv, ← zpow_neg, zpow_eq_ratio f (-q) hab]
      congr 1
      push_cast
      field_simp
  · rfl

/--
Kernel form of `Arithmetic.hypot` (`hypot_eq`): the exact sum of the squares of two finite data
is a natural number at twice the smaller of the two quantum exponents, and `sqrtScaled` rounds
its root with that smaller exponent as the preferred exponent. An infinity and a NaN are left
to the specification.
-/
def hypot (f : Format) (mode : RoundingMode) (x y : Datum) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun _ cx qx => Datum.casesOn (motive := fun _ => Outcome) y
      (fun _ cy qy =>
        gaps qx qy fun a b =>
          (fun least =>
            offsets3 (Int.add least least) f.bias f.bias fun above below =>
              sqrtScaled f mode
                (Nat.add (Nat.mul (Nat.pow cx 2) (Nat.pow 100 a))
                  (Nat.mul (Nat.pow cy 2) (Nat.pow 100 b)))
                (Nat.pow 10 below) above least)
            (Bool.casesOn (motive := fun _ => Int) (Nat.beq b 0) qx qy))
      (fun _ => Arithmetic.hypot f mode x y) (fun _ _ _ => Arithmetic.hypot f mode x y))
    (fun _ => Arithmetic.hypot f mode x y) (fun _ _ _ => Arithmetic.hypot f mode x y)

/--
IEEE 754-2019 §9.2 `hypot` on decimal data is its kernel form, for every format, rounding
direction and pair of data: the same datum and the same flags.
-/
@[kernel_optimize] theorem hypot_eq (f : Format) (mode : RoundingMode) (x y : Datum) :
    Arithmetic.hypot f mode x y = hypot f mode x y := by
  rcases x with ⟨sx, cx, qx⟩ | sx | ⟨sx, tx, px⟩ <;>
    rcases y with ⟨sy, cy, qy⟩ | sy | ⟨sy, ty, py⟩ <;> try rfl
  have hten : (10 : ℚ) ≠ 0 := by norm_num
  have hadd : ∀ m n : Int, Int.add m n = m + n := fun _ _ => rfl
  have hleast : Bool.rec (motive := fun _ => Int) qx qy (Nat.beq (qy - qx).toNat 0) =
      min qx qy := by
    by_cases h : qy ≤ qx
    · have hzero : (qy - qx).toNat = 0 := by omega
      rw [hzero, min_eq_right h]
      rfl
    · obtain ⟨k, hk⟩ : ∃ k, (qy - qx).toNat = k + 1 := ⟨(qy - qx).toNat - 1, by omega⟩
      rw [hk, min_eq_left (by omega)]
      rfl
  change sqrtMagnitude f mode
      (Datum.finiteValue sx cx qx ^ 2 + Datum.finiteValue sy cy qy ^ 2) (min qx qy) =
    gaps qx qy fun a b =>
      (fun least =>
        offsets3 (Int.add least least) f.bias f.bias fun above below =>
          sqrtScaled f mode
            (Nat.add (Nat.mul (Nat.pow cx 2) (Nat.pow 100 a))
              (Nat.mul (Nat.pow cy 2) (Nat.pow 100 b)))
            (Nat.pow 10 below) above least)
        (Bool.casesOn (motive := fun _ => Int) (Nat.beq b 0) qx qy)
  rw [gaps_eq]
  dsimp only
  rw [hleast, offsets3_eq]
  simp only [hadd, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
  generalize hm : min qx qy = m
  generalize ha : (qx - qy).toNat = a
  generalize hb : (qy - qx).toNat = b
  have hqx : m + (a : Int) = qx := by omega
  have hqy : m + (b : Int) = qy := by omega
  generalize hA : (m + m + f.bias + f.bias).toNat = A
  generalize hB : (-(m + m + f.bias + f.bias)).toNat = B
  have hAB : (A : Int) - (B : Int) = m + m + f.bias + f.bias := by omega
  have hsquare := zpow_eq_ratio f (m + m) hAB
  rw [zpow_add₀ hten, ← pow_two] at hsquare
  have hx : (10 : ℚ) ^ qx = (10 : ℚ) ^ m * (10 : ℚ) ^ a := by
    rw [← zpow_natCast (10 : ℚ) a, ← zpow_add₀ hten, hqx]
  have hy : (10 : ℚ) ^ qy = (10 : ℚ) ^ m * (10 : ℚ) ^ b := by
    rw [← zpow_natCast (10 : ℚ) b, ← zpow_add₀ hten, hqy]
  have h100 : ∀ k : Nat, (100 : ℚ) ^ k = ((10 : ℚ) ^ k) ^ 2 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [sqrtScaled_eq f mode _ (by positivity), sqrtRatio_eq f mode _ (by positivity), ← sq_abs,
    Datum.finiteValue_abs, ← sq_abs (Datum.finiteValue sy cy qy), Datum.finiteValue_abs, hx, hy]
  congr 1
  push_cast
  rw [h100 a, h100 b,
    show ∀ sum : ℚ, sum * (10 : ℚ) ^ A / (10 : ℚ) ^ B * (10 : ℚ) ^ (2 * f.minQuantum) =
      sum * ((10 : ℚ) ^ A / (10 : ℚ) ^ B * (10 : ℚ) ^ (2 * f.minQuantum)) from
      fun sum => by ring,
    ← hsquare]
  ring

/-! ## Kernel shapes -/

kernel_shape sqrtIncrement
kernel_shape sqrtRatio
kernel_shape sqrtCancelled
kernel_shape sqrtScaled
kernel_shape sqrt
kernel_shape rSqrt
kernel_shape hypot

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath
