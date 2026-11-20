/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Zero
public import FloatLib.Floats.Formats.DecimalInterchange.Cohort.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Queries.Proof
public import FloatLib.Tactic.KernelOptimize

/-!
# The decimal kernel path computes the specified operations

`add_eq`, `sub_eq`, `mul_eq` and `fma_eq` state that `KernelPath.add`, `sub`, `mul` and `fma`
are `Arithmetic.add`, `sub`, `mul` and `fma`: the same datum and the same flags, for every
format (the three IEEE formats and every custom layout), every rounding direction and all
operands, valid for the format or not. They are tagged `@[kernel_optimize]`, so `float_decide`
and `#kernel_cost` rewrite a decimal sum, difference, product or fused multiply-add to its
kernel form. `datum_eq` does
the same for an equation between data, which the kernel otherwise decides through the derived
instance.

The proof goes through `project_eq`: `KernelPath.project` is `projectMagnitude` of the exact
value `c × 10 ^ e` with `e` as the preferred exponent. Its core `projectAt_eq` has three cases:

* `projectMagnitude_zero_eq`: an exact zero;
* `projectMagnitude_scaled_of_fits`: a nonzero coefficient within the precision at an exponent
  not below the least quantum, which is delivered unchanged, scaled to the largest quantum, or
  overflows;
* `projectMagnitude_scaled_of_wide`: every other nonzero value, which loses digits.

They rest on facts about the specification that are stated on integers:

* `log_floor_scaled`, `roundingQuantum_scaled`: the digit count that selects the rounding quantum;
* `roundMagnitude_natCast_div`, `roundAt_scaled_of_lt`: the rounded coefficient, from quotient
  and remainder;
* `stripTrailing_mul_pow`: the preferred cohort member of an exact result;
* `scaled_lt_minNormal_iff`: tininess.

`project_finiteValue` and `addFinite_eq` reduce the sum and the product of two finite data to one
projection of a signed coefficient, and `finiteValue_mul` makes the exact product of two finite
data the first term of the sum that a fused multiply-add rounds.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

/-! ## Integers as pairs of naturals -/

/-- A Boolean case analysis is a conditional. -/
private theorem casesOn_eq_ite {α : Type} (b : Bool) (x y : α) :
    Bool.casesOn (motive := fun _ => α) b x y = if b then y else x := by
  cases b <;> rfl

/-- `flag` is one for `true` and zero for `false`. -/
theorem flag_eq (b : Bool) : flag b = if b then 1 else 0 := by
  cases b <;> rfl

/-- `offsets` passes on how far the sum lies above and below zero. -/
theorem offsets_eq {α : Type} (x y : Int) (k : Nat → Nat → α) :
    offsets x y k = k (x + y).toNat (-(x + y)).toNat := by
  rcases x with m | m <;> rcases y with n | n <;>
    simp only [offsets, Int.ofNat_eq_natCast, Int.negSucc_eq, Nat.sub_eq, Nat.add_eq,
      Nat.succ_eq_add_one] <;> congr 1 <;> omega

/-- `gaps` passes on how far the first integer lies above and below the second. -/
theorem gaps_eq {α : Type} (x y : Int) (k : Nat → Nat → α) :
    gaps x y k = k (x - y).toNat (y - x).toNat := by
  rcases x with m | m <;> rcases y with n | n <;>
    simp only [gaps, Int.ofNat_eq_natCast, Int.negSucc_eq, Nat.sub_eq, Nat.add_eq,
      Nat.succ_eq_add_one] <;> congr 1 <;> omega

/-- `offsets3` passes on how far the sum of three integers lies above and below zero. -/
theorem offsets3_eq {α : Type} (x y z : Int) (k : Nat → Nat → α) :
    offsets3 x y z k = k (x + y + z).toNat (-(x + y + z)).toNat := by
  rcases x with m | m <;> rcases y with n | n <;> rcases z with l | l <;>
    simp only [offsets3, Int.ofNat_eq_natCast, Int.negSucc_eq, Nat.sub_eq, Nat.add_eq,
      Nat.succ_eq_add_one] <;> congr 1 <;> omega

/-- `quantumAt offset bias` is the quantum exponent `offset - bias`. -/
theorem quantumAt_eq (offset : Nat) (bias : Int) :
    quantumAt offset bias = (offset : Int) - bias := by
  rcases bias with b | b
  · simp only [quantumAt, Int.subNatNat_eq_coe, Int.ofNat_eq_natCast]
  · simp only [quantumAt, Int.ofNat_eq_natCast, Int.negSucc_eq, Nat.add_eq, Nat.succ_eq_add_one]
    push_cast
    omega

/-- The kernel's equality test on naturals decides equality. -/
theorem natBeq_eq (m n : Nat) : Nat.beq m n = decide (m = n) := by
  rw [show Nat.beq m n = (m == n) from rfl, beq_eq_decide]

/-- `Nat.ble` decides the order of natural numbers. -/
theorem natBle_eq (m n : Nat) : Nat.ble m n = decide (m ≤ n) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_iff]

/-- `intBeq` decides equality of integers. -/
theorem intBeq_eq (x y : Int) : intBeq x y = decide (x = y) := by
  rcases x with m | m <;> rcases y with n | n <;> simp [intBeq, natBeq_eq]

/-- `boolBeq` decides equality of Booleans. -/
theorem boolBeq_eq (x y : Bool) : boolBeq x y = decide (x = y) := by
  cases x <;> cases y <;> rfl

/-- `differ` is the exclusive or. -/
theorem differ_eq (x y : Bool) : differ x y = Bool.xor x y := by
  cases x <;> cases y <;> rfl

/-- `datumBeq` decides equality of data. -/
theorem datumBeq_eq (x y : Datum) : datumBeq x y = decide (x = y) := by
  cases x <;> cases y <;> simp only [datumBeq, casesOn_eq_ite] <;> rw [Bool.eq_iff_iff] <;>
    simp [intBeq_eq, boolBeq_eq, natBeq_eq] <;> tauto

/-- An equation between data is a comparison of their fields, which the kernel evaluates on
natural numbers. -/
@[kernel_optimize] theorem datum_eq (x y : Datum) : (x = y) = (datumBeq x y = true) := by
  rw [datumBeq_eq, decide_eq_true_eq]

/-! ## Digit count -/

/--
`decimalLength` is the number of decimal digits of a nonzero natural number. The comparisons
with powers of ten prove the count, whatever the estimate from the bit length is.
-/
theorem decimalLength_eq {c : Nat} (hc : c ≠ 0) : decimalLength c = Nat.log 10 c + 1 := by
  unfold decimalLength
  generalize Nat.shiftRight (Nat.mul (Numerics.Kernel.size c) 1233) 12 = d
  simp only [casesOn_eq_ite, Nat.ble_eq, Nat.pow_eq, Nat.sub_eq, Nat.succ_eq_add_one]
  split_ifs with h1 h2 h3
  · rfl
  · rw [Nat.log_eq_of_pow_le_of_lt_pow h1 (not_le.mp h2)]
  · have hd : d ≠ 0 := by
      rintro rfl
      exact h1 (Nat.pos_of_ne_zero hc)
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at h1 h3 ⊢
    rw [Nat.log_eq_of_pow_le_of_lt_pow h3 (not_le.mp h1)]
  · rfl

/-! ## The specification on integers -/

/-- `decimalLength` is `Nat.log 10 c + 1` for every natural number, zero included. -/
theorem decimalLength_eq_log (c : Nat) : decimalLength c = Nat.log 10 c + 1 := by
  by_cases hc : c = 0
  · subst hc
    rfl
  · exact decimalLength_eq hc

/-- A power `a ^ b` is at most `c ^ y` when `a ^ p ≤ c ^ q` and `q * b ≤ p * y`: the comparison
of two logarithms by one known pair of powers. -/
private theorem pow_le_pow_of_mul_le {a c p q b y : Nat} (hbase : a ^ p ≤ c ^ q) (hp : p ≠ 0)
    (hc : 0 < c) (h : q * b ≤ p * y) : a ^ b ≤ c ^ y := by
  refine (Nat.pow_le_pow_iff_left hp).1 ?_
  calc (a ^ b) ^ p = (a ^ p) ^ b := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
    _ ≤ (c ^ q) ^ b := Nat.pow_le_pow_left hbase b
    _ = c ^ (q * b) := (Nat.pow_mul ..).symm
    _ ≤ c ^ (p * y) := Nat.pow_le_pow_right hc h
    _ = (c ^ y) ^ p := by rw [← Nat.pow_mul, Nat.mul_comm]

/-- Every natural number is below ten to the power `digitBound`: it has at most that many
decimal digits. -/
theorem lt_ten_pow_digitBound (c : Nat) : c < 10 ^ digitBound c := by
  have hsize : c < 2 ^ Numerics.Kernel.size c := by
    rw [Numerics.Kernel.size_eq]
    exact Nat.lt_size_self c
  have hbound : digitBound c = Numerics.Kernel.size c * 1234 / 2 ^ 12 + 1 :=
    congrArg Nat.succ (Nat.shiftRight_eq_div_pow (Numerics.Kernel.size c * 1234) 12)
  refine Nat.lt_of_lt_of_le hsize
    (pow_le_pow_of_mul_le (p := 4096) (q := 1234) (by decide +kernel) (by decide) (by decide) ?_)
  rw [hbound]
  omega

/-- A quotient scaled by a power of ten has that many more digits, when it is not zero. -/
theorem decimalLength_mul_pow_div {num den : Nat} (hden : 0 < den) (hq : 0 < num / den)
    (c : Nat) : decimalLength (num * 10 ^ c / den) = decimalLength (num / den) + c := by
  have hpow : 0 < 10 ^ c := Nat.pow_pos (by decide)
  have hlow : num / den * 10 ^ c ≤ num * 10 ^ c / den := by
    rw [Nat.le_div_iff_mul_le hden, Nat.mul_right_comm]
    exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self num den)
  have hhigh : num * 10 ^ c / den < (num / den + 1) * 10 ^ c := by
    rw [Nat.div_lt_iff_lt_mul hden, Nat.mul_right_comm]
    exact Nat.mul_lt_mul_of_pos_right
      ((Nat.lt_mul_div_succ num hden).trans_eq (Nat.mul_comm ..)) hpow
  have hk1 : 10 ^ Nat.log 10 (num / den) ≤ num / den := Nat.pow_log_le_self 10 hq.ne'
  have hk2 : num / den < 10 ^ (Nat.log 10 (num / den) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) _
  have hlog : Nat.log 10 (num * 10 ^ c / den) = Nat.log 10 (num / den) + c := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · calc 10 ^ (Nat.log 10 (num / den) + c) = 10 ^ Nat.log 10 (num / den) * 10 ^ c :=
            Nat.pow_add ..
        _ ≤ num / den * 10 ^ c := Nat.mul_le_mul_right _ hk1
        _ ≤ _ := hlow
    · calc num * 10 ^ c / den < (num / den + 1) * 10 ^ c := hhigh
        _ ≤ 10 ^ (Nat.log 10 (num / den) + 1) * 10 ^ c := Nat.mul_le_mul_right _ hk2
        _ = 10 ^ (Nat.log 10 (num / den) + c + 1) := by
            rw [← Nat.pow_add]
            congr 1
            omega
  rw [decimalLength_eq_log, decimalLength_eq_log, hlog]
  omega

/-- Multiplying by a power of ten adds its exponent to the decimal logarithm. -/
private theorem log_mul_pow {c : Nat} (hc : c ≠ 0) (a : Nat) :
    Nat.log 10 (c * 10 ^ a) = Nat.log 10 c + a := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Nat.pow_succ, ← Nat.mul_assoc,
        Nat.log_mul_base (by decide) (Nat.mul_ne_zero hc (by positivity)), ih]
      omega

/-- Dividing by a power of ten subtracts its exponent from the decimal logarithm. -/
private theorem log_div_pow (c b : Nat) : Nat.log 10 (c / 10 ^ b) = Nat.log 10 c - b := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.log_div_base, ih]
      omega

/--
The digit count that selects the rounding quantum: the integer part of a nonzero coefficient
scaled by ten to `a - b`, where one of `a` and `b` is zero, has the digits of the coefficient
plus `a` minus `b`, and one digit when that is not positive.
-/
theorem log_floor_scaled {c : Nat} (hc : c ≠ 0) (a b : Nat) (hab : a = 0 ∨ b = 0) :
    Nat.log 10 ⌊(c : ℚ) * (10 : ℚ) ^ ((a : Int) - (b : Int))⌋₊ + 1 =
      Nat.log 10 c + 1 + a - b + flag (Nat.ble (Nat.log 10 c + 1 + a) b) := by
  rw [flag_eq]
  rcases hab with rfl | rfl
  · have hvalue : (c : ℚ) * (10 : ℚ) ^ (((0 : Nat) : Int) - (b : Int)) =
        (c : ℚ) / ((10 ^ b : Nat) : ℚ) := by
      rw [Nat.cast_zero, zero_sub, zpow_neg, zpow_natCast, div_eq_mul_inv]
      push_cast
      rfl
    rw [hvalue, Rat.natFloor_natCast_div_natCast, log_div_pow]
    by_cases h : Nat.log 10 c + 1 ≤ b
    · simp only [Nat.add_zero, Nat.ble_eq, h, ite_true]
      omega
    · simp only [Nat.add_zero, Nat.ble_eq, h, ite_false]
      omega
  · have hvalue : (c : ℚ) * (10 : ℚ) ^ ((a : Int) - ((0 : Nat) : Int)) =
        ((c * 10 ^ a : Nat) : ℚ) := by
      rw [Nat.cast_zero, sub_zero, zpow_natCast]
      push_cast
      rfl
    rw [hvalue, Nat.floor_natCast, log_mul_pow hc]
    have h : ¬ Nat.log 10 c + 1 + a ≤ 0 := by omega
    simp only [Nat.ble_eq, h, ite_false]
    omega

/-- The rounding quantum of a nonzero scaled value, from the digit count of its coefficient. -/
theorem roundingQuantum_scaled (f : Format) {c : Nat} (hc : c ≠ 0) {e : Int} {a b : Nat}
    (hoffset : (a : Int) - (b : Int) = e + f.bias) (hab : a = 0 ∨ b = 0) :
    roundingQuantum f ((c : ℚ) * (10 : ℚ) ^ e) =
      ((Nat.log 10 c + 1 + a - b + flag (Nat.ble (Nat.log 10 c + 1 + a) b) - f.precision :
        Nat) : Int) - f.bias := by
  have hscaled : (c : ℚ) * (10 : ℚ) ^ e / (10 : ℚ) ^ f.minQuantum =
      (c : ℚ) * (10 : ℚ) ^ ((a : Int) - (b : Int)) := by
    rw [mul_div_assoc, ← zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), hoffset]
    simp only [Format.minQuantum, sub_neg_eq_add]
  rw [roundingQuantum_eq, hscaled, scaleShift, log_floor_scaled hc a b hab, Format.minQuantum]
  ring

/-- The quotient of a number below twice a positive divisor is zero or one. -/
private theorem div_eq_ite {x d : Nat} (h : x < 2 * d) : x / d = if d ≤ x then 1 else 0 := by
  split_ifs with hle
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt (by omega)

/--
Rounding a quotient of naturals to a coefficient: the truncated quotient, incremented by the
integer rule of `increment` on the remainder.
-/
theorem roundMagnitude_natCast_div (mode : RoundingMode) (negative : Bool) (c d : Nat)
    (hd : 0 < d) :
    mode.roundMagnitude negative ((c : ℚ) / (d : ℚ)) =
      c / d + increment mode negative (c / d) (c % d) d := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hrem : (c : ℚ) / (d : ℚ) - ((c / d : Nat) : ℚ) = ((c % d : Nat) : ℚ) / (d : ℚ) := by
    have h : (c : ℚ) = (d : ℚ) * ((c / d : Nat) : ℚ) + ((c % d : Nat) : ℚ) := by
      exact_mod_cast (Nat.div_add_mod c d).symm
    field_simp
    linarith
  have hlt : (1 < 2 * (((c % d : Nat) : ℚ) / (d : ℚ))) ↔ d < 2 * (c % d) := by
    rw [← mul_div_assoc, one_lt_div hdq]
    norm_cast
  have heq : (2 * (((c % d : Nat) : ℚ) / (d : ℚ)) = 1) ↔ 2 * (c % d) = d := by
    rw [← mul_div_assoc, div_eq_one_iff_eq hdq.ne']
    norm_cast
  have hle : (1 ≤ 2 * (((c % d : Nat) : ℚ) / (d : ℚ))) ↔ d ≤ 2 * (c % d) := by
    rw [← mul_div_assoc, one_le_div hdq]
    norm_cast
  have hpos : (0 < ((c % d : Nat) : ℚ) / (d : ℚ)) ↔ 0 < c % d := by
    rw [div_pos_iff_of_pos_right hdq]
    exact Nat.cast_pos
  rw [RoundingMode.roundMagnitude_eq, Rat.natFloor_natCast_div_natCast]
  dsimp only
  rw [hrem]
  have hr : c % d < d := Nat.mod_lt c hd
  have hmod : ∀ x y : Nat, Nat.mod x y = x % y := fun _ _ => rfl
  have hdiv : ∀ x y : Nat, Nat.div x y = x / y := fun _ _ => rfl
  have hnear := div_eq_ite (x := 2 * (c % d) + c / d % 2) (d := d + 1) (by omega)
  have haway := div_eq_ite (x := 2 * (c % d)) (d := d) (by omega)
  cases mode <;>
    simp only [RoundingMode.increment, increment, hlt, heq, hle, hpos, Nat.ble_eq, flag_eq,
      Nat.mul_eq, Nat.add_eq, hmod, hdiv, Nat.succ_eq_add_one, hnear, haway, casesOn_eq_ite,
      Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      Bool.false_eq_true, ite_false, Nat.add_zero] <;>
    (split_ifs <;> first | rfl | omega | (exfalso; simp_all))

/-- Rounding a scaled value at a quantum `k` places above its exponent drops `k` digits. -/
theorem roundAt_scaled_of_lt (mode : RoundingMode) (negative : Bool) (c : Nat) {e r : Int}
    {k : Nat} (hk : r - e = (k : Int)) :
    mode.roundAt negative ((c : ℚ) * (10 : ℚ) ^ e) r =
      c / 10 ^ k + increment mode negative (c / 10 ^ k) (c % 10 ^ k) (10 ^ k) := by
  have hvalue : (c : ℚ) * (10 : ℚ) ^ e / (10 : ℚ) ^ r = (c : ℚ) / ((10 ^ k : Nat) : ℚ) := by
    rw [mul_div_assoc, ← zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), show e - r = -(k : Int) by omega,
      zpow_neg, zpow_natCast, div_eq_mul_inv]
    push_cast
    rfl
  rw [RoundingMode.roundAt, hvalue, roundMagnitude_natCast_div mode negative c (10 ^ k)
    (by positivity)]

/-- Stripping `n` trailing zeros from a nonzero coefficient with at least `n` of them. -/
theorem stripTrailing_mul_pow {c : Nat} (hc : c ≠ 0) (n m : Nat) (h : n ≤ m) :
    stripTrailing n (c * 10 ^ m) = (c * 10 ^ (m - n), n) := by
  induction n generalizing m with
  | zero => simp [stripTrailing]
  | succ n ih =>
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hne : c * 10 ^ (m + 1) ≠ 0 := Nat.mul_ne_zero hc (by positivity)
      have hmod : c * 10 ^ (m + 1) % 10 = 0 := by
        rw [Nat.pow_succ, ← Nat.mul_assoc]
        exact Nat.mul_mod_left _ _
      have hdiv : c * 10 ^ (m + 1) / 10 = c * 10 ^ m := by
        rw [Nat.pow_succ, ← Nat.mul_assoc]
        exact Nat.mul_div_cancel _ (by decide)
      rw [stripTrailing, ite_eq_right hne, ite_eq_left hmod, hdiv, ih m (by omega)]
      simp

/-- Tininess on integers: a nonzero scaled value is below the least normal magnitude exactly
when its digits end below the precision of the least quantum. -/
theorem scaled_lt_minNormal_iff (f : Format) {c : Nat} (hc : c ≠ 0) {e : Int} {a b : Nat}
    (hoffset : (a : Int) - (b : Int) = e + f.bias) (hab : a = 0 ∨ b = 0) :
    (c : ℚ) * (10 : ℚ) ^ e < f.minNormal ↔ Nat.log 10 c + 1 + a < f.precision + b := by
  have hp := f.precision_pos
  have h10 : (0 : ℚ) < (10 : ℚ) ^ f.minQuantum := zpow_pos (by norm_num) _
  have hstep : (c : ℚ) * (10 : ℚ) ^ e < f.minNormal ↔
      (c : ℚ) * (10 : ℚ) ^ ((a : Int) - (b : Int)) < (10 : ℚ) ^ (f.precision - 1) := by
    rw [Format.minNormal, ← div_lt_iff₀ h10, mul_div_assoc,
      ← zpow_sub₀ (by norm_num : (10 : ℚ) ≠ 0), hoffset]
    simp only [Format.minQuantum, sub_neg_eq_add]
  rw [hstep]
  rcases hab with rfl | rfl
  · have hpow : (0 : ℚ) < (10 : ℚ) ^ b := by positivity
    rw [Nat.cast_zero, zero_sub, zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_lt_iff₀ hpow,
      ← pow_add]
    have hcast : (c : ℚ) < (10 : ℚ) ^ (f.precision - 1 + b) ↔ c < 10 ^ (f.precision - 1 + b) := by
      exact_mod_cast Iff.rfl
    rw [hcast, ← Nat.log_lt_iff_lt_pow (by decide) hc]
    omega
  · rw [Nat.cast_zero, sub_zero, zpow_natCast]
    have hcast : (c : ℚ) * (10 : ℚ) ^ a < (10 : ℚ) ^ (f.precision - 1) ↔
        c * 10 ^ a < 10 ^ (f.precision - 1) := by
      exact_mod_cast Iff.rfl
    rw [hcast, ← Nat.log_lt_iff_lt_pow (by decide) (Nat.mul_ne_zero hc (by positivity)),
      log_mul_pow hc]
    omega

/-! ## The kernel projection is the specified projection -/

/-- No direction increments a coefficient whose dropped digits are all zero. -/
theorem increment_zero (mode : RoundingMode) (negative : Bool) (lower : Nat) {d : Nat}
    (hd : 0 < d) : increment mode negative lower 0 d = 0 := by
  cases mode
  · change (2 * 0 + lower % 2) / (d + 1) = 0
    exact Nat.div_eq_of_lt (by omega)
  · change 2 * 0 / d = 0
    rw [Nat.mul_zero, Nat.zero_div]
  · rfl
  · cases negative <;> rfl
  · cases negative <;> rfl

/-- The increment of a coefficient is zero or one. -/
theorem increment_le_one (mode : RoundingMode) (negative : Bool) (lower : Nat)
    {rem d : Nat} (h : rem < d) : increment mode negative lower rem d ≤ 1 := by
  have hflag : flag (Nat.ble 1 rem) ≤ 1 := by
    rw [flag_eq]
    split <;> omega
  cases mode
  · change (2 * rem + lower % 2) / (d + 1) ≤ 1
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
  · change 2 * rem / d ≤ 1
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
  · exact Nat.zero_le 1
  · cases negative
    · exact hflag
    · exact Nat.zero_le 1
  · cases negative
    · exact Nat.zero_le 1
    · exact hflag

/-- The exponent bound of a format in terms of its largest quantum. -/
private theorem exponentBound_eq (f : Format) :
    (f.exponentBound : Int) = f.maxQuantum + f.bias + 1 := by
  simp only [Format.maxQuantum]
  ring

/--
The precision-rounded coefficient and exponent of a nonzero value whose coefficient fits the
precision at an exponent not below the least quantum: nothing is rounded, and the coefficient is
scaled to the finest quantum that the precision and the exponent range allow. `a` is the
exponent above the least quantum.
-/
theorem roundedPair_of_fits (f : Format) (mode : RoundingMode) (negative : Bool)
    {c : Nat} (hc : c ≠ 0) (hfits : c < 10 ^ f.precision) {e : Int} {a : Nat}
    (hoffset : (a : Int) = e + f.bias) :
    roundedPair f mode negative ((c : ℚ) * (10 : ℚ) ^ e) =
      (c * 10 ^ (a - (Nat.log 10 c + 1 + a - f.precision)),
        ((Nat.log 10 c + 1 + a - f.precision : Nat) : Int) - f.bias) := by
  have hlog : Nat.log 10 c < f.precision := (Nat.log_lt_iff_lt_pow (by decide) hc).2 hfits
  have hflag : flag (Nat.ble (Nat.log 10 c + 1 + a) 0) = 0 := by
    rw [flag_eq, ite_eq_right]
    simp
  have hquantum := roundingQuantum_scaled f hc (e := e) (a := a) (b := 0)
    (by simpa using hoffset) (Or.inr rfl)
  rw [hflag, Nat.sub_zero, Nat.add_zero] at hquantum
  generalize hshift : Nat.log 10 c + 1 + a - f.precision = shift at hquantum ⊢
  have hle : (shift : Int) - f.bias ≤ e := by omega
  have hround := RoundingMode.roundAt_exact mode negative c hle
  have hdiff : (e - ((shift : Int) - f.bias)).toNat = a - shift := by omega
  rw [hdiff] at hround
  have hcoefficient : c * 10 ^ (a - shift) ≠ f.coefficientBound := by
    rw [f.coefficientBound_eq]
    apply Nat.ne_of_lt
    rw [← Nat.log_lt_iff_lt_pow (by decide) (Nat.mul_ne_zero hc (by positivity)), log_mul_pow hc]
    omega
  rw [roundedPair, hquantum, hround, f.carry_eq, ite_eq_right hcoefficient]

/--
The specified projection of a nonzero value whose coefficient fits the precision at an exponent
not below the least quantum: the datum itself when the exponent is in range, the coefficient
scaled to the largest quantum when it still fits there, and an overflow otherwise. `a` is the
exponent above the least quantum.
-/
theorem projectMagnitude_scaled_of_fits (f : Format) (mode : RoundingMode) (negative : Bool)
    {c : Nat} (hc : c ≠ 0) (hfits : c < 10 ^ f.precision) {e : Int} {a : Nat}
    (hoffset : (a : Int) = e + f.bias) :
    projectMagnitude f mode negative ((c : ℚ) * (10 : ℚ) ^ e) e =
      if a < f.exponentBound then { value := .finite negative c e }
      else if c * 10 ^ (a - (f.exponentBound - 1)) < 10 ^ f.precision then
        { value := .finite negative (c * 10 ^ (a - (f.exponentBound - 1))) f.maxQuantum }
      else overflow f mode negative := by
  have hbound := exponentBound_eq f
  have hboundPos := f.exponentBound_pos
  have hlog : Nat.log 10 c < f.precision := (Nat.log_lt_iff_lt_pow (by decide) hc).2 hfits
  have hpair := roundedPair_of_fits f mode negative hc hfits hoffset
  generalize hshift : Nat.log 10 c + 1 + a - f.precision = shift at hpair
  have hle : (shift : Int) - f.bias ≤ e := by omega
  have hdiff : (e - ((shift : Int) - f.bias)).toNat = a - shift := by omega
  have hexact : ((c * 10 ^ (a - shift) : Nat) : ℚ) * (10 : ℚ) ^ ((shift : Int) - f.bias) =
      (c : ℚ) * (10 : ℚ) ^ e := by
    have h := Arithmetic.finer_grid_value c e ((shift : Int) - f.bias) hle
    rwa [hdiff] at h
  rw [projectMagnitude_eq, hpair]
  simp only [hexact, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false,
    Bool.and_false]
  by_cases hrange : a < f.exponentBound
  · have hno : ¬ f.maxQuantum < (shift : Int) - f.bias := by omega
    have hfuel : (min e f.maxQuantum - ((shift : Int) - f.bias)).toNat = a - shift := by omega
    rw [ite_eq_right hno, ite_eq_left hrange, preferredCohort, hfuel,
      stripTrailing_mul_pow hc (a - shift) (a - shift) le_rfl]
    simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    congr 2
    omega
  · rw [ite_eq_right hrange]
    have hscaled : c * 10 ^ (a - (f.exponentBound - 1)) < 10 ^ f.precision ↔
        shift < f.exponentBound := by
      rw [← Nat.log_lt_iff_lt_pow (by decide) (Nat.mul_ne_zero hc (by positivity)),
        log_mul_pow hc]
      omega
    by_cases hover : shift < f.exponentBound
    · have hno : ¬ f.maxQuantum < (shift : Int) - f.bias := by omega
      have hfuel : (min e f.maxQuantum - ((shift : Int) - f.bias)).toNat =
          f.exponentBound - 1 - shift := by omega
      rw [ite_eq_right hno, ite_eq_left (hscaled.2 hover), preferredCohort, hfuel,
        stripTrailing_mul_pow hc (f.exponentBound - 1 - shift) (a - shift) (by omega)]
      have hpower : a - shift - (f.exponentBound - 1 - shift) = a - (f.exponentBound - 1) := by
        omega
      rw [hpower]
      congr 2
      omega
    · have hyes : f.maxQuantum < (shift : Int) - f.bias := by omega
      rw [ite_eq_left hyes, ite_eq_right (fun h => hover (hscaled.1 h))]
      rfl

/--
The outcome that the specification builds from a rounded coefficient at the quantum `shift`
above the least quantum, not below the preferred exponent `e`, is the kernel's `deliver`.
-/
private theorem deliver_eq (f : Format) (mode : RoundingMode) (negative : Bool) (x : ℚ)
    {e : Int} (coefficient shift : Nat) (inexact : Bool) (he : e ≤ (shift : Int) - f.bias) :
    (if f.maxQuantum < (shift : Int) - f.bias then
        ({ value := if mode.overflowToInfinity negative then .infinity negative
              else f.maxFinite negative
           status := { overflow := true, inexact := true } } : Outcome)
      else
        { value := if inexact then .finite negative coefficient ((shift : Int) - f.bias)
            else preferredCohort f negative coefficient ((shift : Int) - f.bias) e
          status := { inexact := inexact, underflow := decide (x < f.minNormal) && inexact } }) =
      deliver f mode negative f.exponentBound coefficient shift inexact
        (decide (x < f.minNormal)) := by
  have hbound := exponentBound_eq f
  have hfuel : (min e f.maxQuantum - ((shift : Int) - f.bias)).toNat = 0 := by omega
  have hcohort : preferredCohort f negative coefficient ((shift : Int) - f.bias) e =
      .finite negative coefficient ((shift : Int) - f.bias) := by
    simp [preferredCohort, hfuel, stripTrailing]
  rw [hcohort, ite_self, deliver, casesOn_eq_ite, quantumAt_eq]
  by_cases hover : f.exponentBound ≤ shift
  · rw [ite_eq_left (show f.maxQuantum < (shift : Int) - f.bias by omega),
      ite_eq_left (Nat.ble_eq_true_of_le hover)]
    rfl
  · rw [ite_eq_right (show ¬ f.maxQuantum < (shift : Int) - f.bias by omega),
      ite_eq_right (fun h => hover (Nat.le_of_ble_eq_true h))]

/--
The specified projection of a nonzero value that does not fit at its own exponent, because the
exponent lies below the least quantum (`b ≠ 0`) or the coefficient has more digits than the
precision: the digits below the rounding quantum are dropped, as `projectInexact` computes.
-/
theorem projectMagnitude_scaled_of_wide (f : Format) (mode : RoundingMode) (negative : Bool)
    {c : Nat} (hc : c ≠ 0) {e : Int} {a b : Nat}
    (hoffset : (a : Int) - (b : Int) = e + f.bias) (hab : a = 0 ∨ b = 0)
    (hwide : b ≠ 0 ∨ 10 ^ f.precision ≤ c) :
    projectMagnitude f mode negative ((c : ℚ) * (10 : ℚ) ^ e) e =
      projectInexact f mode negative c a b f.exponentBound (10 ^ f.precision) := by
  have hbound := exponentBound_eq f
  have hlog : b = 0 → f.precision ≤ Nat.log 10 c := by
    intro hb
    rcases hwide with h | h
    · exact absurd hb h
    · by_contra hlt
      exact absurd ((Nat.log_lt_iff_lt_pow (by decide) hc).1 (not_le.mp hlt)) (not_lt.mpr h)
  have hquantum := roundingQuantum_scaled f hc hoffset hab
  have htiny : decide ((c : ℚ) * (10 : ℚ) ^ e < f.minNormal) =
      Nat.ble (Nat.log 10 c + 1 + a + 1) (f.precision + b) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.ble_eq, scaled_lt_minNormal_iff f hc hoffset hab]
    omega
  have hkernel : projectInexact f mode negative c a b f.exponentBound (10 ^ f.precision) =
      projectRounded f mode negative c f.exponentBound (10 ^ f.precision)
        (Nat.log 10 c + 1 + a - b + flag (Nat.ble (Nat.log 10 c + 1 + a) b) - f.precision)
        (Nat.log 10 c + 1 + a - b + flag (Nat.ble (Nat.log 10 c + 1 + a) b) - f.precision + b - a)
        (Nat.ble (Nat.log 10 c + 1 + a + 1) (f.precision + b)) := by
    rw [projectInexact, decimalLength_eq hc]
    rfl
  rw [hkernel, ← htiny]
  generalize hshift : Nat.log 10 c + 1 + a - b + flag (Nat.ble (Nat.log 10 c + 1 + a) b) -
    f.precision = shift at hquantum ⊢
  have hk : (shift : Int) - f.bias - e = ((shift + b - a : Nat) : Int) := by
    rcases hab with rfl | rfl
    · omega
    · have := hlog rfl
      omega
  have hle : e ≤ (shift : Int) - f.bias := by omega
  have hround := roundAt_scaled_of_lt mode negative c hk
  have hpow : (10 : ℚ) ^ ((shift : Int) - f.bias) =
      (10 : ℚ) ^ e * ((10 ^ (shift + b - a) : Nat) : ℚ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)]
    congr 1
    omega
  have hdm := Nat.div_add_mod c (10 ^ (shift + b - a))
  have hlt := Nat.mod_lt c (Nat.pow_pos (n := shift + b - a) (by decide : 0 < 10))
  have hdivf : ∀ x y : Nat, Nat.div x y = x / y := fun _ _ => rfl
  have hmodf : ∀ x y : Nat, Nat.mod x y = x % y := fun _ _ => rfl
  simp only [projectRounded, casesOn_eq_ite, Nat.pow_eq, Nat.add_eq, hdivf, hmodf,
    Nat.succ_eq_add_one]
  generalize 10 ^ (shift + b - a) = D at hround hpow hdm hlt ⊢
  generalize c / D = lower at hround hdm ⊢
  generalize c % D = rem at hround hdm hlt ⊢
  have hnat : (lower + increment mode negative lower rem D) * D = c ↔ rem = 0 := by
    have hone := increment_le_one mode negative lower hlt
    have hzero : rem = 0 → increment mode negative lower rem D = 0 := by
      rintro rfl
      exact increment_zero mode negative lower hlt
    generalize increment mode negative lower rem D = amount at hone hzero ⊢
    obtain rfl | rfl : amount = 0 ∨ amount = 1 := by omega
    · rw [Nat.add_zero, Nat.mul_comm]
      omega
    · have hrem : rem ≠ 0 := fun h => absurd (hzero h) (by decide)
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      omega
  generalize lower + increment mode negative lower rem D = R at hround hnat ⊢
  have hinexact : decide (((roundedPair f mode negative ((c : ℚ) * (10 : ℚ) ^ e)).1 : ℚ) *
        (10 : ℚ) ^ (roundedPair f mode negative ((c : ℚ) * (10 : ℚ) ^ e)).2 ≠
          (c : ℚ) * (10 : ℚ) ^ e) = Nat.ble 1 rem := by
    have hvalue := roundedPair_value f mode negative ((c : ℚ) * (10 : ℚ) ^ e)
    rw [hquantum, hround, hpow] at hvalue
    have h10 : (10 : ℚ) ^ e ≠ 0 := zpow_ne_zero _ (by norm_num)
    have hcomm : (R : ℚ) * ((10 : ℚ) ^ e * (D : ℚ)) = ((R * D : Nat) : ℚ) * (10 : ℚ) ^ e := by
      push_cast
      ring
    rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.ble_eq, hvalue, hcomm, ne_eq, mul_left_inj' h10,
      Nat.cast_inj, hnat]
    omega
  have hhalf : f.coefficientBound / 10 = f.payloadBound := by
    rw [Format.coefficientBound]
    exact Nat.mul_div_cancel_left _ (by decide)
  have hsucc : (shift : Int) - f.bias + 1 = ((shift + 1 : Nat) : Int) - f.bias := by
    push_cast
    ring
  have hpair : roundedPair f mode negative ((c : ℚ) * (10 : ℚ) ^ e) =
      if R = f.coefficientBound then (f.payloadBound, ((shift + 1 : Nat) : Int) - f.bias)
      else (R, (shift : Int) - f.bias) := by
    rw [roundedPair, hquantum, hround, f.carry_eq, hsucc]
  rw [projectMagnitude_eq, natBeq_eq, ← f.coefficientBound_eq, hhalf]
  dsimp only
  rw [hinexact, hpair]
  by_cases hcarry : R = f.coefficientBound
  · rw [ite_eq_left hcarry, ite_eq_left (decide_eq_true hcarry)]
    exact deliver_eq f mode negative _ f.payloadBound (shift + 1) (Nat.ble 1 rem) (by omega)
  · rw [ite_eq_right hcarry, ite_eq_right (fun h => hcarry (of_decide_eq_true h))]
    exact deliver_eq f mode negative _ R shift (Nat.ble 1 rem) hle

/-- The specified projection of an exact zero is the kernel's `projectZero`. -/
theorem projectMagnitude_zero_eq (f : Format) (mode : RoundingMode) (negative : Bool) {e : Int}
    {a b : Nat} (hoffset : (a : Int) - (b : Int) = e + f.bias) (hab : a = 0 ∨ b = 0) :
    projectMagnitude f mode negative 0 e = projectZero f negative e a b f.exponentBound := by
  have hbound := exponentBound_eq f
  have hpos := f.exponentBound_pos
  have hmin : f.minQuantum = -f.bias := rfl
  have hexponent : max f.minQuantum (min e f.maxQuantum) =
      if b = 0 then
        if f.exponentBound ≤ a then ((f.exponentBound - 1 : Nat) : Int) - f.bias else e
      else ((0 : Nat) : Int) - f.bias := by
    split_ifs <;> omega
  rw [projectMagnitude_zero, hexponent, projectZero]
  simp only [casesOn_eq_ite, natBeq_eq, Nat.ble_eq, decide_eq_true_eq, quantumAt_eq, Nat.sub_eq]

/--
The kernel projection is the specified one: for an exponent that lies `a` above or `b` below the
least quantum (one of the two is zero), `projectAt` on the fields is `projectMagnitude` of the
exact value `c × 10 ^ e` with `e` as the preferred exponent. This covers every format, direction,
sign and coefficient.
-/
theorem projectAt_eq (f : Format) (mode : RoundingMode) (negative : Bool) (c : Nat) {e : Int}
    {a b : Nat} (hoffset : (a : Int) - (b : Int) = e + f.bias) (hab : a = 0 ∨ b = 0) :
    projectAt f mode negative c e a b f.exponentBound (10 ^ f.precision) =
      projectMagnitude f mode negative ((c : ℚ) * (10 : ℚ) ^ e) e := by
  unfold projectAt
  simp only [casesOn_eq_ite, natBeq_eq, Nat.ble_eq, decide_eq_true_eq, Nat.succ_eq_add_one]
  by_cases hc : c = 0
  · subst hc
    rw [ite_eq_left rfl, Nat.cast_zero, zero_mul]
    exact (projectMagnitude_zero_eq f mode negative hoffset hab).symm
  · rw [ite_eq_right hc]
    have hwide := fun h =>
      (projectMagnitude_scaled_of_wide f mode negative hc hoffset hab h).symm
    by_cases hb : b = 0
    · rw [ite_eq_left hb]
      by_cases hfit : c + 1 ≤ 10 ^ f.precision
      · subst hb
        rw [ite_eq_left hfit,
          projectMagnitude_scaled_of_fits f mode negative hc (by omega) (by simpa using hoffset)]
        by_cases hrange : a < f.exponentBound
        · rw [ite_eq_left hrange, ite_eq_right (by omega)]
        · have hbound := exponentBound_eq f
          have hpos := f.exponentBound_pos
          have hmax : ((f.exponentBound - 1 : Nat) : Int) - f.bias = f.maxQuantum := by omega
          rw [ite_eq_right hrange, ite_eq_left (by omega), projectAbove]
          simp only [casesOn_eq_ite, Nat.ble_eq, Nat.succ_eq_add_one, Nat.mul_eq, Nat.pow_eq,
            Nat.sub_eq, quantumAt_eq, hmax]
          rfl
      · rw [ite_eq_right hfit]
        exact hwide (Or.inr (by omega))
    · rw [ite_eq_right hb]
      exact hwide (Or.inl hb)

/--
`KernelPath.project` is the specified projection of the exact value `c × 10 ^ e` of sign
`negative`, with `e` as the preferred exponent.
-/
theorem project_eq (f : Format) (mode : RoundingMode) (negative : Bool) (c : Nat) (e : Int) :
    project f mode negative c e = projectMagnitude f mode negative ((c : ℚ) * (10 : ℚ) ^ e) e := by
  rw [project, offsets_eq]
  exact projectAt_eq f mode negative c (by omega) (by omega)

/-- Below the least quantum the kernel projection does not read its exponent argument. -/
theorem projectAt_of_below_ne_zero (f : Format) (mode : RoundingMode) (negative : Bool)
    (c : Nat) (e e' : Int) (a : Nat) {b : Nat} (hb : b ≠ 0) (bound full : Nat) :
    projectAt f mode negative c e a b bound full =
      projectAt f mode negative c e' a b bound full := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
  rfl

/-! ## The operations -/

/--
The specified projection of a finite value at its own exponent is the kernel projection of its
fields. `zeroSign` is the sign the operation gives an exact zero, which must be `negative` when
the coefficient is zero.
-/
theorem project_finiteValue (f : Format) (mode : RoundingMode) (negative zeroSign : Bool)
    (c : Nat) (m : Int) (hzero : c = 0 → zeroSign = negative) :
    DecimalInterchange.project f mode (Datum.finiteValue negative c m) m zeroSign =
      project f mode negative c m := by
  rw [project_eq, DecimalInterchange.project, Datum.finiteValue_abs]
  congr 1
  by_cases hc : c = 0
  · rw [ite_eq_left ((Datum.finiteValue_eq_zero_iff negative c m).2 hc)]
    exact hzero hc
  · rw [ite_eq_right (fun h => hc ((Datum.finiteValue_eq_zero_iff negative c m).1 h))]
    have hpos : (0 : ℚ) < (c : ℚ) * (10 : ℚ) ^ m :=
      mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hc)) (zpow_pos (by norm_num) _)
    cases negative
    · simp [Datum.finiteValue, hpos.le]
    · simp [Datum.finiteValue, hpos]

/-- A finite value on a finer exponent: the coefficient gains the digits in between. -/
theorem finiteValue_aligned (s : Bool) (c : Nat) {q m : Int} (h : m ≤ q) :
    Datum.finiteValue s c q = Datum.finiteValue s (c * 10 ^ (q - m).toNat) m := by
  rw [Datum.finiteValue, Datum.finiteValue, mul_assoc, mul_assoc,
    Arithmetic.finer_grid_value c q m h]

/--
The specified projection of a sum of two finite values on a common exponent is the kernel's
case analysis on the signs and on the order of the coefficients.
-/
private theorem project_sum (f : Format) (mode : RoundingMode) (sx sy : Bool) (a b : Nat)
    (m : Int) :
    DecimalInterchange.project f mode (Datum.finiteValue sx a m + Datum.finiteValue sy b m) m
        (Arithmetic.zeroSumSign mode sx sy) =
      Bool.casesOn (motive := fun _ => Outcome) (differ sx sy)
        (project f mode sx (Nat.add a b) m)
        (Bool.casesOn (motive := fun _ => Outcome) (Nat.beq a b)
          (Bool.casesOn (motive := fun _ => Outcome) (Nat.ble b a)
            (project f mode sy (Nat.sub b a) m)
            (project f mode sx (Nat.sub a b) m))
          (project f mode (isDown mode) 0 m)) := by
  simp only [casesOn_eq_ite, differ_eq, natBeq_eq, Nat.ble_eq, decide_eq_true_eq, Nat.add_eq,
    Nat.sub_eq]
  by_cases hs : sx = sy
  · subst hs
    have hsum : Datum.finiteValue sx a m + Datum.finiteValue sx b m =
        Datum.finiteValue sx (a + b) m := by
      simp only [Datum.finiteValue]
      push_cast
      ring
    have hsign : Arithmetic.zeroSumSign mode sx sx = sx := by simp [Arithmetic.zeroSumSign]
    rw [hsum, hsign, project_finiteValue f mode sx sx (a + b) m (fun _ => rfl)]
    simp
  · have hxor : (sx ^^ sy) = true := by cases sx <;> cases sy <;> simp_all
    have hsign : Arithmetic.zeroSumSign mode sx sy = isDown mode := by
      rw [Arithmetic.zeroSumSign, ite_eq_right hs]
      cases mode <;> rfl
    rw [ite_eq_left hxor, hsign]
    by_cases hab : a = b
    · subst hab
      have hsum : Datum.finiteValue sx a m + Datum.finiteValue sy a m =
          Datum.finiteValue (isDown mode) 0 m := by
        cases sx <;> cases sy <;>
          first
            | exact absurd rfl hs
            | simp [Datum.finiteValue]
      rw [ite_eq_left rfl, hsum, project_finiteValue f mode _ _ 0 m (fun _ => rfl)]
    · rw [ite_eq_right hab]
      by_cases hle : b ≤ a
      · have hsum : Datum.finiteValue sx a m + Datum.finiteValue sy b m =
            Datum.finiteValue sx (a - b) m := by
          cases sx <;> cases sy <;>
            first
              | exact absurd rfl hs
              | (simp only [Datum.finiteValue, Bool.false_eq_true, ↓reduceIte]
                 push_cast [Nat.cast_sub hle]
                 ring)
        rw [ite_eq_left hle, hsum,
          project_finiteValue f mode sx _ (a - b) m (fun h => absurd h (by omega))]
      · have hle' : a ≤ b := by omega
        have hsum : Datum.finiteValue sx a m + Datum.finiteValue sy b m =
            Datum.finiteValue sy (b - a) m := by
          cases sx <;> cases sy <;>
            first
              | exact absurd rfl hs
              | (simp only [Datum.finiteValue, Bool.false_eq_true, ↓reduceIte]
                 push_cast [Nat.cast_sub hle']
                 ring)
        rw [ite_eq_right hle, hsum,
          project_finiteValue f mode sy _ (b - a) m (fun h => absurd h (by omega))]

/-- `addFinite` on the exponent gaps of two finite data is their specified sum. -/
theorem addFinite_eq (f : Format) (mode : RoundingMode) (sx : Bool) (cx : Nat) (qx : Int)
    (sy : Bool) (cy : Nat) (qy : Int) :
    addFinite f mode sx cx qx sy cy qy (qx - qy).toNat (qy - qx).toNat =
      Arithmetic.add f mode (.finite sx cx qx) (.finite sy cy qy) := by
  have hmin : Bool.casesOn (motive := fun _ => Int) (Nat.beq (qy - qx).toNat 0) qx qy =
      min qx qy := by
    simp only [casesOn_eq_ite, natBeq_eq, decide_eq_true_eq]
    split_ifs <;> omega
  have hax : (qx - min qx qy).toNat = (qx - qy).toNat := by omega
  have hay : (qy - min qx qy).toNat = (qy - qx).toNat := by omega
  have hx := finiteValue_aligned sx cx (min_le_left qx qy)
  have hy := finiteValue_aligned sy cy (min_le_right qx qy)
  rw [hax] at hx
  rw [hay] at hy
  have hspec : Arithmetic.add f mode (.finite sx cx qx) (.finite sy cy qy) =
      DecimalInterchange.project f mode
        (Datum.finiteValue sx cx qx + Datum.finiteValue sy cy qy) (min qx qy)
        (Arithmetic.zeroSumSign mode sx sy) := rfl
  rw [hspec, hx, hy, project_sum, addFinite, hmin]
  rfl

/-- `addFields` is the specified sum of two finite data. -/
theorem addFields_eq (f : Format) (mode : RoundingMode) (sx : Bool) (cx : Nat) (qx : Int)
    (sy : Bool) (cy : Nat) (qy : Int) :
    addFields f mode sx cx qx sy cy qy =
      Arithmetic.add f mode (.finite sx cx qx) (.finite sy cy qy) := by
  rw [addFields, gaps_eq]
  exact addFinite_eq f mode sx cx qx sy cy qy

/--
Decimal addition is its kernel form, for every format, rounding direction and pair of data: the
same datum and the same flags.
-/
@[kernel_optimize] theorem add_eq (f : Format) (mode : RoundingMode) (x y : Datum) :
    Arithmetic.add f mode x y = add f mode x y := by
  cases x <;> cases y <;> first | rfl | exact (addFields_eq ..).symm

/--
Decimal subtraction is its kernel form, for every format, rounding direction and pair of data:
the same datum and the same flags.
-/
@[kernel_optimize] theorem sub_eq (f : Format) (mode : RoundingMode) (x y : Datum) :
    Arithmetic.sub f mode x y = sub f mode x y := by
  cases x <;> cases y <;>
    first
      | rfl
      | (rename_i sx cx qx sy cy qy
         cases sy <;> exact (addFields_eq f mode sx cx qx _ cy qy).symm)

/-- The product of two finite values is the finite value of the product of the coefficients. -/
theorem finiteValue_mul (sx sy : Bool) (cx cy : Nat) (qx qy : Int) :
    Datum.finiteValue sx cx qx * Datum.finiteValue sy cy qy =
      Datum.finiteValue (sx ^^ sy) (cx * cy) (qx + qy) := by
  cases sx <;> cases sy <;>
    simp only [Datum.finiteValue, Bool.false_eq_true, ↓reduceIte, Bool.xor_false,
      Bool.xor_true, Bool.not_false, Bool.not_true] <;>
    push_cast <;> rw [zpow_add₀ (by norm_num : (10 : ℚ) ≠ 0)] <;> ring

/--
Decimal multiplication is its kernel form, for every format, rounding direction and pair of
data: the same datum and the same flags.
-/
@[kernel_optimize] theorem mul_eq (f : Format) (mode : RoundingMode) (x y : Datum) :
    Arithmetic.mul f mode x y = mul f mode x y := by
  cases x <;> cases y <;> try rfl
  rename_i sx cx qx sy cy qy
  have hvalue := finiteValue_mul sx sy cx cy qx qy
  have hspec : Arithmetic.mul f mode (.finite sx cx qx) (.finite sy cy qy) =
      DecimalInterchange.project f mode
        (Datum.finiteValue sx cx qx * Datum.finiteValue sy cy qy) (qx + qy) (sx ^^ sy) := rfl
  have hkernel : mul f mode (.finite sx cx qx) (.finite sy cy qy) =
      offsets3 qx qy f.bias fun above below =>
        projectAt f mode (differ sx sy) (cx * cy) (quantumAt above f.bias) above below
          f.exponentBound (10 ^ f.precision) := rfl
  rw [hspec, hkernel, hvalue, offsets3_eq, differ_eq,
    project_finiteValue f mode _ _ (cx * cy) (qx + qy) (fun _ => rfl), project_eq]
  by_cases hb : (-(qx + qy + f.bias)).toNat = 0
  · have hq : quantumAt (qx + qy + f.bias).toNat f.bias = qx + qy := by
      rw [quantumAt_eq]
      omega
    rw [hq]
    exact (projectAt_eq f mode _ (cx * cy) (by omega) (by omega)).symm
  · rw [projectAt_of_below_ne_zero f mode _ (cx * cy) _ (qx + qy) _ hb]
    exact (projectAt_eq f mode _ (cx * cy) (by omega) (by omega)).symm

/--
The decimal fused multiply-add is its kernel form, for every format, rounding direction and
three data: the same datum and the same flags. For three finite data it is the sum of the exact
product and the third datum, rounded once.
-/
@[kernel_optimize] theorem fma_eq (f : Format) (mode : RoundingMode) (x y z : Datum) :
    Arithmetic.fma f mode x y z = fma f mode x y z := by
  cases x <;> cases y <;> cases z <;> try rfl
  rename_i sx cx qx sy cy qy sz cz qz
  change Arithmetic.fma f mode (.finite sx cx qx) (.finite sy cy qy) (.finite sz cz qz) =
    addFields f mode (differ sx sy) (cx * cy) (qx + qy) sz cz qz
  rw [addFields_eq, differ_eq]
  change DecimalInterchange.project f mode
      (Datum.finiteValue sx cx qx * Datum.finiteValue sy cy qy + Datum.finiteValue sz cz qz)
      (min (qx + qy) qz) (Arithmetic.zeroSumSign mode (sx ^^ sy) sz) =
    DecimalInterchange.project f mode
      (Datum.finiteValue (sx ^^ sy) (cx * cy) (qx + qy) + Datum.finiteValue sz cz qz)
      (min (qx + qy) qz) (Arithmetic.zeroSumSign mode (sx ^^ sy) sz)
  rw [finiteValue_mul]

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath
