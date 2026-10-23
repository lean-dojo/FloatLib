/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.RationalPower.Exact.Runtime
public import FloatLib.Numerics.Exact.IntegerRoot.Proof
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Correctness of exact rational-power classification

Let `base = A / B` and `exponent = n / d` be in lowest terms. If `base ^ exponent` equals a
rational `q`, then `q ^ d = base ^ n`. Comparing reduced numerators and denominators gives
`A ^ |n| = C ^ d` and `B ^ |n| = D ^ d` for the parts `C` and `D` of `q` or of `q⁻¹`. Since
`|n|` and `d` are coprime, Mathlib's `Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow` makes
`A` and `B` perfect `d`-th powers. Hence a missing descriptor proves irrationality. Mathlib's
`irrational_nrt_of_notint_nrt` needs an integer radicand, so this module proves the rational
criterion itself.

Capped exponentiation is proved against the closed form `if base ^ exponent ≤ cap then ...`.
The proofs reason about that power symbolically and never evaluate it.

The dyadic builder is exact in both directions. A built value is the described power. When none is
built, either the root's denominator has an odd prime factor, which divides the denominator of
every positive power, or the odd part of the power is at least `2 ^ (precision + 3)`, and every
dyadic equal to the power then has a significand at least that large.
-/

@[expose] public section

namespace FloatLib.Numerics.RationalPower

/-- For a positive degree, the root test returns `root` exactly when `root ^ degree = value`. -/
theorem perfectRoot?_eq_some_iff {degree value root : Nat} (hdegree : 0 < degree) :
    perfectRoot? degree value = some root ↔ root ^ degree = value := by
  have hsmallPower : ∀ r : Nat, r ≤ 1 → r ^ degree = r := by
    intro r hr
    interval_cases r <;> simp [zero_pow hdegree.ne']
  have htwo : ∀ r : Nat, ¬r ≤ 1 → 2 ^ degree ≤ r ^ degree := fun r hr =>
    Nat.pow_le_pow_left (by omega) degree
  have hdegreeTwo : 2 ≤ 2 ^ degree := Nat.le_self_pow hdegree.ne' 2
  unfold perfectRoot?
  split
  · rename_i hsmall
    rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact hsmallPower _ hsmall
    · intro hpower
      have hroot : root ≤ 1 := by
        by_contra hroot
        have := htwo root hroot
        omega
      rw [hsmallPower root hroot] at hpower
      exact hpower.symm
  · rename_i hsmall
    split
    · rename_i hbits
      simp only [reduceCtorEq, false_iff]
      intro hpower
      have hvalue : value < 2 ^ degree := (Nat.log2_lt (by omega)).mp hbits
      have hroot : ¬root ≤ 1 := by
        intro hroot
        rw [hsmallPower root hroot] at hpower
        omega
      have := htwo root hroot
      omega
    · dsimp only
      rw [IntegerRoot.newton_eq_nthRoot]
      split
      · rename_i hexact
        rw [Option.some.injEq]
        constructor
        · rintro rfl
          exact hexact
        · rintro rfl
          exact Nat.nthRoot_pow hdegree.ne' root
      · rename_i hexact
        simp only [reduceCtorEq, false_iff]
        rintro rfl
        exact hexact (by rw [Nat.nthRoot_pow hdegree.ne'])

/-- Capped exponentiation returns the power exactly when it does not exceed the cap. -/
theorem cappedPow?_eq (base exponent cap : Nat) (hbase : 1 ≤ base) :
    cappedPow? base exponent cap =
      if base ^ exponent ≤ cap then some (base ^ exponent) else none := by
  induction exponent using Nat.strong_induction_on with
  | _ exponent ih =>
    rw [cappedPow?]
    split
    · rename_i hzero
      subst hzero
      simp
    · rename_i hzero
      rw [ih (exponent / 2) (by omega)]
      have hsplit : base ^ exponent =
          base ^ (exponent / 2) * base ^ (exponent / 2) * base ^ (exponent % 2) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      by_cases hhalf : base ^ (exponent / 2) ≤ cap
      · rw [ite_eq_left hhalf]
        dsimp only
        have hpower : (if exponent % 2 = 0 then base ^ (exponent / 2) * base ^ (exponent / 2)
            else base ^ (exponent / 2) * base ^ (exponent / 2) * base) = base ^ exponent := by
          rw [hsplit]
          split
          · rename_i heven
            rw [heven, pow_zero, mul_one]
          · rename_i hodd
            rw [show exponent % 2 = 1 by omega, pow_one]
        rw [hpower]
      · rw [ite_eq_right hhalf]
        dsimp only
        have hle : base ^ (exponent / 2) ≤ base ^ exponent :=
          Nat.pow_le_pow_right hbase (Nat.div_le_self _ _)
        rw [ite_eq_right (by omega)]

/-- The capped equality test decides `base ^ exponent = target`. -/
theorem natPowEq_iff (base exponent target : Nat) :
    natPowEq base exponent target = true ↔ base ^ exponent = target := by
  unfold natPowEq
  split
  · rename_i hbase
    split
    · rename_i hzero
      subst hzero
      simp [eq_comm]
    · rename_i hzero
      have hpower : base ^ exponent = base := by
        interval_cases base <;> simp [zero_pow hzero]
      rw [hpower, decide_eq_true_iff, eq_comm]
  · rename_i hbase
    split
    · rename_i hbits
      simp only [Bool.false_eq_true, false_iff]
      intro hpower
      have hlower : 2 ^ (exponent * base.log2) ≤ base ^ exponent := by
        rw [Nat.mul_comm, pow_mul]
        exact Nat.pow_le_pow_left (Nat.log2_self_le (by omega)) exponent
      have hbound : 2 ^ (target.log2 + 1) ≤ 2 ^ (exponent * base.log2) :=
        Nat.pow_le_pow_right (by decide) hbits
      have htarget : target < 2 ^ (target.log2 + 1) := Nat.lt_log2_self
      omega
    · rw [cappedPow?_eq base exponent target (by omega), decide_eq_true_iff]
      split
      · rename_i hle
        rw [Option.some.injEq]
      · rename_i hgt
        simp only [reduceCtorEq, false_iff]
        omega

/-- Raising a positive rational power to its exponent denominator clears that denominator. -/
theorem rpow_pow_den (base exponent : ℚ) (hbase : 0 < base) :
    ((base : ℝ) ^ (exponent : ℝ)) ^ exponent.den = ((base ^ exponent.num : ℚ) : ℝ) := by
  have hbaseReal : 0 < (base : ℝ) := by exact_mod_cast hbase
  have hden : (exponent.den : ℝ) ≠ 0 := by exact_mod_cast exponent.den_ne_zero
  have hexponent : (exponent : ℝ) * exponent.den = exponent.num := by
    rw [Rat.cast_def, div_mul_cancel₀ _ hden]
  rw [← Real.rpow_mul_natCast hbaseReal.le, hexponent, Real.rpow_intCast]
  norm_cast

/--
If a rational power `s ^ d` equals `base ^ m` with coprime exponents, then the numerator and the
denominator of the base are perfect `d`-th powers.
-/
private theorem perfect_of_pow_eq_pow {base s : ℚ} {m d : Nat} (hcoprime : m.Coprime d)
    (hpower : s ^ d = base ^ m) :
    (∃ c, base.num.natAbs = c ^ d) ∧ ∃ c, base.den = c ^ d := by
  constructor
  · have hnum : base.num.natAbs ^ m = s.num.natAbs ^ d := by
      have := congrArg (fun q : ℚ => q.num.natAbs) hpower
      simpa only [Rat.num_pow, Int.natAbs_pow] using this.symm
    obtain ⟨c, hc, -⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow hcoprime hnum
    exact ⟨c, hc⟩
  · have hden : base.den ^ m = s.den ^ d := by
      have := congrArg Rat.den hpower
      simpa only [Rat.den_pow] using this.symm
    obtain ⟨c, hc, -⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow hcoprime hden
    exact ⟨c, hc⟩

/-- A descriptor's root is a nonnegative `d`-th root of the base, and it keeps the numerator. -/
private theorem root_of_exactRoot? {base exponent : ℚ} {exact : ExactRoot} (hbase : 0 ≤ base)
    (h : exactRoot? base exponent = some exact) :
    exact.root ^ exponent.den = base ∧ 0 ≤ exact.root ∧ exact.numerator = exponent.num := by
  unfold exactRoot? at h
  split at h
  · rename_i numerator denominator hnumerator hdenominator
    rw [Option.some.injEq] at h
    subst h
    have hnum := (perfectRoot?_eq_some_iff exponent.den_pos).mp hnumerator
    have hden := (perfectRoot?_eq_some_iff exponent.den_pos).mp hdenominator
    refine ⟨?_, by positivity, rfl⟩
    have hnumCast : ((base.num.natAbs : ℕ) : ℚ) = (base.num : ℚ) := by
      rw [Nat.cast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hbase)]
    rw [div_pow, ← Nat.cast_pow, ← Nat.cast_pow, hnum, hden, hnumCast]
    exact Rat.num_div_den base
  · simp at h

/-- A descriptor of a positive base has a positive root. -/
theorem root_pos_of_exactRoot?_eq_some {base exponent : ℚ} {exact : ExactRoot} (hbase : 0 < base)
    (h : exactRoot? base exponent = some exact) : 0 < exact.root := by
  obtain ⟨hroot, hnonneg, -⟩ := root_of_exactRoot? hbase.le h
  rcases hnonneg.lt_or_eq with hpos | hzero
  · exact hpos
  · rw [← hzero, zero_pow exponent.den_ne_zero] at hroot
    exact absurd hroot hbase.ne

/--
The exact-root classification is complete: a descriptor gives the real power as an integer power
of a rational root, and no descriptor means that the real power is irrational.
-/
theorem exactRoot?_spec (base exponent : ℚ) (hbase : 0 < base) :
    match exactRoot? base exponent with
    | some exact => (base : ℝ) ^ (exponent : ℝ) = (exact.root : ℝ) ^ exact.numerator
    | none => Irrational ((base : ℝ) ^ (exponent : ℝ)) := by
  cases h : exactRoot? base exponent with
  | some exact =>
    show (base : ℝ) ^ (exponent : ℝ) = (exact.root : ℝ) ^ exact.numerator
    obtain ⟨hroot, hnonneg, hnumerator⟩ := root_of_exactRoot? hbase.le h
    have hrootReal : 0 ≤ (exact.root : ℝ) := by exact_mod_cast hnonneg
    have hden : (exponent.den : ℝ) ≠ 0 := by exact_mod_cast exponent.den_ne_zero
    have hbaseReal : (base : ℝ) = (exact.root : ℝ) ^ exponent.den := by
      rw [← hroot, Rat.cast_pow]
    have hexponent : (exponent.den : ℝ) * (exponent : ℝ) = exponent.num := by
      rw [mul_comm, Rat.cast_def, div_mul_cancel₀ _ hden]
    rw [hbaseReal, ← Real.rpow_natCast_mul hrootReal, hexponent, Real.rpow_intCast, hnumerator]
  | none =>
    show Irrational ((base : ℝ) ^ (exponent : ℝ))
    rintro ⟨q, hq⟩
    have hpower : q ^ exponent.den = base ^ exponent.num := by
      have := rpow_pow_den base exponent hbase
      rw [← hq] at this
      exact_mod_cast this
    have hcoprime := exponent.reduced
    have hperfect : (∃ c, base.num.natAbs = c ^ exponent.den) ∧
        ∃ c, base.den = c ^ exponent.den := by
      rcases Int.natAbs_eq exponent.num with hsign | hsign
      · rw [hsign, zpow_natCast] at hpower
        exact perfect_of_pow_eq_pow hcoprime hpower
      · rw [hsign, zpow_neg, zpow_natCast] at hpower
        apply perfect_of_pow_eq_pow (s := q⁻¹) hcoprime
        rw [inv_pow, hpower, inv_inv]
    obtain ⟨⟨numerator, hnumerator⟩, ⟨denominator, hdenominator⟩⟩ := hperfect
    unfold exactRoot? at h
    rw [(perfectRoot?_eq_some_iff exponent.den_pos).mpr hnumerator.symm,
      (perfectRoot?_eq_some_iff exponent.den_pos).mpr hdenominator.symm] at h
    simp at h

/--
Removing the trailing zeros of a positive numerator leaves a positive odd factor, and the numerator
is that factor times the removed power of two.
-/
private theorem oddPart_spec {base : ℚ} (hbase : 0 < base) :
    0 < base.num >>> base.num.trailingZeros ∧
      (base.num >>> base.num.trailingZeros).natAbs % 2 = 1 ∧
      base.num = (base.num >>> base.num.trailingZeros) * 2 ^ base.num.trailingZeros := by
  have hnum : base.num ≠ 0 := (Rat.num_pos.mpr hbase).ne'
  have hdiv : base.num >>> base.num.trailingZeros = base.num / 2 ^ base.num.trailingZeros :=
    Int.shiftRight_eq_div_pow _ _
  have hodd := Int.shiftRight_trailingZeros_mod_two hnum
  have hnonneg : 0 ≤ base.num >>> base.num.trailingZeros := by
    rw [hdiv]
    exact Int.ediv_nonneg (Rat.num_nonneg.mpr hbase.le) (by positivity)
  have hpositive : 0 < base.num >>> base.num.trailingZeros := by
    rcases hnonneg.lt_or_eq with hpos | hzero
    · exact hpos
    · rw [← hzero] at hodd
      simp at hodd
  refine ⟨hpositive, ?_, ?_⟩
  · have hcast : ((base.num >>> base.num.trailingZeros).natAbs : ℤ) =
        base.num >>> base.num.trailingZeros := Int.natAbs_of_nonneg hnonneg
    omega
  · rw [hdiv, Int.ediv_mul_cancel (Int.two_pow_trailingZeros_dvd hnum)]

/-- A natural number times a power of two is not a larger odd number times a power of two. -/
private theorem natCast_mul_zpow_ne_odd {significand odd : Nat} (hodd : odd % 2 = 1)
    (hlt : significand < odd) (exponent other : Int) :
    (significand : ℚ) * 2 ^ exponent ≠ (odd : ℚ) * 2 ^ other := by
  intro hvalue
  have hshift : (significand : ℚ) * 2 ^ (exponent - other) = odd := by
    rw [zpow_sub₀ two_ne_zero, mul_div_assoc', hvalue,
      mul_div_cancel_right₀ _ (zpow_ne_zero _ two_ne_zero)]
  rcases le_or_gt 0 (exponent - other) with hnonneg | hnegative
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnonneg
    rw [hn, zpow_natCast] at hshift
    have hnat : significand * 2 ^ n = odd := by exact_mod_cast hshift
    rcases n with _ | n
    · rw [pow_zero, mul_one] at hnat
      omega
    · obtain ⟨c, hc⟩ : 2 ∣ odd := ⟨significand * 2 ^ n, by rw [← hnat, pow_succ]; ring⟩
      omega
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hnegative.le
    rw [hn, zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_eq_iff (by positivity)] at hshift
    have hnat : significand = odd * 2 ^ n := by exact_mod_cast hshift
    have hle : odd ≤ odd * 2 ^ n := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos n)
    omega

/-- A positive power of a rational whose denominator is not a power of two is not a dyadic. -/
private theorem natCast_mul_zpow_ne_of_den {base : ℚ} {exponent : Nat} (hbase : 0 < base)
    (hexponent : exponent ≠ 0) (hden : base.den ≠ 2 ^ base.den.log2)
    (significand : Nat) (scale : Int) :
    (significand : ℚ) * 2 ^ scale ≠ base ^ exponent := by
  intro hvalue
  have hscale : scale = (scale.toNat : Int) - ((-scale).toNat : Int) :=
    (Int.toNat_sub_toNat_neg scale).symm
  have hnumCast : ((base.num.natAbs : ℕ) : ℚ) = (base.num : ℚ) := by
    rw [Nat.cast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hbase.le)]
  have hbaseValue : base = (base.num.natAbs : ℚ) / (base.den : ℚ) := by
    rw [hnumCast]
    exact (Rat.num_div_den base).symm
  have hcross : significand * 2 ^ scale.toNat * base.den ^ exponent =
      base.num.natAbs ^ exponent * 2 ^ (-scale).toNat := by
    rw [hscale, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, hbaseValue, div_pow,
      mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)] at hvalue
    exact_mod_cast hvalue
  have hdvd : base.den ^ exponent ∣ 2 ^ (-scale).toNat := by
    have hcoprime : (base.den ^ exponent).Coprime (base.num.natAbs ^ exponent) :=
      Nat.Coprime.pow _ _ base.reduced.symm
    exact hcoprime.dvd_of_dvd_mul_left
      ⟨significand * 2 ^ scale.toNat, by rw [← hcross]; ring⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    ((dvd_pow_self base.den hexponent).trans hdvd)
  exact hden (by rw [hi, Nat.log2_two_pow])

namespace ExactRoot

/-- The described power is the natural power `|numerator|` of `powerBase`. -/
theorem zpow_eq_powerBase_pow (exact : ExactRoot) :
    exact.root ^ exact.numerator = exact.powerBase ^ exact.numerator.natAbs := by
  unfold powerBase
  split
  · rename_i hnonneg
    rw [← zpow_natCast, Int.natAbs_of_nonneg hnonneg]
  · rename_i hnegative
    rw [inv_pow, ← zpow_natCast, ← zpow_neg, Int.ofNat_natAbs_of_nonpos (by omega), neg_neg]

/-- A positive root has a positive power base. -/
theorem powerBase_pos (exact : ExactRoot) (hroot : 0 < exact.root) : 0 < exact.powerBase := by
  unfold powerBase
  split <;> positivity

/-- For a positive root, the capped test decides equality of the described power and a target. -/
theorem powEq_iff (exact : ExactRoot) (target : ℚ) (hroot : 0 < exact.root) :
    exact.powEq target = true ↔ exact.root ^ exact.numerator = target := by
  rw [zpow_eq_powerBase_pow]
  have hbase := exact.powerBase_pos hroot
  unfold powEq
  simp only [Bool.and_eq_true, decide_eq_true_eq, natPowEq_iff]
  constructor
  · rintro ⟨⟨htarget, hnum⟩, hden⟩
    apply Rat.ext
    · have hnonneg : 0 ≤ (exact.powerBase ^ exact.numerator.natAbs).num :=
        Rat.num_nonneg.mpr (pow_nonneg hbase.le _)
      have habs : (exact.powerBase ^ exact.numerator.natAbs).num.natAbs = target.num.natAbs := by
        rw [Rat.num_pow, Int.natAbs_pow, hnum]
      have hcast := congrArg (fun n : ℕ => (n : ℤ)) habs
      simp only [Int.natAbs_of_nonneg hnonneg,
        Int.natAbs_of_nonneg (Rat.num_nonneg.mpr htarget.le)] at hcast
      exact hcast
    · rw [Rat.den_pow, hden]
  · rintro rfl
    exact ⟨⟨pow_pos hbase _, by rw [Rat.num_pow, Int.natAbs_pow]⟩, by rw [Rat.den_pow]⟩

/--
When the denominator of the power base is a power of two, the described power is the power of
the numerator's odd part times a power of two.
-/
private theorem powerBase_pow_eq_odd (exact : ExactRoot) (hroot : 0 < exact.root)
    (hden : exact.powerBase.den = 2 ^ exact.powerBase.den.log2) :
    exact.powerBase ^ exact.numerator.natAbs =
      (((exact.powerBase.num >>> exact.powerBase.num.trailingZeros).natAbs ^
          exact.numerator.natAbs : ℕ) : ℚ) *
        2 ^ (((exact.powerBase.num.trailingZeros : Int) - exact.powerBase.den.log2) *
          exact.numerator.natAbs) := by
  have hbase := exact.powerBase_pos hroot
  obtain ⟨hpositive, -, hsplit⟩ := oddPart_spec hbase
  set scale := exact.powerBase.den.log2
  set shift := exact.powerBase.num.trailingZeros
  set oddPart := exact.powerBase.num >>> shift
  have hdenPow : (exact.powerBase.den : ℚ) = 2 ^ scale := by
    exact_mod_cast hden
  have hoddCast : ((oddPart.natAbs : ℕ) : ℚ) = (oddPart : ℚ) := by
    rw [Nat.cast_natAbs, abs_of_nonneg hpositive.le]
  have hbaseValue : exact.powerBase = (oddPart.natAbs : ℚ) * 2 ^ ((shift : Int) - scale) := by
    have hnumCast : (exact.powerBase.num : ℚ) = (oddPart : ℚ) * 2 ^ shift := by
      exact_mod_cast hsplit
    rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, mul_div_assoc', ← hdenPow,
      hoddCast, ← hnumCast]
    exact (Rat.num_div_den _).symm
  rw [hbaseValue, mul_pow, Nat.cast_pow]
  congr 1
  rw [← zpow_natCast, ← zpow_mul]

/--
An exact dyadic built from a descriptor denotes the described power, with a nonnegative sign and
a significand below `2 ^ (precision + 3)`.
-/
theorem toDyadic?_spec (exact : ExactRoot) (precision : Nat) {value : Dyadic}
    (hroot : 0 < exact.root) (h : exact.toDyadic? precision = some value) :
    value.toRat = exact.root ^ exact.numerator ∧ value.negative = false ∧
      value.significand < 2 ^ (precision + 3) := by
  have hbase := exact.powerBase_pos hroot
  obtain ⟨hpositive, -, -⟩ := oddPart_spec hbase
  unfold toDyadic? at h
  dsimp only at h
  split at h
  · simp at h
  rename_i hdenominatorTest
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i significand hpower
  rw [Option.some.injEq] at h
  subst h
  rw [cappedPow?_eq _ _ _ (Int.natAbs_pos.mpr hpositive.ne')] at hpower
  split at hpower
  · rename_i hbound
    rw [Option.some.injEq] at hpower
    subst hpower
    refine ⟨?_, rfl, ?_⟩
    · rw [Dyadic.toRat_mk_false, zpow_eq_powerBase_pow]
      by_cases hzero : exact.numerator.natAbs = 0
      · rw [hzero]
        simp
      have hden : exact.powerBase.den = 2 ^ exact.powerBase.den.log2 := by
        by_contra hne
        exact hdenominatorTest ⟨hzero, hne⟩
      rw [powerBase_pow_eq_odd exact hroot hden]
    · show _ ^ exact.numerator.natAbs < 2 ^ (precision + 3)
      have := Nat.one_le_two_pow (n := precision + 3)
      omega
  · simp at hpower

/--
When no dyadic is built, the described power is not a dyadic with a significand below
`2 ^ (precision + 3)`, so it is not a cell boundary of a `precision`-bit binary format.
-/
theorem ne_of_toDyadic?_eq_none (exact : ExactRoot) (precision : Nat) (hroot : 0 < exact.root)
    (h : exact.toDyadic? precision = none) {significand : Nat} (scale : Int)
    (hsignificand : significand < 2 ^ (precision + 3)) :
    (significand : ℚ) * 2 ^ scale ≠ exact.root ^ exact.numerator := by
  rw [zpow_eq_powerBase_pow]
  have hbase := exact.powerBase_pos hroot
  obtain ⟨hpositive, hodd, -⟩ := oddPart_spec hbase
  have hoddPositive : 1 ≤ (exact.powerBase.num >>> exact.powerBase.num.trailingZeros).natAbs :=
    Int.natAbs_pos.mpr hpositive.ne'
  unfold toDyadic? at h
  dsimp only at h
  split at h
  · rename_i hdenominatorTest
    exact natCast_mul_zpow_ne_of_den hbase hdenominatorTest.1 hdenominatorTest.2 significand scale
  rename_i hdenominatorTest
  have hlarge : exact.numerator.natAbs ≠ 0 ∧ 2 ^ (precision + 3) ≤
      (exact.powerBase.num >>> exact.powerBase.num.trailingZeros).natAbs ^
        exact.numerator.natAbs := by
    split at h
    · rename_i hbits
      have hnonzero : exact.numerator.natAbs ≠ 0 := by
        intro hzero
        rw [hzero, Nat.zero_mul] at hbits
        omega
      refine ⟨hnonzero, ?_⟩
      calc 2 ^ (precision + 3)
          ≤ 2 ^ (exact.numerator.natAbs *
              (exact.powerBase.num >>> exact.powerBase.num.trailingZeros).natAbs.log2) :=
            Nat.pow_le_pow_right (by decide) hbits
        _ = (2 ^ (exact.powerBase.num >>> exact.powerBase.num.trailingZeros).natAbs.log2) ^
              exact.numerator.natAbs := by rw [Nat.mul_comm, pow_mul]
        _ ≤ _ := Nat.pow_le_pow_left (Nat.log2_self_le (by omega)) _
    · split at h
      · rename_i hcapped
        rw [cappedPow?_eq _ _ _ hoddPositive] at hcapped
        split at hcapped
        · simp at hcapped
        · rename_i hbound
          have hnonzero : exact.numerator.natAbs ≠ 0 := by
            intro hzero
            rw [hzero, pow_zero] at hbound
            have := Nat.one_le_two_pow (n := precision + 3)
            have : 2 ≤ 2 ^ (precision + 3) := Nat.le_self_pow (by omega) 2
            omega
          exact ⟨hnonzero, by omega⟩
      · simp at h
  have hden : exact.powerBase.den = 2 ^ exact.powerBase.den.log2 := by
    by_contra hne
    exact hdenominatorTest ⟨hlarge.1, hne⟩
  rw [powerBase_pow_eq_odd exact hroot hden]
  have hoddPower : ((exact.powerBase.num >>> exact.powerBase.num.trailingZeros).natAbs ^
      exact.numerator.natAbs) % 2 = 1 := by
    rw [Nat.pow_mod, hodd, Nat.one_pow]
  exact natCast_mul_zpow_ne_odd hoddPower (lt_of_lt_of_le hsignificand hlarge.2) scale _

end ExactRoot

/-- For a positive base, the equality test decides the real-power boundary equation. -/
theorem powEq_iff (base exponent target : ℚ) (hbase : 0 < base) :
    powEq base exponent target = true ↔ (base : ℝ) ^ (exponent : ℝ) = (target : ℝ) := by
  have hspec := exactRoot?_spec base exponent hbase
  unfold powEq
  cases h : exactRoot? base exponent with
  | some exact =>
    rw [h] at hspec
    change (base : ℝ) ^ (exponent : ℝ) = (exact.root : ℝ) ^ exact.numerator at hspec
    change exact.powEq target = true ↔ _
    rw [hspec, exact.powEq_iff target (root_pos_of_exactRoot?_eq_some hbase h), ← Rat.cast_zpow,
      Rat.cast_inj]
  | none =>
    rw [h] at hspec
    change Irrational ((base : ℝ) ^ (exponent : ℝ)) at hspec
    change false = true ↔ _
    simp only [Bool.false_eq_true, false_iff]
    exact hspec.ne_rat target

end FloatLib.Numerics.RationalPower
