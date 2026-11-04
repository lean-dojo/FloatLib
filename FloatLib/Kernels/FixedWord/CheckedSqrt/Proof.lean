/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.CheckedSqrt.Runtime
public import FloatLib.Kernels.FixedWord.Difference.Proof
public import FloatLib.Kernels.FixedWord.Product.Proof
public import FloatLib.Kernels.FixedWord.RestoringSqrt.Proof
public import FloatLib.Kernels.FixedWord.LimbRound.Proof
public import Mathlib.Data.Nat.Sqrt

/-!
# Correctness of checked square roots

An accepted candidate is the floor square root with its exact remainder (`checkRoot?_spec`,
`acceptRootWide?_spec`). Both `rootAndRemainder` and `Internal.rootAndRemainder` equal the restoring
loop on every input, which is what the compiler substitution in `CheckedSqrt.Compiler` relies on.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord.CheckedSquareRoot

open FloatLib.Numerics.FixedWord

private theorem toNat_of_hi_eq_zero {x : UInt128} (h : x.hi = 0) :
    x.lo.toNat = x.toNat := by
  simp [UInt128.toNat, h]

/-- A four-word value with zero upper limbs is below `2^128`. -/
private theorem toNat_lt_of_limb3_limb2_eq_zero {x : UInt256}
    (h3 : x.limb3 = 0) (h2 : x.limb2 = 0) :
    x.toNat < 2 ^ 128 := by
  have h0 := x.limb0.toNat_lt
  have h1 := x.limb1.toNat_lt
  unfold UInt256.toNat
  simp only [h3, h2, UInt64.toNat_zero, zero_mul, add_zero]
  omega

/-- A candidate whose square is at most `n`, with remainder at most twice the candidate, is the
floor square root of `n`. -/
private theorem eq_sqrt_of_sub_le {guess n : Nat} (hle : guess * guess ≤ n)
    (hremainder : n - guess * guess ≤ guess + guess) :
    guess = Nat.sqrt n := by
  apply Nat.eq_sqrt.mpr
  refine ⟨hle, ?_⟩
  have : (guess + 1) * (guess + 1) = guess * guess + (guess + guess) + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
  omega

/-- An accepted candidate is the floor square root, with the exact remainder. -/
theorem checkRoot?_spec {radicand : UInt128} {guess : UInt64}
    {state : RestoringRootState UInt64} (h : checkRoot? radicand guess = some state) :
    state.root.toNat = Nat.sqrt radicand.toNat ∧
      state.remainder.toNat =
        radicand.toNat - Nat.sqrt radicand.toNat * Nat.sqrt radicand.toNat := by
  unfold checkRoot? at h
  dsimp only at h
  split at h
  · rename_i hsmall
    have hg : guess.toNat < 2 ^ 62 := by
      have := UInt64.lt_iff_toNat_lt.mp hsmall; simpa using this
    split at h
    · rename_i hless
      rw [UInt128.less_eq_true_iff,
        mul64_toNat] at hless
      split at h
      · simp at h
      · rename_i hzero
        have hgpos : 0 < guess.toNat := by
          rcases Nat.eq_zero_or_pos guess.toNat with h0 | h0
          · exact absurd (by simpa using UInt64.toNat_inj.mp (h0.trans UInt64.toNat_zero.symm))
              hzero
          · exact h0
        have hprev : (guess - 1).toNat = guess.toNat - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
          simp
        split at h
        · simp at h
        · rename_i hless'
          rw [UInt128.less_eq_true_iff,
            mul64_toNat, hprev] at hless'
          have hle : (guess.toNat - 1) * (guess.toNat - 1) ≤ radicand.toNat := by omega
          have hroot : guess.toNat - 1 = Nat.sqrt radicand.toNat := by
            apply Nat.eq_sqrt.mpr
            refine ⟨hle, ?_⟩
            rw [show guess.toNat - 1 + 1 = guess.toNat by omega]; exact hless
          split at h
          · rename_i hrem
            simp only [Option.some.injEq] at h
            subst h
            simp only [Bool.and_eq_true, beq_iff_eq] at hrem
            refine ⟨by rw [hprev, hroot], ?_⟩
            rw [toNat_of_hi_eq_zero hrem.1, UInt128.sub_toNat _ _
              (by rw [mul64_toNat, hprev]; exact hle),
              mul64_toNat, hprev, ← hroot]
          · simp at h
    · rename_i hless
      rw [UInt128.less_eq_true_iff,
        mul64_toNat] at hless
      have hle : guess.toNat * guess.toNat ≤ radicand.toNat := by omega
      split at h
      · rename_i hrem
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq, UInt64.le_iff_toNat_le, decide_eq_true_eq] at hrem
        have hsub := UInt128.sub_toNat radicand
          (mul64 guess guess)
          (by rw [mul64_toNat]; exact hle)
        rw [mul64_toNat] at hsub
        have hdouble : (guess + guess).toNat = guess.toNat + guess.toNat := by
          rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
        have hremNat : radicand.toNat - guess.toNat * guess.toNat ≤ guess.toNat + guess.toNat := by
          rw [← hsub, ← toNat_of_hi_eq_zero hrem.1, ← hdouble]; exact hrem.2
        have hroot := eq_sqrt_of_sub_le hle hremNat
        refine ⟨hroot, ?_⟩
        rw [toNat_of_hi_eq_zero hrem.1, hsub, ← hroot]
      · simp at h
  · simp at h

/--
A two-word state that carries the floor square root of the radicand and its remainder is the
restoring loop's result, within the loop's range.
-/
private theorem eq_loop_of_spec {radicand : UInt256} {steps : Nat}
    (hupper : steps ≤ 125) (hfit : radicand.toNat < 2 ^ (2 * steps))
    {state : RestoringRootState UInt128}
    (hroot : state.root.toNat = Nat.sqrt radicand.toNat)
    (hrem : state.remainder.toNat =
      radicand.toNat - Nat.sqrt radicand.toNat * Nat.sqrt radicand.toNat) :
    state = RestoringSquareRoot.rootAndRemainder radicand steps := by
  obtain ⟨hroot', hrem'⟩ := RestoringSquareRoot.rootAndRemainder_spec radicand steps hupper hfit
  cases state
  cases hloop : RestoringSquareRoot.rootAndRemainder radicand steps
  rw [hloop] at hroot' hrem'
  simp only at hroot hrem hroot' hrem' ⊢
  congr 1
  · exact UInt128.toNat_injective (hroot.trans hroot'.symm)
  · exact UInt128.toNat_injective (hrem.trans hrem'.symm)

/-- `rootAndRemainder` equals the restoring loop on every input. -/
theorem rootAndRemainder_eq (radicand : UInt256) (steps : Nat) :
    rootAndRemainder radicand steps =
      RestoringSquareRoot.rootAndRemainder radicand steps := by
  unfold rootAndRemainder
  split
  · rename_i hguard
    dsimp only
    split
    · rename_i state hstate
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hguard
      obtain ⟨⟨⟨hlower, hupper⟩, h3⟩, h2⟩ := hguard
      have hfit128 := toNat_lt_of_limb3_limb2_eq_zero h3 h2
      have hlow := UInt256.low128_toNat_of_lt radicand hfit128
      have hfit : radicand.toNat < 2 ^ (2 * steps) :=
        lt_of_lt_of_le hfit128 (Nat.pow_le_pow_right (by decide) (by omega))
      obtain ⟨hroot, hrem⟩ := checkRoot?_spec hstate
      rw [hlow] at hroot hrem
      exact eq_loop_of_spec hupper hfit (by simpa [UInt128.toNat] using hroot)
        (by simpa [UInt128.toNat] using hrem)
    · rfl
  · rfl

/-- An accepted four-word candidate is the floor square root, with the exact remainder. -/
theorem acceptRootWide?_spec {radicand : UInt256} {guess : UInt128}
    {state : RestoringRootState UInt128} (h : acceptRootWide? radicand guess = some state) :
    state.root.toNat = Nat.sqrt radicand.toNat ∧
      state.remainder.toNat =
        radicand.toNat - Nat.sqrt radicand.toNat * Nat.sqrt radicand.toNat := by
  unfold acceptRootWide? at h
  dsimp only at h
  split at h
  · rename_i hsmall
    have hguess : guess.toNat < 2 ^ 125 := by
      have hhi := UInt64.lt_iff_toNat_lt.mp hsmall
      have hlo := guess.lo.toNat_lt
      simp only [UInt64.reduceToNat] at hhi
      unfold UInt128.toNat
      omega
    split at h
    · simp at h
    · rename_i hless
      rw [UInt256.less_eq_true_iff, mul128_toNat] at hless
      have hle : guess.toNat * guess.toNat ≤ radicand.toNat := by omega
      have hsub := UInt256.sub_toNat radicand (mul128 guess guess) (by rw [mul128_toNat]; exact hle)
      rw [mul128_toNat] at hsub
      split at h
      · rename_i hrem
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hrem
        obtain ⟨⟨h3, h2⟩, hdoubleLe⟩ := hrem
        have hremFit := toNat_lt_of_limb3_limb2_eq_zero h3 h2
        have hlow := UInt256.low128_toNat_of_lt _ hremFit
        have hdouble : (add128 guess guess).value.toNat = guess.toNat + guess.toNat :=
          add128_value_toNat_of_lt guess guess (by omega)
        have hremLe :
            radicand.toNat - guess.toNat * guess.toNat ≤ guess.toNat + guess.toNat := by
          have hnot : ¬(UInt128.less (add128 guess guess).value
              (UInt256.sub radicand (mul128 guess guess)).low128 = true) := by
            rw [hdoubleLe]
            decide
          rw [UInt128.less_eq_true_iff, hdouble, hlow, hsub] at hnot
          omega
        have hroot := eq_sqrt_of_sub_le hle hremLe
        refine ⟨hroot, ?_⟩
        rw [hlow, hsub, ← hroot]
      · simp at h
  · simp at h

/-- `Internal.rootAndRemainder` equals the two-word checked path, hence the loop, on every
input. -/
theorem Internal.rootAndRemainder_eq (radicand : UInt256) (steps : Nat) :
    Internal.rootAndRemainder radicand steps =
      CheckedSquareRoot.rootAndRemainder radicand steps := by
  unfold Internal.rootAndRemainder
  split
  · rename_i hguard
    split
    · rename_i state hstate
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hguard
      obtain ⟨⟨⟨hlower, hupper⟩, _⟩, hlog⟩ := hguard
      rw [CheckedSquareRoot.rootAndRemainder_eq]
      have hfit : radicand.toNat < 2 ^ (2 * steps) := by
        rw [UInt256.log2_toNat] at hlog
        by_cases hzero : radicand.toNat = 0
        · rw [hzero]; exact Nat.two_pow_pos _
        · exact (Nat.lt_log2_self (n := radicand.toNat)).trans_le
            (Nat.pow_le_pow_right (by decide) (by omega))
      obtain ⟨hroot, hrem⟩ := acceptRootWide?_spec hstate
      exact eq_loop_of_spec hupper hfit hroot hrem
    · rfl
  · rfl

end FloatLib.Numerics.FixedWord.CheckedSquareRoot
