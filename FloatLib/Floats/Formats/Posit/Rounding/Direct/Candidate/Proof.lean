/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Candidate.Runtime
import FloatLib.Kernels.FixedWord.Core.Proof.Word
import all Init.Data.Fin.Log2
import all Init.Data.UInt.Log2

/-!
# Correctness of direct posit field construction

These theorems connect adaptive leading-bit discovery and direct field packing to their exact
natural-number specifications. Complete rounding refinement belongs to `Direct.Proof`; this module
contains only reusable facts about the field constructor.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicPacking

open FloatLib.Numerics

/-- The adaptive leading-bit primitive is exactly `Nat.log2`. -/
theorem leadingBit_eq_log2 (value : Nat) :
    leadingBit value = value.log2 := by
  unfold leadingBit
  simp only [FixedWord.log2Word_eq_log2]
  split
  next h =>
    rw [show (UInt64.ofNatLT value h).log2.toNat =
        (UInt64.ofNatLT value h).toNat.log2 by
      unfold UInt64.log2 Fin.log2
      rfl]
    rw [UInt64.toNat_ofNatLT]
  next =>
    rfl

/--
The normalized fraction prefix fits in exactly the number of requested positions.

The hypotheses characterize `leading` as the index of the leading one. This formulation is
independent of `Nat.log2`, so packed backends may reuse it after proving their own normalization
invariant.
-/
theorem fractionPrefix_lt_two_pow
    (significand leading count : Nat)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    fractionPrefix significand leading count < 2 ^ count := by
  have hfraction :
      significand - 2 ^ leading < 2 ^ leading := by
    rw [pow_succ] at hupper
    omega
  unfold fractionPrefix
  simp only [Nat.shiftLeft_eq, one_mul]
  split
  next hcount =>
    rw [Nat.shiftRight_eq_div_pow]
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [← Nat.pow_add]
    rw [Nat.add_sub_of_le hcount]
    exact hfraction
  next hcount =>
    have hmul :=
      (Nat.mul_lt_mul_right (Nat.two_pow_pos (count - leading))).2
        hfraction
    rw [← Nat.pow_add] at hmul
    have hleading : leading ≤ count := by omega
    rw [Nat.add_sub_of_le hleading] at hmul
    exact hmul

/-- A valid two-bit exponent followed by a normalized fraction fits in `count` bits. -/
theorem tailPrefix_lt_two_pow
    (exponentField significand leading count : Nat)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    tailPrefix exponentField significand leading count < 2 ^ count := by
  unfold tailPrefix
  split
  next hcount =>
    rw [Nat.shiftRight_eq_div_pow]
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    have hpower :
        2 ^ count * 2 ^ (2 - count) = 4 := by
      rw [← Nat.pow_add]
      rw [Nat.add_sub_of_le hcount]
    rw [hpower]
    exact hexponent
  next hcount =>
    rw [Nat.shiftLeft_eq]
    have hfraction :=
      fractionPrefix_lt_two_pow significand leading (count - 2)
        hlower hupper
    let scale := 2 ^ (count - 2)
    have hstep :
        exponentField * scale +
            fractionPrefix significand leading (count - 2) <
          (exponentField + 1) * scale := by
      dsimp [scale]
      rw [Nat.add_mul]
      simpa using Nat.add_lt_add_left hfraction
        (exponentField * 2 ^ (count - 2))
    have hexponentStep : exponentField + 1 ≤ 4 := by
      omega
    have hbounded :
        (exponentField + 1) * scale ≤ 4 * scale :=
      Nat.mul_le_mul_right scale hexponentStep
    calc
      exponentField * scale +
          fractionPrefix significand leading (count - 2) <
          (exponentField + 1) * scale := hstep
      _ ≤ 4 * scale := hbounded
      _ = 2 ^ count := by
        dsimp [scale]
        rw [show (4 : Nat) = 2 ^ 2 by decide, ← Nat.pow_add]
        congr 1
        omega

/-- A positive regime run, its terminator, and a bounded tail stay below the payload width. -/
private theorem regimePrefix_add_lt_two_pow
    (run payload tail : Nat) (hrun : run < payload)
    (htail : tail < 2 ^ (payload - run - 1)) :
    (2 ^ run - 1) * 2 ^ (payload - run) + tail < 2 ^ payload := by
  obtain ⟨trailing, rfl⟩ : ∃ trailing, payload = run + trailing + 1 :=
    ⟨payload - run - 1, by omega⟩
  rw [show run + trailing + 1 - run - 1 = trailing by omega] at htail
  rw [show run + trailing + 1 - run = trailing + 1 by omega, pow_succ,
    show 2 ^ (run + trailing + 1) = 2 ^ run * 2 ^ trailing * 2 by
      rw [pow_succ, pow_add]]
  have hrun := Nat.one_le_two_pow (n := run)
  generalize 2 ^ run = regimeField at *
  generalize 2 ^ trailing = tailField at *
  rw [Nat.sub_one_mul, Nat.mul_assoc]
  have hle : tailField * 2 ≤ regimeField * (tailField * 2) :=
    Nat.le_mul_of_pos_left _ hrun
  omega

/-- A negative regime terminator followed by a bounded tail stays below the payload width. -/
private theorem two_pow_add_lt_two_pow
    (run payload tail : Nat) (hrunPos : 0 < run) (hrun : run < payload)
    (htail : tail < 2 ^ (payload - run - 1)) :
    2 ^ (payload - run - 1) + tail < 2 ^ payload := by
  have := Nat.pow_lt_pow_right (by decide : 1 < 2)
    (show payload - run - 1 + 1 ≤ payload - 1 by omega)
  have : 2 ^ payload = 2 ^ (payload - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  omega

/--
A normalized field prefix always encodes a nonnegative finite posit.

This range theorem removes a runtime candidate-bound check from specialized rounders. Its
hypotheses are exactly the exponent-width and leading-bit invariants established by normalization.
-/
theorem lowerCandidateFromFields_lt_signMask
    (format : Format) (regime : Int)
    (exponentField significand leading : Nat)
    (hexponentField : exponentField < 4)
    (hleading : 2 ^ leading ≤ significand)
    (hsignificandUpper : significand < 2 ^ (leading + 1)) :
    lowerCandidateFromFields format regime exponentField significand leading <
      format.signMaskNat := by
  have htail := tailPrefix_lt_two_pow exponentField significand leading
  unfold lowerCandidateFromFields
  simp only [Nat.shiftLeft_eq, one_mul]
  split_ifs with hregime hsaturated hsaturated
  · exact Nat.sub_lt format.signMaskNat_pos one_pos
  · exact regimePrefix_add_lt_two_pow _ _ _ (by omega)
      (htail _ hexponentField hleading hsignificandUpper)
  · exact format.signMaskNat_pos
  · exact two_pow_add_lt_two_pow _ _ _ (by omega) (by omega)
      (htail _ hexponentField hleading hsignificandUpper)

/-- The direct dyadic candidate is always a nonnegative finite posit code. -/
theorem lowerCandidate_lt_signMask
    (format : Format) (target : FloatLib.Numerics.Dyadic) :
    lowerCandidate format target < format.signMaskNat := by
  unfold lowerCandidate
  split
  next =>
    exact format.signMaskNat_pos
  next hnontrivial =>
    have hsignificand : target.significand ≠ 0 := by
      intro hzero
      apply hnontrivial
      simp [hzero]
    let leading := leadingBit target.significand
    let scale := target.exponent + Int.ofNat leading
    let regime := scale.ediv 4
    let exponentField := (scale.emod 4).toNat
    change
      lowerCandidateFromFields format regime exponentField
          target.significand leading <
        format.signMaskNat
    apply lowerCandidateFromFields_lt_signMask
    · dsimp [exponentField]
      have hnonnegative : 0 ≤ scale.emod 4 :=
        Int.emod_nonneg scale (by norm_num)
      rw [Int.toNat_lt hnonnegative]
      exact Int.emod_lt_of_pos scale (by norm_num)
    · rw [show leading = target.significand.log2 by
        exact leadingBit_eq_log2 target.significand]
      exact Nat.log2_self_le hsignificand
    · rw [show leading = target.significand.log2 by
        exact leadingBit_eq_log2 target.significand]
      exact Nat.lt_log2_self

end FloatLib.Floats.Formats.Posit.Model.DirectDyadicPacking
