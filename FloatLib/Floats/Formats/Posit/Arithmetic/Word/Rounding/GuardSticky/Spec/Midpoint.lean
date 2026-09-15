/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Spec.Tail
import FloatLib.Numerics.Bitwise
import Mathlib.Tactic.Ring

/-!
# Midpoint decisions for guard-and-sticky rounding

Guard and sticky bits are useful only if they denote the same midpoint test as the exact bit
stream. This module represents that one-bit-wider boundary as a bounded integer and proves the
usual decision table (below, above, and tie broken by retained parity) implements nearest-even.

The statement is deliberately independent of a particular posit width or machine carrier. Both
word and limb rounders reuse it, which keeps their optimized bit extraction separate from the one
rounding rule they must all satisfy.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding

/--
The exact stream value of the one-bit-wider nearest-rounding boundary.

The retained prefix is followed by one, then padded with zeros back to the complete stream width.
-/
@[inline] def streamMidpointRaw
    (raw width retained : Nat) : Nat :=
  (2 * streamPrefix raw width retained + 1) *
    2 ^ (width - retained - 1)

/-- A retained prefix of a bounded stream fits in its requested width. -/
theorem streamPrefix_lt_two_pow_of_lt
    {raw width retained : Nat}
    (hraw : raw < 2 ^ width)
    (hretained : retained ≤ width) :
    streamPrefix raw width retained < 2 ^ retained := by
  unfold streamPrefix
  rw [if_pos hretained, Nat.div_lt_iff_lt_mul
    (Nat.two_pow_pos (width - retained))]
  rw [← Nat.pow_add, Nat.add_comm,
    Nat.sub_add_cancel hretained]
  exact hraw

/-- The padded one-bit-wider boundary still fits in the complete stream width. -/
theorem streamMidpointRaw_lt_two_pow
    {raw width retained : Nat}
    (hraw : raw < 2 ^ width)
    (hretained : retained < width) :
    streamMidpointRaw raw width retained < 2 ^ width := by
  have hprefix :=
    streamPrefix_lt_two_pow_of_lt hraw hretained.le
  have hprefixOne :
      2 * streamPrefix raw width retained + 1 <
        2 ^ (retained + 1) := by
    rw [Nat.pow_succ]
    omega
  have hscalePos :
      0 < 2 ^ (width - retained - 1) :=
    Nat.two_pow_pos _
  have hscaled :=
    (Nat.mul_lt_mul_right hscalePos).2 hprefixOne
  unfold streamMidpointRaw
  calc
    (2 * streamPrefix raw width retained + 1) *
          2 ^ (width - retained - 1) <
        2 ^ (retained + 1) *
          2 ^ (width - retained - 1) :=
      hscaled
    _ = 2 ^ width := by
      rw [← Nat.pow_add]
      congr 1
      omega

/-- Algebraic decomposition of the padded nearest-rounding boundary. -/
theorem streamMidpointRaw_eq_div
    (raw width retained : Nat) (hretained : retained < width) :
    streamMidpointRaw raw width retained =
      2 ^ (width - retained) *
          (raw / 2 ^ (width - retained)) +
        2 ^ (width - retained - 1) := by
  have hprefix :
      streamPrefix raw width retained =
        raw / 2 ^ (width - retained) := by
    unfold streamPrefix
    rw [if_pos hretained.le]
  unfold streamMidpointRaw
  rw [hprefix]
  rw [show
      2 ^ (width - retained) =
        2 * 2 ^ (width - retained - 1) by
    calc
      2 ^ (width - retained) =
          2 ^ (width - retained - 1 + 1) := by
        congr 1
        omega
      _ = 2 ^ (width - retained - 1) * 2 := by
        rw [Nat.pow_succ]
      _ = 2 * 2 ^ (width - retained - 1) := by
        omega]
  ring

/--
The one-bit-wider boundary and its zero-padded complete-stream form denote the same rational.
-/
theorem trailingRat_streamMidpointRaw
    (raw width retained : Nat)
    (hretained : retained < width) :
    Model.trailingRat (retained + 1)
        (2 * streamPrefix raw width retained + 1) =
      Model.trailingRat width
        (streamMidpointRaw raw width retained) := by
  let extra := width - retained - 1
  have hwidth :
      retained + 1 + extra = width := by
    dsimp [extra]
    omega
  have hpadding :=
    trailingRat_mul_two_pow
      (retained + 1)
      (2 * streamPrefix raw width retained + 1)
      extra
  rw [hwidth] at hpadding
  unfold streamMidpointRaw
  simpa [extra] using hpadding.symm

/--
Comparing the normalized exact tail with the one-bit-wider boundary is equivalent to comparing
their bounded complete-stream integers.
-/
theorem normalizedTail_lt_midpoint_iff
    {raw width retained : Nat} (regime : Int)
    (hraw : raw < 2 ^ width)
    (hretained : retained < width) :
    Model.trailingRat width raw *
          (2 : Rat) ^ (regime * 4) <
        Model.trailingRat (retained + 1)
            (2 * streamPrefix raw width retained + 1) *
          (2 : Rat) ^ (regime * 4) ↔
      raw < streamMidpointRaw raw width retained := by
  have hscale : 0 < (2 : Rat) ^ (regime * 4) :=
    zpow_pos (by norm_num) _
  rw [trailingRat_streamMidpointRaw
    raw width retained hretained]
  rw [Rat.mul_lt_mul_right hscale]
  exact trailingRat_lt_iff_of_bounded
    hraw (streamMidpointRaw_lt_two_pow hraw hretained)

/-- The reverse normalized-tail comparison has the corresponding bounded-integer meaning. -/
theorem midpoint_lt_normalizedTail_iff
    {raw width retained : Nat} (regime : Int)
    (hraw : raw < 2 ^ width)
    (hretained : retained < width) :
    Model.trailingRat (retained + 1)
            (2 * streamPrefix raw width retained + 1) *
          (2 : Rat) ^ (regime * 4) <
        Model.trailingRat width raw *
          (2 : Rat) ^ (regime * 4) ↔
      streamMidpointRaw raw width retained < raw := by
  have hscale : 0 < (2 : Rat) ^ (regime * 4) :=
    zpow_pos (by norm_num) _
  rw [trailingRat_streamMidpointRaw
    raw width retained hretained]
  rw [Rat.mul_lt_mul_right hscale]
  exact trailingRat_lt_iff_of_bounded
    (streamMidpointRaw_lt_two_pow hraw hretained) hraw

/-- The guard bit states that the exact stream is at or above the nearest-rounding boundary. -/
theorem streamGuard_eq_decide_midpoint_le
    (raw width retained : Nat) (hretained : retained < width) :
    streamGuard raw width retained =
      decide (streamMidpointRaw raw width retained ≤ raw) := by
  let shift := width - retained
  let quotient := raw / 2 ^ shift
  let remainder := raw % 2 ^ shift
  let half := 2 ^ (shift - 1)
  have hshiftPos : 0 < shift := by
    dsimp [shift]
    omega
  have hpower : 2 ^ shift = 2 * half := by
    calc
      2 ^ shift = 2 ^ (shift - 1 + 1) := by
        congr 1
        omega
      _ = 2 ^ (shift - 1) * 2 := by
        rw [Nat.pow_succ]
      _ = 2 * half := by
        dsimp [half]
        omega
  have hbit :
      raw.testBit (shift - 1) =
        decide (half ≤ remainder) := by
    have hmodBit :
        remainder.testBit (shift - 1) =
          raw.testBit (shift - 1) := by
      dsimp [remainder]
      rw [Nat.testBit_mod_two_pow]
      simp [hshiftPos]
    have htop :
        remainder.testBit (shift - 1) = true ↔
          half ≤ remainder := by
      apply Nat.testBit_eq_true_iff_two_pow_le_of_lt
      have hremainderLt : remainder < 2 ^ shift := by
        dsimp [remainder]
        exact Nat.mod_lt raw (Nat.two_pow_pos _)
      rwa [show shift - 1 + 1 = shift by omega]
    apply Bool.eq_iff_iff.mpr
    rw [← hmodBit]
    simpa using htop
  have hdecompose :
      raw = remainder + 2 ^ shift * quotient := by
    dsimp [remainder, quotient]
    simpa [Nat.mul_comm] using
      (Nat.mod_add_div raw (2 ^ shift)).symm
  have hprefix :
      streamPrefix raw width retained = quotient := by
    unfold streamPrefix
    rw [if_pos hretained.le]
  have hmidpoint :
      streamMidpointRaw raw width retained =
        2 ^ shift * quotient + half := by
    unfold streamMidpointRaw
    rw [hprefix]
    rw [show 2 ^ shift = 2 * 2 ^ (shift - 1) by
      simpa [half] using hpower]
    dsimp [half]
    ring
  have horder :
      half ≤ remainder ↔
        streamMidpointRaw raw width retained ≤ raw := by
    rw [hmidpoint, hdecompose]
    omega
  unfold streamGuard
  rw [if_pos hretained]
  change
    raw.testBit (shift - 1) =
      decide (streamMidpointRaw raw width retained ≤ raw)
  rw [hbit]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using horder

/--
Once the guard is set, sticky distinguishes values strictly above the rounding boundary from the
exact tie. This is the final order fact needed by nearest-even selection.
-/
theorem streamSticky_eq_decide_midpoint_lt_of_guard
    (raw width retained : Nat) (hretained : retained < width)
    (hguard : streamGuard raw width retained = true) :
    streamSticky raw width retained =
      decide (streamMidpointRaw raw width retained < raw) := by
  let shift := width - retained
  let quotient := raw / 2 ^ shift
  let remainder := raw % 2 ^ shift
  let half := 2 ^ (shift - 1)
  have hshiftPos : 0 < shift := by
    dsimp [shift]
    omega
  have hhalfPos : 0 < half :=
    Nat.two_pow_pos _
  have hpower : 2 ^ shift = 2 * half := by
    calc
      2 ^ shift = 2 ^ (shift - 1 + 1) := by
        congr 1
        omega
      _ = 2 ^ (shift - 1) * 2 := by
        rw [Nat.pow_succ]
      _ = 2 * half := by
        dsimp [half]
        omega
  have hremainderLt : remainder < 2 * half := by
    dsimp [remainder]
    rw [← hpower]
    exact Nat.mod_lt raw (Nat.two_pow_pos _)
  have hdecompose :
      raw = remainder + 2 ^ shift * quotient := by
    dsimp [remainder, quotient]
    simpa [Nat.mul_comm] using
      (Nat.mod_add_div raw (2 ^ shift)).symm
  have hmidpoint :
      streamMidpointRaw raw width retained =
        2 ^ shift * quotient + half := by
    simpa [shift, quotient, half] using
      streamMidpointRaw_eq_div raw width retained hretained
  have hmidpointLe :
      streamMidpointRaw raw width retained ≤ raw := by
    have equality :=
      streamGuard_eq_decide_midpoint_le
        raw width retained hretained
    rw [hguard] at equality
    have hdecision :
        decide (streamMidpointRaw raw width retained ≤ raw) = true :=
      equality.symm
    exact of_decide_eq_true hdecision
  have hhalfLe : half ≤ remainder := by
    rw [hmidpoint, hdecompose] at hmidpointLe
    omega
  have hhalfDvd : half ∣ 2 ^ shift := by
    rw [hpower]
    exact dvd_mul_left half 2
  have hrawMod :
      raw % half = remainder % half := by
    calc
      raw % half = (raw % 2 ^ shift) % half :=
        (Nat.mod_mod_of_dvd raw hhalfDvd).symm
      _ = remainder % half := by
        rfl
  have hdiv : remainder / half = 1 := by
    apply Nat.div_eq_of_lt_le
    · simpa using hhalfLe
    · exact hremainderLt
  have hremainderDecompose :
      remainder % half + half = remainder := by
    have equality := Nat.mod_add_div remainder half
    rw [hdiv, Nat.mul_one] at equality
    exact equality
  have horder :
      raw % half ≠ 0 ↔
        streamMidpointRaw raw width retained < raw := by
    rw [hrawMod, hmidpoint, hdecompose]
    omega
  unfold streamSticky
  change
    (raw % half != 0) =
      decide (streamMidpointRaw raw width retained < raw)
  apply Bool.eq_iff_iff.mpr
  simpa only [bne_iff_ne, decide_eq_true_eq] using horder

/--
Guard, sticky, and retained-code parity are exactly the standard nearest-even decision at the
one-bit-wider boundary.

The theorem is deliberately independent of the Posit layout. Once a backend proves that its
one-bit-wider code denotes `streamMidpointRaw`, every fixed-word and fixed-limb kernel can reuse
this decision theorem unchanged.
-/
theorem roundFromLower_eq_midpointDecision
    (lower raw width retained : Nat)
    (hretained : retained < width) :
    (if streamGuard raw width retained &&
          (streamSticky raw width retained || lower % 2 != 0) then
        lower + 1
      else
        lower) =
      if raw < streamMidpointRaw raw width retained then
        lower
      else if streamMidpointRaw raw width retained < raw then
        lower + 1
      else if lower % 2 = 0 then
        lower
      else
        lower + 1 := by
  have hguard :=
    streamGuard_eq_decide_midpoint_le raw width retained hretained
  by_cases hbelow : raw < streamMidpointRaw raw width retained
  · have hnotLe :
        ¬streamMidpointRaw raw width retained ≤ raw :=
      Nat.not_le.mpr hbelow
    have hguardFalse :
        streamGuard raw width retained = false := by
      rw [hguard]
      simp [hnotLe]
    simp [hbelow, hguardFalse]
  · have hmidpointLe :
        streamMidpointRaw raw width retained ≤ raw :=
      Nat.le_of_not_gt hbelow
    have hguardTrue :
        streamGuard raw width retained = true := by
      rw [hguard]
      simp [hmidpointLe]
    have hsticky :=
      streamSticky_eq_decide_midpoint_lt_of_guard
        raw width retained hretained hguardTrue
    by_cases habove :
        streamMidpointRaw raw width retained < raw
    · have hstickyTrue :
          streamSticky raw width retained = true := by
        rw [hsticky]
        simp [habove]
      simp [hbelow, habove, hguardTrue, hstickyTrue]
    · have hequal :
          streamMidpointRaw raw width retained = raw := by
        omega
      have hstickyFalse :
          streamSticky raw width retained = false := by
        rw [hsticky]
        simp [habove]
      simp [hequal, hguardTrue, hstickyFalse]
      by_cases heven : lower % 2 = 0
      · simp [heven]
      · have hodd : lower % 2 = 1 := by
          have hmodLt := Nat.mod_lt lower (by decide : 0 < 2)
          omega
        simp [hodd]


end FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding
