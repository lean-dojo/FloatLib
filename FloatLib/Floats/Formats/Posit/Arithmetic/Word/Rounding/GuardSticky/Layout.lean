/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Numerics.Bitwise
import Mathlib.Tactic.Ring
public import FloatLib.Floats.Formats.Posit.Semantics.Positive.BitRuns
public import FloatLib.Floats.Formats.Posit.Semantics.Positive.Trailing
public import FloatLib.Floats.Formats.Posit.Semantics.Positive.Order
public import Mathlib.Data.Nat.Bitwise

/-!
# Semantics of interior Posit field layouts

The native guard/sticky packer constructs an unsigned Posit from a regime prefix and a retained
exponent/fraction tail. This module proves the representation-independent meaning of the two
interior layouts:

* a positive regime is a run of ones followed by a zero terminator;
* a negative regime is a run of zeros followed by a one terminator.

Both the retained code and the standard's one-bit-wider rounding boundary use these layouts.
Keeping the decoder argument here lets scalar, fixed-limb, division, and square-root kernels share
one proof without depending on `UInt64`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding

/--
Decode the all-ones positive payload.

`maxPos` has a regime run occupying the complete payload, no terminator, and no trailing field.
Its regime value is therefore `payloadBits - 1`.
-/
theorem nonnegativeRatAt_maxPositive
    (format : Format) :
    Model.nonnegativeRatAt format (format.signMaskNat - 1) =
      (2 : Rat) ^ ((Int.ofNat format.payloadBits - 1) * 4) := by
  let code := format.signMaskNat - 1
  let value := Model.ofNatBits (format := format) code
  have hpayload : 0 < format.payloadBits :=
    format.payloadBits_pos
  have hmask :
      format.signMaskNat = 2 ^ format.payloadBits := by
    rfl
  have hcode : code = 2 ^ format.payloadBits - 1 := by
    dsimp [code]
    rw [hmask]
  have hcodePos : 0 < code := by
    rw [hcode]
    have hpower : 1 < 2 ^ format.payloadBits :=
      Nat.one_lt_two_pow hpayload.ne'
    omega
  have hcodeLt : code < format.signMaskNat := by
    dsimp [code]
    exact Nat.sub_lt format.signMaskNat_pos (by decide)
  have hsign : value.signBit = false :=
    Model.signBit_ofNatBits_eq_false format code hcodeLt
  have hmagnitude : value.magnitudeBits = code :=
    Model.magnitudeBits_ofNatBits_of_lt_signMask
      format code hcodeLt
  have hregimeBit : value.regimeBit = true := by
    unfold Model.regimeBit
    rw [hmagnitude, hcode, Nat.testBit_two_pow_sub_one]
    simp [hpayload]
  have hrun :
      value.regimeRunLength = format.payloadBits := by
    unfold Model.regimeRunLength
    rw [hmagnitude, hregimeBit]
    rw [Model.countLeadingRun_true_eq_fixedComplement
      code format.payloadBits]
    · rw [hcode]
      simp [Model.countLeadingRun_zero_false]
    · rw [hcode]
      exact Nat.sub_lt (Nat.two_pow_pos _) (by decide)
  have htrailing : value.trailingBits = 0 := by
    unfold Model.trailingBits Model.hasRegimeTerminator
    rw [hrun]
    simp
  have hregime :
      value.regimeValue =
        Int.ofNat format.payloadBits - 1 := by
    simp [Model.regimeValue, hregimeBit, hrun]
  rw [Model.nonnegativeRatAt_of_pos_lt_signMask
    format hcodePos hcodeLt]
  rw [Model.decodeFields_toRat_eq_trailingRat_mul_regime
    value hsign]
  change
    Model.trailingRat value.trailingBits value.magnitudeBits *
        (2 : Rat) ^ (value.regimeValue * 4) =
      (2 : Rat) ^ ((Int.ofNat format.payloadBits - 1) * 4)
  rw [htrailing, hregime]
  norm_num [Model.trailingRat, Model.natToRat]

/-- The leading-zero run of a value lying between two consecutive powers of two. -/
private theorem countLeadingRun_false_eq_of_two_pow_le_of_lt
    (value width trailing : Nat)
    (hlower : 2 ^ trailing ≤ value) (hupper : value < 2 ^ (trailing + 1))
    (hwidth : trailing + 1 ≤ width) :
    Model.countLeadingRun value width false = width - (trailing + 1) := by
  have hpos : 0 < value := (Nat.two_pow_pos trailing).trans_le hlower
  rw [Model.countLeadingRun_false_eq_log2 value width hpos
      (hupper.trans_le (Nat.pow_le_pow_right (by decide) hwidth)),
    (Nat.log2_eq_iff hpos.ne').2 ⟨hlower, hupper⟩]

/--
Decode an interior code from its regime bit, regime run length, and retained tail.

Both interior layouts reduce to this bookkeeping about the decoder projections once the raw
code's leading bit, leading run, and low bits are known.
-/
private theorem nonnegativeRatAt_of_regimeRun
    (format : Format) (code run tail : Nat) (bit : Bool)
    (hcodePos : 0 < code) (hcode : code < 2 ^ format.payloadBits)
    (hrun : run < format.payloadBits)
    (hbit : code.testBit (format.payloadBits - 1) = bit)
    (hrunLength : Model.countLeadingRun code format.payloadBits bit = run)
    (htail : code % 2 ^ (format.payloadBits - run - 1) = tail) :
    Model.nonnegativeRatAt format code =
      Model.trailingRat (format.payloadBits - run - 1) tail *
        (2 : Rat) ^ ((if bit then Int.ofNat run - 1 else -Int.ofNat run) * 4) := by
  have hcodeSign : code < format.signMaskNat := hcode
  let value := Model.ofNatBits (format := format) code
  have hsign : value.signBit = false :=
    Model.signBit_ofNatBits_eq_false format code hcodeSign
  have hmagnitude : value.magnitudeBits = code :=
    Model.magnitudeBits_ofNatBits_of_lt_signMask format code hcodeSign
  have hregimeBit : value.regimeBit = bit := by
    unfold Model.regimeBit
    rw [hmagnitude, hbit]
  have hrunLength' : value.regimeRunLength = run := by
    unfold Model.regimeRunLength
    rw [hmagnitude, hregimeBit, hrunLength]
  have htrailingBits : value.trailingBits = format.payloadBits - run - 1 := by
    unfold Model.trailingBits Model.hasRegimeTerminator
    rw [hrunLength']
    simp [hrun]
  have hregimeValue :
      value.regimeValue = if bit then Int.ofNat run - 1 else -Int.ofNat run := by
    unfold Model.regimeValue
    rw [hregimeBit, hrunLength']
  rw [Model.nonnegativeRatAt_of_pos_lt_signMask format hcodePos hcodeSign,
    Model.decodeFields_toRat_eq_trailingRat_mul_regime value hsign]
  change
    Model.trailingRat value.trailingBits value.magnitudeBits *
        (2 : Rat) ^ (value.regimeValue * 4) = _
  rw [htrailingBits, hmagnitude, hregimeValue, ← htail, Model.trailingRat_mod_twoPow]

/--
Decode an interior positive-regime layout.

The hypotheses say that the regime run and its terminator fit in the payload and that `tail`
fits in every remaining position. The result exposes the exact tail value and regime scale while
hiding all variable-length decoder bookkeeping.
-/
theorem nonnegativeRatAt_positiveInterior
    (format : Format) (run tail : Nat)
    (hrunPos : 0 < run)
    (hrun : run < format.payloadBits)
    (htail : tail < 2 ^ (format.payloadBits - run - 1)) :
    let code :=
      (2 ^ run - 1) * 2 ^ (format.payloadBits - run) + tail
    Model.nonnegativeRatAt format code =
      Model.trailingRat (format.payloadBits - run - 1) tail *
        (2 : Rat) ^ ((Int.ofNat run - 1) * 4) := by
  intro code
  have hcode : code = (2 ^ run - 1) * 2 ^ (format.payloadBits - run) + tail := rfl
  have hpowers : 2 ^ run * 2 ^ (format.payloadBits - run) = 2 ^ format.payloadBits := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hrun.le]
  have hgapPow :
      2 ^ (format.payloadBits - run) = 2 ^ (format.payloadBits - run - 1) * 2 :=
    Nat.two_pow_pred_mul_two (by omega) |>.symm
  have htopPow : 2 ^ (format.payloadBits - 1) * 2 = 2 ^ format.payloadBits :=
    Nat.two_pow_pred_mul_two format.payloadBits_pos
  have hgapLe : 2 ^ (format.payloadBits - run) ≤ 2 ^ (format.payloadBits - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hcodeSplit :
      code = 2 ^ format.payloadBits - 2 ^ (format.payloadBits - run) + tail := by
    rw [hcode, Nat.sub_one_mul, hpowers]
  have hcodeUpper : code < 2 ^ format.payloadBits := by omega
  have hcodeLower : 2 ^ (format.payloadBits - 1) ≤ code := by omega
  refine nonnegativeRatAt_of_regimeRun format code run tail true
    (by omega) hcodeUpper hrun ?_ ?_ ?_
  · exact (Nat.testBit_eq_true_iff_two_pow_le_of_lt (by
      rwa [Nat.sub_add_cancel format.payloadBits_pos])).2 hcodeLower
  · rw [Model.countLeadingRun_true_eq_fixedComplement code _ hcodeUpper,
      countLeadingRun_false_eq_of_two_pow_le_of_lt _ _ (format.payloadBits - run - 1)
        (by omega) (by omega) (by omega)]
    omega
  · rw [hcode, hgapPow, ← Nat.mul_assoc, Nat.mul_right_comm, Nat.mul_add_mod',
      Nat.mod_eq_of_lt htail]

/--
Decode an interior negative-regime layout.

The terminator is the single one above `tail`. The leading-zero count therefore recovers `run`,
and the low tail positions have the same rational interpretation as in the positive layout.
-/
theorem nonnegativeRatAt_negativeInterior
    (format : Format) (run tail : Nat)
    (hrunPos : 0 < run)
    (hrun : run < format.payloadBits)
    (htail : tail < 2 ^ (format.payloadBits - run - 1)) :
    let code :=
      2 ^ (format.payloadBits - run - 1) + tail
    Model.nonnegativeRatAt format code =
      Model.trailingRat (format.payloadBits - run - 1) tail *
        (2 : Rat) ^ (-(Int.ofNat run) * 4) := by
  intro code
  have hcode : code = 2 ^ (format.payloadBits - run - 1) + tail := rfl
  have hgapPow :
      2 ^ (format.payloadBits - run) = 2 ^ (format.payloadBits - run - 1) * 2 :=
    Nat.two_pow_pred_mul_two (by omega) |>.symm
  have hgapLe : 2 ^ (format.payloadBits - run) ≤ 2 ^ (format.payloadBits - 1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have htopLt : 2 ^ (format.payloadBits - 1) < 2 ^ format.payloadBits :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  refine nonnegativeRatAt_of_regimeRun format code run tail false
    (by omega) (by omega) hrun ?_ ?_ ?_
  · exact Nat.testBit_eq_false_of_lt (by omega)
  · rw [countLeadingRun_false_eq_of_two_pow_le_of_lt _ _ (format.payloadBits - run - 1)
      (by omega) (by omega) (by omega)]
    omega
  · rw [hcode, Nat.add_mod_left, Nat.mod_eq_of_lt htail]

/--
Decode the successor of a positive-regime code whose retained tail is all ones.

Adding one carries through the complete retained tail into the regime. For an interior run this
produces the zero-tail base of the next positive regime; at the final run it produces `maxPos`.
This is the representation lemma needed to prove that the native lower candidate and its packed
successor are adjacent Posits.
-/
theorem nonnegativeRatAt_positiveInteriorCarry
    (format : Format) (run : Nat)
    (hrunPos : 0 < run)
    (hrun : run < format.payloadBits) :
    Model.nonnegativeRatAt format
        ((2 ^ run - 1) * 2 ^ (format.payloadBits - run) +
          (2 ^ (format.payloadBits - run - 1) - 1) + 1) =
      (2 : Rat) ^ (Int.ofNat run * 4) := by
  let nextTrailing := format.payloadBits - (run + 1) - 1
  let nextScale := format.payloadBits - (run + 1)
  have hgap :
      format.payloadBits - run = nextScale + 1 := by
    dsimp [nextScale]
    omega
  have hnextScalePos : 0 < 2 ^ nextScale :=
    Nat.two_pow_pos _
  have hcoefficient :
      2 * (2 ^ run - 1) + 1 = 2 ^ (run + 1) - 1 := by
    rw [Nat.pow_succ]
    have hrunPower := Nat.two_pow_pos run
    omega
  have hcode :
      (2 ^ run - 1) * 2 ^ (format.payloadBits - run) +
          (2 ^ (format.payloadBits - run - 1) - 1) + 1 =
        (2 ^ (run + 1) - 1) * 2 ^ nextScale := by
    rw [hgap, show nextScale + 1 - 1 = nextScale by omega,
      Nat.pow_succ]
    calc
      (2 ^ run - 1) * (2 ^ nextScale * 2) +
          (2 ^ nextScale - 1) + 1 =
        (2 ^ run - 1) * (2 ^ nextScale * 2) +
          2 ^ nextScale := by
            omega
      _ =
        (2 * (2 ^ run - 1) + 1) * 2 ^ nextScale := by
          ring
      _ = (2 ^ (run + 1) - 1) * 2 ^ nextScale := by
        rw [hcoefficient]
  by_cases hnext : run + 1 < format.payloadBits
  · have hsemantic :=
      nonnegativeRatAt_positiveInterior
        format (run + 1) 0 (by omega) hnext (by simp)
    rw [show
      format.payloadBits - (run + 1) - 1 =
        nextTrailing by rfl] at hsemantic
    rw [hcode]
    change
      Model.nonnegativeRatAt format
          ((2 ^ (run + 1) - 1) *
            2 ^ (format.payloadBits - (run + 1)) + 0) =
        (2 : Rat) ^ (Int.ofNat run * 4)
    rw [hsemantic]
    norm_num [Model.trailingRat, Model.natToRat]
  · have hfull : run + 1 = format.payloadBits := by
      omega
    rw [hcode]
    have hnextScaleZero : nextScale = 0 := by
      dsimp [nextScale]
      omega
    rw [hnextScaleZero, Nat.pow_zero, Nat.mul_one, hfull]
    change
      Model.nonnegativeRatAt format (format.signMaskNat - 1) =
        (2 : Rat) ^ (Int.ofNat run * 4)
    rw [nonnegativeRatAt_maxPositive]
    have hregime :
        Int.ofNat format.payloadBits - 1 =
          Int.ofNat run := by
      rw [← hfull]
      simp
    rw [hregime]

/--
Decode the successor of a negative-regime code whose retained tail is all ones.

The carry shortens the run of leading zeros, so the successor is the zero-tail base of the next
larger regime. The `run = 1` case crosses the central regime boundary and is handled explicitly.
-/
theorem nonnegativeRatAt_negativeInteriorCarry
    (format : Format) (run : Nat)
    (hrunPos : 0 < run)
    (hrun : run < format.payloadBits) :
    Model.nonnegativeRatAt format
        (2 ^ (format.payloadBits - run - 1) +
          (2 ^ (format.payloadBits - run - 1) - 1) + 1) =
      (2 : Rat) ^ ((-(Int.ofNat run) + 1) * 4) := by
  let trailing := format.payloadBits - run - 1
  have hpowerPos : 0 < 2 ^ trailing :=
    Nat.two_pow_pos _
  have hcode :
      2 ^ (format.payloadBits - run - 1) +
          (2 ^ (format.payloadBits - run - 1) - 1) + 1 =
        2 ^ (trailing + 1) := by
    rw [show
      format.payloadBits - run - 1 = trailing by rfl]
    rw [Nat.pow_succ]
    omega
  by_cases hone : run = 1
  · subst run
    have hpayload : 1 < format.payloadBits := by
      omega
    have hsemantic :=
      nonnegativeRatAt_positiveInterior
        format 1 0 (by decide) hpayload (by simp)
    rw [hcode]
    have htrailingCode :
        trailing + 1 = format.payloadBits - 1 := by
      dsimp [trailing]
      omega
    rw [htrailingCode]
    simpa [Model.trailingRat, Model.natToRat] using hsemantic
  · have hrunPredPos : 0 < run - 1 := by
      omega
    have hrunPred : run - 1 < format.payloadBits := by
      omega
    have hsemantic :=
      nonnegativeRatAt_negativeInterior
        format (run - 1) 0 hrunPredPos hrunPred (by simp)
    have hexponent :
        -(Int.ofNat (run - 1)) * 4 =
          (-(Int.ofNat run) + 1) * 4 := by
      simp only [Int.ofNat_eq_natCast]
      rw [Int.ofNat_sub (m := 1) (n := run) (by omega)]
      ring
    rw [hexponent] at hsemantic
    rw [hcode]
    have htrailingCode :
        trailing + 1 =
          format.payloadBits - (run - 1) - 1 := by
      dsimp [trailing]
      omega
    rw [htrailingCode]
    simpa [Model.trailingRat, Model.natToRat] using hsemantic

/--
Decode the standard one-bit-wider boundary above a positive-regime retained code.

Doubling the retained code appends `0`; adding one changes only that new bit. Consequently the
regime is unchanged and the trailing field is exactly `2 * tail + 1`.
-/
theorem nonnegativeRatAt_positiveInteriorThreshold
    (format : Format) (run tail : Nat)
    (hrunPos : 0 < run)
    (hrun : run < format.payloadBits)
    (htail : tail < 2 ^ (format.payloadBits - run - 1)) :
    Model.nonnegativeRatAt format.nextPrecision
        (2 * ((2 ^ run - 1) * 2 ^ (format.payloadBits - run) + tail) + 1) =
      Model.trailingRat
          (format.payloadBits - run - 1 + 1) (2 * tail + 1) *
        (2 : Rat) ^ ((Int.ofNat run - 1) * 4) := by
  have hrunNext : run < format.nextPrecision.payloadBits := by
    rw [Format.nextPrecision_payloadBits]
    omega
  have htailNext :
      2 * tail + 1 <
        2 ^ (format.nextPrecision.payloadBits - run - 1) := by
    rw [Format.nextPrecision_payloadBits]
    have hpower :
        2 ^ (format.payloadBits - run - 1 + 1) =
          2 * 2 ^ (format.payloadBits - run - 1) := by
      rw [Nat.pow_succ]
      omega
    rw [show
      format.payloadBits + 1 - run - 1 =
        format.payloadBits - run - 1 + 1 by omega]
    rw [hpower]
    omega
  have hsemantic :=
    nonnegativeRatAt_positiveInterior
      format.nextPrecision run (2 * tail + 1)
      hrunPos hrunNext htailNext
  rw [show
      format.nextPrecision.payloadBits - run - 1 =
        format.payloadBits - run - 1 + 1 by
      rw [Format.nextPrecision_payloadBits]
      omega] at hsemantic
  have hcode :
      (2 ^ run - 1) *
            2 ^ (format.nextPrecision.payloadBits - run) +
          (2 * tail + 1) =
        2 * ((2 ^ run - 1) *
            2 ^ (format.payloadBits - run) + tail) + 1 := by
    rw [Format.nextPrecision_payloadBits]
    rw [show
      format.payloadBits + 1 - run =
        (format.payloadBits - run) + 1 by omega]
    rw [Nat.pow_succ]
    ring
  rw [← hcode]
  exact hsemantic

/--
Decode the standard one-bit-wider boundary above a negative-regime retained code.

As in the positive case, appending `1` preserves the regime and extends the trailing field by one
bit. The theorem is separated only because the two variable-length regime layouts differ.
-/
theorem nonnegativeRatAt_negativeInteriorThreshold
    (format : Format) (run tail : Nat)
    (hrunPos : 0 < run)
    (hrun : run < format.payloadBits)
    (htail : tail < 2 ^ (format.payloadBits - run - 1)) :
    Model.nonnegativeRatAt format.nextPrecision
        (2 * (2 ^ (format.payloadBits - run - 1) + tail) + 1) =
      Model.trailingRat
          (format.payloadBits - run - 1 + 1) (2 * tail + 1) *
        (2 : Rat) ^ (-(Int.ofNat run) * 4) := by
  have hrunNext : run < format.nextPrecision.payloadBits := by
    rw [Format.nextPrecision_payloadBits]
    omega
  have htailNext :
      2 * tail + 1 <
        2 ^ (format.nextPrecision.payloadBits - run - 1) := by
    rw [Format.nextPrecision_payloadBits]
    have hpower :
        2 ^ (format.payloadBits - run - 1 + 1) =
          2 * 2 ^ (format.payloadBits - run - 1) := by
      rw [Nat.pow_succ]
      omega
    rw [show
      format.payloadBits + 1 - run - 1 =
        format.payloadBits - run - 1 + 1 by omega]
    rw [hpower]
    omega
  have hsemantic :=
    nonnegativeRatAt_negativeInterior
      format.nextPrecision run (2 * tail + 1)
      hrunPos hrunNext htailNext
  dsimp only at hsemantic
  rw [show
      format.nextPrecision.payloadBits - run - 1 =
        format.payloadBits - run - 1 + 1 by
      rw [Format.nextPrecision_payloadBits]
      omega] at hsemantic
  have hcode :
      2 ^ (format.nextPrecision.payloadBits - run - 1) +
          (2 * tail + 1) =
        2 * (2 ^ (format.payloadBits - run - 1) + tail) + 1 := by
    rw [Format.nextPrecision_payloadBits]
    rw [show
      format.payloadBits + 1 - run - 1 =
        (format.payloadBits - run - 1) + 1 by omega]
    rw [Nat.pow_succ]
    ring
  rw [← hcode]
  rw [show
      format.nextPrecision.payloadBits - run - 1 =
        format.payloadBits - run - 1 + 1 by
      rw [Format.nextPrecision_payloadBits]
      omega]
  exact hsemantic

end FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding
