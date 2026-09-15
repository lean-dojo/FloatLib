/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import Mathlib.Tactic.Ring
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Layout
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Spec.Midpoint
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Spec.Stream
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Spec.Tail
public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Candidate.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Proof
import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Candidate semantics for direct Posit field rounding

The field-oriented lower-candidate constructor denotes the Posit Standard's one-bit-wider `U1`
boundary. `Layout` proves the meaning of raw regime/tail words; the theorems below instantiate
those results with normalized exponent and significand fields and establish the range and
threshold facts consumed by the interior-rounding proof.

The split between nonnegative and negative regimes mirrors the two encodings. Both use the shared
finite-stream and tail semantics in `GuardSticky.Spec`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding

open FloatLib.Numerics

/-- Advancing one Posit regime multiplies its rational scale by sixteen. -/
theorem regimeScale_succ (regime : Int) :
    (2 : Rat) ^ ((regime + 1) * 4) =
      16 * (2 : Rat) ^ (regime * 4) := by
  rw [show (regime + 1) * 4 = regime * 4 + 4 by ring]
  rw [zpow_add₀ (by norm_num : (2 : Rat) ≠ 0)]
  norm_num
  ring

/-!
## Saturated regime endpoints

The endpoint decision depends only on the normalized rational scale, not on the representation
that produced it. Keeping these lemmas over an arbitrary rational significand lets exact dyadics,
quotient prefixes, and other arithmetic kernels share the same overflow and underflow proof.
-/

/--
A nonnegative regime that consumes the payload places the normalized target at or above `maxPos`.
-/
theorem lowerCodeForPositive_eq_maxPositive_of_saturatedScale
    (format : Format) (fraction : Rat)
    (targetExponent regime : Int)
    (exponentField leading : Nat)
    (hregime : 0 ≤ regime)
    (hsaturated : format.payloadBits ≤ regime.toNat + 1)
    (hlower : (2 : Rat) ^ Int.ofNat leading ≤ fraction)
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    Model.lowerCodeForPositive format
        (fraction * (2 : Rat) ^ targetExponent) =
      format.signMaskNat - 1 := by
  apply Model.lowerCodeForPositive_eq_of_bracket
  · exact Nat.sub_lt format.signMaskNat_pos (by decide)
  · rw [nonnegativeRatAt_maxPositive]
    have hsaturatedInt :
        (format.payloadBits : Int) ≤ (regime.toNat : Int) + 1 := by
      exact_mod_cast hsaturated
    have hregimeNat : (regime.toNat : Int) = regime :=
      Int.toNat_of_nonneg hregime
    have hregimePayload :
        Int.ofNat format.payloadBits - 1 ≤ regime := by
      change (format.payloadBits : Int) - 1 ≤ regime
      omega
    have hregimePower :
        (2 : Rat) ^ ((Int.ofNat format.payloadBits - 1) * 4) ≤
          (2 : Rat) ^ (regime * 4) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hexponentPower :
        (2 : Rat) ^ (regime * 4) ≤
          (2 : Rat) ^ (regime * 4 + Int.ofNat exponentField) :=
      zpow_le_zpow_right₀ (by norm_num)
        (le_add_of_nonneg_right (Int.natCast_nonneg exponentField))
    calc
      (2 : Rat) ^ ((Int.ofNat format.payloadBits - 1) * 4) ≤
          (2 : Rat) ^ (regime * 4) :=
        hregimePower
      _ ≤ (2 : Rat) ^ (regime * 4 + Int.ofNat exponentField) :=
        hexponentPower
      _ = (2 : Rat) ^ (targetExponent + Int.ofNat leading) := by
        rw [hscale]
      _ = (2 : Rat) ^ Int.ofNat leading *
          (2 : Rat) ^ targetExponent := by
        rw [show
            targetExponent + Int.ofNat leading =
              Int.ofNat leading + targetExponent by omega,
          zpow_add₀ (by norm_num)]
      _ ≤ fraction * (2 : Rat) ^ targetExponent :=
        mul_le_mul_of_nonneg_right hlower
          (zpow_nonneg (by norm_num) _)
  · intro hsuccessor
    have hsignMaskPositive := format.signMaskNat_pos
    omega

/--
A negative regime that consumes the payload places every normalized target below `minPos`.
-/
theorem normalizedTarget_lt_minPositive_of_saturatedScale
    (format : Format) (fraction : Rat)
    (targetExponent regime : Int)
    (exponentField leading : Nat)
    (hregime : regime < 0)
    (hsaturated : format.payloadBits ≤ (-regime).toNat)
    (hexponent : exponentField < 4)
    (hupper :
      fraction < (2 : Rat) ^ Int.ofNat (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    fraction * (2 : Rat) ^ targetExponent <
      Model.minPositiveRat format := by
  let minScale : Int :=
    -(4 * Int.ofNat (format.payloadBits - 1))
  have hscaleBound :
      targetExponent + Int.ofNat leading + 1 ≤ minScale := by
    have hpayloadPredInt :
        ((format.payloadBits - 1 : Nat) : Int) = (format.payloadBits : Int) - 1 :=
      Int.ofNat_sub format.payloadBits_pos
    dsimp [minScale]
    simp only [Int.ofNat_eq_natCast] at hscale ⊢
    rw [hpayloadPredInt]
    omega
  have htargetUpper :
      fraction * (2 : Rat) ^ targetExponent <
        (2 : Rat) ^ (targetExponent + Int.ofNat leading + 1) := by
    calc
      fraction * (2 : Rat) ^ targetExponent <
          (2 : Rat) ^ Int.ofNat (leading + 1) *
            (2 : Rat) ^ targetExponent :=
        mul_lt_mul_of_pos_right hupper
          (zpow_pos (by norm_num : (0 : Rat) < 2) _)
      _ = (2 : Rat) ^
          (targetExponent + Int.ofNat leading + 1) := by
        rw [← zpow_add₀ (by norm_num)]
        congr 1
        simp
        omega
  have htargetMinScale :
      fraction * (2 : Rat) ^ targetExponent <
        (2 : Rat) ^ minScale :=
    htargetUpper.trans_le
      (zpow_le_zpow_right₀
        (by norm_num : (1 : Rat) ≤ 2) hscaleBound)
  rw [← DyadicRounding.minPositive_toRat,
    DyadicRounding.minPositive_eq_fields]
  norm_num [FloatLib.Numerics.Dyadic.toRat,
    FloatLib.Numerics.Dyadic.signedSignificand]
  calc
    fraction * (2 : Rat) ^ targetExponent <
        (2 : Rat) ^ minScale :=
      htargetMinScale
    _ =
        (2 ^ (4 * (format.payloadBits - 1) : Nat) : Rat)⁻¹ := by
      dsimp [minScale]
      rw [zpow_neg]
      congr 1

/-!
## Layout of the direct lower candidate

Both regime signs pack the candidate as a regime prefix followed by the retained tail. The
lemmas below expose that shape and convert the natural run length back to the integer regime.
-/

/-- A positive-regime lower candidate is its regime prefix plus the retained tail. -/
private theorem lowerCandidateFromFields_eq_positive
    (format : Format) (regime : Int)
    (exponentField significand leading : Nat)
    (hregime : 0 ≤ regime)
    (hrun : regime.toNat + 1 < format.payloadBits) :
    DirectDyadicPacking.lowerCandidateFromFields
        format regime exponentField significand leading =
      (2 ^ (regime.toNat + 1) - 1) * 2 ^ (format.payloadBits - (regime.toNat + 1)) +
        DirectDyadicPacking.tailPrefix exponentField significand leading
          (format.payloadBits - (regime.toNat + 1) - 1) := by
  simp [DirectDyadicPacking.lowerCandidateFromFields, hregime, Nat.not_le.mpr hrun,
    Nat.shiftLeft_eq]

/-- A negative-regime lower candidate is its regime terminator plus the retained tail. -/
private theorem lowerCandidateFromFields_eq_negative
    (format : Format) (regime : Int)
    (exponentField significand leading : Nat)
    (hregime : regime < 0)
    (hrun : (-regime).toNat < format.payloadBits) :
    DirectDyadicPacking.lowerCandidateFromFields
        format regime exponentField significand leading =
      2 ^ (format.payloadBits - (-regime).toNat - 1) +
        DirectDyadicPacking.tailPrefix exponentField significand leading
          (format.payloadBits - (-regime).toNat - 1) := by
  simp [DirectDyadicPacking.lowerCandidateFromFields, Int.not_le.mpr hregime,
    Nat.not_le.mpr hrun, Nat.shiftLeft_eq]

/-- The positive-regime run length decodes back to the regime. -/
private theorem ofNat_toNat_add_one_sub_one (regime : Int) (hregime : 0 ≤ regime) :
    Int.ofNat (regime.toNat + 1) - 1 = regime := by
  simp only [Int.ofNat_eq_natCast]
  omega

/-- The negative-regime run length decodes back to the regime. -/
private theorem neg_ofNat_toNat_neg (regime : Int) (hregime : regime < 0) :
    -(Int.ofNat (-regime).toNat) = regime := by
  simp only [Int.ofNat_eq_natCast]
  omega

/-- The direct positive-regime lower candidate denotes its retained tail at the regime scale. -/
theorem lowerCandidateValue_positive
    (format : Format) (regime : Int)
    (exponentField significand leading : Nat)
    (hregime : 0 ≤ regime)
    (hrun : regime.toNat + 1 < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    Model.nonnegativeRatAt format
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading) =
      Model.trailingRat
          (format.payloadBits - (regime.toNat + 1) - 1)
          (DirectDyadicPacking.tailPrefix
              exponentField significand leading
              (format.payloadBits - (regime.toNat + 1) - 1)) *
        (2 : Rat) ^ (regime * 4) := by
  have hsemantic :=
    nonnegativeRatAt_positiveInterior format (regime.toNat + 1) _ (Nat.succ_pos _) hrun
      (DirectDyadicPacking.tailPrefix_lt_two_pow exponentField significand leading
        (format.payloadBits - (regime.toNat + 1) - 1) hexponent hlower hupper)
  rw [ofNat_toNat_add_one_sub_one regime hregime] at hsemantic
  rwa [lowerCandidateFromFields_eq_positive format regime exponentField significand leading
    hregime hrun]

/-- The direct negative-regime lower candidate denotes its retained tail at the regime scale. -/
theorem lowerCandidateValue_negative
    (format : Format) (regime : Int)
    (exponentField significand leading : Nat)
    (hregime : regime < 0)
    (hrun : (-regime).toNat < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    Model.nonnegativeRatAt format
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading) =
      Model.trailingRat
          (format.payloadBits - (-regime).toNat - 1)
          (DirectDyadicPacking.tailPrefix
              exponentField significand leading
              (format.payloadBits - (-regime).toNat - 1)) *
        (2 : Rat) ^ (regime * 4) := by
  have hsemantic :=
    nonnegativeRatAt_negativeInterior format (-regime).toNat _ (by omega) hrun
      (DirectDyadicPacking.tailPrefix_lt_two_pow exponentField significand leading
        (format.payloadBits - (-regime).toNat - 1) hexponent hlower hupper)
  rw [neg_ofNat_toNat_neg regime hregime] at hsemantic
  rwa [lowerCandidateFromFields_eq_negative format regime exponentField significand leading
    hregime hrun]

/--
The direct positive-regime candidate is never above its normalized exact target.

This is the lower half of the local adjacency certificate, proved by ordinary bitstream
truncation rather than by decoding a proposed candidate at runtime.
-/
theorem lowerCandidateValue_le_normalized_positive
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hregime : 0 ≤ regime)
    (hrun : regime.toNat + 1 < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    Model.nonnegativeRatAt format
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading) ≤
      (significand : Rat) * (2 : Rat) ^ targetExponent := by
  rw [lowerCandidateValue_positive format regime
    exponentField significand leading
    hregime hrun hexponent hlower hupper]
  rw [normalizedValue_eq_trailingRat_mul_regime
    targetExponent regime exponentField significand leading
    hexponent hlower hupper hscale]
  rw [tailPrefix_eq_streamPrefix
    exponentField significand leading
    (format.payloadBits - (regime.toNat + 1) - 1)
    hlower hupper]
  exact mul_le_mul_of_nonneg_right
    (trailingRat_streamPrefix_le_total
      (exactTailRaw_lt_two_pow
        exponentField significand leading
        hexponent hlower hupper))
    (zpow_pos (by norm_num : (0 : Rat) < 2) _).le

/--
The direct negative-regime candidate is never above its normalized exact target.

As in the positive-regime theorem, every live comparison reduces to the retained finite stream;
the regime scale is strictly positive and therefore preserves order.
-/
theorem lowerCandidateValue_le_normalized_negative
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hregime : regime < 0)
    (hrun : (-regime).toNat < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    Model.nonnegativeRatAt format
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading) ≤
      (significand : Rat) * (2 : Rat) ^ targetExponent := by
  rw [lowerCandidateValue_negative format regime
    exponentField significand leading
    hregime hrun hexponent hlower hupper]
  rw [normalizedValue_eq_trailingRat_mul_regime
    targetExponent regime exponentField significand leading
    hexponent hlower hupper hscale]
  rw [tailPrefix_eq_streamPrefix
    exponentField significand leading
    (format.payloadBits - (-regime).toNat - 1)
    hlower hupper]
  exact mul_le_mul_of_nonneg_right
    (trailingRat_streamPrefix_le_total
      (exactTailRaw_lt_two_pow
        exponentField significand leading
        hexponent hlower hupper))
    (zpow_pos (by norm_num : (0 : Rat) < 2) _).le

/--
The successor of an interior candidate is strictly above the normalized target.

`base` is the regime prefix of the candidate and `trailing` the number of retained tail positions.
When the complete exponent/fraction stream fits, the candidate is exact and global Posit
monotonicity proves the claim. Otherwise the successor either increments the retained tail or
carries into the next regime, which `hinterior` and `hcarry` decode; those cases follow from
finite-stream order and the universal `trailingRat < 16` regime bound.
-/
private theorem normalized_lt_succ_of_interior
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading base trailing : Nat)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField)
    (hcandidate :
      DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading =
        base + DirectDyadicPacking.tailPrefix exponentField significand leading trailing)
    (hinterior : ∀ tail, tail < 2 ^ trailing →
      Model.nonnegativeRatAt format (base + tail) =
        Model.trailingRat trailing tail * (2 : Rat) ^ (regime * 4))
    (hcarry :
      Model.nonnegativeRatAt format (base + (2 ^ trailing - 1) + 1) =
        (2 : Rat) ^ ((regime + 1) * 4))
    (hsuccessor :
      DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading + 1 <
        format.signMaskNat) :
    (significand : Rat) * (2 : Rat) ^ targetExponent <
      Model.nonnegativeRatAt format
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading + 1) := by
  set raw := exactTailRaw exponentField significand leading
  set width := leading + 2
  set tail := DirectDyadicPacking.tailPrefix exponentField significand leading trailing
  have hraw : raw < 2 ^ width :=
    exactTailRaw_lt_two_pow exponentField significand leading hexponent hlower hupper
  have htailBound : tail < 2 ^ trailing :=
    DirectDyadicPacking.tailPrefix_lt_two_pow exponentField significand leading trailing
      hexponent hlower hupper
  have htailStream : tail = streamPrefix raw width trailing :=
    tailPrefix_eq_streamPrefix exponentField significand leading trailing hlower hupper
  have hpos : (0 : Rat) < (2 : Rat) ^ (regime * 4) := zpow_pos (by norm_num) _
  rw [normalizedValue_eq_trailingRat_mul_regime targetExponent regime exponentField significand
    leading hexponent hlower hupper hscale]
  by_cases hcomplete : width ≤ trailing
  · have hvalue :
        Model.nonnegativeRatAt format
            (DirectDyadicPacking.lowerCandidateFromFields
              format regime exponentField significand leading) =
          Model.trailingRat width raw * (2 : Rat) ^ (regime * 4) := by
      rw [hcandidate, hinterior tail htailBound, htailStream,
        trailingRat_streamPrefix_eq_of_width_le raw width trailing hcomplete]
    rw [← hvalue]
    exact Model.nonnegativeRatAt_lt_of_lt format (Nat.lt_succ_self _) hsuccessor
  · rw [hcandidate]
    by_cases htailSucc : tail + 1 < 2 ^ trailing
    · rw [Nat.add_assoc, hinterior (tail + 1) htailSucc, htailStream]
      exact mul_lt_mul_of_pos_right
        (trailingRat_lt_streamPrefix_succ hraw (by omega) (htailStream ▸ htailSucc)) hpos
    · rw [show tail = 2 ^ trailing - 1 by omega, hcarry, regimeScale_succ]
      exact mul_lt_mul_of_pos_right (Model.trailingRat_bounds width raw).2 hpos

/-- The successor of the direct positive-regime candidate exceeds the normalized target. -/
theorem normalized_lt_lowerCandidateSuccessor_positive
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hregime : 0 ≤ regime)
    (hrun : regime.toNat + 1 < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField)
    (hsuccessor :
      DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading + 1 <
        format.signMaskNat) :
    (significand : Rat) * (2 : Rat) ^ targetExponent <
      Model.nonnegativeRatAt format
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading + 1) := by
  have hrunPos : 0 < regime.toNat + 1 := Nat.succ_pos _
  refine normalized_lt_succ_of_interior format targetExponent regime exponentField significand
    leading _ _ hexponent hlower hupper hscale
    (lowerCandidateFromFields_eq_positive format regime exponentField significand leading
      hregime hrun)
    (fun tail htail => by
      have hsemantic :=
        nonnegativeRatAt_positiveInterior format (regime.toNat + 1) tail hrunPos hrun htail
      rwa [ofNat_toNat_add_one_sub_one regime hregime] at hsemantic)
    (by
      have hsemantic :=
        nonnegativeRatAt_positiveInteriorCarry format (regime.toNat + 1) hrunPos hrun
      rwa [show Int.ofNat (regime.toNat + 1) = regime + 1 by
        have := ofNat_toNat_add_one_sub_one regime hregime
        omega] at hsemantic)
    hsuccessor

/-- The successor of the direct negative-regime candidate exceeds the normalized target. -/
theorem normalized_lt_lowerCandidateSuccessor_negative
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hregime : regime < 0)
    (hrun : (-regime).toNat < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField)
    (hsuccessor :
      DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading + 1 <
        format.signMaskNat) :
    (significand : Rat) * (2 : Rat) ^ targetExponent <
      Model.nonnegativeRatAt format
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading + 1) := by
  have hrunPos : 0 < (-regime).toNat := by omega
  refine normalized_lt_succ_of_interior format targetExponent regime exponentField significand
    leading _ _ hexponent hlower hupper hscale
    (lowerCandidateFromFields_eq_negative format regime exponentField significand leading
      hregime hrun)
    (fun tail htail => by
      have hsemantic :=
        nonnegativeRatAt_negativeInterior format (-regime).toNat tail hrunPos hrun htail
      rwa [neg_ofNat_toNat_neg regime hregime] at hsemantic)
    (by
      have hsemantic :=
        nonnegativeRatAt_negativeInteriorCarry format (-regime).toNat hrunPos hrun
      rwa [neg_ofNat_toNat_neg regime hregime] at hsemantic)
    hsuccessor

/--
For a positive regime, direct field packing returns exactly the specification's lower code.

The normalized-field invariants imply that the candidate lies below the target and its successor
lies above it. This bracket identifies the result with the specification's bisection result.
-/
theorem lowerCodeForPositive_eq_lowerCandidateFromFields_positive
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hregime : 0 ≤ regime)
    (hrun : regime.toNat + 1 < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    DyadicRounding.lowerCodeForPositive format
        { negative := false
          significand
          exponent := targetExponent } =
      DirectDyadicPacking.lowerCandidateFromFields
        format regime exponentField significand leading := by
  let candidate :=
    DirectDyadicPacking.lowerCandidateFromFields
      format regime exponentField significand leading
  apply DyadicRounding.lowerCodeForPositive_eq_of_bracket
  · exact DirectDyadicPacking.lowerCandidateFromFields_lt_signMask
      format regime exponentField significand leading
      hexponent hlower hupper
  · simp only [Dyadic.isLessOrEqual_eq_decide, decide_eq_true_eq,
      DyadicRounding.nonnegativeDyadicAt_toRat]
    change
      Model.nonnegativeRatAt format candidate ≤
        (significand : Rat) * (2 : Rat) ^ targetExponent
    exact lowerCandidateValue_le_normalized_positive
      format targetExponent regime exponentField significand leading
      hregime hrun hexponent hlower hupper hscale
  · intro hsuccessor
    simp only [Dyadic.isLess_eq_decide, decide_eq_true_eq,
      DyadicRounding.nonnegativeDyadicAt_toRat]
    change
      (significand : Rat) * (2 : Rat) ^ targetExponent <
        Model.nonnegativeRatAt format (candidate + 1)
    exact normalized_lt_lowerCandidateSuccessor_positive
      format targetExponent regime exponentField significand leading
      hregime hrun hexponent hlower hupper hscale hsuccessor

/--
For a negative regime, direct field packing returns exactly the specification's lower code.

Together with the positive-regime theorem this proves direct lower-code construction for every
interior normalized target, independently of the machine-word implementation that produced its
fields.
-/
theorem lowerCodeForPositive_eq_lowerCandidateFromFields_negative
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hregime : regime < 0)
    (hrun : (-regime).toNat < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    DyadicRounding.lowerCodeForPositive format
        { negative := false
          significand
          exponent := targetExponent } =
      DirectDyadicPacking.lowerCandidateFromFields
        format regime exponentField significand leading := by
  let candidate :=
    DirectDyadicPacking.lowerCandidateFromFields
      format regime exponentField significand leading
  apply DyadicRounding.lowerCodeForPositive_eq_of_bracket
  · exact DirectDyadicPacking.lowerCandidateFromFields_lt_signMask
      format regime exponentField significand leading
      hexponent hlower hupper
  · simp only [Dyadic.isLessOrEqual_eq_decide, decide_eq_true_eq,
      DyadicRounding.nonnegativeDyadicAt_toRat]
    change
      Model.nonnegativeRatAt format candidate ≤
        (significand : Rat) * (2 : Rat) ^ targetExponent
    exact lowerCandidateValue_le_normalized_negative
      format targetExponent regime exponentField significand leading
      hregime hrun hexponent hlower hupper hscale
  · intro hsuccessor
    simp only [Dyadic.isLess_eq_decide, decide_eq_true_eq,
      DyadicRounding.nonnegativeDyadicAt_toRat]
    change
      (significand : Rat) * (2 : Rat) ^ targetExponent <
        Model.nonnegativeRatAt format (candidate + 1)
    exact normalized_lt_lowerCandidateSuccessor_negative
      format targetExponent regime exponentField significand leading
      hregime hrun hexponent hlower hupper hscale hsuccessor

/-- The direct positive-regime lower candidate has the expected one-bit-wider boundary value. -/
theorem lowerCandidateThreshold_positive
    (format : Format) (regime : Int)
    (exponentField significand leading : Nat)
    (hregime : 0 ≤ regime)
    (hrun : regime.toNat + 1 < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    Model.nonnegativeRatAt format.nextPrecision
        (2 * DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading + 1) =
      Model.trailingRat
          (format.payloadBits - (regime.toNat + 1) - 1 + 1)
          (2 * DirectDyadicPacking.tailPrefix
              exponentField significand leading
              (format.payloadBits - (regime.toNat + 1) - 1) + 1) *
        (2 : Rat) ^ (regime * 4) := by
  have hsemantic :=
    nonnegativeRatAt_positiveInteriorThreshold format (regime.toNat + 1) _ (Nat.succ_pos _) hrun
      (DirectDyadicPacking.tailPrefix_lt_two_pow exponentField significand leading
        (format.payloadBits - (regime.toNat + 1) - 1) hexponent hlower hupper)
  rw [ofNat_toNat_add_one_sub_one regime hregime] at hsemantic
  rwa [lowerCandidateFromFields_eq_positive format regime exponentField significand leading
    hregime hrun]

/-- The direct negative-regime lower candidate has the expected one-bit-wider boundary value. -/
theorem lowerCandidateThreshold_negative
    (format : Format) (regime : Int)
    (exponentField significand leading : Nat)
    (hregime : regime < 0)
    (hrun : (-regime).toNat < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    Model.nonnegativeRatAt format.nextPrecision
        (2 * DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading + 1) =
      Model.trailingRat
          (format.payloadBits - (-regime).toNat - 1 + 1)
          (2 * DirectDyadicPacking.tailPrefix
              exponentField significand leading
              (format.payloadBits - (-regime).toNat - 1) + 1) *
        (2 : Rat) ^ (regime * 4) := by
  have hsemantic :=
    nonnegativeRatAt_negativeInteriorThreshold format (-regime).toNat _ (by omega) hrun
      (DirectDyadicPacking.tailPrefix_lt_two_pow exponentField significand leading
        (format.payloadBits - (-regime).toNat - 1) hexponent hlower hupper)
  rw [neg_ofNat_toNat_neg regime hregime] at hsemantic
  rwa [lowerCandidateFromFields_eq_negative format regime exponentField significand leading
    hregime hrun]

/--
The successor of an interior positive-regime candidate remains below the posit sign bit.

The retained tail has one fewer position than the gap between consecutive positive-regime
prefixes. Consequently even its maximal value, followed by the rounding increment, remains
strictly inside the nonnegative code interval.
-/
theorem lowerCandidateFromFields_succ_lt_signMask_positive
    (format : Format) (regime : Int)
    (exponentField significand leading : Nat)
    (hregime : 0 ≤ regime)
    (hrun : regime.toNat + 1 < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    DirectDyadicPacking.lowerCandidateFromFields
        format regime exponentField significand leading + 1 <
      format.signMaskNat := by
  have htail :=
    DirectDyadicPacking.tailPrefix_lt_two_pow exponentField significand leading
      (format.payloadBits - (regime.toNat + 1) - 1) hexponent hlower hupper
  have hpowers :
      2 ^ (regime.toNat + 1) * 2 ^ (format.payloadBits - (regime.toNat + 1)) =
        2 ^ format.payloadBits := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hrun.le]
  have hgapPow :
      2 ^ (format.payloadBits - (regime.toNat + 1)) =
        2 ^ (format.payloadBits - (regime.toNat + 1) - 1) * 2 :=
    (Nat.two_pow_pred_mul_two (by omega)).symm
  have hgapLe :
      2 ^ (format.payloadBits - (regime.toNat + 1)) ≤ 2 ^ format.payloadBits :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [lowerCandidateFromFields_eq_positive format regime exponentField significand leading
    hregime hrun]
  change _ < 2 ^ format.payloadBits
  rw [Nat.sub_one_mul, hpowers]
  omega

/--
The successor of an interior negative-regime candidate remains below the posit sign bit.

Here the leading regime marker occupies bit `trailing`; the tail and one rounding increment fit
below the next power of two, which itself lies strictly below the sign-bit position.
-/
theorem lowerCandidateFromFields_succ_lt_signMask_negative
    (format : Format) (regime : Int)
    (exponentField significand leading : Nat)
    (hregime : regime < 0)
    (hrun : (-regime).toNat < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1)) :
    DirectDyadicPacking.lowerCandidateFromFields
        format regime exponentField significand leading + 1 <
      format.signMaskNat := by
  have htail :=
    DirectDyadicPacking.tailPrefix_lt_two_pow exponentField significand leading
      (format.payloadBits - (-regime).toNat - 1) hexponent hlower hupper
  have hgapPow :
      2 ^ (format.payloadBits - (-regime).toNat) =
        2 ^ (format.payloadBits - (-regime).toNat - 1) * 2 :=
    (Nat.two_pow_pred_mul_two (by omega)).symm
  have hgapLt :
      2 ^ (format.payloadBits - (-regime).toNat) < 2 ^ format.payloadBits :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  rw [lowerCandidateFromFields_eq_negative format regime exponentField significand leading
    hregime hrun]
  change _ < 2 ^ format.payloadBits
  omega

end FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding
