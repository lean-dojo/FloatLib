/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.GuardSticky.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.GuardSticky.Spec
public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Candidate.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Proof
import FloatLib.Kernels.FixedWord.Core.Proof.Word
public import FloatLib.Numerics.Exact.Dyadic.Comparison.Proof
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Pow

/-!
# Laws and correctness of carrier-generic guard-and-sticky rounding

The shared rounding kernel is written once for every carrier, so its proof has to know what each
carrier operation that `GuardStickyCarrier` uses means as a natural number. `LawfulTailCarrier` and
`LawfulCandidateCarrier` say that, and no more than the kernel needs. Every arithmetic law holds
only under bounds the kernel itself establishes, which is why wrapping machine operations can
satisfy them. We prove the concrete `UInt64` and `UInt128` records lawful next to their kernels.

Take a lawful carrier of `capacity` bits and a format whose payload is shorter than `capacity`.
Then the shared kernel is an execution refinement of the arbitrary-width direct rounder:

* `tailBit_eq_spec` and `tailHasNonzeroAfter_eq_spec` cover reading the tail,
* `lowerCandidateFromFields_toNat` covers packing,
* `roundNormalizedPositive_toNat_eq_direct` covers the whole positive rounder, against
  `DirectDyadicPacking.roundPositiveCode`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.GuardStickyCarrier

variable {α : Type}

/--
Natural-number semantics of a finite-tail carrier.

This record lives in `Prop`, and the executable carrier contains only the operations.
-/
structure LawfulTailCarrier
    (carrier : TailCarrier α) (toNat : α → Nat) : Prop where
  /-- Carrier bit reads agree with natural-number bit reads. -/
  bitAt_eq_testBit :
    ∀ value index, carrier.bitAt value index = (toNat value).testBit index
  /-- Carrier suffix tests are natural-number remainder tests. -/
  hasLowBits_eq :
    ∀ value width,
      carrier.hasLowBits value width = (toNat value % 2 ^ width != 0)

/--
Natural-number semantics of a candidate carrier of `capacity` bits.

Each law holds only under the bound the shared rounder establishes before applying the operation,
so the record can be instantiated by wrapping machine arithmetic. Like `LawfulTailCarrier`, it is
a proof record that callers pass as an argument.
-/
structure LawfulCandidateCarrier
    (carrier : CandidateCarrier α) (toNat : α → Nat) (capacity : Nat) : Prop
    extends LawfulTailCarrier carrier.toTailCarrier toNat where
  /-- Every carrier value is below `2 ^ capacity`. -/
  toNat_lt : ∀ value, toNat value < 2 ^ capacity
  /-- Embedding a machine word is exact. -/
  toNat_ofWord : ∀ word, toNat (carrier.ofWord word) = word.toNat
  /-- A left shift below the carrier width whose result fits is exact. -/
  shiftLeft_toNat :
    ∀ value shift, shift < capacity → toNat value <<< shift < 2 ^ capacity →
      toNat (carrier.shiftLeft value shift) = toNat value <<< shift
  /-- A right shift below the carrier width is exact. -/
  shiftRight_toNat :
    ∀ value shift, shift < capacity →
      toNat (carrier.shiftRight value shift) = toNat value >>> shift
  /-- Removing the leading one of a normalized significand subtracts its power of two. -/
  fractionBelow_toNat :
    ∀ value leading, leading < capacity → 2 ^ leading ≤ toNat value →
      toNat value < 2 ^ (leading + 1) →
      toNat (carrier.fractionBelow value leading) = toNat value - 2 ^ leading
  /-- Addition is exact when the mathematical sum fits the carrier. -/
  add_toNat :
    ∀ left right, toNat left + toNat right < 2 ^ capacity →
      toNat (carrier.add left right) = toNat left + toNat right
  /-- The low-ones mask below the carrier width has its mathematical value. -/
  lowOnes_toNat :
    ∀ width, width < capacity → toNat (carrier.lowOnes width) = 2 ^ width - 1
  /-- The successor is exact when it fits the carrier. -/
  increment_toNat :
    ∀ value, toNat value + 1 < 2 ^ capacity →
      toNat (carrier.increment value) = toNat value + 1
  /-- The parity test reads the least significant bit. -/
  isOdd_eq : ∀ value, carrier.isOdd value = (toNat value % 2 != 0)
  /-- The leading-bit index is the natural-number logarithm. -/
  log2_eq : ∀ value, carrier.log2 value = (toNat value).log2

/--
The tail laws of a lawful candidate carrier: its bit reads and suffix tests are the natural-number
ones. `tailBit_eq_spec` and `tailHasNonzeroAfter_eq_spec` take this projection.
-/
add_decl_doc LawfulCandidateCarrier.toLawfulTailCarrier

/-- A neutral fixed-word suffix test is the corresponding natural-number remainder test. -/
private theorem lowBitsWord_ne_zero_eq
    (value : UInt64) (width : Nat) (hwidth : width ≤ 64) :
    (FloatLib.Numerics.FixedWord.lowBitsWord
        value (UInt64.ofNat width) != 0) =
      (value.toNat % 2 ^ width != 0) := by
  have hwidthBound : width < 2 ^ 64 :=
    hwidth.trans_lt (by norm_num)
  have hwidthNat : (UInt64.ofNat width).toNat = width :=
    UInt64.toNat_ofNat_of_lt hwidthBound
  have hbits :=
    FloatLib.Numerics.FixedWord.lowBitsWord_toNat
      value (UInt64.ofNat width)
  rw [hwidthNat] at hbits
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne]
  constructor
  · intro hword hremainder
    apply hword
    apply UInt64.toNat_inj.mp
    rw [hbits]
    simpa using hremainder
  · intro hremainder hword
    apply hremainder
    have equality := congrArg UInt64.toNat hword
    rw [hbits] at equality
    simpa using equality

section Tail

variable
  {carrier : TailCarrier α} {toNat : α → Nat}
  (lawful : LawfulTailCarrier carrier toNat)

include lawful

/-- Shared carrier bit inspection reads the representation-independent normalized tail stream. -/
theorem tailBit_eq_spec
    (exponentField : UInt64) (significand : α) (leading index : Nat) :
    tailBit carrier exponentField significand leading index =
      GuardStickyRounding.tailBit
        exponentField.toNat (toNat significand) leading index := by
  unfold tailBit GuardStickyRounding.tailBit
  split
  next hindex =>
    rw [FloatLib.Numerics.FixedWord.bitAtWord_eq_testBit]
    rw [UInt64.toNat_ofNat_of_lt' (by omega : 1 - index < 2 ^ 64)]
  · dsimp only
    split
    · exact LawfulTailCarrier.bitAt_eq_testBit lawful _ _
    · rfl

/-- Shared carrier suffix inspection is the representation-independent sticky-bit query. -/
theorem tailHasNonzeroAfter_eq_spec
    (exponentField : UInt64) (significand : α)
    (leading consumed : Nat) :
    tailHasNonzeroAfter carrier exponentField significand leading consumed =
      GuardStickyRounding.tailHasNonzeroAfter
        exponentField.toNat (toNat significand) leading consumed := by
  unfold tailHasNonzeroAfter GuardStickyRounding.tailHasNonzeroAfter
  split
  next =>
    let remainingExponentBits := 2 - consumed
    have hremaining : remainingExponentBits ≤ 64 := by
      dsimp [remainingExponentBits]
      omega
    change
      (FloatLib.Numerics.FixedWord.lowBitsWord
            exponentField (UInt64.ofNat remainingExponentBits) != 0 ||
          carrier.hasLowBits significand leading) =
        (exponentField.toNat % 2 ^ remainingExponentBits != 0 ||
          toNat significand % 2 ^ leading != 0)
    rw [lowBitsWord_ne_zero_eq exponentField
      remainingExponentBits hremaining]
    rw [LawfulTailCarrier.hasLowBits_eq lawful]
  next =>
    let consumedFractionBits := consumed - 2
    change
      (if consumedFractionBits < leading then
          carrier.hasLowBits significand (leading - consumedFractionBits)
        else false) =
        if consumedFractionBits < leading then
          toNat significand % 2 ^ (leading - consumedFractionBits) != 0
        else false
    split
    next =>
      exact LawfulTailCarrier.hasLowBits_eq lawful significand
        (leading - consumedFractionBits)
    next =>
      rfl

end Tail

end FloatLib.Floats.Formats.Posit.Model.GuardStickyCarrier

namespace FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding

open FloatLib.Numerics

/--
The direct rounder's leading-bit underflow test is comparison against the smallest positive
posit, whatever native carrier a backend uses.
-/
theorem isLessPowerOfTwoAtLeading_leadingBit_eq_isLess_minPositive
    (format : Format) (significand : Nat) (exponent : Int) :
    Dyadic.isLessPowerOfTwoAtLeading significand exponent
        (DirectDyadicPacking.leadingBit significand)
        (-(4 * Int.ofNat (format.payloadBits - 1))) =
      ({ negative := false, significand, exponent } : FloatLib.Numerics.Dyadic).isLess
        (DyadicRounding.minPositive format) := by
  rw [Dyadic.isLessPowerOfTwoAtLeading_eq significand exponent _ _
      (DirectDyadicPacking.leadingBit_eq_log2 significand),
    Dyadic.isLessNonnegativeFields_eq, Dyadic.isLessFields_eq,
    DyadicRounding.minPositive_eq_fields]

/-- The exponent field extracted from a scale occupies the two standard exponent bits. -/
theorem emod_four_toNat_lt (scale : Int) : (scale.emod 4).toNat < 4 := by
  change (scale % 4).toNat < 4
  omega

/-- Storing the two-bit exponent field in a machine word is exact. -/
private theorem toNat_ofNat_emod_four_toNat (scale : Int) :
    (UInt64.ofNat (scale.emod 4).toNat).toNat = (scale.emod 4).toNat :=
  UInt64.toNat_ofNat_of_lt ((emod_four_toNat_lt scale).trans (by decide))

/-- The regime of a scale is its arithmetic right shift by two. -/
theorem shiftRight_two_eq_ediv (scale : Int) : scale >>> 2 = scale.ediv 4 := by
  rw [Int.shiftRight_eq_div_pow]
  rfl

/-- The low two bits of the wrapped scale are its exponent field. -/
theorem toUInt64_ofInt_and_three (scale : Int) :
    (Int64.ofInt scale).toUInt64 &&& 3 = UInt64.ofNat (scale.emod 4).toNat := by
  apply UInt64.toNat_inj.mp
  rw [toNat_ofNat_emod_four_toNat, UInt64.toNat_and]
  have hwrap : (Int64.ofInt scale).toUInt64.toNat = (scale % 2 ^ 64).toNat := by
    rw [← UInt64.toNat_toBitVec, Int64.toBitVec_toUInt64]
    exact BitVec.toNat_ofInt scale
  rw [hwrap, show (3 : UInt64).toNat = 2 ^ 2 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  change (scale % 2 ^ 64).toNat % 2 ^ 2 = (scale % 4).toNat
  norm_num
  omega

end FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding

namespace FloatLib.Floats.Formats.Posit.Model.GuardStickyCarrier

open FloatLib.Numerics

variable {α : Type}
  {carrier : CandidateCarrier α} {toNat : α → Nat} {capacity : Nat}
  (lawful : LawfulCandidateCarrier carrier toNat capacity)

include lawful

/-! ## Packed field refinement -/

/-- Adding a tail to a shifted prefix is exact when the mathematical sum fits the carrier. -/
private theorem add_shiftLeft_toNat
    (base tail : α) (shift : Nat) (hshift : shift < capacity)
    (hfit : toNat base <<< shift + toNat tail < 2 ^ capacity) :
    toNat (carrier.add (carrier.shiftLeft base shift) tail) =
      toNat base <<< shift + toNat tail := by
  have hbase : toNat base <<< shift < 2 ^ capacity := by omega
  rw [lawful.add_toNat _ _ (by rw [lawful.shiftLeft_toNat _ _ hshift hbase]; exact hfit),
    lawful.shiftLeft_toNat _ _ hshift hbase]

/-- The shared fraction-prefix kernel implements the representation-independent normalized prefix. -/
theorem fractionPrefix_toNat
    (significand : α) (leading count : Nat) (hcount : count < capacity)
    (hlower : 2 ^ leading ≤ toNat significand)
    (hupper : toNat significand < 2 ^ (leading + 1)) :
    toNat (fractionPrefix carrier significand leading count) =
      DirectDyadicPacking.fractionPrefix (toNat significand) leading count := by
  have hleading : leading < capacity :=
    (Nat.pow_lt_pow_iff_right (by decide)).mp (hlower.trans_lt (lawful.toNat_lt significand))
  have hfraction :
      toNat (carrier.fractionBelow significand leading) = toNat significand - 2 ^ leading :=
    lawful.fractionBelow_toNat significand leading hleading hlower hupper
  unfold fractionPrefix DirectDyadicPacking.fractionPrefix
  split
  next =>
    have hshift : leading - count < capacity := by omega
    rw [lawful.shiftRight_toNat _ _ hshift, hfraction]
    simp only [Nat.shiftLeft_eq, one_mul]
  next hprefix =>
    have hshift : count - leading < capacity := by omega
    have hprefixBound :
        DirectDyadicPacking.fractionPrefix (toNat significand) leading count < 2 ^ count :=
      DirectDyadicPacking.fractionPrefix_lt_two_pow (toNat significand) leading count hlower hupper
    have hfit : (toNat significand - 2 ^ leading) <<< (count - leading) < 2 ^ capacity := by
      have hcountPower : 2 ^ count < 2 ^ capacity := Nat.pow_lt_pow_right (by decide) hcount
      unfold DirectDyadicPacking.fractionPrefix at hprefixBound
      simp only [Nat.shiftLeft_eq, one_mul] at hprefixBound
      rw [ite_eq_right hprefix] at hprefixBound
      simpa only [Nat.shiftLeft_eq] using hprefixBound.trans hcountPower
    have hfitCarrier :
        toNat (carrier.fractionBelow significand leading) <<< (count - leading) < 2 ^ capacity := by
      rw [hfraction]
      exact hfit
    rw [lawful.shiftLeft_toNat _ _ hshift hfitCarrier, hfraction]
    simp only [Nat.shiftLeft_eq, one_mul]

/-- The shared exponent/fraction prefix is the representation-independent tail prefix. -/
theorem tailPrefix_toNat
    (exponentField : UInt64) (significand : α) (leading count : Nat)
    (hcount : count < capacity) (hexponent : exponentField.toNat < 4)
    (hlower : 2 ^ leading ≤ toNat significand)
    (hupper : toNat significand < 2 ^ (leading + 1)) :
    toNat (tailPrefix carrier exponentField significand leading count) =
      DirectDyadicPacking.tailPrefix exponentField.toNat (toNat significand) leading count := by
  unfold tailPrefix DirectDyadicPacking.tailPrefix
  split
  next =>
    have hshift : 2 - count < 64 := by omega
    rw [lawful.toNat_ofWord]
    exact FixedWord.shiftRight_toNat exponentField (2 - count) hshift
  next hprefix =>
    have hshift : count - 2 < capacity := by omega
    have hcountPower : 2 ^ count < 2 ^ capacity := Nat.pow_lt_pow_right (by decide) hcount
    have htailBound :
        exponentField.toNat <<< (count - 2) +
            DirectDyadicPacking.fractionPrefix (toNat significand) leading (count - 2) <
          2 ^ count := by
      have htail :=
        DirectDyadicPacking.tailPrefix_lt_two_pow
          exponentField.toNat (toNat significand) leading count hexponent hlower hupper
      unfold DirectDyadicPacking.tailPrefix at htail
      rw [ite_eq_right hprefix] at htail
      exact htail
    have hfraction :=
      fractionPrefix_toNat lawful significand leading (count - 2) (by omega) hlower hupper
    rw [add_shiftLeft_toNat lawful _ _ _ hshift
        (by rw [lawful.toNat_ofWord, hfraction]; exact htailBound.trans hcountPower),
      lawful.toNat_ofWord, hfraction]

/--
Shared field packing implements the representation-independent lower-candidate constructor
whenever the format's payload is shorter than the carrier.
-/
theorem lowerCandidateFromFields_toNat
    (format : Format) (regime : Int) (exponentField : UInt64) (significand : α) (leading : Nat)
    (hpayload : format.payloadBits < capacity)
    (hexponent : exponentField.toNat < 4)
    (hlower : 2 ^ leading ≤ toNat significand)
    (hupper : toNat significand < 2 ^ (leading + 1)) :
    toNat (lowerCandidateFromFields carrier format regime exponentField significand leading) =
      DirectDyadicPacking.lowerCandidateFromFields format regime
        exponentField.toNat (toNat significand) leading := by
  have hsignMaskLt : format.signMaskNat < 2 ^ capacity :=
    Nat.pow_lt_pow_right (by decide) hpayload
  have hfit :=
    (DirectDyadicPacking.lowerCandidateFromFields_lt_signMask
      format regime exponentField.toNat (toNat significand) leading
      hexponent hlower hupper).trans hsignMaskLt
  simp only [lowerCandidateFromFields, DirectDyadicPacking.lowerCandidateFromFields,
    Nat.shiftLeft_eq, one_mul] at hfit ⊢
  split_ifs at hfit ⊢ with hregime hrun hrun
  · exact lawful.lowOnes_toNat _ hpayload
  · have hrunLt : regime.toNat + 1 < capacity := by omega
    have hshift : format.payloadBits - (regime.toNat + 1) < capacity := by omega
    have hones := lawful.lowOnes_toNat (regime.toNat + 1) hrunLt
    have htail :=
      tailPrefix_toNat lawful exponentField significand leading
        (format.payloadBits - (regime.toNat + 1) - 1) (by omega) hexponent hlower hupper
    rw [add_shiftLeft_toNat lawful _ _ _ hshift
        (by rw [hones, Nat.shiftLeft_eq, htail]; exact hfit),
      hones, Nat.shiftLeft_eq, htail]
  · rw [lawful.toNat_ofWord]
    rfl
  · have htrailing : format.payloadBits - (-regime).toNat - 1 < capacity := by omega
    have htail :=
      tailPrefix_toNat lawful exponentField significand leading
        (format.payloadBits - (-regime).toNat - 1) htrailing hexponent hlower hupper
    rw [add_shiftLeft_toNat lawful _ _ _ htrailing
        (by rw [lawful.toNat_ofWord, UInt64.toNat_one, Nat.shiftLeft_eq, one_mul, htail]
            exact hfit),
      lawful.toNat_ofWord, UInt64.toNat_one, Nat.shiftLeft_eq, one_mul, htail]

/-! ## Rounding -/

/--
The shared interior rounder implements the field-oriented nearest-even rule.

The theorem covers packed field construction, guard/sticky inspection, retained parity, and
the increment, whose result fits the carrier.
-/
theorem roundInterior_toNat
    (format : Format) (regime : Int) (exponentField : UInt64) (significand : α)
    (leading regimeFieldBits : Nat)
    (hpayload : format.payloadBits < capacity)
    (hexponent : exponentField.toNat < 4)
    (hlower : 2 ^ leading ≤ toNat significand)
    (hupper : toNat significand < 2 ^ (leading + 1)) :
    toNat (roundInterior carrier format regime exponentField significand
        leading regimeFieldBits) =
      GuardStickyRounding.roundInteriorCodeFromFields format regime
        exponentField.toNat (toNat significand) leading regimeFieldBits := by
  have hlowerCode :=
    lowerCandidateFromFields_toNat lawful format regime exponentField significand leading
      hpayload hexponent hlower hupper
  have hlowerRange :
      toNat (lowerCandidateFromFields carrier format regime exponentField significand leading) <
        format.signMaskNat := by
    rw [hlowerCode]
    exact DirectDyadicPacking.lowerCandidateFromFields_lt_signMask
      format regime exponentField.toNat (toNat significand) leading hexponent hlower hupper
  have hsignMaskLt : format.signMaskNat < 2 ^ capacity :=
    Nat.pow_lt_pow_right (by decide) hpayload
  have hincrementFit :
      toNat (lowerCandidateFromFields carrier format regime exponentField significand leading) +
          1 < 2 ^ capacity := by
    omega
  unfold roundInterior GuardStickyRounding.roundInteriorCodeFromFields
  dsimp only
  rw [tailBit_eq_spec lawful.toLawfulTailCarrier,
    tailHasNonzeroAfter_eq_spec lawful.toLawfulTailCarrier, lawful.isOdd_eq, hlowerCode]
  split
  next =>
    rw [lawful.increment_toNat _ hincrementFit, hlowerCode]
  next =>
    exact hlowerCode

/--
The shared normalized rounder is the arbitrary-width direct positive rounder.

The significand must be nonzero. Values below `minPos`, whose regime run fills the payload, round
to code 1 on both sides. The payload bound is what makes every intermediate fit the carrier.
-/
theorem roundNormalizedPositive_toNat_eq_direct
    (format : Format) (significand : α) (exponent : Int)
    (hpayload : format.payloadBits < capacity)
    (hnonzero : toNat significand ≠ 0) :
    toNat (roundNormalizedPositive carrier format significand exponent) =
      DirectDyadicPacking.roundPositiveCode format
        { negative := false
          significand := toNat significand
          exponent } := by
  have hzero : (toNat significand == 0) = false := by
    simpa only [beq_eq_false_iff_ne] using hnonzero
  have hlower : 2 ^ (toNat significand).log2 ≤ toNat significand :=
    Nat.log2_self_le hnonzero
  have hupper : toNat significand < 2 ^ ((toNat significand).log2 + 1) :=
    Nat.lt_log2_self
  have hexponent (scale : Int) :
      (UInt64.ofNat (scale.emod 4).toNat).toNat < 4 := by
    rw [GuardStickyRounding.toNat_ofNat_emod_four_toNat]
    exact GuardStickyRounding.emod_four_toNat_lt scale
  unfold DirectDyadicPacking.roundPositiveCode roundNormalizedPositive
  simp only [GuardStickyRounding.shiftRight_two_eq_ediv,
    GuardStickyRounding.toUInt64_ofInt_and_three]
  simp only [hzero, Bool.false_or, Bool.false_eq_true, ite_false]
  simp only [DirectDyadicPacking.leadingBit_eq_log2, lawful.log2_eq]
  by_cases hunderflow :
      Dyadic.isLessPowerOfTwoAtLeading (toNat significand) exponent (toNat significand).log2
        (-(4 * Int.ofNat (format.payloadBits - 1))) = true
  · -- Below `minPos` the regime is negative and its run fills the payload.
    rw [ite_eq_left hunderflow]
    unfold Dyadic.isLessPowerOfTwoAtLeading at hunderflow
    simp only [hzero, Bool.false_eq_true, ite_false, decide_eq_true_eq,
      Int.ofNat_eq_natCast] at hunderflow
    have hpositive := format.payloadBits_pos
    have hscale : (exponent + Int.ofNat (toNat significand).log2).ediv 4 =
        (exponent + Int.ofNat (toNat significand).log2) / 4 := rfl
    have hregime : ¬0 ≤ (exponent + Int.ofNat (toNat significand).log2).ediv 4 := by
      rw [hscale, Int.ofNat_eq_natCast]
      omega
    have hrun : format.payloadBits ≤
        (-(exponent + Int.ofNat (toNat significand).log2).ediv 4).toNat := by
      rw [hscale, Int.ofNat_eq_natCast]
      omega
    rw [ite_eq_right hregime, ite_eq_left hrun, lawful.toNat_ofWord]
    exact UInt64.toNat_one
  rw [ite_eq_right hunderflow]
  split_ifs with hregime hsaturated hsaturated
  · rw [lawful.lowOnes_toNat _ hpayload]
    rfl
  · rw [roundInterior_toNat lawful format _ _ _ _ _ hpayload (hexponent _) hlower hupper,
      GuardStickyRounding.toNat_ofNat_emod_four_toNat]
  · rw [lawful.toNat_ofWord]
    exact UInt64.toNat_one
  · rw [roundInterior_toNat lawful format _ _ _ _ _ hpayload (hexponent _) hlower hupper,
      GuardStickyRounding.toNat_ofNat_emod_four_toNat]

end FloatLib.Floats.Formats.Posit.Model.GuardStickyCarrier
