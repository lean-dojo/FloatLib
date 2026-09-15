/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Descriptor
public import FloatLib.Kernels.FixedWord.Core.Runtime

/-!
# Shared fixed-carrier guard-and-sticky Posit rounding

One-word and two-limb posit kernels round the same normalized exponent/fraction stream. They
differ only in the carrier that holds the significand and the packed code, so everything from tail
inspection through candidate packing to the round-to-nearest-even decision is written once here
and instantiated by each carrier.

* `TailCarrier` records the two operations that reading the discarded tail needs: one bit, and
  whether a low-bit suffix is nonzero. `tailBit` and `tailHasNonzeroAfter` are the readers.
* `CandidateCarrier` extends it with the arithmetic that packing needs: shifts, an addition that
  callers keep from overflowing, a low-ones mask, the successor, the parity test, and the leading
  bit. `fractionPrefix`, `tailPrefix`, `lowerCandidateFromFields`, `roundInterior`, and
  `roundNormalizedPositive` form the shared kernel.

Both records are passed explicitly to always-inlined functions. The `UInt64` and `UInt128`
instances are transparent constants, allowing specialization to their primitive operations.
The sibling proof module
states the natural-number meaning of every operation (`LawfulTailCarrier`,
`LawfulCandidateCarrier`) and proves the shared kernel against the arbitrary-width rounder
`DirectDyadicPacking.roundPositiveCode`.

The two exponent bits are always stored in `UInt64`, so this module reads them through neutral
fixed-word primitives and depends on neither posit storage backend. Underflow detection, the zero
test, and sign restoration stay in the specialized kernels: they use carrier-specific comparison
and complement primitives with their own contracts.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.GuardStickyCarrier

/--
Operations needed to inspect the finite tail of a packed significand.

The structure contains executable data only. `LawfulTailCarrier` in the sibling proof module
states how these operations represent natural-number bit streams.
-/
structure TailCarrier (α : Type) where
  /-- Read one bit using least-significant-bit numbering. -/
  bitAt : α → Nat → Bool
  /-- Test whether any of the low `width` bits is set. -/
  hasLowBits : α → Nat → Bool

/--
Operations needed to pack and round a positive normalized posit candidate inside one fixed-width
carrier.

Every operation is total. Its natural-number meaning, stated by `LawfulCandidateCarrier`, is
guaranteed only under the bounds the shared rounder establishes: `add` and `increment` are exact
when the mathematical result fits the carrier, `shiftLeft` when the shifted value fits, `lowOnes`
below the carrier width, and `fractionBelow` on a significand whose leading one sits at the given
index. The structure contains executable data only.
-/
structure CandidateCarrier (α : Type) extends TailCarrier α where
  /-- Embed a machine word; used for the two-bit exponent field and the constants zero and one. -/
  ofWord : UInt64 → α
  /-- Shift left, returning zero once the shift reaches the carrier width. -/
  shiftLeft : α → Nat → α
  /-- Shift right, returning zero once the shift reaches the carrier width. -/
  shiftRight : α → Nat → α
  /-- Remove the leading one, at the given bit index, from a normalized significand. -/
  fractionBelow : α → Nat → α
  /-- Addition; exact whenever the mathematical sum fits the carrier. -/
  add : α → α → α
  /-- A mask whose low `width` bits are one. -/
  lowOnes : Nat → α
  /-- Successor; exact whenever it fits the carrier. -/
  increment : α → α
  /-- Whether the least significant bit is set. -/
  isOdd : α → Bool
  /-- Index of the leading one of a nonzero value. -/
  log2 : α → Nat

variable {α : Type}

/-- Read one bit of the two-bit exponent followed by the finite fraction. -/
@[always_inline, inline] def tailBit
    (carrier : TailCarrier α)
    (exponentField : UInt64) (significand : α)
    (leading index : Nat) : Bool :=
  if index < 2 then
    FloatLib.Numerics.FixedWord.bitAtWord
      exponentField (UInt64.ofNat (1 - index))
  else
    let fractionIndex := index - 2
    if fractionIndex < leading then
      carrier.bitAt significand (leading - fractionIndex - 1)
    else
      false

/-- Test whether the exact exponent/fraction suffix after `consumed` contains a one. -/
@[always_inline, inline] def tailHasNonzeroAfter
    (carrier : TailCarrier α)
    (exponentField : UInt64) (significand : α)
    (leading consumed : Nat) : Bool :=
  if consumed < 2 then
    let remainingExponentBits := 2 - consumed
    FloatLib.Numerics.FixedWord.lowBitsWord
        exponentField (UInt64.ofNat remainingExponentBits) != 0 ||
      carrier.hasLowBits significand leading
  else
    let consumedFractionBits := consumed - 2
    if consumedFractionBits < leading then
      carrier.hasLowBits significand (leading - consumedFractionBits)
    else
      false

/-- First `count` normalized fraction bits after the leading one at index `leading`. -/
@[always_inline, inline] def fractionPrefix
    (carrier : CandidateCarrier α) (significand : α) (leading count : Nat) : α :=
  let fraction := carrier.fractionBelow significand leading
  if count ≤ leading then
    carrier.shiftRight fraction (leading - count)
  else
    carrier.shiftLeft fraction (count - leading)

/-- Prefix of the standard two-bit exponent followed by the normalized fraction. -/
@[always_inline, inline] def tailPrefix
    (carrier : CandidateCarrier α)
    (exponentField : UInt64) (significand : α) (leading count : Nat) : α :=
  if count ≤ 2 then
    carrier.ofWord (exponentField >>> UInt64.ofNat (2 - count))
  else
    carrier.add
      (carrier.shiftLeft (carrier.ofWord exponentField) (count - 2))
      (fractionPrefix carrier significand leading (count - 2))

/--
Pack normalized regime, exponent, and significand fields into the unsigned lower posit candidate.

Regimes that consume the whole payload saturate to `maxPos` or truncate to zero. Interior regimes
place the run, its terminator, and the retained tail prefix.
-/
@[always_inline, inline] def lowerCandidateFromFields
    (carrier : CandidateCarrier α) (format : Format) (regime : Int)
    (exponentField : UInt64) (significand : α) (leading : Nat) : α :=
  let payload := format.payloadBits
  if 0 ≤ regime then
    let run := regime.toNat + 1
    if payload ≤ run then
      carrier.lowOnes payload
    else
      let trailing := payload - run - 1
      carrier.add
        (carrier.shiftLeft (carrier.lowOnes run) (payload - run))
        (tailPrefix carrier exponentField significand leading trailing)
  else
    let run := (-regime).toNat
    if payload ≤ run then
      carrier.ofWord 0
    else
      let trailing := payload - run - 1
      carrier.add
        (carrier.shiftLeft (carrier.ofWord 1) trailing)
        (tailPrefix carrier exponentField significand leading trailing)

/--
Round an interior normalized target to nearest even from its retained prefix, guard bit, and
sticky suffix.
-/
@[always_inline, inline] def roundInterior
    (carrier : CandidateCarrier α) (format : Format) (regime : Int)
    (exponentField : UInt64) (significand : α)
    (leading regimeFieldBits : Nat) : α :=
  let lower :=
    lowerCandidateFromFields carrier format regime exponentField significand leading
  let retainedTailBits := format.payloadBits - regimeFieldBits
  let guard :=
    tailBit carrier.toTailCarrier exponentField significand leading retainedTailBits
  let sticky :=
    tailHasNonzeroAfter carrier.toTailCarrier exponentField significand leading
      (retainedTailBits + 1)
  if guard && (sticky || carrier.isOdd lower) then
    carrier.increment lower
  else
    lower

/--
Round the nonzero positive value `significand * 2 ^ exponent`, known not to underflow, to its
unsigned posit code.

Regimes that consume the payload map directly to `maxPos` or `minPos`; interior values use the
field-oriented guard/sticky rule. For a lawful carrier whose capacity is strictly greater than the
format's payload width, the result is the carrier image of `DirectDyadicPacking.roundPositiveCode`
(`roundNormalizedPositive_toNat_eq_direct`).
-/
@[always_inline, inline] def roundNormalizedPositive
    (carrier : CandidateCarrier α) (format : Format)
    (significand : α) (exponent : Int) : α :=
  let leading := carrier.log2 significand
  let scale := exponent + Int.ofNat leading
  let regime := scale.ediv 4
  let exponentField := UInt64.ofNat (scale.emod 4).toNat
  if 0 ≤ regime then
    let run := regime.toNat + 1
    if format.payloadBits ≤ run then
      carrier.lowOnes format.payloadBits
    else
      roundInterior carrier format regime exponentField significand leading (run + 1)
  else
    let run := (-regime).toNat
    if format.payloadBits ≤ run then
      carrier.ofWord 1
    else
      roundInterior carrier format regime exponentField significand leading (run + 1)

end FloatLib.Floats.Formats.Posit.Model.GuardStickyCarrier
