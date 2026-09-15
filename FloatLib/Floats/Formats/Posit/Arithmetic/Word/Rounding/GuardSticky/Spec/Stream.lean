/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Candidate.Runtime
public import FloatLib.Numerics.Quantization.Deterministic
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Inv

/-!
# Pure guard-and-sticky Posit tail specification

The finite exponent/fraction stream specifies the bits consumed by fixed-word Posit packers. It
deliberately uses `Nat` and `Nat.testBit`: executable backends refine these functions to
machine-word operations, while the semantic proof relates the same stream to the standard's
one-bit-wider rounding boundary.

Keeping this specification independent of `UInt64` lets division, square root, and fixed-limb
backends use the same rounding argument.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding

/-- Explicit normalized fraction below the leading significand bit. -/
@[inline] def fractionRaw (significand leading : Nat) : Nat :=
  significand - 2 ^ leading

/--
Complete finite exponent/fraction stream as one natural number.

Its bit width is `leading + 2`: two exponent bits followed by `leading` explicit fraction bits.
-/
@[inline] def exactTailRaw
    (exponentField significand leading : Nat) : Nat :=
  exponentField * 2 ^ leading + fractionRaw significand leading

/--
Retain the first `count` bits of a finite most-significant-bit-first stream.

Requests longer than the finite stream append exact zero padding. This is the representation-free
counterpart of the shift logic used by `DirectDyadicPacking.tailPrefix`.
-/
@[inline] def streamPrefix (raw width count : Nat) : Nat :=
  if count ≤ width then
    raw / 2 ^ (width - count)
  else
    raw * 2 ^ (count - width)

/-- The first discarded bit of a finite most-significant-bit-first stream. -/
@[inline] def streamGuard (raw width retained : Nat) : Bool :=
  if retained < width then
    raw.testBit (width - retained - 1)
  else
    false

/--
Whether a finite stream has a nonzero bit strictly below its first discarded bit.

When no such position exists, the exponent of two is zero and the remainder modulo one is zero.
This total formulation avoids a second branch in both the specification and its native refinement.
-/
@[inline] def streamSticky (raw width retained : Nat) : Bool :=
  raw % 2 ^ (width - retained - 1) != 0

/--
Nearest-even rounding of a retained finite-stream prefix.

This is the representation-independent guard/sticky rule shared with binary-interchange
rounding: increment exactly when the guard bit is set and either a later bit is set or the
kept prefix is odd.
-/
@[inline] def roundStreamPrefix (raw width retained : Nat) : Nat :=
  let lower := streamPrefix raw width retained
  if streamGuard raw width retained &&
      (streamSticky raw width retained || lower % 2 != 0) then
    lower + 1
  else
    lower

/--
Pure field-oriented specification of the interior Posit packer.

`regimeFieldBits` includes the regime terminator, so the remaining payload positions retain an
exponent/fraction prefix. The complete lower code, rather than the tail prefix alone, supplies
the nearest-even parity bit. This distinction matters when the regime consumes the entire
retained payload except its terminator.
-/
@[inline] def roundInteriorCode
    (format : Format) (regime : Int)
    (exponentField significand leading regimeFieldBits : Nat) : Nat :=
  let lower :=
    DirectDyadicPacking.lowerCandidateFromFields
      format regime exponentField significand leading
  let retainedTailBits := format.payloadBits - regimeFieldBits
  let raw := exactTailRaw exponentField significand leading
  let guard := streamGuard raw (leading + 2) retainedTailBits
  let sticky := streamSticky raw (leading + 2) retainedTailBits
  if guard && (sticky || lower % 2 != 0) then
    lower + 1
  else
    lower

/--
The generic guard/sticky rule is the ordinary nearest-even power-of-two shift rounder.

Posit-specific proofs only need to identify their conceptual exponent/fraction stream with
`raw`; the rounding mathematics itself is shared with the binary-interchange backend.
-/
theorem roundStreamPrefix_eq_roundShiftRightEven
    (raw width retained : Nat) (hretained : retained ≤ width) :
    roundStreamPrefix raw width retained =
      FloatLib.Numerics.roundShiftRightEven raw (width - retained) := by
  rcases Nat.eq_or_lt_of_le hretained with hequal | hlt
  · subst hequal
    simp [roundStreamPrefix, streamPrefix, streamGuard, streamSticky]
  · obtain ⟨shift, hshift⟩ : ∃ shift, width - retained = shift + 1 :=
      ⟨width - retained - 1, by omega⟩
    have hhalfPos := Nat.two_pow_pos shift
    have hmodLt := Nat.mod_lt raw hhalfPos
    have hmod :
        raw % 2 ^ (shift + 1) =
          raw % 2 ^ shift + 2 ^ shift * (raw / 2 ^ shift % 2) := by
      rw [Nat.pow_succ, Nat.mod_mul]
    rw [roundStreamPrefix, streamPrefix, streamGuard, streamSticky, ite_eq_left hretained,
      ite_eq_left hlt, show width - retained - 1 = shift by omega, hshift,
      FloatLib.Numerics.roundShiftRightEven_def, Nat.testBit_eq_decide_div_mod_eq]
    simp only [Nat.shiftRight_eq', Nat.shiftLeft_eq', Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
      ← Nat.mod_eq_sub_div_mul, hmod, Nat.add_one_ne_zero, beq_iff_eq, ite_false,
      Nat.add_sub_cancel]
    rcases Nat.mod_two_eq_zero_or_one (raw / 2 ^ shift) with hguard | hguard <;>
      rcases Nat.mod_two_eq_zero_or_one (raw / 2 ^ (shift + 1)) with hparity | hparity <;>
      simp [hguard, hparity] <;> (try split_ifs) <;> omega

end FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding
