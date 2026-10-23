/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Product.Runtime
public import FloatLib.Kernels.FixedWord.Difference.Runtime

/-!
# Fixed-limb rounding

Two- and four-limb shifts and nearest-even rounding, with guard, sticky, and carry results.
Fixed tuples give these small kernels a statically sized representation. Callers handle exponents
and packing, and `LimbRound.Proof` relates the operations to natural-number arithmetic.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/-- Increment modulo `2^128`, propagating the low-word carry. -/
@[inline] def UInt128.increment (value : UInt128) : UInt128 :=
  let sum := add64 value.lo 1
  ⟨value.hi + sum.carry, sum.value⟩

/-- `UInt128.increment` with the low-word carry kept as a native word. -/
@[inline] def UInt128.Internal.increment (value : UInt128) : UInt128 :=
  let low := value.lo + 1
  ⟨value.hi + (if low < value.lo then 1 else 0), low⟩

/-- Compiled code runs `UInt128.increment` as `UInt128.Internal.increment`. The two are equal by
`rfl`. -/
-- grind: no rule; this equation selects a compiler implementation.
@[csimp] theorem UInt128.increment_eq_internal :
    @UInt128.increment = @UInt128.Internal.increment := rfl

/-- Set the least-significant bit of a two-limb value. -/
@[inline] def UInt128.setLowBit (value : UInt128) : UInt128 :=
  ⟨value.hi, value.lo ||| 1⟩

namespace UInt128

/-- Shift a two-word value right by one bit. -/
@[inline] def shiftRightOne (value : UInt128) : UInt128 :=
  {
    hi := value.hi >>> 1
    lo := (value.lo >>> 1) ||| ((value.hi &&& 1) <<< 63)
  }

/--
Round a two-word value right by one bit using round-to-nearest, ties-to-even.

For a one-bit shift, the quotient is incremented exactly when the two low input bits are `11`.
-/
@[inline] def roundShiftRightOneEven (value : UInt128) : UInt128 :=
  let quotient := value.shiftRightOne
  if (value.lo &&& 3) == 3 then
    quotient.increment
  else
    quotient

/-- Low 64 bits of a right shift by an amount strictly between zero and 64. -/
@[inline] def shiftRightLow (value : UInt128) (shift : Nat) : UInt64 :=
  (value.lo >>> UInt64.ofNat shift) |||
    (value.hi <<< UInt64.ofNat (64 - shift))

/--
Round a two-limb value right by `shift`, returning a single native word.

The kernel is meaningful for `0 < shift < 64` with `value.hi < 2^shift`, so that the quotient
fits one word, and callers also keep the incremented quotient below `2^64`.
`roundShiftRightEven_toNat` states these hypotheses.
-/
@[inline] def roundShiftRightEven (value : UInt128) (shift : Nat) : UInt64 :=
  let quotient := shiftRightLow value shift
  let remainder := value.lo &&& ((1 <<< UInt64.ofNat shift) - 1)
  let half := (1 : UInt64) <<< UInt64.ofNat (shift - 1)
  if remainder < half then
    quotient
  else if remainder > half then
    quotient + 1
  else if (quotient &&& 1) == 0 then
    quotient
  else
    quotient + 1

/--
Round a two-limb value right by `shift` using round-to-nearest, ties-to-even, keeping both limbs.

The kernel is meaningful for `0 < shift < 64`, the contract of
`UInt128.roundShiftRightEven128_toNat`.
-/
@[inline] def roundShiftRightEven128 (value : UInt128) (shift : Nat) : UInt128 :=
  let quotient := value.shiftRight shift
  let remainder := value.lo &&& ((1 <<< UInt64.ofNat shift) - 1)
  let half := (1 : UInt64) <<< UInt64.ofNat (shift - 1)
  if remainder < half then
    quotient
  else if remainder > half then
    quotient.increment
  else if (quotient.lo &&& 1) == 0 then
    quotient
  else
    quotient.increment

/-- `FixedWord.jamCombine` on two-word values (`UInt128.jamCombine_toNat`). -/
@[inline] def jamCombine (sameSign exact : Bool) (A q : UInt128) : UInt128 :=
  if sameSign then
    let sum := (add128 A q).value
    if exact then sum else sum.setLowBit
  else
    let difference := A.sub q
    if exact then difference else (difference.sub ⟨0, 1⟩).setLowBit

end UInt128

namespace UInt256

/--
Low 128 bits of a four-word right shift.

Shifts at and beyond 256 return zero. A caller that needs the complete quotient must show that
no nonzero bit remains above the returned two-word window. The limb ranges avoid the modulo
reduction performed by native machine-word shifts.
-/
@[inline] def shiftRight128 (value : UInt256) (shift : Nat) : UInt128 :=
  if shift == 0 then
    ⟨value.limb1, value.limb0⟩
  else if shift < 64 then
    let complement := 64 - shift
    {
      hi := (value.limb1 >>> UInt64.ofNat shift) |||
        (value.limb2 <<< UInt64.ofNat complement)
      lo := (value.limb0 >>> UInt64.ofNat shift) |||
        (value.limb1 <<< UInt64.ofNat complement)
    }
  else if shift == 64 then
    ⟨value.limb2, value.limb1⟩
  else if shift < 128 then
    let inner := shift - 64
    let complement := 64 - inner
    {
      hi := (value.limb2 >>> UInt64.ofNat inner) |||
        (value.limb3 <<< UInt64.ofNat complement)
      lo := (value.limb1 >>> UInt64.ofNat inner) |||
        (value.limb2 <<< UInt64.ofNat complement)
    }
  else if shift == 128 then
    ⟨value.limb3, value.limb2⟩
  else if shift < 192 then
    let inner := shift - 128
    let complement := 64 - inner
    {
      hi := value.limb3 >>> UInt64.ofNat inner
      lo := (value.limb2 >>> UInt64.ofNat inner) |||
        (value.limb3 <<< UInt64.ofNat complement)
    }
  else if shift < 256 then
    ⟨0, value.limb3 >>> UInt64.ofNat (shift - 192)⟩
  else
    ⟨0, 0⟩

/-- Test whether any of the lowest `width` bits of a four-word value is nonzero. -/
@[inline] def hasNonzeroBelow (value : UInt256) (width : Nat) : Bool :=
  if width == 0 then
    false
  else if width < 64 then
    (value.limb0 &&& ((1 <<< UInt64.ofNat width) - 1)) != 0
  else if width == 64 then
    value.limb0 != 0
  else if width < 128 then
    let inner := width - 64
    value.limb0 != 0 ||
      (value.limb1 &&& ((1 <<< UInt64.ofNat inner) - 1)) != 0
  else if width == 128 then
    value.limb0 != 0 || value.limb1 != 0
  else if width < 192 then
    let inner := width - 128
    value.limb0 != 0 || value.limb1 != 0 ||
      (value.limb2 &&& ((1 <<< UInt64.ofNat inner) - 1)) != 0
  else if width == 192 then
    value.limb0 != 0 || value.limb1 != 0 || value.limb2 != 0
  else if width < 256 then
    let inner := width - 192
    value.limb0 != 0 || value.limb1 != 0 || value.limb2 != 0 ||
      (value.limb3 &&& ((1 <<< UInt64.ofNat inner) - 1)) != 0
  else
    value.limb0 != 0 || value.limb1 != 0 ||
      value.limb2 != 0 || value.limb3 != 0

/--
Shift right into two words, setting the low bit if any bit below the shift position is nonzero.

When the shifted quotient fits in two words, this is round-to-odd, or sticky, normalization.
It preserves nearest-even rounding when the final rounder discards at least two more bits.

For the floating-point formulation, see Sylvie Boldo and Guillaume Melquiond,
"Emulation of a FMA and Correctly Rounded Sums: Proved Algorithms Using Rounding to Odd"
(2008), §III-C, Theorem 3. The fixed-grid statement used here is
`FloatLib.Numerics.roundShiftRightEven_shiftRightJam`.
-/
@[inline] def shiftRightJam128
    (value : UInt256) (shift : Nat) : UInt128 :=
  let shifted := shiftRight128 value shift
  if hasNonzeroBelow value shift then
    shifted.setLowBit
  else
    shifted

/--
Number of low bits discarded when reducing a four-limb value to a normalized two-limb value.

Values already below `2^128` use a zero shift. Wider values keep their leading bit at position
127.
-/
@[inline] def normalizationShift128 (value : UInt256) : Nat :=
  value.log2 - 127

/--
Normalize a four-limb value into two limbs while jamming every discarded one bit into bit zero.

The result retains the leading 128-bit window, with its low bit ORed with the sticky bit of the
discarded suffix. This preserves nearest-even rounding when the final rounder discards at least
two more bits.
-/
@[inline] def normalizeJam128 (value : UInt256) : UInt128 :=
  shiftRightJam128 value value.normalizationShift128

/--
Round a four-limb value right by `shift`, returning a two-limb result.

The kernel is only valid for `64 < shift < 128`, because the discarded field is read from `limb1`
and `limb0` and the halfway marker is built inside `limb1`. Callers also keep
`value.limb3 < 2^(shift - 64)` and the incremented quotient below `2^128`, so that
`shiftRight128` returns the complete quotient. `roundShiftRightEven128_toNat` states these
hypotheses. Two-word products call this with shifts `fracWidth` or `fracWidth + 1`, which
is 112 or 113 for binary128.
-/
@[inline] def roundShiftRightEven128 (value : UInt256) (shift : Nat) : UInt128 :=
  let inner := shift - 64
  let quotient := shiftRight128 value shift
  let highRemainder :=
    value.limb1 &&& ((1 <<< UInt64.ofNat inner) - 1)
  let halfHigh := (1 : UInt64) <<< UInt64.ofNat (inner - 1)
  if highRemainder < halfHigh then
    quotient
  else if highRemainder > halfHigh || value.limb0 != 0 then
    quotient.increment
  else if (quotient.lo &&& 1) == 0 then
    quotient
  else
    quotient.increment


/-- Bitwise complement of a four-word value. -/
@[inline] def complement (value : UInt256) : UInt256 :=
  ⟨~~~value.limb3, ~~~value.limb2, ~~~value.limb1, ~~~value.limb0⟩

/--
Subtract two four-word values modulo `2^256` by adding the two's complement of the subtrahend.
`sub_toNat` gives the natural-number difference when the subtrahend is at most the minuend.
-/
@[inline] def sub (x y : UInt256) : UInt256 :=
  (add256 x (add256 y.complement ⟨0, 0, 0, 1⟩).value).value

/-- Compare two four-word values. -/
@[inline] def less (x y : UInt256) : Bool :=
  x.limb3 < y.limb3 || (x.limb3 == y.limb3 && (x.limb2 < y.limb2 || (x.limb2 == y.limb2 &&
    (x.limb1 < y.limb1 || (x.limb1 == y.limb1 && x.limb0 < y.limb0)))))

/-- Set the least-significant bit of a four-word value. -/
@[inline] def setLowBit (value : UInt256) : UInt256 :=
  ⟨value.limb3, value.limb2, value.limb1, value.limb0 ||| 1⟩

/-- Double a four-word value modulo `2^256`. -/
@[inline] def double (value : UInt256) : UInt256 :=
  (add256 value value).value

end UInt256

/--
Embed a two-word value shifted left by `shift < 128` bits into four words. Every shift below 128
is supported, including those `UInt256.ofUInt128ShiftedLeft` does not cover.
-/
@[inline] def UInt128.shiftLeft256 (value : UInt128) (shift : Nat) : UInt256 :=
  if shift == 0 then
    UInt256.ofUInt128 value
  else if shift < 64 then
    let complement := 64 - shift
    {
      limb3 := 0
      limb2 := value.hi >>> UInt64.ofNat complement
      limb1 := (value.lo >>> UInt64.ofNat complement) ||| (value.hi <<< UInt64.ofNat shift)
      limb0 := value.lo <<< UInt64.ofNat shift
    }
  else if shift == 64 then
    ⟨0, value.hi, value.lo, 0⟩
  else
    UInt256.ofUInt128ShiftedLeft value shift

end FloatLib.Numerics.FixedWord
