/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.Carrier
public import FloatLib.Kernels.LimbArray.Shift.Runtime

/-!
# Wide-limb storage runtime

The wide-limb backend serves binary descriptors wider than 128 bits. A stored value is a
`LimbArray` of exactly `limbCount fmt` little-endian 32-bit limbs whose bits at and above
`fmt.bitWidth` are clear; `Value fmt` packages the array with that invariant, decided by one limb
comparison in `topLimbFits`. Because the invariant is a Boolean test, the smart constructor
`ofLimbs` checks a candidate array at runtime. `Core.Proof` proves that model conversion and field
packing produce arrays that pass this check.

Field access reads the sign bit, the exponent field, and the fraction limbs directly from the
array. `pack` assembles a result from its sign, exponent word, and fraction limbs with two
carry-free additions at the field offsets. The correspondence with `Model` is proved in
`Core.Proof`; every arithmetic kernel of this backend is written over these accessors.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

/--
Structural capability required by the wide-limb kernels.

The conventional IEEE encoding selects the exact binary semantics and default bias shared with the
generic kernels. Widths above 128 bits are the formats no fixed-limb kernel serves. An exponent
field of at most 32 bits lets the encoded exponent be read from one 32-bit window. Scale and
position arithmetic uses `Nat`; the fraction width is unrestricted.
-/
def Eligible (fmt : FloatFormat) : Prop :=
  fmt.isIEEE = true ∧ 128 < fmt.bitWidth ∧ fmt.expWidth ≤ 32

/--
Eligibility is decided by an explicit conditional on descriptor fields, exposing those tests to
specialization. See `Dispatch.Add.Runtime` for the shared dispatch convention.
-/
@[inline] instance (fmt : FloatFormat) : Decidable (Eligible fmt) :=
  if h : fmt.isIEEE = true ∧ 128 < fmt.bitWidth ∧ fmt.expWidth ≤ 32 then isTrue h else isFalse h

/-- Number of 32-bit limbs holding one encoded value. -/
@[inline] def limbCount (fmt : FloatFormat) : Nat :=
  (fmt.bitWidth + 31) / 32

/-- Whether the bits at and above `bitWidth` in the top limb are clear. -/
@[inline] def topLimbFits (fmt : FloatFormat) (v : LimbArray) : Bool :=
  (v.limb (limbCount fmt - 1)).toUInt64 >>>
      UInt64.ofNat (fmt.bitWidth - 32 * (limbCount fmt - 1)) == 0

/--
A value of `fmt` stored as exactly `limbCount fmt` limbs with clear spare bits.

The invariant is a decidable Boolean test so kernels can construct values through `ofLimbs`.
`topLimbFits_iff` gives the numerical bound for arrays of the required size.
-/
abbrev Value (fmt : FloatFormat) : Type :=
  { v : LimbArray // v.size = limbCount fmt ∧ topLimbFits fmt v = true }

/-- The all-zero array satisfies the storage invariant. -/
theorem zero_valid (fmt : FloatFormat) :
    (LimbArray.zero (limbCount fmt)).size = limbCount fmt ∧
      topLimbFits fmt (LimbArray.zero (limbCount fmt)) = true := by
  refine ⟨by simp [LimbArray.zero, LimbArray.size], ?_⟩
  unfold topLimbFits LimbArray.limb LimbArray.zero
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> simp

instance (fmt : FloatFormat) : Inhabited (Value fmt) :=
  ⟨⟨LimbArray.zero (limbCount fmt), zero_valid fmt⟩⟩

/--
Wrap a kernel output as a stored value.

An array with the required size and clear spare bits is retained; any other array yields zero.
`ofLimbs_val` proves the successful case from an explicit size equality and numerical bound.
-/
@[inline] def ofLimbs (fmt : FloatFormat) (w : LimbArray) : Value fmt :=
  if h : w.size = limbCount fmt ∧ topLimbFits fmt w = true then
    ⟨w, h⟩
  else
    ⟨LimbArray.zero (limbCount fmt), zero_valid fmt⟩

/-- Interpret a stored value in the exact-width proof model. -/
@[inline] def toModel {fmt : FloatFormat} (v : Value fmt) : Model fmt :=
  Model.ofNatBits v.1.toNat

/-- Store a proof-model value as limbs. -/
@[inline] def ofModel {fmt : FloatFormat} (x : Model fmt) : Value fmt :=
  ofLimbs fmt (LimbArray.ofNat x.toNatBits (limbCount fmt))

/-! ## Field access -/

/-- The stored sign bit. -/
@[inline] def signBit {fmt : FloatFormat} (v : Value fmt) : Bool :=
  v.1.testBit (fmt.expWidth + fmt.fracWidth)

/-- Mask of the exponent field within a 32-bit window, for exponent widths of at most 32. -/
@[inline] def expMask32 (fmt : FloatFormat) : UInt32 :=
  if fmt.expWidth < 32 then LimbArray.lowMask32 fmt.expWidth else 0xFFFFFFFF

/-- The biased exponent field as a machine word. -/
@[inline] def expWord {fmt : FloatFormat} (v : Value fmt) : UInt32 :=
  v.1.bitsAt32 fmt.fracWidth &&& expMask32 fmt

/-- The biased exponent field. -/
@[inline] def expField {fmt : FloatFormat} (v : Value fmt) : Nat :=
  (expWord v).toNat

/-- The all-ones exponent field as a machine word. -/
@[inline] def expAllOnes (fmt : FloatFormat) : UInt32 :=
  expMask32 fmt

/-- The fraction field, in the stored limb count. -/
@[inline] def fraction {fmt : FloatFormat} (v : Value fmt) : LimbArray :=
  v.1.lowBits fmt.fracWidth

/-- The significand of a normal value: the fraction with the implicit bit `2^fracWidth`. -/
@[inline] def normalMantissa {fmt : FloatFormat} (v : Value fmt) : LimbArray :=
  (fraction v).addAt fmt.fracWidth 1

/--
Pack a sign, an exponent word, and fraction limbs into a stored value.

The exponent word is masked to the exponent field and the fraction to `fracWidth` bits, so the
result is meaningful for every input; `Core.Proof.toModel_pack` states the exact model produced.
-/
def pack (fmt : FloatFormat) (sign : Bool) (exponent : UInt32) (fraction : LimbArray) :
    Value fmt :=
  let base := (fraction.lowBits fmt.fracWidth).resize (limbCount fmt)
  let withExponent := base.addAt fmt.fracWidth (exponent &&& expMask32 fmt)
  ofLimbs fmt
    (if sign then withExponent.addAt (fmt.expWidth + fmt.fracWidth) 1 else withExponent)

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
