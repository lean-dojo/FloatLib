/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Core.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Codecs

/-!
# Direct storage-word arithmetic for configured binary formats

On the `word64` plan the code is the encoding itself. Binary64 addition and subtraction run the
one-word kernel on the stored `UInt64` values and rebuild the proof model only when the kernel
declines. A binary64 model value with the sign bit set is a natural number of at least `2 ^ 63`,
which the runtime allocates, so negative operands would otherwise pay for several allocations per
operation.

On the `pair` plan the code is the two storage words of the encoding. Formats with the two-word
layout of `NativePair` add, subtract, multiply, divide, fuse multiply-adds, and take square roots
through the two-word kernels on those words. Above 64 bits every model value is an allocated
natural number, and splitting and joining it costs far more than the arithmetic. `Direct.Proof`
shows each direct operation equals the word operation it replaces.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Floats.ExecFloat

namespace Backend

/-- Pack a kernel's storage word as a `word64` code, masked below the radix. -/
@[inline] def word64Code {format : FloatFormat} (hw : format.bitWidth ≤ 64) (bits : UInt64) :
    Code (StoragePlan.word64 (format := format) hw) :=
  ⟨bits &&& Model.NativeSmallWord.storageMask format,
    lt_of_le_of_lt (by rw [UInt64.toNat_and]; exact Nat.and_le_right)
      (Model.NativeSmallWord.storageMask_toNat_lt format)⟩

/--
The model fallback of `binary64Add`, kept out of line so the word path stays small, and
specialized on the format so declined inputs run the descriptor-specialized dispatcher.
-/
@[noinline, specialize format] def Internal.Fallback.binary64Add {format : FloatFormat}
    (hw : format.bitWidth ≤ 64)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw)) :=
  wordAdd left right

/-- Addition on stored binary64 words, rebuilding the model only when the word kernel declines. -/
@[inline] def binary64Add {format : FloatFormat} (hw : format.bitWidth ≤ 64)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw)) :=
  match Model.NativeSmallWordAdd.addFiniteWord? format left.raw.1 right.raw.1 false with
  | some bits => ofRaw (word64Code hw bits)
  | none => Internal.Fallback.binary64Add hw left right

/-- Out-of-line model fallback of `binary64Sub`, as for `binary64Add`. -/
@[noinline, specialize format] def Internal.Fallback.binary64Sub {format : FloatFormat}
    (hw : format.bitWidth ≤ 64)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw)) :=
  wordSub left right

/-- Subtraction on stored binary64 words, with the right operand's sign toggled in the kernel. -/
@[inline] def binary64Sub {format : FloatFormat} (hw : format.bitWidth ≤ 64)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw)) :=
  match Model.NativeSmallWordAdd.addFiniteWord? format left.raw.1 right.raw.1 true with
  | some bits => ofRaw (word64Code hw bits)
  | none => Internal.Fallback.binary64Sub hw left right

/-- Out-of-line model fallback of `binary64Mul`, as for `binary64Add`. -/
@[noinline, specialize format] def Internal.Fallback.binary64Mul {format : FloatFormat}
    (hw : format.bitWidth ≤ 64)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw)) :=
  wordMul left right

/-- Multiplication on stored binary64 words through the two-word normal-product kernel. -/
@[inline] def binary64Mul {format : FloatFormat} (hw : format.bitWidth ≤ 64)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw)) :=
  match Model.NativeTwoWordMul.mulNormalWord? format left.raw.1 right.raw.1 with
  | some bits => ofRaw (word64Code hw bits)
  | none => Internal.Fallback.binary64Mul hw left right

/-- Out-of-line model fallback of `binary64Div`, as for `binary64Add`. -/
@[noinline, specialize format] def Internal.Fallback.binary64Div {format : FloatFormat}
    (hw : format.bitWidth ≤ 64)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw)) :=
  wordDiv left right

/-- Division on stored binary64 words through the normal-result divider. -/
@[inline] def binary64Div {format : FloatFormat} (hw : format.bitWidth ≤ 64)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw)) :=
  match Model.NativeBinary64.divNormalWord? left.raw.1 right.raw.1 with
  | some bits => ofRaw (word64Code hw bits)
  | none => Internal.Fallback.binary64Div hw left right

/-- Out-of-line model fallback of `binary64Fma`, as for `binary64Add`. -/
@[noinline, specialize format] def Internal.Fallback.binary64Fma {format : FloatFormat}
    (hw : format.bitWidth ≤ 64)
    (left right addend :
      FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw)) :=
  wordFma left right addend

/-- Fused multiply-add on stored binary64 words through the normal-result kernel. -/
@[inline] def binary64Fma {format : FloatFormat} (hw : format.bitWidth ≤ 64)
    (left right addend :
      FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.word64 hw)) (.word64 hw)) :=
  match Model.NativeBinary64.fmaNormalWord? left.raw.1 right.raw.1 addend.raw.1 with
  | some bits => ofRaw (word64Code hw bits)
  | none => Internal.Fallback.binary64Fma hw left right addend

/-! ## Two-word carriers -/

/-- Mask of the encoded bits in the high word of a `pair` code: `2 ^ (bitWidth - 64) - 1`. -/
@[inline] def pairHighMask (format : FloatFormat) : UInt64 :=
  UInt64.ofNat (2 ^ (format.bitWidth - 64) - 1)

/-- The high-word mask is exact for every width up to 128 bits. -/
theorem pairHighMask_toNat (format : FloatFormat) (hle : format.bitWidth ≤ 128) :
    (pairHighMask format).toNat = 2 ^ (format.bitWidth - 64) - 1 := by
  have hpow : 2 ^ (format.bitWidth - 64) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos := Nat.two_pow_pos (format.bitWidth - 64)
  unfold pairHighMask
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-- A high word masked by `pairHighMask` and any low word form an encoding below the radix. -/
theorem pairWords_lt {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128) (words : FloatLib.Numerics.FixedWord.UInt128) :
    ({ hi := words.hi &&& pairHighMask format, lo := words.lo } :
      FloatLib.Numerics.FixedWord.UInt128).toNat < 2 ^ format.bitWidth := by
  have hhi : (words.hi &&& pairHighMask format).toNat ≤ 2 ^ (format.bitWidth - 64) - 1 := by
    rw [UInt64.toNat_and, ← pairHighMask_toNat format hle]
    exact Nat.and_le_right
  have hpos := Nat.two_pow_pos (format.bitWidth - 64)
  have hsplit : 2 ^ format.bitWidth = 2 ^ (format.bitWidth - 64) * 2 ^ 64 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hlo := words.lo.toNat_lt
  unfold FloatLib.Numerics.FixedWord.UInt128.toNat
  rw [hsplit]
  calc words.lo.toNat + (words.hi &&& pairHighMask format).toNat * 2 ^ 64
      < ((words.hi &&& pairHighMask format).toNat + 1) * 2 ^ 64 := by
        rw [Nat.succ_mul]
        omega
    _ ≤ 2 ^ (format.bitWidth - 64) * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)

/-- Pack a kernel's two storage words as a `pair` code, masked below the radix. -/
@[inline] def pairCode {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128) (words : FloatLib.Numerics.FixedWord.UInt128) :
    Code (StoragePlan.pair hgt hle) :=
  ⟨{ hi := words.hi &&& pairHighMask format, lo := words.lo }, pairWords_lt hgt hle words⟩

/-- Out-of-line model fallback of `pairAdd`, as for `binary64Add`. -/
@[noinline, specialize format] def Internal.Fallback.pairAdd {format : FloatFormat}
    (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle)) :=
  wordAdd left right

/-- Addition on stored two-word codes through the two-word finite addition kernel. -/
@[specialize format] def pairAdd {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle)) :=
  match Model.NativePair.addFiniteWords? format left.raw.1 right.raw.1 false with
  | some words => ofRaw (pairCode hgt hle words)
  | none => Internal.Fallback.pairAdd hgt hle left right

/-- Out-of-line model fallback of `pairSub`, as for `binary64Add`. -/
@[noinline, specialize format] def Internal.Fallback.pairSub {format : FloatFormat}
    (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle)) :=
  wordSub left right

/-- Subtraction on stored two-word codes, with the right operand's sign toggled in the kernel. -/
@[specialize format] def pairSub {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle)) :=
  match Model.NativePair.addFiniteWords? format left.raw.1 right.raw.1 true with
  | some words => ofRaw (pairCode hgt hle words)
  | none => Internal.Fallback.pairSub hgt hle left right

/-- Out-of-line model fallback of `pairMul`, as for `binary64Add`. -/
@[noinline, specialize format] def Internal.Fallback.pairMul {format : FloatFormat}
    (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle)) :=
  wordMul left right

/-- Multiplication on stored two-word codes through the two-word normal-product kernel. -/
@[specialize format] def pairMul {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle)) :=
  match Model.NativePair.mulNormalWords? format left.raw.1 right.raw.1 with
  | some words => ofRaw (pairCode hgt hle words)
  | none => Internal.Fallback.pairMul hgt hle left right

/-- Out-of-line model fallback of `pairDiv`, as for `binary64Add`. -/
@[noinline, specialize format] def Internal.Fallback.pairDiv {format : FloatFormat}
    (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle)) :=
  wordDiv left right

/-- Division on stored two-word codes through the certified two-word normal divider. -/
@[specialize format] def pairDiv {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle)) :=
  match Model.NativePair.divNormalWords? format left.raw.1 right.raw.1 with
  | some words => ofRaw (pairCode hgt hle words)
  | none => Internal.Fallback.pairDiv hgt hle left right

/-- Out-of-line fixed-limb fallback of `pairSqrt`, as for `binary64Add`. -/
@[noinline, specialize format] def Internal.Fallback.pairSqrt {format : FloatFormat}
    (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128)
    (value : FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle)) :=
  fixedLimbSqrt value

/-- Square root of a stored two-word code through the two-word normal root kernel. -/
@[specialize format] def pairSqrt {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128)
    (value : FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle)) :=
  match Model.NativePair.sqrtNormalWords? format value.raw.1 with
  | some words => ofRaw (pairCode hgt hle words)
  | none => Internal.Fallback.pairSqrt hgt hle value

/-- Out-of-line fixed-limb fallback of `pairFma`, as for `binary64Add`. -/
@[noinline, specialize format] def Internal.Fallback.pairFma {format : FloatFormat}
    (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128)
    (left right addend :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle)) :=
  fixedLimbFma left right addend

/-- Fused multiply-add on stored two-word codes through the two-word finite FMA kernel. -/
@[specialize format] def pairFma {format : FloatFormat} (hgt : 64 < format.bitWidth)
    (hle : format.bitWidth ≤ 128)
    (left right addend :
      FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle))) :
    FloatLib.Floats.ExecFloat (Family format (Code (.pair hgt hle)) (.pair hgt hle)) :=
  match Model.NativePair.fmaFiniteWords? format left.raw.1 right.raw.1 addend.raw.1 with
  | some words => ofRaw (pairCode hgt hle words)
  | none => Internal.Fallback.pairFma hgt hle left right addend

/-! ## Plan dispatch -/

/-- Word addition for the configured code, with direct binary64 and two-word kernels. -/
@[inline] def directAdd {format : FloatFormat} {plan : StoragePlan format} :
    FloatLib.Floats.ExecFloat (Family format (Code plan) plan) →
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan) →
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan) :=
  match plan with
  | .word64 hw => if FloatFormat.IsBinary64 format then binary64Add hw else wordAdd
  | .pair hgt hle => if Model.NativePair.Eligible format then pairAdd hgt hle else wordAdd
  | _ => wordAdd

/-- Word subtraction for the configured code, with direct binary64 and two-word kernels. -/
@[inline] def directSub {format : FloatFormat} {plan : StoragePlan format} :
    FloatLib.Floats.ExecFloat (Family format (Code plan) plan) →
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan) →
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan) :=
  match plan with
  | .word64 hw => if FloatFormat.IsBinary64 format then binary64Sub hw else wordSub
  | .pair hgt hle => if Model.NativePair.Eligible format then pairSub hgt hle else wordSub
  | _ => wordSub

/--
Word multiplication for the configured code, using the two-word kernel when the layout allows.
-/
@[inline] def directMul {format : FloatFormat} {plan : StoragePlan format} :
    FloatLib.Floats.ExecFloat (Family format (Code plan) plan) →
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan) →
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan) :=
  match plan with
  | .pair hgt hle => if Model.NativePair.Eligible format then pairMul hgt hle else wordMul
  | _ => wordMul

/-- Word division for the configured code, using the two-word kernel when the layout allows. -/
@[inline] def directDiv {format : FloatFormat} {plan : StoragePlan format} :
    FloatLib.Floats.ExecFloat (Family format (Code plan) plan) →
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan) →
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan) :=
  match plan with
  | .pair hgt hle => if Model.NativePair.Eligible format then pairDiv hgt hle else wordDiv
  | _ => wordDiv

end Backend

end FloatLib.Floats.Formats.BinaryInterchange.Configured
