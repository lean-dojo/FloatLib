/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.ByteTable.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.WideLimbCandidates

/-!
# Automatic portfolios for built-in configured carriers

These dependent matches inspect the already selected `StoragePlan` and add direct candidates when
their proofs apply: byte tables for the byte carrier and the wide-limb kernels for the limb
carrier. Word and wide carriers reuse the representation-independent structural portfolios.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

namespace Internal

/-!
Byte-table eligibility depends only on encoded width. Every table is certified against the same
configured specification used by the structural portfolio.
-/

/-- Certified addition table for any configured descriptor that fits in one byte. -/
def byteAdd (format : FloatFormat) (width_le : format.bitWidth ≤ 8) :
    Certified (@Spec.add format (.byte width_le) (Code (.byte width_le)) inferInstance) :=
  let kernel := ByteTable.addTable width_le
  Certified.binary (directByteEstimate format .add)
    Spec.add (ByteTable.runBinary width_le kernel)
    (ByteTable.runBinary_eq_lift width_le kernel)

/-- Certified subtraction table for any configured descriptor that fits in one byte. -/
def byteSub (format : FloatFormat) (width_le : format.bitWidth ≤ 8) :
    Certified (@Spec.sub format (.byte width_le) (Code (.byte width_le)) inferInstance) :=
  let kernel := ByteTable.subTable width_le
  Certified.binary (directByteEstimate format .sub)
    Spec.sub (ByteTable.runBinary width_le kernel)
    (ByteTable.runBinary_eq_lift width_le kernel)

/-- Certified multiplication table for any configured descriptor that fits in one byte. -/
def byteMul (format : FloatFormat) (width_le : format.bitWidth ≤ 8) :
    Certified (@Spec.mul format (.byte width_le) (Code (.byte width_le)) inferInstance) :=
  let kernel := ByteTable.mulTable width_le
  Certified.binary (directByteEstimate format .mul)
    Spec.mul (ByteTable.runBinary width_le kernel)
    (ByteTable.runBinary_eq_lift width_le kernel)

/-- Certified division table for any configured descriptor that fits in one byte. -/
def byteDiv (format : FloatFormat) (width_le : format.bitWidth ≤ 8) :
    Certified (@Spec.div format (.byte width_le) (Code (.byte width_le)) inferInstance) :=
  let kernel := ByteTable.divTable width_le
  Certified.binary (directByteEstimate format .div)
    Spec.div (ByteTable.runBinary width_le kernel)
    (ByteTable.runBinary_eq_lift width_le kernel)

/-- Certified square-root table for any configured descriptor that fits in one byte. -/
def byteSqrt (format : FloatFormat) (width_le : format.bitWidth ≤ 8) :
    Certified (@Spec.sqrt format (.byte width_le) (Code (.byte width_le)) inferInstance) :=
  let kernel := ByteTable.sqrtTable width_le
  Certified.unary (directByteEstimate format .sqrt)
    Spec.sqrt (ByteTable.runUnary width_le kernel)
    (ByteTable.runUnary_eq_lift width_le kernel)

/-- Certified fused-multiply-add table for any configured descriptor that fits in one byte. -/
def byteFma (format : FloatFormat) (width_le : format.bitWidth ≤ 8) :
    Certified (@Spec.fma format (.byte width_le) (Code (.byte width_le)) inferInstance) :=
  let kernel := ByteTable.fmaTable width_le
  Certified.ternary (directByteEstimate format .fma)
    Spec.fma (ByteTable.runTernary width_le kernel)
    (ByteTable.runTernary_eq_lift width_le kernel)

end Internal

/-! ## Complete portfolios for automatically selected built-in carriers -/

/--
Addition candidates for the carrier selected by `Configured.Code`.

Matching `Code plan` before inspecting `plan` is important for parameterized public types.
Typeclass discrimination does not unfold an arbitrary `forKnownWidth` expression far enough to
discover an instance whose head mentions `.byte` directly. This dependent match makes the byte
table available after the built-in carrier instance has already been selected.
-/
def automaticAddCandidates (format : FloatFormat) (plan : StoragePlan format) :
    CandidateSet (Certified (@Spec.add format plan (Code plan) inferInstance)) :=
  match plan with
  | .byte width_le =>
      addCandidates format (.byte width_le) [Internal.byteAdd format width_le]
  | .word16 width_le => addCandidates format (.word16 width_le)
  | .word32 width_le => addCandidates format (.word32 width_le)
  | .word64 width_le => addCandidates format (.word64 width_le)
  | .wide => addCandidates format .wide
  | .limbs width_gt =>
      addCandidates format (.limbs width_gt) (wideLimbAdd? format width_gt).toList

/-- Subtraction candidates for the automatically selected built-in carrier. -/
def automaticSubCandidates (format : FloatFormat) (plan : StoragePlan format) :
    CandidateSet (Certified (@Spec.sub format plan (Code plan) inferInstance)) :=
  match plan with
  | .byte width_le =>
      subCandidates format (.byte width_le) [Internal.byteSub format width_le]
  | .word16 width_le => subCandidates format (.word16 width_le)
  | .word32 width_le => subCandidates format (.word32 width_le)
  | .word64 width_le => subCandidates format (.word64 width_le)
  | .wide => subCandidates format .wide
  | .limbs width_gt =>
      subCandidates format (.limbs width_gt) (wideLimbSub? format width_gt).toList

/-- Multiplication candidates for the automatically selected built-in carrier. -/
def automaticMulCandidates (format : FloatFormat) (plan : StoragePlan format) :
    CandidateSet (Certified (@Spec.mul format plan (Code plan) inferInstance)) :=
  match plan with
  | .byte width_le =>
      mulCandidates format (.byte width_le) [Internal.byteMul format width_le]
  | .word16 width_le => mulCandidates format (.word16 width_le)
  | .word32 width_le => mulCandidates format (.word32 width_le)
  | .word64 width_le => mulCandidates format (.word64 width_le)
  | .wide => mulCandidates format .wide
  | .limbs width_gt =>
      mulCandidates format (.limbs width_gt) (wideLimbMul? format width_gt).toList

/-- Division candidates for the automatically selected built-in carrier. -/
def automaticDivCandidates (format : FloatFormat) (plan : StoragePlan format) :
    CandidateSet (Certified (@Spec.div format plan (Code plan) inferInstance)) :=
  match plan with
  | .byte width_le =>
      divCandidates format (.byte width_le) [Internal.byteDiv format width_le]
  | .word16 width_le => divCandidates format (.word16 width_le)
  | .word32 width_le => divCandidates format (.word32 width_le)
  | .word64 width_le => divCandidates format (.word64 width_le)
  | .wide => divCandidates format .wide
  | .limbs width_gt =>
      divCandidates format (.limbs width_gt) (wideLimbDiv? format width_gt).toList

/-- Square-root candidates for the automatically selected built-in carrier. -/
def automaticSqrtCandidates (format : FloatFormat) (plan : StoragePlan format) :
    CandidateSet (Certified (@Spec.sqrt format plan (Code plan) inferInstance)) :=
  match plan with
  | .byte width_le =>
      sqrtCandidates format (.byte width_le) [Internal.byteSqrt format width_le]
  | .word16 width_le => sqrtCandidates format (.word16 width_le)
  | .word32 width_le => sqrtCandidates format (.word32 width_le)
  | .word64 width_le => sqrtCandidates format (.word64 width_le)
  | .wide => sqrtCandidates format .wide
  | .limbs width_gt =>
      sqrtCandidates format (.limbs width_gt) (wideLimbSqrt? format width_gt).toList

/-- Fused-multiply-add candidates for the automatically selected built-in carrier. -/
def automaticFmaCandidates (format : FloatFormat) (plan : StoragePlan format) :
    CandidateSet (Certified (@Spec.fma format plan (Code plan) inferInstance)) :=
  match plan with
  | .byte width_le =>
      fmaCandidates format (.byte width_le) [Internal.byteFma format width_le]
  | .word16 width_le => fmaCandidates format (.word16 width_le)
  | .word32 width_le => fmaCandidates format (.word32 width_le)
  | .word64 width_le => fmaCandidates format (.word64 width_le)
  | .wide => fmaCandidates format .wide
  | .limbs width_gt =>
      fmaCandidates format (.limbs width_gt) (wideLimbFma? format width_gt).toList

end FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan
