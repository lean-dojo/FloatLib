/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Byte.Proof
public import FloatLib.Floats.Formats.Posit.Configured.ByteTable.Construction
public import FloatLib.Floats.Formats.Posit.Configured.ByteTable.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Plan.Core.GeneralCandidates

/-!
# Certified candidates for byte-sized posits

A posit of at most eight bits can run four ways: from an exhaustive table, with packed-word
arithmetic, with width-generic integer arithmetic, or through the exact reference implementation.
This module puts those four choices together for each operation, and ties every one of them to the
same configured specification. So the choice changes execution cost and memory residency, and
never the posit arithmetic.

`ByteDispatch.Proof` shows that the tag-based executor reads the same selection metadata. Other
storage plans are handled in `Configured.Plan.Dispatch`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Plan

open FloatLib.Floats.ExecFloat.Backend

/-- Addition candidates for a byte-sized posit. -/
@[noinline] def addByteCandidates (format : Format) (width_le : format.bits ≤ 8) :
    CandidateSet (Certified
      (@Spec.addition format (.byte width_le) (Code (.byte width_le)) inferInstance)) :=
  CandidateSet.withReference (genericEstimate (.byte width_le) .add) Spec.addition <|
    [Certified.binary (tableEstimate format width_le .add) Spec.addition
      (ByteTable.runBinary width_le (ByteTable.addTable width_le))
      (ByteTable.runBinary_eq_lift width_le (ByteTable.addTable width_le)),
    Certified.binary (storedNativeWordEstimate (.byte width_le) .add)
      Spec.addition (Backend.Byte.add width_le) (Backend.Byte.add_eq_spec width_le),
    Certified.binary (dyadicEstimate (.byte width_le) .add)
      Spec.addition Backend.dyadicAdd Backend.dyadicAdd_eq_spec]

/-- Subtraction candidates for a byte-sized posit. -/
@[noinline] def subByteCandidates (format : Format) (width_le : format.bits ≤ 8) :
    CandidateSet (Certified
      (@Spec.subtraction format (.byte width_le) (Code (.byte width_le)) inferInstance)) :=
  CandidateSet.withReference (genericEstimate (.byte width_le) .sub) Spec.subtraction <|
    [Certified.binary (tableEstimate format width_le .sub) Spec.subtraction
      (ByteTable.runBinary width_le (ByteTable.subTable width_le))
      (ByteTable.runBinary_eq_lift width_le (ByteTable.subTable width_le)),
    Certified.binary (storedNativeWordEstimate (.byte width_le) .sub)
      Spec.subtraction (Backend.Byte.sub width_le) (Backend.Byte.sub_eq_spec width_le),
    Certified.binary (dyadicEstimate (.byte width_le) .sub)
      Spec.subtraction Backend.dyadicSub Backend.dyadicSub_eq_spec]

/-- Multiplication candidates for a byte-sized posit. -/
@[noinline] def mulByteCandidates (format : Format) (width_le : format.bits ≤ 8) :
    CandidateSet (Certified
      (@Spec.multiplication format (.byte width_le) (Code (.byte width_le)) inferInstance)) :=
  CandidateSet.withReference (genericEstimate (.byte width_le) .mul) Spec.multiplication <|
    [Certified.binary (tableEstimate format width_le .mul) Spec.multiplication
      (ByteTable.runBinary width_le (ByteTable.mulTable width_le))
      (ByteTable.runBinary_eq_lift width_le (ByteTable.mulTable width_le)),
    Certified.binary (storedNativeWordEstimate (.byte width_le) .mul)
      Spec.multiplication (Backend.Byte.mul width_le) (Backend.Byte.mul_eq_spec width_le),
    Certified.binary (dyadicEstimate (.byte width_le) .mul)
      Spec.multiplication Backend.dyadicMul Backend.dyadicMul_eq_spec]

/-- Division candidates for a byte-sized posit. -/
@[noinline] def divByteCandidates (format : Format) (width_le : format.bits ≤ 8) :
    CandidateSet (Certified
      (@Spec.division format (.byte width_le) (Code (.byte width_le)) inferInstance)) :=
  CandidateSet.withReference (genericEstimate (.byte width_le) .div) Spec.division <|
    [Certified.binary (tableEstimate format width_le .div) Spec.division
      (ByteTable.runBinary width_le (ByteTable.divTable width_le))
      (ByteTable.runBinary_eq_lift width_le (ByteTable.divTable width_le)),
    Certified.binary (storedNativeWordEstimate (.byte width_le) .div)
      Spec.division (Backend.Byte.div width_le) (Backend.Byte.div_eq_spec width_le),
    Certified.binary (dyadicEstimate (.byte width_le) .div)
      Spec.division Backend.dyadicDiv Backend.dyadicDiv_eq_spec]

/-- Square-root candidates for a byte-sized posit. -/
@[noinline] def sqrtByteCandidates (format : Format) (width_le : format.bits ≤ 8) :
    CandidateSet (Certified
      (@Spec.sqrt format (.byte width_le) (Code (.byte width_le)) inferInstance)) :=
  CandidateSet.withReference (genericEstimate (.byte width_le) .sqrt) Spec.sqrt <|
    [Certified.unary (tableEstimate format width_le .sqrt) Spec.sqrt
      (ByteTable.runUnary width_le (ByteTable.sqrtTable width_le))
      (ByteTable.runUnary_eq_lift width_le (ByteTable.sqrtTable width_le)),
    Certified.unary (storedNativeWordEstimate (.byte width_le) .sqrt)
      Spec.sqrt (Backend.Byte.sqrt width_le) (Backend.Byte.sqrt_eq_spec width_le),
    Certified.unary (dyadicEstimate (.byte width_le) .sqrt)
      Spec.sqrt Backend.dyadicSqrt Backend.dyadicSqrt_eq_spec]

/-- Fused-multiply-add candidates for a byte-sized posit. -/
@[noinline] def fmaByteCandidates (format : Format) (width_le : format.bits ≤ 8) :
    CandidateSet (Certified
      (@Spec.fma format (.byte width_le) (Code (.byte width_le)) inferInstance)) :=
  CandidateSet.withReference (genericEstimate (.byte width_le) .fma) Spec.fma <|
    [Certified.ternary (tableEstimate format width_le .fma) Spec.fma
      (ByteTable.runTernary width_le (ByteTable.fmaTable width_le))
      (ByteTable.runTernary_eq_lift width_le (ByteTable.fmaTable width_le)),
    Certified.ternary (storedNativeWordEstimate (.byte width_le) .fma)
      Spec.fma (Backend.Byte.fma width_le) (Backend.Byte.fma_eq_spec width_le),
    Certified.ternary (dyadicEstimate (.byte width_le) .fma)
      Spec.fma Backend.dyadicFma Backend.dyadicFma_eq_spec]

end FloatLib.Floats.Formats.Posit.Configured.Plan
