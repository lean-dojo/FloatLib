/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Selection.Certified
public import FloatLib.Floats.Formats.Posit.Configured.Plan.Core.Estimates
public import FloatLib.Floats.Formats.Posit.Configured.Plan.Core.GeneralCandidates
public import FloatLib.Floats.Formats.Posit.Configured.Plan.Core.ModelCandidates
public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Byte.Proof
public import FloatLib.Floats.Formats.Posit.Configured.ByteTable.Proof
public import FloatLib.Floats.Formats.Posit.Configured.ByteTable.Construction

/-!
# Certified candidates for byte-sized posits

Byte carriers support exhaustive tables, packed-word arithmetic, width-generic integer arithmetic,
and the exact reference implementation. This module assembles those four choices for each
operation.

Every candidate is connected to the same configured specification. Selection affects execution
cost and memory residency only; it does not alter posit arithmetic.

`ByteDispatch.Proof` proves that the tag-based executor uses the same selection metadata.
Other storage plans are handled in `Configured.Plan.Dispatch`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Plan

open FloatLib.Floats.ExecFloat.Backend

/-- Addition candidates for a byte-sized posit. -/
@[noinline] def addByteCandidates (format : Format) (width_le : format.bits ≤ 8) :
    CandidateSet (Certified
      (@Spec.add format (.byte width_le) (Code (.byte width_le)) inferInstance)) :=
  CandidateSet.withReference (genericEstimate (.byte width_le) .add) Spec.add <|
    [Certified.binary (tableEstimate format width_le .add) Spec.add
      (ByteTable.runBinary width_le (ByteTable.addTable width_le))
      (ByteTable.runBinary_eq_lift width_le (ByteTable.addTable width_le)),
    Certified.binary (storedNativeWordEstimate (.byte width_le) .add)
      Spec.add (Backend.Byte.add width_le) (Backend.Byte.add_eq_spec width_le),
    Certified.binary (dyadicEstimate (.byte width_le) .add)
      Spec.add Backend.dyadicAdd Backend.dyadicAdd_eq_spec]

/-- Subtraction candidates for a byte-sized posit. -/
@[noinline] def subByteCandidates (format : Format) (width_le : format.bits ≤ 8) :
    CandidateSet (Certified
      (@Spec.sub format (.byte width_le) (Code (.byte width_le)) inferInstance)) :=
  CandidateSet.withReference (genericEstimate (.byte width_le) .sub) Spec.sub <|
    [Certified.binary (tableEstimate format width_le .sub) Spec.sub
      (ByteTable.runBinary width_le (ByteTable.subTable width_le))
      (ByteTable.runBinary_eq_lift width_le (ByteTable.subTable width_le)),
    Certified.binary (storedNativeWordEstimate (.byte width_le) .sub)
      Spec.sub (Backend.Byte.sub width_le) (Backend.Byte.sub_eq_spec width_le),
    Certified.binary (dyadicEstimate (.byte width_le) .sub)
      Spec.sub Backend.dyadicSub Backend.dyadicSub_eq_spec]

/-- Multiplication candidates for a byte-sized posit. -/
@[noinline] def mulByteCandidates (format : Format) (width_le : format.bits ≤ 8) :
    CandidateSet (Certified
      (@Spec.mul format (.byte width_le) (Code (.byte width_le)) inferInstance)) :=
  CandidateSet.withReference (genericEstimate (.byte width_le) .mul) Spec.mul <|
    [Certified.binary (tableEstimate format width_le .mul) Spec.mul
      (ByteTable.runBinary width_le (ByteTable.mulTable width_le))
      (ByteTable.runBinary_eq_lift width_le (ByteTable.mulTable width_le)),
    Certified.binary (storedNativeWordEstimate (.byte width_le) .mul)
      Spec.mul (Backend.Byte.mul width_le) (Backend.Byte.mul_eq_spec width_le),
    Certified.binary (dyadicEstimate (.byte width_le) .mul)
      Spec.mul Backend.dyadicMul Backend.dyadicMul_eq_spec]

/-- Division candidates for a byte-sized posit. -/
@[noinline] def divByteCandidates (format : Format) (width_le : format.bits ≤ 8) :
    CandidateSet (Certified
      (@Spec.div format (.byte width_le) (Code (.byte width_le)) inferInstance)) :=
  CandidateSet.withReference (genericEstimate (.byte width_le) .div) Spec.div <|
    [Certified.binary (tableEstimate format width_le .div) Spec.div
      (ByteTable.runBinary width_le (ByteTable.divTable width_le))
      (ByteTable.runBinary_eq_lift width_le (ByteTable.divTable width_le)),
    Certified.binary (storedNativeWordEstimate (.byte width_le) .div)
      Spec.div (Backend.Byte.div width_le) (Backend.Byte.div_eq_spec width_le),
    Certified.binary (dyadicEstimate (.byte width_le) .div)
      Spec.div Backend.dyadicDiv Backend.dyadicDiv_eq_spec]

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
