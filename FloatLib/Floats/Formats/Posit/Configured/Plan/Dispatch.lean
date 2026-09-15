/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Core.Capability
public import FloatLib.Floats.Formats.Posit.Configured.Plan.ByteDispatch.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Word16.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Word32.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Word64.Proof

/-!
# Static Posit storage-plan dispatch

Public posits choose their carrier from a type-static width. This module turns that chosen
`StoragePlan` constructor into one independently certified capability per operation. Keeping the
capabilities operation-indexed lets a monomorphic public call reduce to its first-order backend
without allocating a package of unrelated function fields.

An abstract or custom codec still receives the representation-independent candidate set. A closed
public width reduces its carrier match at compile time. Packed-word, packed-pair, and wide plans
then name their single proved kernel directly. Byte plans retain policy-sensitive selection
between exhaustive tables and direct arithmetic because setup cost and residency depend on the
width, operation arity, and workload policy.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend

/--
Addition capability selected directly from a storage-plan constructor.

The byte plan retains its policy-sensitive table portfolio. Every other built-in plan has one
first-order winner, so its capability is constructed directly from that operation's kernel.
This definition is deliberately inlined: a closed public width reduces the plan match at compile
time and leaves only the named carrier kernel in the generated hot path.
-/
@[always_inline, instance_reducible] def addCapabilityForPlan
    (format : Format) (plan : StoragePlan format)
    [planning : PolicyFor (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Add (Family format (Code plan) plan) :=
  match plan, planning with
  | .byte width_le, planning =>
      Capability.ofCandidates .add
        Spec.add (addByteCandidates format width_le)
        (ByteDispatch.add planning.policy width_le)
        (ByteDispatch.add_fun_eq_spec planning.policy width_le)
  | .word16 width_le, _planning =>
      Capability.ofCertified .add <| Certified.binary
        (storedNativeWordEstimate (.word16 width_le) .add)
        Spec.add
        (Backend.Word16.add width_le)
        (Backend.Word16.add_eq_spec width_le)
  | .word32 width_le, _planning =>
      Capability.ofCertified .add <| Certified.binary
        (storedNativeWordEstimate (.word32 width_le) .add)
        Spec.add
        (Backend.Word32.add width_le)
        (Backend.Word32.add_eq_spec width_le)
  | .word64 width_le, _planning =>
      Capability.ofCertified .add <| Certified.binary
        (storedNativeWordEstimate (.word64 width_le) .add)
        Spec.add
        (Backend.Word64.add width_le)
        (Backend.Word64.add_eq_spec width_le)
  | .pair width_le, _planning =>
      let heligible : Model.NativeLimb.Eligible format := width_le
      Capability.ofCertified .add <| Certified.binary
        (storedNativeLimbEstimate (format := format) .add)
        Spec.add
        (Backend.storedNativeLimbAdd width_le heligible)
        (Backend.storedNativeLimbAdd_eq_spec width_le heligible)
  | .wide, _planning =>
      Capability.ofCertified .add <| Certified.binary
        (dyadicEstimate (.wide : StoragePlan format) .add)
        Spec.add Backend.dyadicAdd Backend.dyadicAdd_eq_spec

/-- Subtraction capability selected directly from a storage-plan constructor. -/
@[always_inline, instance_reducible] def subCapabilityForPlan
    (format : Format) (plan : StoragePlan format)
    [planning : PolicyFor (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Sub (Family format (Code plan) plan) :=
  match plan, planning with
  | .byte width_le, planning =>
      Capability.ofCandidates .sub
        Spec.sub (subByteCandidates format width_le)
        (ByteDispatch.sub planning.policy width_le)
        (ByteDispatch.sub_fun_eq_spec planning.policy width_le)
  | .word16 width_le, _planning =>
      Capability.ofCertified .sub <| Certified.binary
        (storedNativeWordEstimate (.word16 width_le) .sub)
        Spec.sub
        (Backend.Word16.sub width_le)
        (Backend.Word16.sub_eq_spec width_le)
  | .word32 width_le, _planning =>
      Capability.ofCertified .sub <| Certified.binary
        (storedNativeWordEstimate (.word32 width_le) .sub)
        Spec.sub
        (Backend.Word32.sub width_le)
        (Backend.Word32.sub_eq_spec width_le)
  | .word64 width_le, _planning =>
      Capability.ofCertified .sub <| Certified.binary
        (storedNativeWordEstimate (.word64 width_le) .sub)
        Spec.sub
        (Backend.Word64.sub width_le)
        (Backend.Word64.sub_eq_spec width_le)
  | .pair width_le, _planning =>
      let heligible : Model.NativeLimb.Eligible format := width_le
      Capability.ofCertified .sub <| Certified.binary
        (storedNativeLimbEstimate (format := format) .sub)
        Spec.sub
        (Backend.storedNativeLimbSub width_le heligible)
        (Backend.storedNativeLimbSub_eq_spec width_le heligible)
  | .wide, _planning =>
      Capability.ofCertified .sub <| Certified.binary
        (dyadicEstimate (.wide : StoragePlan format) .sub)
        Spec.sub Backend.dyadicSub Backend.dyadicSub_eq_spec

/-- Multiplication capability selected directly from a storage-plan constructor. -/
@[always_inline, instance_reducible] def mulCapabilityForPlan
    (format : Format) (plan : StoragePlan format)
    [planning : PolicyFor (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Mul (Family format (Code plan) plan) :=
  match plan, planning with
  | .byte width_le, planning =>
      Capability.ofCandidates .mul
        Spec.mul (mulByteCandidates format width_le)
        (ByteDispatch.mul planning.policy width_le)
        (ByteDispatch.mul_fun_eq_spec planning.policy width_le)
  | .word16 width_le, _planning =>
      Capability.ofCertified .mul <| Certified.binary
        (storedNativeWordEstimate (.word16 width_le) .mul)
        Spec.mul
        (Backend.Word16.mul width_le)
        (Backend.Word16.mul_eq_spec width_le)
  | .word32 width_le, _planning =>
      Capability.ofCertified .mul <| Certified.binary
        (storedNativeWordEstimate (.word32 width_le) .mul)
        Spec.mul
        (Backend.Word32.mul width_le)
        (Backend.Word32.mul_eq_spec width_le)
  | .word64 width_le, _planning =>
      Capability.ofCertified .mul <| Certified.binary
        (storedNativeWordEstimate (.word64 width_le) .mul)
        Spec.mul
        (Backend.Word64.mul width_le)
        (Backend.Word64.mul_eq_spec width_le)
  | .pair width_le, _planning =>
      let heligible : Model.NativeLimb.Eligible format := width_le
      Capability.ofCertified .mul <| Certified.binary
        (storedNativeLimbEstimate (format := format) .mul)
        Spec.mul
        (Backend.storedNativeLimbMul width_le heligible)
        (Backend.storedNativeLimbMul_eq_spec width_le heligible)
  | .wide, _planning =>
      Capability.ofCertified .mul <| Certified.binary
        (dyadicEstimate (.wide : StoragePlan format) .mul)
        Spec.mul Backend.dyadicMul Backend.dyadicMul_eq_spec

/-- Division capability selected directly from a storage-plan constructor. -/
@[always_inline, instance_reducible] def divCapabilityForPlan
    (format : Format) (plan : StoragePlan format)
    [planning : PolicyFor (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Div (Family format (Code plan) plan) :=
  match plan, planning with
  | .byte width_le, planning =>
      Capability.ofCandidates .div
        Spec.div (divByteCandidates format width_le)
        (ByteDispatch.div planning.policy width_le)
        (ByteDispatch.div_fun_eq_spec planning.policy width_le)
  | .word16 width_le, _planning =>
      Capability.ofCertified .div <| Certified.binary
        (storedNativeWordEstimate (.word16 width_le) .div)
        Spec.div
        (Backend.Word16.div width_le)
        (Backend.Word16.div_eq_spec width_le)
  | .word32 width_le, _planning =>
      Capability.ofCertified .div <| Certified.binary
        (storedNativeWordEstimate (.word32 width_le) .div)
        Spec.div
        (Backend.Word32.div width_le)
        (Backend.Word32.div_eq_spec width_le)
  | .word64 width_le, _planning =>
      Capability.ofCertified .div <| Certified.binary
        (storedNativeWordEstimate (.word64 width_le) .div)
        Spec.div
        (Backend.Word64.div width_le)
        (Backend.Word64.div_eq_spec width_le)
  | .pair width_le, _planning =>
      Capability.ofCertified .div <| Certified.binary
        (dyadicEstimate (.pair width_le) .div)
        Spec.div
        (Backend.storedNativeLimbDiv width_le)
        (Backend.storedNativeLimbDiv_eq_spec width_le)
  | .wide, _planning =>
      Capability.ofCertified .div <| Certified.binary
        (dyadicEstimate (.wide : StoragePlan format) .div)
        Spec.div Backend.dyadicDiv Backend.dyadicDiv_eq_spec

/-- Square-root capability selected directly from a storage-plan constructor. -/
@[always_inline, instance_reducible] def sqrtCapabilityForPlan
    (format : Format) (plan : StoragePlan format)
    [planning : PolicyFor (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Sqrt (Family format (Code plan) plan) :=
  match plan, planning with
  | .byte width_le, planning =>
      Capability.ofCandidates .sqrt
        Spec.sqrt (sqrtByteCandidates format width_le)
        (ByteDispatch.sqrt planning.policy width_le)
        (ByteDispatch.sqrt_fun_eq_spec planning.policy width_le)
  | .word16 width_le, _planning =>
      Capability.ofCertified .sqrt <| Certified.unary
        (storedNativeWordEstimate (.word16 width_le) .sqrt)
        Spec.sqrt
        (Backend.Word16.sqrt width_le)
        (Backend.Word16.sqrt_eq_spec width_le)
  | .word32 width_le, _planning =>
      Capability.ofCertified .sqrt <| Certified.unary
        (storedNativeWordEstimate (.word32 width_le) .sqrt)
        Spec.sqrt
        (Backend.Word32.sqrt width_le)
        (Backend.Word32.sqrt_eq_spec width_le)
  | .word64 width_le, _planning =>
      Capability.ofCertified .sqrt <| Certified.unary
        (storedNativeWordEstimate (.word64 width_le) .sqrt)
        Spec.sqrt
        (Backend.Word64.sqrt width_le)
        (Backend.Word64.sqrt_eq_spec width_le)
  | .pair width_le, _planning =>
      Capability.ofCertified .sqrt <| Certified.unary
        (storedNativeLimbEstimate (format := format) .sqrt)
        Spec.sqrt
        (Backend.storedNativeLimbSqrt width_le)
        (Backend.storedNativeLimbSqrt_eq_spec width_le)
  | .wide, _planning =>
      Capability.ofCertified .sqrt <| Certified.unary
        (dyadicEstimate (.wide : StoragePlan format) .sqrt)
        Spec.sqrt Backend.dyadicSqrt Backend.dyadicSqrt_eq_spec

/-- Fused-multiply-add capability selected directly from a storage-plan constructor. -/
@[always_inline, instance_reducible] def fmaCapabilityForPlan
    (format : Format) (plan : StoragePlan format)
    [planning : PolicyFor (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Fma (Family format (Code plan) plan) :=
  match plan, planning with
  | .byte width_le, planning =>
      Capability.ofCandidates .fma
        Spec.fma (fmaByteCandidates format width_le)
        (ByteDispatch.fma planning.policy width_le)
        (ByteDispatch.fma_fun_eq_spec planning.policy width_le)
  | .word16 width_le, _planning =>
      Capability.ofCertified .fma <| Certified.ternary
        (storedNativeWordEstimate (.word16 width_le) .fma)
        Spec.fma
        (Backend.Word16.fma width_le)
        (Backend.Word16.fma_eq_spec width_le)
  | .word32 width_le, _planning =>
      Capability.ofCertified .fma <| Certified.ternary
        (storedNativeWordEstimate (.word32 width_le) .fma)
        Spec.fma
        (Backend.Word32.fma width_le)
        (Backend.Word32.fma_eq_spec width_le)
  | .word64 width_le, _planning =>
      Capability.ofCertified .fma <| Certified.ternary
        (storedNativeWordEstimate (.word64 width_le) .fma)
        Spec.fma
        (Backend.Word64.fma width_le)
        (Backend.Word64.fma_eq_spec width_le)
  | .pair width_le, _planning =>
      let heligible : Model.NativeLimb.Eligible format := width_le
      Capability.ofCertified .fma <| Certified.ternary
        (storedNativeLimbEstimate (format := format) .fma)
        Spec.fma
        (Backend.storedNativeLimbFma width_le heligible)
        (Backend.storedNativeLimbFma_eq_spec width_le heligible)
  | .wide, _planning =>
      Capability.ofCertified .fma <| Certified.ternary
        (dyadicEstimate (.wide : StoragePlan format) .fma)
        Spec.fma Backend.dyadicFma Backend.dyadicFma_eq_spec

end FloatLib.Floats.Formats.Posit.Configured.Plan

namespace FloatLib.Floats.Formats.Posit.Configured

/-!
Built-in storage-plan instances have higher priority than the representation-independent instance.
Their inline operation-specific constructors specialize a closed public width to one carrier and
one first-order executor. Custom codecs retain the generic certified candidate portfolios below.
-/

@[always_inline] instance (priority := 1100) addPlannedCapability
    (format : Format) (plan : StoragePlan format)
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Add (Family format (Code plan) plan) :=
  Plan.addCapabilityForPlan format plan

@[always_inline] instance (priority := 1100) subPlannedCapability
    (format : Format) (plan : StoragePlan format)
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Sub (Family format (Code plan) plan) :=
  Plan.subCapabilityForPlan format plan

@[always_inline] instance (priority := 1100) mulPlannedCapability
    (format : Format) (plan : StoragePlan format)
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Mul (Family format (Code plan) plan) :=
  Plan.mulCapabilityForPlan format plan

@[always_inline] instance (priority := 1100) divPlannedCapability
    (format : Format) (plan : StoragePlan format)
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Div (Family format (Code plan) plan) :=
  Plan.divCapabilityForPlan format plan

@[always_inline] instance (priority := 1100) sqrtPlannedCapability
    (format : Format) (plan : StoragePlan format)
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Sqrt (Family format (Code plan) plan) :=
  Plan.sqrtCapabilityForPlan format plan

@[always_inline] instance (priority := 1100) fmaPlannedCapability
    (format : Format) (plan : StoragePlan format)
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor
      (Family format (Code plan) plan)] :
    FloatLib.Floats.ExecFloat.Fma (Family format (Code plan) plan) :=
  Plan.fmaCapabilityForPlan format plan

instance addCapability
    (format : Format) (plan : StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family format code plan)] :
    FloatLib.Floats.ExecFloat.Add (Family format code plan) where
  spec := Spec.add
  candidates := Plan.addCandidates format plan

instance subCapability
    (format : Format) (plan : StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family format code plan)] :
    FloatLib.Floats.ExecFloat.Sub (Family format code plan) where
  spec := Spec.sub
  candidates := Plan.subCandidates format plan

instance mulCapability
    (format : Format) (plan : StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family format code plan)] :
    FloatLib.Floats.ExecFloat.Mul (Family format code plan) where
  spec := Spec.mul
  candidates := Plan.mulCandidates format plan

instance divCapability
    (format : Format) (plan : StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family format code plan)] :
    FloatLib.Floats.ExecFloat.Div (Family format code plan) where
  spec := Spec.div
  candidates := Plan.divCandidates format plan

instance sqrtCapability
    (format : Format) (plan : StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family format code plan)] :
    FloatLib.Floats.ExecFloat.Sqrt (Family format code plan) where
  spec := Spec.sqrt
  candidates := Plan.sqrtCandidates format plan

instance fmaCapability
    (format : Format) (plan : StoragePlan format) (code : Type)
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    [FloatLib.Floats.ExecFloat.Backend.PolicyFor (Family format code plan)] :
    FloatLib.Floats.ExecFloat.Fma (Family format code plan) where
  spec := Spec.fma
  candidates := Plan.fmaCandidates format plan

end FloatLib.Floats.Formats.Posit.Configured
