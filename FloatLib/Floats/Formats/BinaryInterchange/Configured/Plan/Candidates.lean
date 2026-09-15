/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Core.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Estimates
public import FloatLib.Floats.ExecFloat.Backends.Selection.Certified

/-!
# Structural candidate portfolios for configured binary formats

Each operation receives the single structural route entered by its executable dispatcher. Callers
may prepend representation-specific direct candidates. The generic kernel remains the certified
total baseline for every precision and encoding.

The constructors are planning-time code and are marked `@[nospecialize]`. Their closures contain
the inlined word dispatchers, and specializing them for every storage plan of `Configured.Code`
would duplicate that code once per plan and operation without any effect on the arithmetic hot
path, which reaches the kernels through the first-order `execute` entry points instead.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan

open FloatLib.Floats.ExecFloat
open FloatLib.Floats.ExecFloat.Backend
/-! ## Complete per-operation candidate sets -/

/-- Complete certified addition portfolio for a configured carrier and optional direct kernels. -/
@[nospecialize] def addCandidates
    (format : FloatFormat) (plan : StoragePlan format)
    {code : Type} [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    (direct : List (Certified (@Spec.add format plan code inferInstance)) := []) :
    CandidateSet (Certified (@Spec.add format plan code inferInstance)) where
  alternatives := direct ++
    (Descriptor.Plan.structuralRoute? format .add).toList.map (fun route =>
      Certified.binary
        (structuralEstimate plan .add route)
        Spec.add Backend.wordAdd Backend.wordAdd_eq_spec)
  baseline :=
    Certified.binary (genericEstimate plan .add)
      Spec.add Backend.genericAdd Backend.genericAdd_eq_spec

/--
Complete certified subtraction portfolio for a configured carrier and optional direct kernels.
-/
@[nospecialize] def subCandidates
    (format : FloatFormat) (plan : StoragePlan format)
    {code : Type} [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    (direct : List (Certified (@Spec.sub format plan code inferInstance)) := []) :
    CandidateSet (Certified (@Spec.sub format plan code inferInstance)) where
  alternatives := direct ++
    (Descriptor.Plan.structuralRoute? format .sub).toList.map (fun route =>
      Certified.binary
        (structuralEstimate plan .sub route)
        Spec.sub Backend.wordSub Backend.wordSub_eq_spec)
  baseline :=
    Certified.binary (genericEstimate plan .sub)
      Spec.sub Backend.genericSub Backend.genericSub_eq_spec

/--
Complete certified multiplication portfolio for a configured carrier and optional direct kernels.
-/
@[nospecialize] def mulCandidates
    (format : FloatFormat) (plan : StoragePlan format)
    {code : Type} [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    (direct : List (Certified (@Spec.mul format plan code inferInstance)) := []) :
    CandidateSet (Certified (@Spec.mul format plan code inferInstance)) where
  alternatives := direct ++
    (Descriptor.Plan.structuralRoute? format .mul).toList.map (fun route =>
      Certified.binary
        (structuralEstimate plan .mul route)
        Spec.mul Backend.wordMul Backend.wordMul_eq_spec)
  baseline :=
    Certified.binary (genericEstimate plan .mul)
      Spec.mul Backend.genericMul Backend.genericMul_eq_spec

/-- Complete certified division portfolio for a configured carrier and optional direct kernels. -/
@[nospecialize] def divCandidates
    (format : FloatFormat) (plan : StoragePlan format)
    {code : Type} [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    (direct : List (Certified (@Spec.div format plan code inferInstance)) := []) :
    CandidateSet (Certified (@Spec.div format plan code inferInstance)) where
  alternatives := direct ++
    (Descriptor.Plan.structuralRoute? format .div).toList.map (fun route =>
      Certified.binary
        (structuralEstimate plan .div route)
        Spec.div Backend.wordDiv Backend.wordDiv_eq_spec)
  baseline :=
    Certified.binary (genericEstimate plan .div)
      Spec.div Backend.genericDiv Backend.genericDiv_eq_spec

/--
Complete certified square-root portfolio for a configured carrier and optional direct kernels.
-/
@[nospecialize] def sqrtCandidates
    (format : FloatFormat) (plan : StoragePlan format)
    {code : Type} [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    (direct : List (Certified (@Spec.sqrt format plan code inferInstance)) := []) :
    CandidateSet (Certified (@Spec.sqrt format plan code inferInstance)) where
  alternatives := direct ++
    (Descriptor.Plan.structuralRoute? format .sqrt).toList.map (fun route =>
      match route with
      | .fixedLimbs =>
          Certified.unary (structuralEstimate plan .sqrt route)
            Spec.sqrt Backend.fixedLimbSqrt Backend.fixedLimbSqrt_eq_spec
      | .fixedFormat | .nativeWord =>
          Certified.unary (structuralEstimate plan .sqrt route)
            Spec.sqrt Backend.wordSqrt Backend.wordSqrt_eq_spec)
  baseline :=
    Certified.unary (genericEstimate plan .sqrt)
      Spec.sqrt Backend.genericSqrt Backend.genericSqrt_eq_spec

/--
Complete certified fused-multiply-add portfolio for a configured carrier and optional direct
kernels.
-/
@[nospecialize] def fmaCandidates
    (format : FloatFormat) (plan : StoragePlan format)
    {code : Type} [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]
    (direct : List (Certified (@Spec.fma format plan code inferInstance)) := []) :
    CandidateSet (Certified (@Spec.fma format plan code inferInstance)) where
  alternatives := direct ++
    (Descriptor.Plan.structuralRoute? format .fma).toList.map (fun route =>
      match route with
      | .fixedLimbs =>
          Certified.ternary (structuralEstimate plan .fma route)
            Spec.fma Backend.fixedLimbFma Backend.fixedLimbFma_eq_spec
      | .fixedFormat | .nativeWord =>
          Certified.ternary (structuralEstimate plan .fma route)
            Spec.fma Backend.wordFma Backend.wordFma_eq_spec)
  baseline :=
    Certified.ternary (genericEstimate plan .fma)
      Spec.fma Backend.genericFma Backend.genericFma_eq_spec

end FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan
