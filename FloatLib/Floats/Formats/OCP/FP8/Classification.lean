/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.FP8.Conversion
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Classification

/-!
# OFP8 SAT finiteness and real-value contract

OCP OFP8 revision 1.0 (2023-12-01), §5.2.1: conversion of a finite source
under SAT succeeds with a finite result. Its real value is nearest-even
rounding followed by endpoint clipping. The proofs apply to arbitrary exact
source decoders and binary destination descriptors.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.FP8

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat
open FloatLib.Floats.Formats.BinaryInterchange

universe u

/-- OFP8 rev. 1.0, §5.2.1: SAT sends every finite exact source to a finite word. -/
theorem isFinite_convert_sat {Source : Type u} [ExactDecoder Source SignedRat]
    (destination : FloatFormat) (value : Source) (exact : SignedRat)
    (rounded : Model destination) (status : ConversionStatus)
    (hsource : ExactDecoder.run value = .finite exact)
    (hout : convert destination .saturate value = .success rounded status) :
    Model.isFinite rounded = true := by
  rw [convert_finite destination .saturate value exact hsource] at hout
  simp only [ExecFloat.Binary.Conversion.quantizeFiniteWith] at hout
  split at hout
  next result hround =>
    cases hout
    exact Model.Policy.isFinite_roundRat_saturate_nearest destination 0 exact.negative
      exact.value.num.natAbs exact.value.den exact.value.den_nz result
      (by simpa only [policy, ExecFloat.Binary.Conversion.Policy.withRounding] using hround)
  next => cases hout

/-- OFP8 rev. 1.0, §5.2.1: SAT is nearest-even real-grid rounding followed by clipping. -/
theorem toReal_convert_sat {Source : Type u} [ExactDecoder Source SignedRat]
    (destination : FloatFormat) (value : Source) (exact : SignedRat)
    (rounded : Model destination) (status : ConversionStatus)
    (hsource : ExactDecoder.run value = .finite exact)
    (hout : convert destination .saturate value = .success rounded status) :
    Model.toReal rounded =
      Model.clampAt destination (Model.roundAt destination (exact.value : ℝ)) := by
  simpa using toReal_convert_finite destination .saturate value exact rounded status
    hsource hout (isFinite_convert_sat destination value exact rounded status hsource hout)

/--
OFP8 rev. 1.0, §5.2.1: every finite source has a successful finite SAT result,
with the independent real-grid value. No output-finiteness premise is required.
-/
theorem convert_sat_finite {Source : Type u} [ExactDecoder Source SignedRat]
    (destination : FloatFormat) (value : Source) (exact : SignedRat)
    (hsource : ExactDecoder.run value = .finite exact) :
    ∃ rounded status,
      convert destination .saturate value = .success rounded status ∧
      Model.isFinite rounded = true ∧
      Model.toReal rounded =
        Model.clampAt destination (Model.roundAt destination (exact.value : ℝ)) := by
  let rounded := Model.Policy.roundRatGeneralOfDenNeZero destination
    { rounding := .nearest, overflow := .saturate } 0 exact.negative
    exact.value.num.natAbs exact.value.den exact.value.den_nz
  have hout : convert destination .saturate value =
      .success rounded (ExecFloat.Binary.Conversion.finiteStatus
        ((policy .saturate).withRounding .nearest) exact.value rounded) := by
    rw [convert_finite destination .saturate value exact hsource]
    simp [ExecFloat.Binary.Conversion.quantizeFiniteWith, Model.Policy.roundRat,
      exact.value.den_nz, policy, ExecFloat.Binary.Conversion.Policy.withRounding,
      QuantizationPolicy.nearest, rounded]
  exact ⟨_, _, hout, isFinite_convert_sat destination value exact _ _ hsource hout,
    toReal_convert_sat destination value exact _ _ hsource hout⟩

end FloatLib.Floats.Formats.OCP.FP8
