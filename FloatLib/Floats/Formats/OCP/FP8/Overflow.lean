/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.FP8.Classification
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Overflow

/-!
# OFP8 overflow after precision rounding

OCP OFP8 revision 1.0 (2023-12-01), §5.2.1: NONSAT tests the rounded
value against the finite endpoints. The classification and exact exceptional
word are proved for arbitrary destination descriptors and exact source decoders.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.FP8

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat
open FloatLib.Floats.Formats.BinaryInterchange

universe u

/--
OFP8 rev. 1.0, §5.2.1: a finite source produces a finite word exactly when
the policy or encoding saturates, or the nearest-even rounded value fits.
Fully finite encodings are a generalization beyond the two OFP8 formats.
-/
theorem isFinite_convert_iff {Source : Type u} [ExactDecoder Source SignedRat]
    (destination : FloatFormat) (overflow : OverflowMode) (value : Source)
    (exact : SignedRat) (rounded : Model destination) (status : ConversionStatus)
    (hsource : ExactDecoder.run value = .finite exact)
    (hout : convert destination overflow value = .success rounded status) :
    Model.isFinite rounded = true ↔
      overflow = .saturate ∨ destination.encoding = .finite ∨
        |Model.roundAt destination (exact.value : ℝ)| ≤
          Model.toReal (Model.posMaxFinite destination) := by
  rw [convert_finite destination overflow value exact hsource] at hout
  simp only [ExecFloat.Binary.Conversion.quantizeFiniteWith] at hout
  split at hout
  next result hround =>
    cases hout
    have h := Model.Policy.isFinite_roundRat_nearest_iff destination overflow 0
      exact.negative exact.value.num.natAbs exact.value.den exact.value.den_nz result
      (by simpa only [policy, ExecFloat.Binary.Conversion.Policy.withRounding] using hround)
    simpa only [id_eq, ExecFloat.Binary.Conversion.signedRat_toReal,
      Model.Policy.isFinite_overflowResult_nearest_eq, decide_eq_true_eq, or_assoc] using h
  next => cases hout

/-- OFP8 rev. 1.0, §5.2.1: NONSAT classification for encodings with exceptional words. -/
theorem isFinite_convert_native_iff {Source : Type u} [ExactDecoder Source SignedRat]
    (destination : FloatFormat) (hencoding : destination.encoding ≠ .finite)
    (value : Source) (exact : SignedRat) (rounded : Model destination)
    (status : ConversionStatus) (hsource : ExactDecoder.run value = .finite exact)
    (hout : convert destination .native value = .success rounded status) :
    Model.isFinite rounded = true ↔
      |Model.roundAt destination (exact.value : ℝ)| ≤
        Model.toReal (Model.posMaxFinite destination) := by
  simpa [hencoding] using
    isFinite_convert_iff destination .native value exact rounded status hsource hout

/--
OFP8 rev. 1.0, §5.2.1 Table 3: a nonfinite result from a finite source is
exactly the native overflow word. This is NaN for E4M3 and signed infinity
for E5M2, according to their destination descriptors.
-/
theorem convert_native_eq_overflow_of_not_isFinite
    {Source : Type u} [ExactDecoder Source SignedRat]
    (destination : FloatFormat) (value : Source) (exact : SignedRat)
    (rounded : Model destination) (status : ConversionStatus)
    (hsource : ExactDecoder.run value = .finite exact)
    (hout : convert destination .native value = .success rounded status)
    (hfinite : Model.isFinite rounded ≠ true) :
    rounded = Model.nativeOverflow destination exact.negative := by
  rw [convert_finite destination .native value exact hsource] at hout
  simp only [ExecFloat.Binary.Conversion.quantizeFiniteWith] at hout
  split at hout
  next result hround =>
    cases hout
    have h := Model.Policy.roundRat_nearest_eq_overflow_of_not_isFinite
      destination .native 0 exact.negative exact.value.num.natAbs exact.value.den
      exact.value.den_nz result
      (by simpa only [policy, ExecFloat.Binary.Conversion.Policy.withRounding] using hround)
      hfinite
    simpa only [id_eq, Model.Policy.overflowResult, Model.Policy.overflowRoundsMagnitudeUp,
      Model.directedOverflow, ite_true] using h
  next => cases hout

end FloatLib.Floats.Formats.OCP.FP8
