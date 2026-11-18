/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.FP8.Overflow

/-! OFP8 rev. 1.0, §5.2.1: SAT finiteness and the exact NONSAT overflow boundary. -/

@[expose] public section

namespace FloatLibTests.Conformance.OCP.OFP8Classification

open FloatLib.Floats FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.OCP.FP8

example {Source : Type} [ExecFloat.ExactDecoder Source SignedRat]
    (destination : FloatFormat) (value : Source) (exact : SignedRat)
    (hsource : ExecFloat.ExactDecoder.run value = .finite exact) :
    ∃ rounded status,
      convert destination .saturate value = .success rounded status ∧
      Model.isFinite rounded = true ∧
      Model.toReal rounded =
        Model.clampAt destination (Model.roundAt destination (exact.value : ℝ)) :=
  convert_sat_finite destination value exact hsource

example {Source : Type} [ExecFloat.ExactDecoder Source SignedRat]
    (destination : FloatFormat) (hencoding : destination.encoding ≠ .finite)
    (value : Source) (exact : SignedRat) (rounded : Model destination)
    (status : ExecFloat.ConversionStatus)
    (hsource : ExecFloat.ExactDecoder.run value = .finite exact)
    (hout : convert destination .native value = .success rounded status) :
    Model.isFinite rounded = true ↔
      |Model.roundAt destination (exact.value : ℝ)| ≤
        Model.toReal (Model.posMaxFinite destination) :=
  isFinite_convert_native_iff destination hencoding value exact rounded status hsource hout

example {Source : Type} [ExecFloat.ExactDecoder Source SignedRat]
    (value : Source) (exact : SignedRat) (rounded : Model .e4m3)
    (status : ExecFloat.ConversionStatus)
    (hsource : ExecFloat.ExactDecoder.run value = .finite exact)
    (hout : convert .e4m3 .native value = .success rounded status)
    (hfinite : Model.isFinite rounded ≠ true) :
    Model.isNaN rounded = true := by
  rw [convert_native_eq_overflow_of_not_isFinite .e4m3 value exact rounded status
    hsource hout hfinite]
  cases exact.negative <;> decide

example {Source : Type} [ExecFloat.ExactDecoder Source SignedRat]
    (value : Source) (exact : SignedRat) (rounded : Model .e5m2)
    (status : ExecFloat.ConversionStatus)
    (hsource : ExecFloat.ExactDecoder.run value = .finite exact)
    (hout : convert .e5m2 .native value = .success rounded status)
    (hfinite : Model.isFinite rounded ≠ true) :
    rounded = if exact.negative then Model.negInf .e5m2 else Model.posInf .e5m2 := by
  rw [convert_native_eq_overflow_of_not_isFinite .e5m2 value exact rounded status
    hsource hout hfinite]
  cases exact.negative <;> rfl

end FloatLibTests.Conformance.OCP.OFP8Classification
