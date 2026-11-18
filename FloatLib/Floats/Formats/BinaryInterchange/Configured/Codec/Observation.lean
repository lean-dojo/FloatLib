/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real

/-!
# Observations of configured codec operations

Decoding and real observation commute with model lifts and packed outcomes.
-/

public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]

/-- The binary decoder preserves values packed by the same configured family. -/
theorem decode_family (value : Model format) :
    ExecFloat.Binary.toModel
        (Configured.Family.ofModel (plan := plan) (code := code) value) = value := by
  change Configured.Family.toModel (Configured.Family.ofModel value) = value
  exact Configured.Family.toModel_ofModel value

/-- The codec preserves any unary model operation, including the scalar context's functions. -/
theorem decode_unary (operation : Model format → Model format)
    (value : ExecFloat (Configured.Family format code plan)) :
    ExecFloat.Binary.toModel
        (ExecFloat.ModelCodec.liftUnary (Model := Model format) (plan := plan) operation value) =
      operation (ExecFloat.Binary.toModel value) :=
  ExecFloat.ModelCodec.decode_liftUnary operation value

/-- Binary scalar lifts use the same codec law regardless of their numerical operation. -/
theorem decode_binary (operation : Model format → Model format → Model format)
    (left right : ExecFloat (Configured.Family format code plan)) :
    ExecFloat.Binary.toModel
        (ExecFloat.ModelCodec.liftBinary (Model := Model format) (plan := plan)
          operation left right) =
      operation (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) :=
  ExecFloat.ModelCodec.decode_liftBinary operation left right

/-- The codec preserves an outcome's value independently of its exception indicators. -/
theorem decode_outcome (outcome : Model.IEEEOutcome format) :
    ExecFloat.Binary.toModel
        ((ExecFloat.Binary.IEEEOutcome.ofModel (plan := plan) (code := code) outcome).value) =
      outcome.value := by
  simpa only [ExecFloat.Binary.IEEEOutcome.toModel] using
    congrArg Model.IEEEOutcome.value
      (ExecFloat.Binary.IEEEOutcome.toModel_ofModel (plan := plan) (code := code) outcome)

/-- A real observation can pass through a scalar lift before its numerical law is applied. -/
theorem toReal_liftUnary (operation : Model format → Model format)
    (value : ExecFloat (Configured.Family format code plan)) :
    ExecFloat.Binary.toReal
        (ExecFloat.ModelCodec.liftUnary (Model := Model format) (plan := plan) operation value) =
      Model.toReal (operation (ExecFloat.Binary.toModel value)) :=
  congrArg Model.toReal (decode_unary operation value)

/-- Binary lifts retain the chosen model operation and both operands. -/
theorem toReal_liftBinary (operation : Model format → Model format → Model format)
    (left right : ExecFloat (Configured.Family format code plan)) :
    ExecFloat.Binary.toReal
        (ExecFloat.ModelCodec.liftBinary (Model := Model format) (plan := plan)
          operation left right) =
      Model.toReal (operation (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)) :=
  congrArg Model.toReal (decode_binary operation left right)

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
