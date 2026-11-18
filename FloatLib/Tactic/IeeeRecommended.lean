/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Reduction.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MagnitudeExtrema.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Payload.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Augmented.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Magnitude.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.ScaledProduct.Runtime
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# IeeeRecommended generators

The commands expand into declarations checked in the importing module.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

set_option hygiene false in
/--
`magnitude_extremum name := larger, base` declares the configured operation `name` as the
selection by magnitude that falls back to the model operation `base`.
-/
macro (name := magnitudeExtremumCommand) doc:docComment "magnitude_extremum " name:ident " := "
    larger:ident ", " base:ident :
    command =>
  `($doc:docComment
    @[macro_inline] def $name (left right : (ExecFloat.Binary format.expWidth format.fracWidth
      format.encoding format.exponentBias
          format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
          format.exponentBias_le_maxFinite plan code)) (status : Bool := false) :
        match status with
        | true => IEEEOutcome (format := format) (plan := plan) (code := code)
        | false => (ExecFloat.Binary format.expWidth format.fracWidth format.encoding
          format.exponentBias
          format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
          format.exponentBias_le_maxFinite plan code) :=
      magnitudeExtremum $larger (fun x y => $base x y) left right status)


set_option hygiene false in
/--
`magnitude_reduction name := model` declares the configured reduction `name` of one array as
the model reduction `model` on the decoded operands, with the rounding direction and the status
option of `sum`.
-/
macro (name := magnitudeReductionCommand) doc:docComment "magnitude_reduction " name:ident " := "
    model:ident : command =>
  `($doc:docComment
    @[macro_inline] def $name (values : Array (ExecFloat.Binary format.expWidth format.fracWidth
      format.encoding format.exponentBias
          format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
          format.exponentBias_le_maxFinite plan code))
        (mode : Model.IEEERoundingMode := .nearest) (status : Bool := false) :
        match status with
        | true => IEEEOutcome (format := format) (plan := plan) (code := code)
        | false => (ExecFloat.Binary format.expWidth format.fracWidth format.encoding
          format.exponentBias
          format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
          format.exponentBias_le_maxFinite plan code) :=
      match status with
      | true =>
          IEEEOutcome.ofModel <|
            $model format (values.map ExecFloat.Binary.toModel) mode (status := true)
      | false =>
          ExecFloat.Binary.ofModel ($model format (values.map ExecFloat.Binary.toModel) mode))


end FloatLib.Floats.ExecFloat.Binary
