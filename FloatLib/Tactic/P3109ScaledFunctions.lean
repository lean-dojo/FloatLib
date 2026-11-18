/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Functions.Operations
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# P3109ScaledFunctions generators

The commands expand into declarations checked in the importing module.
-/

public meta section

namespace FloatLib.Floats.Formats.P3109.Arithmetic.Mixed

open FloatLib.Numerics FloatLib.Floats.ExecFloat

set_option hygiene false in
/-- Expand `scaled_function` into its checked family declarations. -/
macro (name := scaledFunction) "scaled_function " name:ident " := " operation:term : command =>
  `(/-- P3109 interim report v4.1 §5.8, using the §4.10 scalar function: one exact scaled operand
    and one final destination projection through the one-lane block schema. -/
    def $name {Scale ScaleExact Source SourceExact : Type}
        [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
        [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
        (format : Format) (scale : Scale) (value : Source)
        (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
        ExecFloat.P3109 format :=
      scaledUnaryFunction format $operation scale value mode saturation)


set_option hygiene false in
/-- Expand `scaled_angle` into its checked family declarations. -/
macro (name := scaledAngle) "scaled_angle " name:ident " := " scaled:term : command =>
  `(/-- P3109 interim report v4.1 §5.8, using §4.10.15–4.10.16: independently scaled operands
    retain their exact argument, optionally in units of π, until final projection. -/
    def $name {Scale ScaleExact Source SourceExact RightScale RightScaleExact Right RightExact :
      Type}
        [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
        [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
        [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
        [ExactDecoder Right RightExact] [ExactMap RightExact Rat]
        (format : Format) (yScale : Scale) (y : Source) (xScale : RightScale) (x : Right)
        (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
        ExecFloat.P3109 format :=
      scaledAngleFunction format $scaled yScale y xScale x mode saturation)


end FloatLib.Floats.Formats.P3109.Arithmetic.Mixed
