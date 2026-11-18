/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Operations
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# P3109Scaled generators

The commands expand into declarations checked in the importing module.
-/

public meta section

namespace FloatLib.Floats.Formats.P3109.Arithmetic.Mixed

open FloatLib.Numerics FloatLib.Floats.ExecFloat

set_option hygiene false in
/-- Expand `scaled_unary` into its checked family declarations. -/
macro (name := scaledUnaryCommand) doc:docComment "scaled_unary " name:ident " := " op:term :
    command =>
  `($doc:docComment@[inline] def $name
        {Scale ScaleExact Source SourceExact Result : Type}
        [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
        [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
        (destination : Destination Result) (scale : Scale) (value : Source)
        (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
      scaledUnary destination $op scale value mode saturation)


set_option hygiene false in
/-- Expand `scaled_binary` into its checked family declarations. -/
macro (name := scaledBinaryCommand) doc:docComment "scaled_binary " name:ident " := " op:term :
    command =>
  `($doc:docComment@[inline] def $name
        {Scale ScaleExact Source SourceExact RightScale RightScaleExact Right RightExact Result
          : Type}
        [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
        [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
        [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
        [ExactDecoder Right RightExact] [ExactMap RightExact Rat]
        (destination : Destination Result) (scale : Scale) (value : Source)
        (rightScale : RightScale) (right : Right)
        (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
      scaledBinary destination $op scale value rightScale right mode saturation)


set_option hygiene false in
/-- Expand `scaled_ternary` into its checked family declarations. -/
macro (name := scaledTernaryCommand) doc:docComment "scaled_ternary " name:ident " := " op:term :
    command =>
  `($doc:docComment@[inline] def $name
        {Scale ScaleExact Source SourceExact RightScale RightScaleExact Right RightExact
          ThirdScale ThirdScaleExact Third ThirdExact Result : Type}
        [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
        [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
        [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
        [ExactDecoder Right RightExact] [ExactMap RightExact Rat]
        [ExactDecoder ThirdScale ThirdScaleExact] [ExactMap ThirdScaleExact Rat]
        [ExactDecoder Third ThirdExact] [ExactMap ThirdExact Rat]
        (destination : Destination Result) (scale : Scale) (value : Source)
        (rightScale : RightScale) (right : Right) (thirdScale : ThirdScale) (third : Third)
        (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) : Result :=
      scaledTernary destination $op scale value rightScale right thirdScale third mode saturation)


end FloatLib.Floats.Formats.P3109.Arithmetic.Mixed
