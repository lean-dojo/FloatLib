/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Functions.Runtime
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# P3109BlockFunctions generators

The commands expand into declarations checked in the importing module.
-/

public meta section

namespace FloatLib.Floats.Formats.P3109.Block

open FloatLib.Numerics FloatLib.Floats.ExecFloat

set_option hygiene false in
/-- Expand `block_function` into its checked family declarations. -/
macro (name := blockFunction) "block_function " name:ident " := " operation:term : command =>
  `(/-- P3109 interim report v4.1 §5.7, using the §4.10 scalar function: exact lane evaluation,
    result-scale normalization, and one projection with the lane's policy. -/
    def $name {length : ℕ+}
        {Scale ScaleExact Source SourceExact ResultScale ResultScaleExact : Type}
        [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
        [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
        [ExactDecoder ResultScale ResultScaleExact] [ExactMap ResultScaleExact Rat]
        (format : Format) (policy : BlockPolicy length)
        (block : Block Scale Source length) (resultScale : ResultScale) :
        Block ResultScale (ExecFloat.P3109 format) length :=
      unaryFunction format policy $operation block resultScale)


set_option hygiene false in
/-- Expand `block_angle` into its checked family declarations. -/
macro (name := blockAngle) "block_angle " name:ident " := " scaled:term : command =>
  `(/-- P3109 interim report v4.1 §5.7, using §4.10.15–4.10.16: the exact argument of independently
    decoded lanes, optionally divided by π, normalized before one final projection. -/
    def $name {length : ℕ+}
        {Scale ScaleExact Source SourceExact RightScale RightScaleExact Right RightExact
          ResultScale ResultScaleExact : Type}
        [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
        [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
        [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
        [ExactDecoder Right RightExact] [ExactMap RightExact Rat]
        [ExactDecoder ResultScale ResultScaleExact] [ExactMap ResultScaleExact Rat]
        (format : Format) (policy : BlockPolicy length)
        (y : Block Scale Source length) (x : Block RightScale Right length)
        (resultScale : ResultScale) : Block ResultScale (ExecFloat.P3109 format) length :=
      angleFunction format policy $scaled y x resultScale)


end FloatLib.Floats.Formats.P3109.Block
