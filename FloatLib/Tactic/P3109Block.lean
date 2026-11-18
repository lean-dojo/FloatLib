/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Block.Proof
public import FloatLib.Floats.Formats.P3109.Block.Root.Proof
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# P3109Block generators

The commands expand into declarations checked in the importing module.
-/

public meta section

namespace FloatLib.Floats.Formats.P3109.Block

open FloatLib.Numerics FloatLib.Floats.ExecFloat Arithmetic

set_option hygiene false in
/-- Expand `block_unary` into its checked family declarations. -/
macro (name := blockUnary) doc:docComment "block_unary " name:ident " := " op:term : command =>
  `($doc:docComment@[inline] def $name {length : ℕ+}
        {Scale ScaleExact Source SourceExact ResultScale ResultScaleExact Result : Type}
        [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
        [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
        [ExactDecoder ResultScale ResultScaleExact] [ExactMap ResultScaleExact Rat]
        (destination : Destination Result) (policy : BlockPolicy length)
        (block : Block Scale Source length) (resultScale : ResultScale) :
        Block ResultScale Result length :=
      unary destination policy $op block resultScale)


set_option hygiene false in
/-- Expand `block_binary` into its checked family declarations. -/
macro (name := blockBinary) doc:docComment "block_binary " name:ident " := " op:term : command =>
  `($doc:docComment@[inline] def $name {length : ℕ+}
        {Scale ScaleExact Source SourceExact RightScale RightScaleExact Right RightExact
          ResultScale ResultScaleExact Result : Type}
        [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
        [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
        [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
        [ExactDecoder Right RightExact] [ExactMap RightExact Rat]
        [ExactDecoder ResultScale ResultScaleExact] [ExactMap ResultScaleExact Rat]
        (destination : Destination Result) (policy : BlockPolicy length)
        (left : Block Scale Source length) (right : Block RightScale Right length)
        (resultScale : ResultScale) : Block ResultScale Result length :=
      binary destination policy $op left right resultScale)


set_option hygiene false in
/-- Expand `block_ternary` into its checked family declarations. -/
macro (name := blockTernary) doc:docComment "block_ternary " name:ident " := " op:term : command =>
  `($doc:docComment@[inline] def $name {length : ℕ+}
        {Scale ScaleExact Source SourceExact RightScale RightScaleExact Right RightExact
          ThirdScale ThirdScaleExact Third ThirdExact ResultScale ResultScaleExact Result : Type}
        [ExactDecoder Scale ScaleExact] [ExactMap ScaleExact Rat]
        [ExactDecoder Source SourceExact] [ExactMap SourceExact Rat]
        [ExactDecoder RightScale RightScaleExact] [ExactMap RightScaleExact Rat]
        [ExactDecoder Right RightExact] [ExactMap RightExact Rat]
        [ExactDecoder ThirdScale ThirdScaleExact] [ExactMap ThirdScaleExact Rat]
        [ExactDecoder Third ThirdExact] [ExactMap ThirdExact Rat]
        [ExactDecoder ResultScale ResultScaleExact] [ExactMap ResultScaleExact Rat]
        (destination : Destination Result) (policy : BlockPolicy length)
        (left : Block Scale Source length) (right : Block RightScale Right length)
        (third : Block ThirdScale Third length) (resultScale : ResultScale) :
        Block ResultScale Result length :=
      ternary destination policy $op left right third resultScale)


end FloatLib.Floats.Formats.P3109.Block
