/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Runtime
public import FloatLib.Floats.Formats.P3109.Arithmetic.Runtime
public import FloatLib.Numerics.Exact.Functions.Runtime
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# P3109Functions generators

The commands expand into declarations checked in the importing module.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.P3109

open FloatLib.Numerics
open Formats.P3109

set_option hygiene false in
/-- Expand `unary_function` into its checked family declarations. -/
macro (name := unaryFunction) doc:docComment "unary_function " name:ident " := " operation:term
    : command =>
  `($doc:docComment@[inline] def $name {format : Format} (input : ExecFloat.P3109 format)
        (target : Format := format) (mode : RoundingMode := .nearest)
        (saturation : SaturationMode := .none) : ExecFloat.P3109 target :=
      projectFunction (Functions.unary $operation input.toClosedRat) mode saturation)


set_option hygiene false in
/-- Expand `binary_angle` into its checked family declarations. -/
macro (name := binaryAngle) doc:docComment "binary_angle " name:ident " := " piScaled:term :
    command =>
  `($doc:docComment@[inline] def $name {yFormat xFormat : Format}
        (y : ExecFloat.P3109 yFormat) (x : ExecFloat.P3109 xFormat)
        (target : Format := yFormat) (mode : RoundingMode := .nearest)
        (saturation : SaturationMode := .none) : ExecFloat.P3109 target :=
      projectFunction (Functions.arcTan2 $piScaled y.toClosedRat x.toClosedRat) mode saturation)


end FloatLib.Floats.ExecFloat.P3109
