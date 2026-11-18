/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Functions.Runtime
public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Report
public import FloatLib.Numerics.Exact.Functions.Proof
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# P3109FunctionProofs generators

The commands expand into declarations checked in the importing module.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.P3109

open FloatLib.Numerics
open Formats.P3109

set_option hygiene false in
/-- Expand `prove_unary` into its checked family declarations. -/
macro (name := proveUnary) "prove_unary " operation:ident " via " selection:term
    " as " name:ident : command =>
  `(/-- P3109 interim report v4.1 §§4.10.9–4.10.13: the named function refines its exact real
    reference
    for independent source and target formats and every projection policy. -/
    theorem $name {format : Format} (input : ExecFloat.P3109 format)
        (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
        Format.SameDatum (decode ($operation input target mode saturation))
          (Functions.referenceValue target { rounding := mode, saturation }
            (Functions.unary $selection input.toClosedRat)) :=
      decode_projectFunction _ _ _)


set_option hygiene false in
/-- Expand `prove_angle` into its checked family declarations. -/
macro (name := proveAngle) "prove_angle " operation:ident " via " piScaled:term
    " as " name:ident : command =>
  `(/-- P3109 interim report v4.1 §§4.10.15–4.10.16: independent source formats reach the real
    argument
    reference before a single destination projection. -/
    theorem $name {yFormat xFormat : Format}
        (y : ExecFloat.P3109 yFormat) (x : ExecFloat.P3109 xFormat)
        (target : Format) (mode : RoundingMode) (saturation : SaturationMode) :
        Format.SameDatum (decode ($operation y x target mode saturation))
          (Functions.referenceValue target { rounding := mode, saturation }
            (Functions.arcTan2 $piScaled y.toClosedRat x.toClosedRat)) :=
      decode_projectFunction _ _ _)


end FloatLib.Floats.ExecFloat.P3109
