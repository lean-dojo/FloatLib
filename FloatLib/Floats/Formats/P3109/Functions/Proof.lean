/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.ReferencePaths

public import FloatLib.Floats.Formats.P3109.Functions.Runtime
public meta import FloatLib.Tactic.P3109FunctionProofs
public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Report
public import FloatLib.Numerics.Exact.Functions.Proof

/-!
# P3109 elementary function certificates

P3109 interim report v4.1 (14 September 2026), §§4.10.9–4.10.16,
unapproved draft. Finite function expressions denote real functions; the exact
comparators implement the report's logarithmic-quantum and fractional-part
rounding, followed by saturation. Encoding preserves the resulting datum.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Functions

/-- Closed real-function semantics followed by P3109 interim report v4.1, §§4.7.4–4.7.5 rounding
    and saturation. -/
noncomputable def referenceValue (format : Format) (policy : ProjectionPolicy)
    (expression : NumericalValue FunctionExpr) : NumericalValue Numerics.Dyadic :=
  format.saturate policy.saturation policy.rounding
    (expression.map (fun expr =>
      ComparisonRounding.reportRounded format policy.rounding expr.toReal))

/-- Exact finite-function comparison refines the real reference for every closed expression. -/
theorem value_eq_referenceValue (format : Format) (policy : ProjectionPolicy)
    (expression : NumericalValue FunctionExpr) :
    value format policy expression = referenceValue format policy expression := by
  cases expression with
  | finite expr =>
      change ComparisonRounding.value format policy (expr.prepare 8).compare =
        ComparisonRounding.reportValue format policy expr.toReal
      exact ComparisonRounding.value_eq_reportValue format policy
        (expr.prepare 8).compare expr.toReal (expr.prepare_eq_real 8)
  | infinity negative => rfl
  | exceptional category => rfl

/-- Saturation and encoding preserve every rounded elementary expression at any precision. -/
theorem sameDatum_decode_code (format : Format) (policy : ProjectionPolicy)
    (expression : NumericalValue FunctionExpr) :
    Format.SameDatum (format.decode (code format policy expression))
      (value format policy expression) := by
  unfold code value
  apply format.sameDatum_decode_encodeSaturate
  cases expression with
  | finite expr => exact ComparisonRounding.rounded_fitsPrecisionGrid _ _ _
  | infinity _ | exceptional _ => trivial

end FloatLib.Floats.Formats.P3109.Functions

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

/-- P3109 interim report v4.1, §§4.7–4.8: decoding a function projection gives its closed real
    reference datum. -/
theorem decode_projectFunction {format : Format}
    (expression : NumericalValue FunctionExpr) (mode : RoundingMode)
    (saturation : SaturationMode) :
    Format.SameDatum
      (decode (projectFunction (format := format) expression mode saturation))
      (Functions.referenceValue format { rounding := mode, saturation } expression) := by
  rw [← Functions.value_eq_referenceValue, decode_eq_format_decode]
  exact Functions.sameDatum_decode_code format _ expression


prove_unary Log via Functions.Unary.log as decode_Log
prove_unary Log2 via Functions.Unary.log2 as decode_Log2
prove_unary LogOnePlus via Functions.Unary.logOnePlus as decode_LogOnePlus
prove_unary Exp via Functions.Unary.exp as decode_Exp
prove_unary Exp2 via Functions.Unary.exp2 as decode_Exp2
prove_unary ExpMinusOne via Functions.Unary.expMinusOne as decode_ExpMinusOne
prove_unary Sin via Functions.Unary.sin as decode_Sin
prove_unary Cos via Functions.Unary.cos as decode_Cos
prove_unary Tan via Functions.Unary.tan as decode_Tan
prove_unary ArcSin via Functions.Unary.arcSin as decode_ArcSin
prove_unary ArcCos via Functions.Unary.arcCos as decode_ArcCos
prove_unary ArcTan via Functions.Unary.arcTan as decode_ArcTan
prove_unary Sinh via Functions.Unary.sinh as decode_Sinh
prove_unary Cosh via Functions.Unary.cosh as decode_Cosh
prove_unary Tanh via Functions.Unary.tanh as decode_Tanh
prove_unary ArcSinh via Functions.Unary.arcSinh as decode_ArcSinh
prove_unary ArcCosh via Functions.Unary.arcCosh as decode_ArcCosh
prove_unary ArcTanh via Functions.Unary.arcTanh as decode_ArcTanh
prove_unary SinPi via Functions.Unary.sinPi as decode_SinPi
prove_unary CosPi via Functions.Unary.cosPi as decode_CosPi
prove_unary TanPi via Functions.Unary.tanPi as decode_TanPi
prove_unary ArcSinPi via Functions.Unary.arcSinPi as decode_ArcSinPi
prove_unary ArcCosPi via Functions.Unary.arcCosPi as decode_ArcCosPi
prove_unary ArcTanPi via Functions.Unary.arcTanPi as decode_ArcTanPi
prove_unary Softplus via Functions.Unary.softplus as decode_Softplus


prove_angle ArcTan2 via false as decode_ArcTan2
prove_angle ArcTan2Pi via true as decode_ArcTan2Pi

end FloatLib.Floats.ExecFloat.P3109

/-!
# P3109 elementary function execution paths

P3109 interim report v4.1 §§4.10.9–4.10.13 and §§4.10.15–4.10.16 (unapproved draft).
Every named function has a compiled reference certificate and a kernel
defining equation. The function proof supplies the real-value contract; these
certificates retain that same algorithm at all descriptors and policies.
The planner estimate is descriptive metadata, with no performance claim.
-/

namespace FloatLib.Floats.ExecFloat.P3109

reference_paths Log
reference_paths Log2
reference_paths LogOnePlus
reference_paths Exp
reference_paths Exp2
reference_paths ExpMinusOne
reference_paths Sin
reference_paths Cos
reference_paths Tan
reference_paths ArcSin
reference_paths ArcCos
reference_paths ArcTan
reference_paths Sinh
reference_paths Cosh
reference_paths Tanh
reference_paths ArcSinh
reference_paths ArcCosh
reference_paths ArcTanh
reference_paths SinPi
reference_paths CosPi
reference_paths TanPi
reference_paths ArcSinPi
reference_paths ArcCosPi
reference_paths ArcTanPi
reference_paths Softplus
reference_paths ArcTan2
reference_paths ArcTan2Pi

attribute [kernel_optimize] projectFunction.eq_def

end FloatLib.Floats.ExecFloat.P3109
