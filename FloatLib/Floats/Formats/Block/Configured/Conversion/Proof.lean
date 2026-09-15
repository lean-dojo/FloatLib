/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Conversion.Proof
public import FloatLib.Floats.Formats.Block.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.Block.Configured.Proof

/-!
# Shared-scale block conversion proofs

The principal result proves that direct block conversion satisfies the lane-wise nearest-even
`QuantizesAt` relation at the caller-supplied shared exponent.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat.SharedScale
namespace Conversion

variable {lanes : Nat}

/-- Finite vectors are quantized lane-wise at the explicitly supplied exponent. -/
@[simp, grind =] theorem run_finite (exponent : Int) (exact : Vector Rat lanes) :
    run exponent (.finite exact) =
      let rounded := ExecFloat.SharedScale.quantizeAt exponent exact
      .success rounded (status exact rounded) :=
  rfl

/-- The generic shared-scale block has no infinity encoding. -/
@[simp, grind =] theorem run_infinity (exponent : Int) (negative : Bool) :
    run (lanes := lanes) exponent (.infinity negative) =
      .failure (.infinity .source negative) :=
  rfl

/-- The generic shared-scale block has no exceptional encoding. -/
@[simp, grind =] theorem run_exceptional
    (exponent : Int) (exceptional : ExceptionalValue) :
    run (lanes := lanes) exponent (.exceptional exceptional) =
      .failure (.exceptional .source exceptional) :=
  rfl

/-- The direct configured block converter satisfies the lane-wise relational specification. -/
theorem implements_run :
    Quantization.Spec.Implements
      (spec (lanes := lanes))
      (run (lanes := lanes)) := by
  intro exponent input
  cases input with
  | finite exact =>
      refine ⟨ExecFloat.SharedScale.quantizeAt exponent exact, rfl, ?_⟩
      exact ExecFloat.SharedScale.quantizesAt_quantizeAt exponent exact
  | infinity negative => rfl
  | exceptional exceptional => rfl

/-- The installed decoder exposes the exact decoded block. -/
@[simp, grind =] theorem exactDecoder_run (value : ExecFloat.SharedScale lanes) :
    FloatLib.Floats.ExecFloat.ExactDecoder.run value =
      .finite (ExecFloat.SharedScale.decode value) :=
  rfl

/-- The explicit exponent supplied to conversion is stored exactly. -/
@[simp, grind =] theorem exponent_of_finite_run (exponent : Int) (exact : Vector Rat lanes) :
    (FloatLib.Floats.ExecFloat.ConversionOutcome.value?
        (run exponent (.finite exact))).map ExecFloat.SharedScale.exponent =
      some exponent := by
  simp [run]

end Conversion
end ExecFloat.SharedScale
end FloatLib.Floats
