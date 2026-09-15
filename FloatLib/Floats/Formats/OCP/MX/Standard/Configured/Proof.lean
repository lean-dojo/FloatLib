/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.Configured.Runtime
public import FloatLib.Floats.Formats.OCP.MX.Standard.Proof

/-!
# Certified configured standard MX conversion

The common destination capability is backed by the numerical nearest-even and shared-scale
contracts. SAT is the default specified by this implementation of the recommendation in §6.3;
the explicit context also permits FP8 OVF conversion.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.OCP.MX.Standard

open FloatLib.Numerics
open FloatLib.Floats.Formats.OCP.MX.Standard

variable {profile : Profile}

/-- The configured source decoder agrees with the format's exact finite-block denotation. -/
theorem exactDecoder_eq_denote (value : Standard profile) :
    ExecFloat.ExactDecoder.decode value =
      FormatSemantics.denote (F := Family profile) value.toCode :=
  rfl

namespace Conversion

/-- Configured conversion satisfies the numerical block contract for both explicit modes. -/
theorem implements_run :
    Quantization.Spec.Implements (spec (profile := profile)) (run (profile := profile)) := by
  intro mode input
  cases input with
  | finite exact =>
    exact ⟨quantize mode exact, rfl,
      Formats.OCP.MX.Standard.quantizeFinite_quantizes profile mode exact⟩
  | infinity sign => rfl
  | exceptional value => rfl

/-- The standard block destination quantizer has an explicit FP8 overflow policy context. -/
instance quantizer : ExecFloat.Quantizer (Standard profile) (Vector SignedRat 32) where
  Context := OverflowMode
  run := run
  spec := spec
  correct := implements_run

/-- Standard max-binade block conversion defaults to nearest-even with finite saturation. -/
instance defaultQuantizer :
    ExecFloat.DefaultQuantizer (Standard profile) (Vector SignedRat 32) where
  defaultContext := .saturate

end Conversion
end FloatLib.Floats.ExecFloat.OCP.MX.Standard
