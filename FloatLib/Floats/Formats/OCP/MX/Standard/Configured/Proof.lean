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

The numerical nearest-even and shared-scale contracts back the common destination capability.
SAT is the default in this implementation of the recommendation in §6.3, and the context also
permits FP8 OVF conversion.
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

/-- Configured conversion satisfies the numerical block contract in both overflow modes. -/
theorem implements_run :
    Quantization.Spec.Implements (spec (profile := profile)) (run (profile := profile)) := by
  intro overflow input
  cases input with
  | finite exact =>
    exact ⟨quantize exact overflow, rfl,
      Formats.OCP.MX.Standard.quantizeFinite_quantizes profile overflow exact⟩
  | infinity sign => rfl
  | exceptional value => rfl

/-- Standard block destination quantizer, with the FP8 overflow mode as its context. -/
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
