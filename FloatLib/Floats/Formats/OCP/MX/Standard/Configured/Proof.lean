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

Conversion into a standard MX block goes through the common destination capability, and the
numerical nearest-even and shared-scale contracts are what certify it. Our implementation of the
§6.3 recommendation defaults to SAT, and the conversion context also allows FP8 OVF conversion.
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

/--
Configured conversion satisfies `spec` in both overflow modes. The stored block is checked against
the independent nearest-even, shared-scale relation `Quantizes`. The status flags enter `spec` as
`status exact rounded`, the function `run` itself calls, so their part of this theorem holds by
definition and checks the flags against no independent statement.
-/
theorem implements_run :
    Quantization.Spec.Implements (spec (profile := profile)) (run (profile := profile)) := by
  intro overflow input
  cases input with
  | finite exact =>
    exact ⟨quantize exact overflow, rfl,
      Formats.OCP.MX.Standard.quantizeFinite_quantizes profile overflow exact⟩
  | infinity sign => rfl
  | exceptional value => rfl

/-- Standard block destination quantizer, with the FP8 overflow mode as its context. Its `correct`
field is `implements_run`, which certifies the stored block but not the status flags. -/
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
