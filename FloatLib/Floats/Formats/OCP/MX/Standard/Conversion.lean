/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Configured
public import FloatLib.Floats.Formats.OCP.MX.Standard.Format

/-!
# OCP MX conversion outcomes

These conversions use the general coded-tensor quantizer for any grouping and scale-selection
policy. Their reporting rule compares normalized inputs with signed finite element endpoints.
Source infinities and exceptional values map to a tensor of NaN scales and zero element words,
with `mappedSpecial` set. The finite quantization contract is the same reconstruction and
stored-code contract as for other coded tensors.

`Conversion.quantizer` is an explicit alternative quantizer with these special-value and reporting
policies. Its context is the scale-selection policy; `policy group profile` supplies the standard
max-binade selection. No additional global quantizer instance is installed.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.OCP.MX.Standard

open FloatLib.Numerics

variable {ι γ : Type}

/-- NaN scales with zero element words, for every group and position of an OCP tensor. -/
def nanTensor (group : ι → γ) (profile : Profile) (overflow : OverflowMode) :
    Block.Tensor (format group profile overflow) where
  scales := (fun _ => E8M0.ofNatBits 255, ())
  elements _ := 0

namespace Conversion

/-- A normalized input is outside the finite range when its magnitude exceeds its signed
endpoint, or that endpoint has no finite value. -/
def outsideFinite (profile : Profile) (value : SignedRat) : Bool :=
  match Element.toRat? (Element.endpoint profile value.negative) with
  | none => true
  | some endpoint => |endpoint| < |value.value|

variable [Fintype ι] {group : ι → γ} {profile : Profile} {overflow : OverflowMode}

/--
OCP flags for the stored tensor: exact signed observations determine inexactness; normalized
inputs determine overflow and endpoint saturation; a nonzero input stored as a finite zero
determines underflow. A non-finite used scale raises overflow immediately.
-/
def status (input : ι → SignedRat)
    (rounded : ExecFloat.Block (format group profile overflow)) : ExecFloat.ConversionStatus :=
  let tensor := rounded.toCode
  let inexact := decide (∃ i, rounded.decode i ≠ .finite (input i))
  if ∃ i, (tensor.scales.1 (group i)).exponent? = none then
    { inexact, overflow := true }
  else
    let normalized i := input i * SignedRat.ofRat (1 / tensor.scale i)
    { inexact
      overflow := decide (∃ i, outsideFinite profile (normalized i) = true)
      saturated := decide (∃ i, outsideFinite profile (normalized i) = true ∧
        tensor.elements i = Element.endpoint profile (normalized i).negative)
      underflow := decide (∃ i, (input i).value ≠ 0 ∧
        Element.toRat? (tensor.elements i) = some 0) }

/-- Quantize finite inputs and map non-finite sources to NaN scales, retaining OCP status flags. -/
def run (group : ι → γ) (profile : Profile) (overflow : OverflowMode)
    (selection : Block.Policy ι γ) :
    NumericalValue (ι → SignedRat) →
      ExecFloat.ConversionOutcome (ExecFloat.Block (format group profile overflow)) :=
  ExecFloat.Conversion.runFinite
    (ExecFloat.Block.quantize (format group profile overflow) selection) status
    (.map (ExecFloat.Block.ofCode (nanTensor group profile overflow)))

/-- Finite OCP conversion satisfies the coded-tensor rounding relation with OCP flags;
non-finite sources produce the designated NaN tensor and `mappedSpecial`. -/
def Spec (group : ι → γ) (profile : Profile) (overflow : OverflowMode)
    (selection : Block.Policy ι γ) :
    NumericalValue (ι → SignedRat) →
      ExecFloat.ConversionOutcome (ExecFloat.Block (format group profile overflow)) → Prop :=
  ExecFloat.Conversion.FiniteSpec
    (ExecFloat.Block.Quantizes (format group profile overflow) selection) status
    (.map (ExecFloat.Block.ofCode (nanTensor group profile overflow)))

/-- OCP reporting and special-value mapping preserve the complete finite quantization contract. -/
theorem implements_run (group : ι → γ) (profile : Profile) (overflow : OverflowMode) :
    Quantization.Spec.Implements (Spec group profile overflow) (run group profile overflow) := by
  intro selection input
  exact ExecFloat.Conversion.implements_runFinite
    (ExecFloat.Block.quantize (format group profile overflow) selection)
    (ExecFloat.Block.Quantizes (format group profile overflow) selection)
    (ExecFloat.Block.quantizes_quantize (format group profile overflow) selection) status
    (.map (ExecFloat.Block.ofCode (nanTensor group profile overflow))) input

/-- An explicit quantizer with OCP status reporting and special-value mapping, under a supplied
scale-selection policy. -/
@[instance_reducible] def quantizer (group : ι → γ) (profile : Profile)
    (overflow : OverflowMode) :
    ExecFloat.Quantizer (ExecFloat.Block (format group profile overflow)) (ι → SignedRat) where
  Context := Block.Policy ι γ
  run := run group profile overflow
  spec := Spec group profile overflow
  correct := implements_run group profile overflow

end Conversion

end FloatLib.Floats.Formats.OCP.MX.Standard
