/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.Reduction.Proof
public import FloatLib.Tactic.Roundoff

/-!
# Stored dot products with finite binary intermediates

OCP MX v1.0, §§6.1–6.2: the intermediate format, product projection, order and
output format are independent parameters. The bounds below concern stored
operands. They retain finiteness of projected products, all partial sums and
the final output as explicit range hypotheses.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block.Tensor

open FloatLib.Numerics FloatLib.Floats.Formats.BinaryInterchange

variable {ι γ δ : Type} {F : CodedFormat ι γ} {G : CodedFormat ι δ}

/--
OCP MX v1.0, §6.1: finite binary accumulation of stored products has a
cancellation-safe absolute intermediate bound, followed by final output rounding.
The product projection may have any proved mixed-error contract.
-/
theorem Dot_binary_rounding (fmt output : FloatFormat)
    (hfmt : fmt.isIEEE = true) (houtput : output.isIEEE = true)
    (project : NumericalValue Rat → Model fmt) (a : Tensor F) (b : Tensor G)
    (order : List ι) (rel err : Rat → ℝ)
    (ha : ∀ i ∈ order, (a.decode i).isFinite = true)
    (hb : ∀ i ∈ order, (b.decode i).isFinite = true)
    (hfinite : ∀ word ∈ (order.map fun i => a.value i * b.value i).scanl
      (fun sum q => Model.add sum (project (.finite q))) (Model.zero fmt false),
      Model.isFinite word = true)
    (hterm : ∀ i ∈ order,
      Model.isFinite (project (.finite (a.value i * b.value i))) = true)
    (eterm : ∀ i ∈ order,
      MixedError (Model.toReal (project (.finite (a.value i * b.value i))))
        ((a.value i * b.value i : Rat) : ℝ)
        (rel (a.value i * b.value i)) (err (a.value i * b.value i)))
    (hout : Model.isFinite
      (OCP.MX.Dot output a b order (.binary fmt project)) = true) :
    MixedError (Model.toReal (OCP.MX.Dot output a b order (.binary fmt project)))
      (order.map fun i => ((a.value i * b.value i : Rat) : ℝ)).sum
      (Model.unitRoundoffAt output)
      ((1 + Model.unitRoundoffAt output) *
          Reduction.binaryErrorBound fmt (order.map fun i => a.value i * b.value i) rel err +
        Model.underflowErrorAt output) := by
  have hproducts := products_finite a b order ha hb
  have h := Reduction.mixedError_round_binary fmt output hfmt houtput project
    (order.map fun i => a.value i * b.value i) rel err hfinite
    (by
      rintro q hq
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      exact hterm i hi)
    (by
      rintro q hq
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      exact eterm i hi)
    (by simpa only [OCP.MX.Dot, hproducts] using hout)
  simpa only [OCP.MX.Dot, hproducts, List.map_map, Function.comp_def] using h

/--
OCP MX v1.0, §6.1: concrete nearest-even product projection and binary-word
accumulation, with independent accumulator and delivered-output descriptors.
-/
theorem Dot_nearest_binary_rounding (fmt output : FloatFormat)
    (hfmt : fmt.isIEEE = true) (houtput : output.isIEEE = true)
    (a : Tensor F) (b : Tensor G) (order : List ι)
    (ha : ∀ i ∈ order, (a.decode i).isFinite = true)
    (hb : ∀ i ∈ order, (b.decode i).isFinite = true)
    (hfinite : ∀ word ∈ (order.map fun i => a.value i * b.value i).scanl
      (fun sum q => Model.add sum (Extended.round fmt (.finite q))) (Model.zero fmt false),
      Model.isFinite word = true)
    (hterm : ∀ i ∈ order,
      Model.isFinite (Extended.round fmt (.finite (a.value i * b.value i))) = true)
    (hout : Model.isFinite
      (OCP.MX.Dot output a b order (.binary fmt (Extended.round fmt))) = true) :
    MixedError
      (Model.toReal (OCP.MX.Dot output a b order (.binary fmt (Extended.round fmt))))
      (order.map fun i => ((a.value i * b.value i : Rat) : ℝ)).sum
      (Model.unitRoundoffAt output)
      ((1 + Model.unitRoundoffAt output) *
          Reduction.binaryErrorBound fmt (order.map fun i => a.value i * b.value i)
            (fun _ => Model.unitRoundoffAt fmt) (fun _ => Model.underflowErrorAt fmt) +
        Model.underflowErrorAt output) :=
  Dot_binary_rounding fmt output hfmt houtput (Extended.round fmt) a b order
    (fun _ => Model.unitRoundoffAt fmt) (fun _ => Model.underflowErrorAt fmt)
    ha hb hfinite hterm
    (fun i hi => Reduction.mixedError_round_finite fmt hfmt _ (hterm i hi)) hout

/--
OCP MX v1.0, §6.2: the same finite-accumulator bound for ordered blocks.
All word operations use the flattened order, including across block boundaries.
-/
theorem DotGeneral_nearest_binary_rounding (fmt output : FloatFormat)
    (hfmt : fmt.isIEEE = true) (houtput : output.isIEEE = true)
    (a : Tensor F) (b : Tensor G) (blocks : List (List ι))
    (ha : ∀ i ∈ blocks.flatten, (a.decode i).isFinite = true)
    (hb : ∀ i ∈ blocks.flatten, (b.decode i).isFinite = true)
    (hfinite : ∀ word ∈ (blocks.flatten.map fun i => a.value i * b.value i).scanl
      (fun sum q => Model.add sum (Extended.round fmt (.finite q))) (Model.zero fmt false),
      Model.isFinite word = true)
    (hterm : ∀ i ∈ blocks.flatten,
      Model.isFinite (Extended.round fmt (.finite (a.value i * b.value i))) = true)
    (hout : Model.isFinite
      (OCP.MX.DotGeneral output a b blocks (.binary fmt (Extended.round fmt))) = true) :
    MixedError
      (Model.toReal (OCP.MX.DotGeneral output a b blocks (.binary fmt (Extended.round fmt))))
      (blocks.flatten.map fun i => ((a.value i * b.value i : Rat) : ℝ)).sum
      (Model.unitRoundoffAt output)
      ((1 + Model.unitRoundoffAt output) *
          Reduction.binaryErrorBound fmt (blocks.flatten.map fun i => a.value i * b.value i)
            (fun _ => Model.unitRoundoffAt fmt) (fun _ => Model.underflowErrorAt fmt) +
        Model.underflowErrorAt output) :=
  Dot_nearest_binary_rounding fmt output hfmt houtput a b blocks.flatten
    ha hb hfinite hterm hout

attribute [roundoff_rule] Dot_binary_rounding Dot_nearest_binary_rounding
  DotGeneral_nearest_binary_rounding

end FloatLib.Floats.Formats.Block.Tensor
