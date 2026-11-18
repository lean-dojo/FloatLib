/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block.CodedDot.Reduction
public import FloatLib.Floats.Formats.OCP.MX.Standard.KernelPath

/-!
OCP MX v1.0, §§6.1–6.2: finite reduction states, cancellation and composition.
The three-position example uses the general block-shape extension.
-/

@[expose] public section

namespace FloatLibTests.Conformance.OCP.MXFiniteReduction

open FloatLib.Numerics FloatLib.Floats FloatLib.Floats.Formats
open FloatLib.Floats.Formats.BinaryInterchange

-- The decoded values are 2048, 1, -2048. The common E8M0 scale is 16.
private def left : Block.Tensor
    (OCP.MX.Standard.format (fun _ : Fin 3 => ()) .e4m3) where
  scales := (fun _ => OCP.MX.E8M0.ofNatBits 131, ())
  elements i := BitVec.ofNat 8 (if i.val = 0 then 0x70 else if i.val = 1 then 0x18 else 0xf0)

private def right : Block.Tensor
    (OCP.MX.Standard.format (fun _ : Fin 3 => ()) .e4m3) where
  scales := (fun _ => OCP.MX.E8M0.ofNatBits 127, ())
  elements _ := BitVec.ofNat 8 0x38

-- Exact intermediates preserve the unit between the two large opposite products.
example : (OCP.MX.Dot .binary32 left right (List.finRange 3)).toNatBits = 0x3f800000 := by
  decide +kernel

-- Binary16 rounds 2048 + 1 back to 2048, so the delivered result is zero.
example : (OCP.MX.Dot .binary32 left right (List.finRange 3)
    (.binary .binary16 (Block.Extended.round .binary16))).toNatBits = 0 := by
  decide +kernel

-- The block boundary does not reset the supplied reduction state.
example : (OCP.MX.DotGeneral .binary32 left right [[0, 1], [2]]
    (.binary .binary16 (Block.Extended.round .binary16))).toNatBits = 0 := by
  decide +kernel

-- Every range premise of the error theorem holds for this cancellation example.
example :
    MixedError
      (Model.toReal (OCP.MX.Dot .binary32 left right (List.finRange 3)
        (.binary .binary16 (Block.Extended.round .binary16))))
      ((List.finRange 3).map fun i => ((left.value i * right.value i : Rat) : ℝ)).sum
      (Model.unitRoundoffAt .binary32)
      ((1 + Model.unitRoundoffAt .binary32) *
          Block.Reduction.binaryErrorBound .binary16
            ((List.finRange 3).map fun i => left.value i * right.value i)
            (fun _ => Model.unitRoundoffAt .binary16)
            (fun _ => Model.underflowErrorAt .binary16) +
        Model.underflowErrorAt .binary32) := by
  apply Block.Tensor.Dot_nearest_binary_rounding
  all_goals first
    | decide +kernel
    | simp only [show List.finRange 3 = [0, 1, 2] from rfl,
        List.map_cons, List.map_nil, List.scanl_cons, List.scanl_nil, Model.Proof.add_eq_spec]
      decide +kernel

-- The full family of compiled reduction states refines the same specification.
example (reduction : Block.Reduction) (values : List (NumericalValue Rat)) :
    (compiled_reference% Block.Reduction.run using
      { name := "stored product reduction", kind := .generic,
        steadyCost := 1 }).run reduction values =
        reduction.run values := by
  rfl

section Contracts

variable {ι γ δ : Type} {F : Block.CodedFormat ι γ} {G : Block.CodedFormat ι δ}
variable (fmt output : FloatFormat) (hfmt : fmt.isIEEE = true) (houtput : output.isIEEE = true)
variable (a : Block.Tensor F) (b : Block.Tensor G) (order : List ι)
variable (ha : ∀ i ∈ order, (a.decode i).isFinite = true)
variable (hb : ∀ i ∈ order, (b.decode i).isFinite = true)
variable (hfinite : ∀ word ∈ (order.map fun i => a.value i * b.value i).scanl
  (fun sum q => Model.add sum (Block.Extended.round fmt (.finite q))) (Model.zero fmt false),
  Model.isFinite word = true)
variable (hterm : ∀ i ∈ order,
  Model.isFinite (Block.Extended.round fmt (.finite (a.value i * b.value i))) = true)
variable (hout : Model.isFinite
  (OCP.MX.Dot output a b order (.binary fmt (Block.Extended.round fmt))) = true)

-- Expose the proved dot contract, then compose it with another operation through roundoff.
example :
    MixedError
      (-Model.toReal (OCP.MX.Dot output a b order (.binary fmt (Block.Extended.round fmt))))
      (-(order.map fun i => ((a.value i * b.value i : Rat) : ℝ)).sum)
      (Model.unitRoundoffAt output)
      ((1 + Model.unitRoundoffAt output) *
          Block.Reduction.binaryErrorBound fmt (order.map fun i => a.value i * b.value i)
            (fun _ => Model.unitRoundoffAt fmt) (fun _ => Model.underflowErrorAt fmt) +
        Model.underflowErrorAt output) := by
  have hdot := Block.Tensor.Dot_nearest_binary_rounding fmt output hfmt houtput
    a b order ha hb hfinite hterm hout
  roundoff

end Contracts

end FloatLibTests.Conformance.OCP.MXFiniteReduction
