/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.MX.Standard.KernelPath
public import FloatLib.Floats.Formats.Block.Roundoff

/-! OCP MX v1.0, §§6.1–6.2: standard names, generic contracts and kernel examples. -/

@[expose] public section

namespace FloatLibTests.Conformance.OCP.MX

open FloatLib.Floats FloatLib.Numerics FloatLib.Floats.Formats
open FloatLib.Floats.Formats.BinaryInterchange

-- The registered compiled converter satisfies the independent nearest-even/overflow relation.
example (profile : OCP.MX.Standard.Profile) (overflow : OverflowMode) (input : SignedRat) :
    OCP.MX.Standard.Element.QuantizesWith overflow input
      ((OCP.MX.Standard.Element.Compiled.conversion profile).run (.finite input) overflow) := by
  rw [(OCP.MX.Standard.Element.Compiled.conversion profile).run_eq_spec]
  exact OCP.MX.Standard.Element.quantize_quantizesWith profile overflow input

private def constant (profile : OCP.MX.Standard.Profile) (scale word : Nat) :
    Block.Tensor (OCP.MX.Standard.format (fun _ : Fin 32 => ()) profile) where
  scales := (fun _ => OCP.MX.E8M0.ofNatBits scale, ())
  elements _ := BitVec.ofNat profile.width word

-- A mixed-profile, standard-length block: 32 * (2 * 1) * (1/2 * 1) = 32.
example : (OCP.MX.Dot .binary32 (constant .e2m1 128 2) (constant .int8 126 64)
    (List.finRange 32)).toNatBits = 0x42000000 := by
  decide +kernel

-- Empty padded vectors give positive zero, independently of the element profiles.
example : (OCP.MX.DotGeneral .binary32 (constant .e4m3 127 0)
    (constant .e5m2 127 0) []).toNatBits = 0 := by
  decide +kernel

section Contracts

variable {ι γ δ : Type} {F : Block.CodedFormat ι γ} {G : Block.CodedFormat ι δ}
variable (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
variable (a : Block.Tensor F) (b : Block.Tensor G) (blocks : List (List ι))
variable (ha : ∀ block ∈ blocks, ∀ i ∈ block, (a.decode i).isFinite = true)
variable (hb : ∀ block ∈ blocks, ∀ i ∈ block, (b.decode i).isFinite = true)
variable (hfinite : Model.isFinite (OCP.MX.DotGeneral fmt a b blocks) = true)

example :
    Model.toReal (OCP.MX.DotGeneral fmt a b blocks) =
      Model.roundAt fmt
        (((blocks.map fun block =>
          (block.map fun i => a.value i * b.value i).sum).sum : ℚ) : ℝ) :=
  Block.Tensor.toReal_DotGeneral_eq_roundAt fmt hfmt a b blocks ha hb hfinite

end Contracts

-- A caller can expose the proved contract before composing a stored dot with real arithmetic.
-- Automatic discovery of a stored Tensor.value observation remains separate from this contract.
example {ι γ δ : Type} {F : Block.CodedFormat ι γ} {G : Block.CodedFormat ι δ}
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (a : Block.Tensor F) (b : Block.Tensor G)
    (order : List ι) (ha : ∀ i ∈ order, (a.decode i).isFinite = true)
    (hb : ∀ i ∈ order, (b.decode i).isFinite = true)
    (hfinite : Model.isFinite (OCP.MX.Dot fmt a b order) = true) :
    MixedError (-Model.toReal (OCP.MX.Dot fmt a b order))
      (-(((order.map fun i => a.value i * b.value i).sum : ℚ) : ℝ))
      (Model.unitRoundoffAt fmt) (Model.underflowErrorAt fmt) := by
  have hdot := Block.Tensor.Dot_rounding fmt hfmt a b order ha hb hfinite
  roundoff

example {ι γ δ : Type} {F : Block.CodedFormat ι γ} {G : Block.CodedFormat ι δ}
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (a : Block.Tensor F) (b : Block.Tensor G)
    (blocks : List (List ι))
    (ha : ∀ block ∈ blocks, ∀ i ∈ block, (a.decode i).isFinite = true)
    (hb : ∀ block ∈ blocks, ∀ i ∈ block, (b.decode i).isFinite = true)
    (hfinite : Model.isFinite (OCP.MX.DotGeneral fmt a b blocks) = true) :
    MixedError (-Model.toReal (OCP.MX.DotGeneral fmt a b blocks))
      (-(((blocks.map fun block =>
        (block.map fun i => a.value i * b.value i).sum).sum : ℚ) : ℝ))
      (Model.unitRoundoffAt fmt) (Model.underflowErrorAt fmt) := by
  have hdot := Block.Tensor.DotGeneral_rounding fmt hfmt a b blocks ha hb hfinite
  roundoff

end FloatLibTests.Conformance.OCP.MX
